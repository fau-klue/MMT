package info.kwarc.mmt.api.parser

import info.kwarc.mmt.api._
import documents._
import archives.{BuildResult, BuildSuccess, BuildTask, LogicalDependency}
import checking.Interpreter
import frontend.Controller
import modules._
import notations._
import objects._
import opaque._
import patterns._
import symbols._
import utils._

/**
 * This class bundles all state that is maintained by a [[StructureParser]]
 *
 * @param reader the input stream, from which the parser reads (see ps below)
 * @param ps the encapsulated input that contains the buffered reader (also encapsulated in reader!)
 */
class ParserState(val reader: Reader, val ps: ParsingStream, val cont: StructureParserContinuations) {
  /**
   * the namespace mapping set by
   * {{{
   * import prefix URI
   * }}}
   * commands
   *
   * the initial namespace map
   */
  var namespaces = ps.nsMap

  /** the position at which the current StructuralElement started */
  var startPosition = reader.getSourcePosition

  def copy(rd: Reader = reader): ParserState = {
    val s = new ParserState(rd, ps, cont)
    s.namespaces = namespaces
    s
  }

  def makeSourceRef(reg: SourceRegion) = SourceRef(ps.source, reg)

  val errorCont = cont.errorCont
}

/** matches the keyword for a view */
object ViewKey {
  def unapply(s: String): Option[String] = s match {
    case "view" | "morphism" => Some(s)
    case _ => None
  }
}


/**
 * A StructureParser reads MMT declarations (but not objects) and
 * defers to continuation functions for the found StructuralElement, ParsingUnits, and SourceErrors.
 *
 * This class provides 3 things
 *
 * 1) High-level read methods that read MMT-related entities from a stream,
 * which implementing classes can use.
 * These methods throw do not read more than necessary from the stream and
 * throw [[SourceError]] where appropriate.
 *
 * 2) It is stateless and maintains the parse state via an implicit argument of type
 * [[ParserState]] in most functions.
 *
 * 3) It leaves processing of MMT entities application-independently via high-level continuation functions.
 */

// TODO first add all structure, notations, then check semantics

class KeywordBasedParser(objectParser: ObjectParser) extends Parser(objectParser) {
  override val logPrefix = "structure-parser"
  val format = "mmt"

  // *********************************** interface to the controller: add elements and errors etc.

  /**
   * A continuation function called on every StructuralElement that was found
   *
   * For grouping elements (documents, modules with body), this must be called on the empty element first
   * and then on each child, finally end(se) must be called on the grouping element.
   */
  protected def seCont(se: StructuralElement)(implicit state: ParserState) {
    log(se.toString)
    val reg = currentSourceRegion
    SourceRef.update(se, state.makeSourceRef(reg))
    try {
      controller.add(se)
      state.cont.onElement(se)
    } catch {case e: Error =>
      val se = makeError(reg, "error while adding successfully parsed element", Some(e))
      errorCont(se)
    }
  }
  /** called at the end of a document or module, does common bureaucracy */
  protected def end(s: ContainerElement[_])(implicit state: ParserState) {
    //extend source reference until end of element
    SourceRef.get(s) foreach { r =>
      SourceRef.update(s, r.copy(region = r.region.copy(end = state.reader.getSourcePosition - 2)))
      // the -2 seems to be necessary at the end of files (to avoid sourceref errors)
    }
    state.cont.onElementEnd(s)
    log("end " + s.path)
  }

  /** the region from the start of the current structural element to the current position */
  protected def currentSourceRegion(implicit state: ParserState) =
    SourceRegion(state.startPosition, state.reader.getSourcePosition)


  /** like seCont but may wrap in NestedModule */
  private def moduleCont(m: Module, par: HasParentInfo)(implicit state: ParserState) {
    val se = par match {
       case IsDoc(_) => m
       case IsMod(mp, ln) =>
          // mp.name / mname == m.name
          val mname = m.name.dropPrefix(mp.name).getOrElse {throw ImplementationError("illegal name of nested module")}
          val nm = new NestedModule(OMMOD(mp), mname, m)
          nm.setDocumentHome(ln)
          nm
    }
    seCont(se)
  }


  /**
   * A continuation function called on every ParsingUnit that was found
   *
   * Objects are opaque to the parser, and parsing is deferred to objectParser via this function.
   *
   * Fatal errors are recovered from by defaulting to [[DefaultObjectParser]]
   */
  private def puCont(pu: ParsingUnit)(implicit state: ParserState): ParseResult = {
    try {
      objectParser(pu)(state.errorCont)
    } catch {
      case e: Error =>
        val se = makeError(pu.source.region, "error in object, recovered by using default parser", Some(e))
        state.errorCont(se)
        DefaultObjectParser(pu)(state.errorCont)
    }
  }

  /**
   * A continuation function called on every error that occurred
   */
  protected def errorCont(e: => SourceError)(implicit state: ParserState) = {
    state.errorCont(e)
  }
  /** convenience function to create SourceError's */
  protected def makeError(reg: SourceRegion, s: String, causedBy: Option[Exception] = None)(implicit state: ParserState) = {
    val msg = s + causedBy.map(": " + _.getMessage).getOrElse("")
    val e = SourceError("structure-parser", state.makeSourceRef(reg), msg)
    causedBy.foreach {c => e.setCausedBy(c)}
    e
  }


  // ******************************* the entry points

  def apply(ps: ParsingStream)(implicit cont: StructureParserContinuations) = {
    val (se, _) = apply(new ParserState(new Reader(ps.stream), ps, cont))
    se
  }

  private def apply(state: ParserState): (StructuralElement, ParserState) = {
    state.ps.parentInfo match {
       case IsRootDoc(dpath) =>
          val doc = new Document(dpath, root = true, nsMap = state.namespaces)
          seCont(doc)(state)
          logGroup {
            readInDocument(doc)(state)
          }
          end(doc)(state)
          (doc, state)
       case IsRootMod(mpath) => throw LocalError("unsupported")
       case _ => throw LocalError("unsupported")
       /*case IsDoc(dp) =>
          val doc = controller.globalLookup.getAs(classOf[Document],dp)
          readInDocument(doc)(state)
          (???,state)
       case IsMod(mp, rd) =>
          val mod = controller.globalLookup.getAs(classOf[DeclaredModule],mp)
          readInModule(mod, mod.getInnerContext, Nil)(state)
          (???, state)*/
    }
  }

  // ********************************* low level read functions for names, terms, etc.

  /** read a LocalName from the stream
    * throws SourceError iff ill-formed or empty
    */
  def readName(implicit state: ParserState): LocalName = {
    val (s, reg) = state.reader.readToSpace
    if (s == "")
      throw makeError(reg, "name expected")
    try {
      LocalName.parse(s, state.namespaces)
    }
    catch {
      case e: ParseError =>
        throw makeError(reg, "invalid identifier: " + e.getMessage)
    }
  }

  /** read a DPath from the stream
    * throws SourceError iff ill-formed or empty
    */
  def readDPath(implicit state: ParserState): DPath = {
    val (s, reg) = state.reader.readToSpace
    if (s == "")
      throw makeError(reg, "MMT URI expected")
    try {
      val p = Path.parseD(s, state.namespaces)
      p
    }
    catch {
      case e: ParseError =>
        throw makeError(reg, "invalid identifier: " + e.getMessage)
    }
  }

  /** read a MPath from the stream
    * throws SourceError iff ill-formed or empty
    */
  def readMPath(newBase: Path)(implicit state: ParserState): (SourceRef, MPath) = {
    val (s, reg) = state.reader.readToSpace
    if (s == "")
      throw makeError(reg, "MMT URI expected")
    val mp = try {
      Path.parseM(s, state.namespaces(newBase))
    }
    catch {
      case e: ParseError =>
        throw makeError(reg, "invalid identifier: " + e.getMessage)
    }
    val ref = state.makeSourceRef(reg)
    (ref, mp)
  }

  /** read a GlobalName from the stream
    * throws SourceError iff ill-formed or empty
    */
  def readSPath(newBase: Path)(implicit state: ParserState): GlobalName = {
    val (s, reg) = state.reader.readToSpace
    if (s == "")
      throw makeError(reg, "MMT URI expected")
    try {
      Path.parseS(s, state.namespaces(newBase))
    }
    catch {
      case e: ParseError =>
        throw makeError(reg, "invalid identifier: " + e.getMessage)
    }
  }

  /**
   * reads one out of a list of permitted delimiters
 *
   * @param delims the permitted delimiter
   * @return the read delimiter
   * throws SourceError iff anything else found
   */
  def readDelimiter(delims: String*)(implicit state: ParserState): String = {
    val delim = state.reader.readToken
    if (delims.contains(delim._1))
      delim._1
    else
      throw makeError(delim._2, delims.map("'" + _ + "'").mkString("", " or ", "") + "expected")
  }

  /**
   * reads until the object delimiter and parses the found string
 *
   * @return the raw string, the region, and the parsed term
   */
  def readParsedObject(context: Context, topRule: Option[ParsingRule] = None)(implicit state: ParserState): (String, SourceRegion, ParseResult) = {
    val (obj, reg) = state.reader.readObject
    val pu = ParsingUnit(state.makeSourceRef(reg), context, obj, state.namespaces, topRule)
    val pr = puCont(pu)
    (obj, reg, pr)
  }
  
  private def doComponent(c: ComponentKey, tc: TermContainer, cont: Context)(implicit state: ParserState) {
    val (obj, _, pr) = readParsedObject(cont)
    tc.read = obj
    tc.parsed = pr.toTerm
  }

  private val contextRule = ParsingRule(utils.mmt.context, Nil, TextNotation.fromMarkers(Precedence.integer(0), None)(Var(1, true, Some(Delim(",")))))
  /** like doComponent, but expects to find a context (using contextRule notation) */
  private def doContextComponent(cc: ContextContainer, context: Context)(implicit state: ParserState) {
    val (obj, reg, pr) = readParsedObject(context, Some(contextRule))
    cc.read = obj
    val cont: Context = pr.term match {
      case OMBINDC(OMS(utils.mmt.context), cont, Nil) =>
        cont
      case _ =>
        errorCont(makeError(reg, "not a context: " + controller.presenter.asString(pr.toTerm)))
        Context.empty
    }
    cc.parsed = cont
    cc.unknowns = pr.unknown
    cc.free = pr.free
  }
/*
    val cont = ParseResult.fromTerm(p) match {

*/
  
  
  
  private def doNotation(c: NotationComponentKey, nc: NotationContainer, treg: SourceRegion)(implicit state: ParserState) {
    val notString = state.reader.readObject._1
    if (nc(c).isDefined)
      errorCont(makeError(treg, "notation of this constant already given, ignored"))
    else {
      val notation = TextNotation.parse(notString, state.namespaces)
      nc(c) = notation
    }
  }

  /** resolve a name in the domain of a link and insert the necessary ComplexStep */
  protected def resolveAssignmentName[A <: Declaration](cls: Class[A], home: Term, name: LocalName)(implicit state: ParserState) = {
    TheoryExp.getSupport(home) foreach {p => controller.simplifier(p)}
    controller.globalLookup.resolve(home, name) match {
      case Some(d: Declaration) if cls.isInstance(d) =>
        ComplexStep(d.parent) / d.name
      case Some(_) =>
        errorCont(makeError(currentSourceRegion, "not a declaration name of the right type: " + name))
        name
      case None =>
        errorCont(makeError(currentSourceRegion, "unknown or ambiguous name: " + name))
        name
    }
  }

  // *************** the two major methods for reading in documents and modules

  /** the main loop for reading declarations that can occur in documents
    *
    * @param doc the containing Document (must be in the controller already)
    */
  private def readInDocument(doc: Document)(implicit state: ParserState) {
    if (state.reader.endOfDocument) return
    val (keyword, reg) = state.reader.readToken
    val parentInfo = IsDoc(doc.path)
    state.startPosition = reg.start
    try {
      keyword match {
        case "" =>
          if (state.reader.endOfDocument) {
            return
          } else
            throw makeError(reg, "keyword expected, within " + doc).copy(level = Level.Fatal)
        case "document" =>
          val name = readName
          val dpath = doc.path / name
          val d = new Document(dpath, nsMap = state.namespaces)
          seCont(d)
          logGroup {
            readInDocument(d)
          }
          end(d)
          //TODO awkward hack, avoid the FS delimiter of d to make the end-of-document check doc succeed as well
          state.reader.forceLastDelimiter(Reader.GS.toChar.toInt)
        case "ref" =>
          val (_,path) = readMPath(DPath(state.namespaces.default))
          seCont(MRef(doc.path,path))
        case "/" =>
            val oe = readOpaque(parentInfo, Context.empty)
            seCont(oe)
        case "namespace" =>
          // default namespace is set relative to current default namespace
          val ns = readDPath
          state.namespaces = state.namespaces(DPath(ns.uri))
        case "import" =>
          val (n, _) = state.reader.readToken
          val ns = readDPath
          state.namespaces = state.namespaces.add(n, ns.uri)
        case "theory" =>
          readTheory(parentInfo, Context.empty)
        case ViewKey(_) => readView(parentInfo, Context.empty, isImplicit = false)
        case "implicit" =>
          val (keyword2, reg2) = state.reader.readToken
          keyword2 match {
            case ViewKey(_) => readView(parentInfo, Context.empty, isImplicit = true)
            case _ => throw makeError(reg2, "only views can be implicit here")
          }
        case k =>
          // other keywords are treated as parser plugins
          val extParser = getParseExt(doc, k).getOrElse {
            throw makeError(reg, "unknown keyword: " + k)
          }
          val (mod, mreg) = state.reader.readModule
          val reader = Reader(mod)
          reader.setSourcePosition(mreg.start)
          val pea = new ParserExtensionArguments(this, state.copy(reader), doc, k)
          extParser(pea) foreach {
            case m: Module => moduleCont(m, parentInfo)
            case _ => throw makeError(reg, "parser extension returned non-module")
          }
      }
      // check that the reader is at the end of a module level declaration, throws error otherwise
      if (!state.reader.endOfModule) {
        val (rest, reg) = state.reader.readModule
        if (rest != "")
          throw makeError(reg, "extraneous tokens, ignored: " + rest)
      }
    } catch {
      case e: Error =>
        val se = e match {
          case e: SourceError => e
          case e => makeError(currentSourceRegion, "error in module", Some(e))
        }
        errorCont(se)
        if (!state.reader.endOfModule)
          state.reader.readModule
    }
    readInDocument(doc) // compiled code is not actually tail-recursive
  }

  /** the main loop for reading declarations that can occur in a theory
 *
    * @param mod the containing module (added already)
    * @param context the context (including the containing module)
    * @param patterns the patterns of the meta-theory (precomputed in readInDocument)
    *
    * this function handles one declaration if possible, then calls itself recursively
    */
  def readInModule(mod: Body, context: Context, features: Features)(implicit state: ParserState) {
     readInModuleAux(mod, mod.asDocument.path, context, features)
  }

  private def readInModuleAux(mod: Body, docHome: DPath, context: Context, features: Features)(implicit state: ParserState) {
    //This would make the last RS marker of a module optional, but it's problematic with nested modules.
    //if (state.reader.endOfModule) return
    val linkOpt = mod match {
      case l: DeclaredLink => Some(l)
      case _ => None
    }
    val mpath = mod.path.toMPath // non-trivial only for structures
    /** the root name of all sections and the LocalName of the currentSection */
    val docRoot = mpath.toDPath
    val currentSection = docHome.dropPrefix(docRoot).getOrElse {
       throw ImplementationError("document home must extend content home")
    }
    lazy val parentInfo = IsMod(mpath, currentSection)
    /* declarations must only be added through this method */
    def addDeclaration(d: Declaration) {
       d.setDocumentHome(currentSection)
       seCont(d)
    }
    // to be set if the section changes
    var nextSection = currentSection
    try {
      val (keyword, reg) = state.reader.readToken
      state.startPosition = reg.start
      def fail(s: String) = throw makeError(reg, s)
      keyword match {
        //this case occurs if we read the GS marker
        case "" =>
          if (state.reader.endOfModule) {
            return
          } else
            fail("keyword expected, within module " + mod.path)
        //Constant
        case "constant" =>
          val name = readName
          val c = readConstant(name, mpath, linkOpt, context)
          addDeclaration(c)
        //PlainInclude
        case "include" =>
          mod match {
            case thy: DeclaredTheory =>
              val (fromRef, from) = readMPath(thy.path)
              val incl = PlainInclude(from, thy.path)
              SourceRef.update(incl.from, fromRef) //TODO awkward, same problem for metatheory
              addDeclaration(incl)
            case link: DeclaredLink =>
              val (fromRef, from) = readMPath(link.path)
              readDelimiter("=")
              val (inclRef, incl) = readMPath(link.path)
              //readParsedObject(view.to)
              val as = PlainViewInclude(link.toTerm, from, incl)
              SourceRef.update(as.from, fromRef)
              SourceRef.update(as.df, inclRef)
              addDeclaration(as)
          }
        case "structure" =>
          mod match {
            case thy: DeclaredTheory => readStructure(parentInfo, linkOpt, context, isImplicit = false)
            case link: DeclaredLink =>
              val name = readName
              val orig = controller.get(link.from.toMPath ? name) match {
                case s: Structure => s
                case _ => fail("not a structure: "+link.from.toMPath?name)
              }
              readDelimiter("=")
              val incl = readSPath(link.path)
              val target = controller.get(incl) match {
                case s: Link => s
                case _ => fail("not a link: "+incl)
              }
              val as = DefLinkAssignment(link.toTerm,name,target.from,target.toTerm)
              // SourceRef.update(as.df,SourceRef.fromURI(URI.apply(target.path.toString)))
              // SourceRef.update(as.from,SourceRef.fromURI(URI.apply(orig.path.toString)))
              addDeclaration(as)
          }
        case "theory" => readTheory(parentInfo, context)
        case ViewKey(_) => readView(parentInfo, context, isImplicit = false)
        case k if k.forall(_ == '#') =>
            val currentLevel = currentSection.length
            val thisLevel = k.length
            val (nameTitle,reg) = state.reader.readDeclaration
            // close all sections from currentLevel up to and including thisLevel
            if (thisLevel <= currentLevel) {
               Range(currentLevel,thisLevel-1,-1).foreach {l =>
                  mod.asDocument.getLocally(currentSection.take(l)).foreach {
                    case d: Document => end(d)
                  }
               }
               nextSection = currentSection.take(thisLevel-1)
            }
            if (nameTitle.isEmpty) {
               // just end a section: #...#
               if (thisLevel > currentLevel) {
                  throw makeError(reg, s"no document at level $thisLevel open")
               }
            } else {
               // additionally begin a new section: #...# :NAME TITLE  or #...# TITLE
               if (thisLevel > currentLevel+1) {
                  throw makeError(reg, s"no document at level ${thisLevel-1} open")
               }
               val (name,title) = if (nameTitle.startsWith(":")) {
                  val pos = nameTitle.indexWhere(_.isWhitespace)
                  (nameTitle.substring(1,pos),nameTitle.substring(pos).trim)
               } else {
                  // at this point, nextSection is the current section, i.e., the parent of the one to be opened
                  val name = mod.asDocument.getLocally(nextSection) match {
                     case Some(d) => "section_" + (d.getDeclarations.length+1)
                     case _ => throw ImplementationError("section not found")
                  }
                  (name, nameTitle)
               }
               nextSection = nextSection / name
               val innerDoc = new Document(docRoot / nextSection, contentAncestor = Some(mod))
               NarrativeMetadata.title.update(innerDoc, title)
               seCont(innerDoc)
            }
        case "/" =>
            val oe = readOpaque(parentInfo, context)
            seCont(oe)
        //instances of patterns
        case "instance" =>
          mod match {
            case thy: DeclaredTheory =>
              val patS = readName
              val pat = listmap(features.patterns, patS).getOrElse {
                fail("unknown pattern: " + patS)
              }
              val i = readInstance(pat, thy.path)
              addDeclaration(i)
            case link: DeclaredLink =>
              fail("instance declaration in link")
          }
        case "implicit" =>
          val (keyword2, reg2) = state.reader.readToken
          keyword2 match {
            case ViewKey(_) => readView(parentInfo, context, isImplicit = true)
            case "structure" => readStructure(parentInfo, linkOpt, context, isImplicit = true)
            case _ => throw makeError(reg2, "only links can be implicit here")
          }
        case k =>
          // other keywords are treated as ...
          val featureOpt = listmap(features.features, k)
          featureOpt match {
            case Some(sf) =>
              // 0) a derived declarations for a StructuralFeature visible to the theory
              readDerivedDeclaration(sf, parentInfo, context)
            case None =>
              val patOpt = listmap(features.patterns, LocalName.parse(k))
              patOpt match {
                case Some(pattern) =>
                  // 1) an instance of a Pattern with LocalName k visible in meta-theory
                  val i = readInstance(pattern, mpath)
                  addDeclaration(i)
                case None =>
                  val parsOpt = getParseExt(mod, k)
                  if (parsOpt.isDefined) {
                    // 2) a parser extension identified by k
                    val (decl, reg) = state.reader.readDeclaration
                    val reader = Reader(decl)
                    reader.setSourcePosition(reg.start)
                    val se = if (currentSection.length == 0) mod
                    else mod.asDocument.getLocally(currentSection).getOrElse {
                      throw ImplementationError("section not found in module")
                    }
                    val pea = new ParserExtensionArguments(this, state.copy(reader), se, k, context)
                    val dO = parsOpt.get.apply(pea)
                    dO foreach {
                      case d: Declaration => addDeclaration(d)
                      case _ => throw makeError(reg, "parser extension returned non-declaration")
                    }
                  } else {
                    // 3) a constant with name k
                    val name = LocalName.parse(k)
                    val c = readConstant(name, mpath, linkOpt, context)
                    addDeclaration(c)
                  }
              }
          }
      }
      if (!state.reader.endOfDeclaration) {
        val (rest, reg) = state.reader.readDeclaration
        if (rest != "")
          throw makeError(reg, "end of declaration expected, found and ignored: " + rest)
      }
    } catch {
      case e: Error =>
        // wrap in source error if not source error already
        val se: SourceError = e match {
          case se: SourceError => se
          case _ => makeError(currentSourceRegion, "error in declaration", Some(e))
        }
        errorCont(se)
        if (!state.reader.endOfDeclaration)
          state.reader.readDeclaration
    }
    readInModuleAux(mod, docRoot / nextSection, context, features) // compiled code is not actually tail-recursive
  }

  /** auxiliary function to read Theories
    *
    * @param parent the containing document or module (if any)
    * @param context the context (excluding the theory to be read)
    */
  private def readTheory(parent: HasParentInfo, context: Context)(implicit state: ParserState) {
    val rname = readName
    val (ns, name) = parent match {
      case IsDoc(doc) =>
        val ns = DPath(state.namespaces.default)
        val mref = MRef(doc, ns ? rname)
        mref.setOrigin(GeneratedMRef)
        seCont(mref)
        (ns, rname)
      case IsMod(mod,_) =>
        (mod.doc, mod.name / rname)
    }
    val tpath = ns ? name
    var delim = state.reader.readToken
    val metaReg = if (delim._1 == ":") {
      val (r,m) = readMPath(tpath)
      delim = state.reader.readToken
      Some((m,r))
    } else
      None
    val meta = (metaReg,parent) match {
      case (Some((p,_)),_) => Some(p)
      case _ => None
    }
    val contextMeta = meta match {
      case Some(p) => context ++ p
      case _ => context
    }
    val paramC = new ContextContainer
    if (delim._1 == ">") {
      doContextComponent(paramC, contextMeta)
      delim = state.reader.readToken
    }
    val contextMetaParams = paramC.get match {
      case None => contextMeta
      case Some(params) => contextMeta ++ params
    }
    val dfC = new TermContainer
    if (delim._1 == "abbrev" || delim._1 == "extends") {
      doComponent(DefComponent,  dfC, contextMetaParams)
      delim = state.reader.readToken
    }
    val t = new DeclaredTheory(ns, name, meta, paramC, dfC)
    metaReg foreach {case (_,r) => SourceRef.update(t.metaC.get.get, r)} //awkward, but needed attach a region to the meta-theory; same problem for structure domains
    moduleCont(t, parent)
    if (delim._1 == "") {
      end(t)
    } else if (delim._1 == "=") {
      val features = getFeatures(contextMeta)
      logGroup {
        readInModule(t, context ++ t.getInnerContext, features)
      }
      end(t)
    } else {
      throw makeError(delim._2, "':' or '=' or 'abbrev' expected")
    }
  }

  /** auxiliary function to read views
    *
    * @param parent the containing document/module
    * @param context the context (excluding the view to be read)
    * @param isImplicit whether the view is implicit
    */
  private def readView(parent: HasParentInfo, context: Context, isImplicit: Boolean)(implicit state: ParserState) {
    val rname = readName
    val (ns, name) = parent match {
      case IsDoc(doc) =>
        val ns = DPath(state.namespaces.default)
        val mref = MRef(doc, ns ? rname)
        mref.setOrigin(GeneratedMRef)
        seCont(mref)
        (ns, rname)
      case IsMod(mod,_) =>
        (mod.doc, mod.name / rname)
    }
    val vpath = ns ? name
    readDelimiter(":")
    val (fromRef, fromPath) = readMPath(vpath)
    val from = OMMOD(fromPath)
    SourceRef.update(from, fromRef)
    readDelimiter("->", "→")
    val (toRef, toPath) = readMPath(vpath)
    val to = OMMOD(toPath)
    SourceRef.update(to, toRef)
    readDelimiter("abbrev", "=") match {
      case "abbrev" =>
        val (_, _, df) = readParsedObject(context)
        val v = DefinedView(ns, name, from, to, df.toTerm, isImplicit)
        moduleCont(v, parent)
      case "=" =>
        val v = new DeclaredView(ns, name, from, to, isImplicit) // TODO add metamorph?
        moduleCont(v, parent)
        logGroup {
          readInModule(v, context ++ v.getInnerContext, noFeatures)
        }
        end(v)
    }
  }

  /**
   * allow to control certain parser extensions
   * i.e. those with side effects like [[RuleConstantParser]]
   */
  protected def getParseExt(se: StructuralElement, key: String): Option[ParserExtension] =
    controller.extman.getParserExtension(se, key)

  /** holds the structural features and patterns that are available during parsing */
  protected class Features(val features: List[(String,StructuralFeature)], val patterns: List[(LocalName,(StructuralFeature,DerivedDeclaration))]) {
    def +(f : Features) = new Features((features ::: f.features).distinct,(patterns ::: f.patterns).distinct)
  }
  protected val noFeatures = new Features(Nil,Nil)
  
  /** auxiliary function to collect all structural feature rules in a given context */
  protected def getFeatures(mp: MPath): Features = {
    controller.simplifier(mp)
    var fs: List[(String,StructuralFeature)] = Nil
    var ps: List[(LocalName,(StructuralFeature,DerivedDeclaration))] = Nil
    controller.globalLookup.getDeclarationsInScope(OMMOD(mp)).foreach {
      case rc: RuleConstant => rc.df.foreach {
        case r: StructuralFeatureRule =>
          controller.extman.get(classOf[StructuralFeature], r.feature) match {
            case Some(sf) =>
              fs ::= r.feature -> sf
            case None =>
              // maybe generate warning; error will be thrown anyway when the rule constant is checked
          }
        case _ =>
      }
      case dd @ Pattern(_,_,_,_) =>
        controller.extman.get(classOf[StructuralFeature], Instance.feature) match {
          case Some(sf) =>
            ps ::= dd.name -> (sf, dd)
          case None =>
        }
      case _ =>
    }
    new Features(fs, ps)
  }
  protected def getFeatures(cont : Context) : Features = cont.collect({
    case IncludeVarDecl(_,OMPMOD(mp,_),_) => getFeatures(mp)
  }).foldLeft(noFeatures)((a,b) => a+b)

  /** auxiliary method for reading declarations that reads a list of components
   *  @param context the current context
   *  @param expected the components to read as (initial delimiter, (key, container))
   *  @param until an initial delimiter that stops parsing components
   *  @return true if the delimiter until was found; false if end of declaration was found
   */
  // TODO use this in readConstant
  private def readComponents(context: Context, expected: List[(String,(ComponentKey,ComponentContainer))], until: Option[String])(implicit state: ParserState): Boolean = {
     while (!state.reader.endOfDeclaration) {
       val (delim, treg) = state.reader.readToken
       if (until contains delim) return true
       listmap(expected, delim) match {
          case Some((key,cont)) =>
            if (cont.isDefined) {
              errorCont(makeError(treg, s"component $key already given, ignored"))
              state.reader.readObject
            } else {
              (key,cont) match {
                case (_, tc: TermContainer) =>
                  doComponent(key, tc, context)
                case (_, cc: ContextContainer) =>
                  doContextComponent(cc, context)
                case (nk: NotationComponentKey, nc: NotationContainer) =>
                  doNotation(nk, nc, treg)
                case _ => throw ImplementationError("illegal component")
              }
            }
          case None =>
            errorCont(makeError(treg, s"component $delim not expected, ignored"))
            state.reader.endOfObject
       }
     }
     return false
  }
  /** auxiliary function to build input for readComponents for notation components */
  private def notationComponentSpec(nc: NotationContainer) =
    List("#" -> ParsingNotationComponent, "##" -> PresentationNotationComponent).map{case (s,k) => s -> (k,nc)} 

  /** reads the components of a [[Constant]]
 *
    * @param givenName the name of the constant
    * @param parent the containing [[DeclaredModule]]
    * @param link the home theory for term components
    */
  private def readConstant(givenName: LocalName, parent: MPath, link: Option[DeclaredLink],
                           context: Context)(implicit state: ParserState): Constant = {
    val name = link.map {l => resolveAssignmentName(classOf[Constant], l.from, givenName)}.getOrElse(givenName)
    val cpath = parent ? name
    //initialize all components as omitted
    val tpC = new TermContainer
    val dfC = new TermContainer
    var al: List[LocalName] = Nil
    val nt = new NotationContainer
    var rl: Option[String] = None
    val cons = Constant(OMMOD(parent), name, Nil, tpC, dfC, None, nt)
    // every iteration reads one delimiter and one object
    // @ alias or : TYPE or = DEFINIENS or #(#) NOTATION
    val keys = List(":", "=", "#", "##", "@", "role")
    val keyString = keys.map("'" + _ + "'").mkString(", ")

    while (!state.reader.endOfDeclaration) {
      val (delim, treg) = state.reader.readToken
      try {
        // branch based on the delimiter
        delim match {
          case ":" =>
            if (tpC.read.isDefined) {
              errorCont(makeError(treg, "type of this constant already given, ignored"))
              state.reader.readObject
            } else
              doComponent(TypeComponent, tpC, context)
          case "=" =>
            if (dfC.read.isDefined) {
              errorCont(makeError(treg, "definiens of this constant already given, ignored"))
              state.reader.readObject
            } else
              doComponent(DefComponent, dfC, context)
          case "#" =>
            doNotation(ParsingNotationComponent, nt, treg)
          case "##" =>
            doNotation(PresentationNotationComponent, nt, treg)
          case "@" =>
            val (str, _) = state.reader.readObject
            al ::= LocalName.parse(str)
          case "role" =>
            val (str, _) = state.reader.readObject
            rl = Some(str)
          case k => getParseExt(cons, k) match {
            case Some(parser) =>
              val (obj, reg) = state.reader.readObject
              val reader = Reader(obj)
              reader.setSourcePosition(reg.start)
              val pea = new ParserExtensionArguments(this, state.copy(reader), cons, k, context) 
              val tO = parser(pea)
              tO foreach {
                case d => throw makeError(reg, "parser extension in constant may not return anything")
              }
            case None =>
              if (!state.reader.endOfDeclaration) {
                errorCont(makeError(treg, "expected " + keyString + ", found " + k))
              } else if (k != "") {
                if (!state.reader.endOfObject)
                  state.reader.readObject
                errorCont(makeError(treg, "expected " + keyString + ", ignoring the next object"))
              }
          }
        }
      } catch {
        case e: Exception =>
          errorCont(makeError(treg, " error in object", Some(e)))
          if (!state.reader.endOfObject)
             state.reader.readObject
      }
    }
    val constant = Constant(OMMOD(parent), name, al, tpC, dfC, rl, nt)
    constant.metadata = cons.metadata
    constant
  }

  /** auxiliary function to read structures
 *
    * @param parentInfo the containing module
    * @param context the context (excluding the structure to be read)
    * @param isImplicit whether the structure is implicit
    */
  private def readStructure(parentInfo: IsMod, link: Option[DeclaredLink], context: Context,
                            isImplicit: Boolean)(implicit state: ParserState) {
    val givenName = readName
    val name = link.map {l => resolveAssignmentName(classOf[Structure], l.from, givenName)}.getOrElse(givenName)
    val spath = parentInfo.modParent ? name
    readDelimiter(":")
    val tpC = new TermContainer
    //doComponent(TypeComponent, tpC, context)
    val tp = OMMOD(readMPath(spath)._2)
    tpC.parsed = tp
    val s = new DeclaredStructure(OMMOD(parentInfo.modParent), name, tpC, isImplicit) // TODO add metamorph?
    s.setDocumentHome(parentInfo.relDocParent)
    seCont(s)
    if (state.reader.endOfDeclaration) {
      // s: tp RS
      end(s)
      return
    }
    val (t, reg) = state.reader.readToken
    t match {
      case "=" =>
        // s : tp US = body GS
        logGroup {
          readInModule(s, context, noFeatures)
        }
      case "" =>
        // good: s : tp US RS
        // bad:  s : tp US _
        if (!state.reader.endOfDeclaration)
          throw makeError(reg, "'=' or end of declaration expected, within structure " + spath)
      case _ =>
        // s : tp US _
        throw makeError(reg, "'=' or end of declaration expected, within structure " + spath)
    }
    end(s)
  }

  /** reads the header of a [[DerivedDeclaration]] */
  private def readDerivedDeclaration(feature: StructuralFeature, parentInfo: IsMod, context: Context)(implicit state: ParserState) = {
    val parent = parentInfo.modParent
    val pr = feature.getHeaderRule
    val (_, reg, header) = readParsedObject(context, Some(pr))
    val (name, tp) = feature.processHeader(header.term)
    SourceRef.update(tp, state.makeSourceRef(reg))
    val tpC = TermContainer(header.copy(term = tp).toTerm)
    val notC = new NotationContainer
    val compSpecs = notationComponentSpec(notC)
    val equalFound = readComponents(context, compSpecs, Some(feature.bodyDelim))
    val dd = new DerivedDeclaration(OMID(parent), name, feature.feature, TermContainer(tp), notC)
    dd.setDocumentHome(parentInfo.relDocParent)
    seCont(dd)
    if (equalFound) {
       //TODO calling the simplifier here is a hack that is not allowed 
       //val innerContext = controller.simplifier.elaborateContext(context,feature.getInnerContext(dd))
       val innerContext = feature.getInnerContext(dd)
       val features = getFeatures(parent)
       readInModule(dd.module, context ++ innerContext, features)
    }
    end(dd.module) //TODO is this correct?
  }

  /** returns an instance of [[InstanceFeature]]
   *  
   *  parses 'pattern(name, args) NOTATIONS' where name is a free variable for the name of the instance */
  private def readInstance(instFeatPattern: (StructuralFeature,DerivedDeclaration), tpath: MPath)(implicit state: ParserState): DerivedDeclaration = {
    val (instFeat, pattern) = instFeatPattern
    val context = Context(tpath)
    val patNot = pattern.notC.parsing map {n => ParsingRule(pattern.modulePath, Nil, n)}
    val (_, reg, pr) = readParsedObject(context, patNot)
    val (name,tp) = instFeat.processHeader(pr.term)
    SourceRef.update(tp, state.makeSourceRef(reg))
    val tpC = TermContainer(pr.copy(term = tp).toTerm)
    val nc = NotationContainer()
    readComponents(context, notationComponentSpec(nc), None)
    Instance(OMMOD(tpath), name, tpC, nc)
  }
  
  private def readOpaque(pi: HasParentInfo, context: Context)(implicit state: ParserState): OpaqueElement = {
      val (format, freg) = state.reader.readToken
      val oi = controller.extman.get(classOf[OpaqueTextParser], format).getOrElse {
         throw makeError(freg, "unknown opaque format: " + format)
      }
      val (text, treg) = pi match {
         case _:IsDoc => state.reader.readModule
         case _:IsMod => state.reader.readDeclaration
      }
      val pu = ParsingUnit(state.makeSourceRef(treg), context, text, state.namespaces)
      oi.fromString(objectParser, pi.docParent, pu)(state.errorCont)
   }
}


/**
  * estimates the [[archives.BuildResult]] of an mmt [[Interpreter]] by using the [[StructureParser]] superficially
  */
trait MMTStructureEstimator {self: Interpreter =>
  private var used: List[MPath] = Nil
  private var provided: List[MPath] = Nil

  override def estimateResult(bt: BuildTask) = {
    if (bt.isDir) BuildSuccess(Nil, Nil)
    else {
      val (dp, ps) = buildTaskToParsingStream(bt)
      used = Nil
      provided = Nil
      parser(ps)(new StructureParserContinuations(bt.errorCont))
      // convert i.e. p?NatRules/NatOnly to p?NatRules
      used = used.map { mp =>
        val steps = mp.name.steps
        if (steps.isEmpty) mp else MPath(mp.parent, List(steps.head))
      }
      used = used.distinct
      provided = provided.distinct
      used = used diff provided
      BuildSuccess(used map LogicalDependency, provided map LogicalDependency)
    }
  }

  private lazy val parser = new KeywordBasedParser(DefaultObjectParser) {
    self.initOther(this)
    private object AddUsed extends StatelessTraverser {
      def traverse(t: Term)(implicit con : Context, init: Unit) = t match {
        case OMMOD(p) =>
          used ::= p
          t
        case _ => Traverser(this, t)
      }
    }

    override def seCont(se: StructuralElement)(implicit state: ParserState) = se match {
      case t: Theory =>
        provided ::= t.path
        t match {
          case t: DeclaredTheory =>
            t.meta foreach { m => used ::= m }
          case t: DefinedTheory =>
            AddUsed(t.df, Context.empty)
        }
      case v: View =>
        provided ::= v.path
        AddUsed(v.from, Context.empty)
        AddUsed(v.to, Context.empty)
      case s: Structure =>
        AddUsed(s.from, Context.empty)
      case _ =>
    }

    // below: trivialize methods that are not needed for structure estimation

    override def resolveAssignmentName[A](cls: Class[A], home: Term, name: LocalName)(implicit state: ParserState) = name
    override def getFeatures(m: MPath) = noFeatures
    override def errorCont(e: => SourceError)(implicit state: ParserState) {}
    override def getParseExt(se: StructuralElement, key: String): Option[ParserExtension] = key match {
      case "rule" => None
      case _ =>
        super.getParseExt(se, key)
    }
    override def end(s: ContainerElement[_])(implicit state: ParserState) {}
  }
}
