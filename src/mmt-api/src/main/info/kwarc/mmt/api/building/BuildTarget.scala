package info.kwarc.mmt.api.building

import info.kwarc.mmt.api.Level.Level
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.archives._
import info.kwarc.mmt.api.frontend._
import info.kwarc.mmt.api.utils._

/*
case class TestModifiers(compareWithTest: Boolean = false, addTest: Boolean = false, updateTest: Boolean = false) {
  def makeTests: Boolean = compareWithTest || addTest || updateTest
}

sealed abstract class BuildTargetModifier {
  def toString(dim: String): String
}

case object Clean extends BuildTargetModifier {
  def toString(dim: String) = "-" + dim
}

case class BuildDepsFirst(update: Update) extends BuildTargetModifier {
  def toString(dim: String) = dim + "&"
}

case class Update(errorLevel: Level, dryRun: Boolean = false, testOpts: TestModifiers = TestModifiers(),
                  dependencyLevel: Option[Level] = Some(Level.Ignore)) {
  def key: String =
    if (errorLevel <= Level.Force) ""
    else if (errorLevel < Level.Ignore) "!" else "*"

  def toString(dim: String) = dim + key

  // use dependency level for dependencies
  def forDependencies: Update = dependencyLevel match {
    case None => this
    case Some(level) => Update(level, dryRun, testOpts, None)
  }

  // simple choice which update policy to use in favor of forcing
  def merge(up: Update): Update =
    if (up.errorLevel < errorLevel) up else this
}

case class Build(update: Update) extends BuildTargetModifier {
  def toString(dim: String) = dim
}

/** forces building independent of status */
object Build extends Build(Update(Level.Force, dependencyLevel = Some(Level.Force)))
*/

/*
object BuildTargetModifier {

  def optDescrs: OptionDescrs = List(
    OptionDescr("clean", "", NoArg, "clean up"),
    OptionDescr("depsFirst", "", OptIntArg, "treat dependencies first"),
    OptionDescr("depsFirst?", "", OptIntArg, "dry-run dependencies first"),
    OptionDescr("onError", "", OptIntArg, "rebuild on error or change"),
    OptionDescr("onError?", "", OptIntArg, "dry-run on error or change"),
    OptionDescr("onChange", "", NoArg, "rebuild on change"),
    OptionDescr("dry-run", "n", NoArg, "only show what needs to be build"),
    OptionDescr("forceDeps", "", OptIntArg, "force building and allow to force dependencies"),
    OptionDescr("force", "", NoArg, "force building"),
    OptionDescr("test", "", NoArg, "compare build results with test dimension"),
    OptionDescr("test-add", "", NoArg, "add new output files to test dimension"),
    OptionDescr("test-update", "", NoArg, "update changed output files in test dimension")
  )

  private def flagToLevel(flag: OptionValue, default: Level) = flag match {
    case IntVal(i) => i - 1
    case _ => default
  }

  private def makeUpdateModifier(flag: OptionValue, dry: Boolean, testMod: TestModifiers): Update = Update(
    flagToLevel(flag, Level.Error),
    dryRun = dry,
    testMod)

  private def makeTestModifiers(m: OptionMap): TestModifiers = TestModifiers(
    compareWithTest = m.isDefinedAt("test"),
    addTest = m.isDefinedAt("test-add"),
    updateTest = m.isDefinedAt("test-update"))

  def splitArgs(args: List[String], log: String => Unit): Option[(BuildTargetModifier, List[String])] = {
    val (m, r) = AnaArgs(optDescrs, args)
    val dr = m.isDefinedAt("dry-run")
    val clean = m.get("clean").toList
    val force = m.get("force").toList
    val forceDeps = m.get("forceDeps").toList
    val onChange = m.get("onChange").toList
    val onError = m.get("onError").toList
    val onErrorDry = m.get("onError?").toList
    val depsFirst = m.get("depsFirst").toList
    val depsFirstDry = m.get("depsFirst?").toList
    val os = clean ++ force ++ forceDeps ++ onChange ++ onError ++ onErrorDry ++ depsFirst ++ depsFirstDry
    val testMod = makeTestModifiers(m)
    var fail = false
    var mod: BuildTargetModifier = Build(Update(Level.Ignore, dryRun = dr, testMod))
    if (os.length > 1) {
      log("only one allowed of: clean, force, forceDeps, onChange, onError, depsFirst")
      fail = true
    }
    if (dr && clean.nonEmpty) {
      log("dry-run not possible for clean")
      fail = true
    }
    clean.foreach { _ =>
      mod = Clean
    }
    force.foreach { _ =>
      mod = Build(Update(Level.Force, dryRun = dr, testMod))
    }
    forceDeps.foreach { o =>
      mod = Build(Update(Level.Force, dryRun = dr, testMod, Some(flagToLevel(o, Level.Force))))
    }
    onChange.foreach { _ =>
      mod = Build(Update(Level.Ignore, dryRun = dr, testMod))
    }
    onError.foreach { o =>
      mod = Build(makeUpdateModifier(o, dr, testMod))
    }
    onErrorDry.foreach { o =>
      mod = Build(makeUpdateModifier(o, dry = true, testMod))
    }
    depsFirst.foreach { o =>
      mod = BuildDepsFirst(makeUpdateModifier(o, dr, testMod))
    }
    depsFirstDry.foreach { o =>
      mod = BuildDepsFirst(makeUpdateModifier(o, dry = true, testMod))
    }
    if (fail) {
      usageMessage(optDescrs).foreach(println)
      None
    } else {
      Some((mod, r))
    }
  }
}

/* a trait for parsing options of extensions **/
trait BuildTargetArguments {
  buildtarget: BuildTarget =>

  def verbOpts: OptionDescrs = List(
    OptionDescr("quiet", "q", NoArg, "do not show result information"),
    OptionDescr("verbose", "v", NoArg, "show log information")
  )

  /** options to be overridden by subclasses */
  def buildOpts: OptionDescrs = Nil

  /** the map computed from buildOpts */
  protected var optionsMap: OptionMap = Map.empty
  /** arguments to be consumed by subclasses */
  protected var remainingStartArguments: List[String] = Nil
  var verbose: Boolean = false
  var quiet: Boolean = false

  def anaStartArgs(args: List[String]) {
    val (m, rest) = AnaArgs(verbOpts ++ buildOpts, args)
    optionsMap = m
    remainingStartArguments = rest
    verbose = m.isDefinedAt("verbose")
    quiet = m.isDefinedAt("quiet")
    if (!quiet) report.groups += key + "-result" // ensure logging if non-quiet
    if (verbose) report.groups += key
    val (otherOpts, _) = splitOptions(rest)
    if (otherOpts.nonEmpty) {
      logError("unknown option: " + otherOpts.mkString(" "))
    }
  }
}
*/

/** A BuildTarget provides build/update/clean methods that generate one or more dimensions in an [[Archive]]
  * from an input dimension.
  */
abstract class BuildTarget extends FormatBasedExtension {
  /** a string identifying this build target, used for parsing commands, logging, error messages */
  def key: String

  def isApplicable(format: String): Boolean = format == key

  /** defaults to the key */
  override def logPrefix: String = key

  /** build or update this target in a given archive */
  def build(a: Archive, /* up: Update,*/ in: FilePath): Unit

  /** clean this target in a given archive */
  def clean(a: Archive, in: FilePath): Unit

  /** the main function to run the build target
    *
    * en empty in filepath addresses the whole archive
    *
    * param modifier chooses build, clean, or update
    * @param arch     the archive to build on
    * @param in       the folder inside the archive's inDim folder to which building is restricted
    */
  def apply(/* modifier: BuildTargetModifier,*/ arch: Archive, in: FilePath) { build(arch,in)
    /*
    modifier match {
      case Build(up) => build(arch, up, in)
      case BuildDepsFirst(up) => buildDepsFirst(arch, up, in)
      case Clean => clean(arch, in)
    }
    */
  }

  /** auxiliary method for deleting a file */
  protected def delete(f: File) {
    if (f.exists) {
      log("deleting " + f)
      f.deleteDir
    }
  }
}

/** This abstract class provides common functionality for [[BuildTarget]]s that traverse all files in the input dimension.
  *
  * It implements BuildTarget in terms of the abstract method buildFile called to build a file in the archive.
  * It is also possible to override the method buildDir to post process directory content.
  */
abstract class TraversingBuildTarget extends BuildTarget {

  // ***************** abstract or overridable methods for configuring basic properties such as file extensions

  /** the input dimension/archive folder */
  def inDim: ArchiveDimension

  /** the output archive folder */
  def outDim: ArchiveDimension

  /** the name that is used for the special file representing the containing folder, empty by default */
  protected val folderName = ""

  /** the file extension used for generated files, defaults to outDim, override as needed */
  def outExt: String = outDim match {
    case Dim(path@_*) => path.last
    case d => d.toString
  }

  /** there is no inExt, instead we test to check which files should be used;
    * this is often a test for the file extension
    *
    * This must be such that all auxiliary files are skipped.
    * see defaultFileExtension if you need an inExt (for meta targets)
    *
    * @param name the name of the file (no path, with extension)
    */
  def includeFile(name: String): Boolean

  /**
    * if this target produces additional files (e.g., the aux files of LaTeX),
    * this method should map them to the respective main file
    *
    * @param outPath the output path (relative to archive)
    * @return the input path (relative to inDim)
    */
  def producesFrom(outPath: FilePath): Option[FilePath] = None

  /** true by default; override to skip auxiliary directories
    *
    * @param name the name of the directory (no path)
    */
  def includeDir(name: String): Boolean = true

  /** if true, multiple files/folders are built in parallel */
  def parallel: Boolean = false


  // ***************** the essential abstract or overridable methods for building

  /** estimate the [[BuildResult]] without building, e.g., to predict dependencies */
  // def estimateResult(bf: BuildTask): BuildSuccess = BuildResult.empty

  /** the main abstract method for building one file
    *
    * @param bf information about input/output file etc
    */
  def buildFile(bf: BuildTask): BuildResult

  /** similar to buildFile but called on every directory (after all its children have been processed)
    *
    * This does nothing by default and can be overridden if needed.
    *
    * @param bd            information about input/output file etc
    * @param builtChildren tasks for building the children
    * param level         error/force level to perform action depending on user input
    */
  def buildDir(bd: BuildTask, builtChildren: List[BuildTask]/*, level: Level*/): BuildResult = BuildEmpty("nothing to be done")

  /// ***************** auxiliary methods for computing paths to output/error files etc.

  protected def getOutFile(a: Archive, inPath: FilePath) = (a / outDim / inPath).setExtension(outExt)

  protected def getTestOutFile(a: Archive, inPath: FilePath) =
    (a / Dim("test", outDim.toString) / inPath).setExtension(outExt)

  protected def getFolderOutFile(a: Archive, inPath: FilePath) = a / outDim / inPath / (folderName + "." + outExt)

  protected def getOutPath(a: Archive, outFile: File) = outFile.toFilePath

  protected def getErrorFile(a: Archive, inPath: FilePath): File =
    FileBuildDependency(key, a, inPath).getErrorFile(controller)

  def getFolderErrorFile(a: Archive, inPath: FilePath) = a / errors / key / inPath / (folderName + ".err")

  /** auxiliary method for logging results */
  protected def logResult(s: String) {
    log(s, Some("result"))
  }

  // ***************** building (i.e., create build tasks and add them to build manager)


  /** delegates to build */
  def build(a: Archive, /* up: Update,*/ in: FilePath, policy: QueuePolicy = QueuePolicy.default) {
    build(a, in, None, policy)
  }

  /** entry point for recursive building */
  def build(a: Archive, /* up: Update,*/ in: FilePath, errorCont: Option[ErrorHandler] = None, policy: QueuePolicy = QueuePolicy.default) {
    val qts = makeBuildTasks(a, in, errorCont, policy)
    //controller.buildManager.addTasks(qts)
    throw new Exception("TODO")
  }


  /** like build, but returns all build tasks without adding them to the build manager */
  private def makeBuildTasks(a: Archive, in: FilePath, errorCont: Option[ErrorHandler], policy: QueuePolicy = QueuePolicy.default): List[BuildTask] = {
    var tasks: List[BuildTask] = Nil
    makeBuildTasksAux(in, a, errorCont, policy) { qt =>
      tasks ::= qt
    }
    tasks.reverse
  }

  /** recursive creation of [[BuildTask]]s */
  private def makeBuildTasksAux(in: FilePath, a: Archive, eCOpt: Option[ErrorHandler], policy: QueuePolicy = QueuePolicy.default)(cont: BuildTask => Unit) {
    //build every file
    a.traverse[BuildTask](inDim, in, TraverseMode(includeFile, includeDir, parallel))({
      case Current(inFile, inPath) =>
        val bf = makeBuildTask(a, inPath, inFile, None, eCOpt, policy)
        cont(bf)
        bf
    }, {
      case (Current(inDir, inPath), builtChildren) =>
        val realChildren = builtChildren.filter(!_.isEmptyDir)
        val bd = makeBuildTask(a, inPath, inDir, Some(realChildren), None, policy)
        cont(bd)
        bd
    })
  }

  /** create a single [[BuildTask]]
    *
    * @param eCOpt optional additional [[ErrorHandler]], errors are always written to errors dimension
    */
  private def makeBuildTask(a: Archive, inPath: FilePath, inFile: File,
                            children: Option[List[BuildTask]], eCOpt: Option[ErrorHandler], policy: QueuePolicy = QueuePolicy.default): BuildTask = {
    val errorWriter = makeHandler(a, inPath, children.isDefined)
    val errorCont = eCOpt match {
      case None => errorWriter
      case Some(eC) => new MultipleErrorHandler(List(eC, errorWriter))
    }
    val outFile = if (children.isDefined) getFolderOutFile(a, inPath) else getOutFile(a, inPath)
    new BuildTask(key, a, inFile, children, inPath, outFile, errorCont, this, policy)
  }

  /** makes a build task for a single file (ignoring built children) or directory */
  // TODO: public because it is called by BuildQueue on dependencies; clean that up
  def makeBuildTask(a: Archive, inPath: FilePath, children: List[BuildTask] = Nil, policy: QueuePolicy = QueuePolicy.default): BuildTask = {
    val inFile = a / inDim / inPath
    val isDir = inFile.isDirectory
    makeBuildTask(a, inPath, inFile, if (isDir) Some(children) else None, None, policy)
  }

  /** auxiliary function to create an error handler */
  private def makeHandler(a: Archive, inPath: FilePath, isDir: Boolean = false) = {
    val errFileName = if (isDir) getFolderErrorFile(a, inPath)
    else getErrorFile(a, inPath)
    new ErrorWriter(errFileName, Some(report))
  }

  // ******************* Actual building (i.e., when the build manager calls a build task)

  // TODO the methods in this section should be revised together with a revision of the BuildQueue

  /** the entry point for build managers */
  /* def checkOrRunBuildTask(deps: Set[Dependency], bt: BuildTask/*, up: Update*/): BuildResult = {
    var res: BuildResult = BuildEmpty("up-to-date")
    val outPath = bt.outPath
    // val Update(errLev, dryRun, testMod, _) = up
    val rn = rebuildNeeded(deps, bt, errLev)
    if (!rn) {
      logResult("up-to-date " + outPath)
    }
    if (rn && dryRun) {
      logResult("out-dated " + outPath)
      res = BuildEmpty("out-dated (dry run)")
    }
    if (rn && !dryRun) {
      res = runBuildTask(bt, errLev)
    }
    if (testMod.makeTests) {
      compareOutputAndTest(testMod, bt)
    }
    res  runBuildTask(bt,Level.Error)
  } */

  /** auxiliary method of checkOrRunBuildTask */
  private def rebuildNeeded(deps: Set[Dependency], bt: BuildTask, level: Level): Boolean = {
    val errorFile = bt.asDependency.getErrorFile(controller)
    val errs = hadErrors(errorFile, level)
    val mod = modified(bt.inFile, errorFile)
    level <= Level.Force || mod || errs ||
      deps.exists {
        case bd: BuildDependency =>
          val errFile = bd.getErrorFile(controller)
          modified(errFile, errorFile)
        case PhysicalDependency(fFile) => modified(fFile, errorFile)
        case _ => false // for now
      } || bt.isDir && bt.children.getOrElse(Nil).exists { bf =>
      modified(bf.asDependency.getErrorFile(controller), errorFile)
    }
  }

  /*
  /** auxiliary method of checkOrRunBuildTask */
  private def compareOutputAndTest(testMod: TestModifiers, bt: BuildTask) {
    val testFile = getTestOutFile(bt.archive, bt.inPath)
    val diffFile = testFile.addExtension("diff")
    val outFile = bt.outFile
    if (outFile.exists) {
      if (testFile.exists) {
        var diffLog: Option[String] = Some("") // assume a difference if no diff is run
        if (testMod.compareWithTest) {
          diffLog = ShellCommand.run("diff", "-u", testFile.toString, outFile.toString)
          if (diffLog.isDefined) {
            File.write(diffFile, diffLog.get)
            logResult("wrote: " + diffFile)
          } else {
            logResult("no differences for: " + outFile)
          }
        }
        if (diffLog.isDefined && testMod.updateTest) {
          Files.copy(outFile.toPath, testFile.toPath, StandardCopyOption.REPLACE_EXISTING)
          logResult("updated " + testFile)
        }
      } else {
        if (testMod.addTest) {
          testFile.up.mkdirs
          Files.copy(outFile.toPath, testFile.toPath)
          logResult("added " + testFile)
        }
      }
    } else {
      logResult("no output: " + outFile)
    }
  } */

  /** wraps around buildFile to add error handling, logging, etc.  */
  // TODO should be private, exposed only because it is overridden by LaTeXDirTarget
  def runBuildTask(bt: BuildTask/*, level: Level*/): BuildResult = {
    if (!bt.isDir) {
      val prefix = "[" + inDim + " -> " + outDim + "] "
      report("archive", prefix + bt.inFile + " -> " + bt.outFile)
      bt.outFile.up.mkdirs
    }
    var res: BuildResult = if (bt.isEmptyDir) BuildEmpty("empty-directory") else BuildResult.empty
    if (!bt.isEmptyDir) bt.errorCont.open
    try {
      res = bt.children match {
        case None =>
          // remove the old document from memory (if any) and build the file
          controller.delete(bt.narrationDPath)
          buildFile(bt)
        case Some(children@_ :: _) =>
          // build a directory
          buildDir(bt, children)
        case _ => res
      }
    } catch {
      case e: Error =>
        bt.errorCont(e)
        res = BuildFailure(Nil, Nil)
      case e: Exception =>
        val le = LocalError("unknown build error: " + e.getMessage).setCausedBy(e)
        bt.errorCont(le)
        res = BuildFailure(Nil, Nil)
    } finally {
      if (!bt.isEmptyDir) bt.errorCont.close
    }
    controller.notifyListeners.onFileBuilt(bt.archive, this, bt.inPath)
    res
  }

  // ********************* functions for delete, update, change management etc.

  /** additional method that implementations may provide: cleans one file
    *
    * deletes the output and error file by default, may be overridden to, e.g., delete auxiliary files
    *
    * @param a    the containing archive
    * @param curr the inDim whose output is to be deleted
    */
  def cleanFile(a: Archive, curr: Current) {
    val inPath = curr.path
    val outFile = getOutFile(a, inPath)
    delete(outFile)
    delete(getErrorFile(a, inPath))
    //controller.notifyListeners.onFileBuilt(a, this, inPath)
  }

  /** additional method that implementations may provide: cleans one directory
    *
    * does nothing by default
    *
    * @param a    the containing archive
    * @param curr the outDim directory to be deleted
    */
  def cleanDir(a: Archive, curr: Current) {
    val inPath = curr.path
    val errFile = getFolderErrorFile(a, inPath)
    delete(errFile)
    val errDir = errFile.up
    if (errDir.isDirectory) errDir.deleteDir
    //controller.notifyListeners.onFileBuilt(a, this, inPath)
  }

  /** recursively delete output files in parallel (!) */
  def clean(a: Archive, in: FilePath = EmptyPath) {
    a.traverse[Unit](inDim, in, TraverseMode(includeFile, includeDir, parallel = true), sendLog = true, forClean = true)(
      { c => cleanFile(a, c) }, { case (c, _) => cleanDir(a, c) })
  }

  private def modified(inFile: File, errorFile: File): Boolean = {
    val mod = Modification(inFile, errorFile)
    mod == Modified || mod == Added
  }

  /** @return status of input file, obtained by comparing to error file */
  private def hadErrors(errorFile: File, errorLevel: Level): Boolean = {
    if (errorLevel > Level.Fatal)
      false // nothing is more severe than a fatal error
    else
      errorFile.exists && ErrorReader.getBuildErrors(errorFile, errorLevel, None).nonEmpty
  }

}

  // *********** methods for the deprecated buildDepsFirst, which is still exposed in the interface and may or may not still be used
  
  /*
   anything here needs complete revision
   
   getFilesRec is similar to makeBuildTasks, both traverse the folders recursively
   - getFilesRec returns files to be built as dependencies (but no directories)
   - makeBuildTasks returns QueuedTasks (also for directories)
   QueuedTasks (bad name?) are created from BuildTasks still to be queued by addTasks in build
   (the construction via traverse, a continuation and reverse is overkill compared to getFilesRec)

   "depsFirst" is a wrapper around checkOrRunBuildTask where dependent tasks are updated earlier
    via the estimated dependencies getDeps. (This only works if the estimated dependencies are
    at least the actual dependencies and are non-cyclic.)

    "depFirst" is currently only kept for comparison and testing purposes and may eventually be disposed off
  */

  /*
  deprecated
  // private def getDeps(bt: BuildTask): Set[Dependency] = estimateResult(bt).used.toSet

  // TODO called by AllTeX target
  @deprecated 
  protected def getFilesRec(a: Archive, in: FilePath): Set[Dependency] = {
    val inFile = a / inDim / in
    if (inFile.isDirectory)
      inFile.list.flatMap(n => getFilesRec(a, FilePath(in.segments ::: List(n)))).toSet
    else if (inFile.isFile && includeFile(inFile.getName) && includeDir(inFile.up.getName))
      Set(FileBuildDependency(key, a, in))
    else Set.empty
  }

  @deprecated 
  private def getAnyDeps(dep: FileBuildDependency): Set[Dependency] = {
    if (dep.key == key) {
      // we are within the current target
      getDeps(makeBuildTask(dep.archive, dep.inPath))
    }
    else {
      val bt = dep.getTarget(controller)
      bt.getDeps(bt.makeBuildTask(dep.archive, dep.inPath))
    }
  }

  // TODO called by AllTeX target
  @deprecated 
  protected def getDepsMap(args: Set[Dependency]): Map[Dependency, Set[Dependency]] = {
    var visited: Set[Dependency] = Set.empty
    var unknown = args
    var deps: Map[Dependency, Set[Dependency]] = Map.empty
    while (unknown.nonEmpty) {
      val p = unknown.head
      val ds: Set[Dependency] = p match {
        case bd: FileBuildDependency => getAnyDeps(bd)
        case _ => Set.empty
      }
      deps += ((p, ds))
      visited += p
      unknown -= p
      unknown ++= ds.diff(visited)
    }
    deps
  }
/*
  @deprecated 
  override def buildDepsFirst(a: Archive, /* up: Update,*/ in: FilePath = EmptyPath) {
    val requestedDeps = getFilesRec(a, in)
    val deps = getDepsMap(getFilesRec(a, in))
    val ts = Relational.flatTopsort(controller, deps)
    ts.foreach {
      case bd: FileBuildDependency =>
        val target = if (bd.key == key) this else bd.getTarget(controller)
        val bt = target.makeBuildTask(bd.archive, bd.inPath)
        target.checkOrRunBuildTask(deps.getOrElse(bd, Set.empty), bt,
          if (requestedDeps.contains(bd)) up else up.forDependencies)
      case _ =>
    }
  } */
}

*/