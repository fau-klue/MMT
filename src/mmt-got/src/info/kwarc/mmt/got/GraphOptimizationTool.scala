package info.kwarc.mmt.got

import info.kwarc.mmt.api
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.modules.DeclaredTheory
import info.kwarc.mmt.api.objects.{Context, OMID, Term, Traverser}
import info.kwarc.mmt.api.ontology.RelationalReader
import info.kwarc.mmt.api.symbols.{Constant, Declaration, PlainInclude}

import scala.collection.mutable
import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.ListBuffer

/**
  * Created by michael on 15.05.17.
  */
class GraphOptimizationTool extends Extension {

  override def start(args: List[String]): Unit = {
    val ret = super.start(args)
    if (controller.extman.get(classOf[RelationalReader]).isEmpty) controller.extman.addExtension(new RelationalReader)
    ret
  }

  def includes(theoryPath : MPath,
               replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = HashMap[MPath, HashMap[Path, HashSet[MPath]]]()
              ) : List[MPath] = {
    var ret = ListBuffer[MPath]()
    for (include <- directIncludes(theoryPath, replacementmap)) {
      ret += include
      ret ++= includes(include, replacementmap)
    }
    ret.toList
  }

  def directIncludes (theoryPath : MPath, replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : List[MPath] = {
    var ret = ListBuffer[MPath]()
    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    val replacement = replacementmap.get(theoryPath)
    for (declaration <- theory.getPrimitiveDeclarations) {
      declaration match {
        case PlainInclude(from, _) =>
          if (!replacement.contains(from)) {
            ret += from
          }
          else {
            ret ++= replacement.get(from)
          }
        case _ => Unit
      }
    }
    ret.toList
  }

  object FindUsedTheories extends Traverser[HashSet[MPath]] {
    /* traverses the term t and adds all used theories to the state*/
    def traverse(t: Term)(implicit con: Context, state: State): Term = t match {
      // look for URIs
      case OMID(path) =>
        // cut path to module path
        state.add(path.module)
        OMID(path)

      // in all other cases, traverse
      case t =>
        Traverser(this, t)
    }

    def apply(t: Term, state: State): Term = apply(t, state, Context())

    def apply(decl: Declaration, state: State): Unit = {
      decl match {
        case PlainInclude(from, to) =>
        case c: Constant =>
          c.df match {
            case Some(t) => apply(t, state)
            case _ =>
          }
          c.tp match {
            case Some(t) => apply(t, state)
            case _ =>
          }
        case _ =>
      }
    }

    def apply(dt: DeclaredTheory): State = {
      val state: State = HashSet[MPath]()
      for (decl <- dt.getDeclarations) {
        FindUsedTheories(decl, state)
      }
      state
    }
  }

  def findRedundantIncludes(theoryPath : MPath,
                            replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = HashMap[MPath, HashMap[Path, HashSet[MPath]]]()
                           ) : List[Path] = {
    var ret = ListBuffer[Path]()
    var subIncludes = HashSet[MPath]()
    for (include <- directIncludes(theoryPath, replacementmap)) {
      for (subInclude <- includes(include, replacementmap)) {
        subIncludes += subInclude
      }
    }
    for (directInclude <- directIncludes(theoryPath, replacementmap)) {
      if (subIncludes.contains(directInclude)) {
        ret += directInclude
      }
    }
    ret.toList
  }

  def findUnusedIncludeReplacements(theoryPath : MPath,
                                    replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = HashMap[MPath, HashMap[Path, HashSet[MPath]]]()
                                   ) : HashMap[Path, HashSet[MPath]] = {
    /* replacements will map the replacement suggestions for each optimization candidate
    *  theory inclusions that can be removed entirely will receive an empty set*/
    var replacements : HashMap[Path, HashSet[MPath]] = new HashMap[Path, HashSet[MPath]]

    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    var usedTheories : HashSet[MPath] = FindUsedTheories(theory)
    if (usedTheories.isEmpty) return replacements

    /* Find candidates for optimization.
    *  Every directly included theory from which there is no used symbol can be optimized in at least some way.*/
    var optimizationCandidates = HashSet[MPath]()
    optimizationCandidates ++= directIncludes(theoryPath, replacementmap)
    optimizationCandidates --= FindUsedTheories(theory)

    /*Find replacement for every candidate*/
    for (optimizationCandidate <- optimizationCandidates) {
      /* Replacement strategy depends on whether
      *  candidate.includes intersects usedTheories
      *  is a subset of
      *  (usedTheories intersects directIncludes).includes
      *  */

      /* find candidate.includes intersects usedTheories */
      var candidateIncludes = HashSet[MPath]()
      candidateIncludes ++= includes(optimizationCandidate, replacementmap)
      candidateIncludes = candidateIncludes.intersect(usedTheories)

      /* find transitive closure of includes of used directIncludes*/
      var usedDirectIncludes = HashSet[MPath]()
      usedDirectIncludes ++= directIncludes(theoryPath, replacementmap)
      controller.get(optimizationCandidate).asInstanceOf[DeclaredTheory].meta match {
        case Some(p : MPath) => usedDirectIncludes += p
        case None =>
      }
      usedDirectIncludes = usedDirectIncludes.intersect(usedTheories)

      var transitiveUsedIncludes = HashSet[MPath]()
      for (usedDirectInclude <- usedDirectIncludes) {
        transitiveUsedIncludes ++= controller.get(usedDirectInclude).asInstanceOf[DeclaredTheory].getIncludes
      }

      if (candidateIncludes.subsetOf(transitiveUsedIncludes)) {
        replacements.put(optimizationCandidate, new HashSet[MPath]())
      }
      else {
        replacements.put(optimizationCandidate, (new HashSet[MPath]()++=candidateIncludes)--=usedDirectIncludes)
      }
    }
    replacements
  }

  def findReplacements() : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = {
    var replacements = HashMap[MPath, HashMap[Path, HashSet[MPath]]]()

    /* Sort graph topologically */
    /*set of already sorted theories for quick check*/
    var sorted = mutable.HashSet[MPath]()
    /*actually sorted list*/
    var orderedTheories = mutable.ListBuffer[MPath]()
    /*set of theories still to be sorted*/
    var unsorted = mutable.HashSet[MPath]()
    var todo : Int = controller.depstore.getInds(api.ontology.IsTheory).length
    for (theoryPath <- controller.depstore.getInds(api.ontology.IsTheory).asInstanceOf[Iterator[MPath]]) {
      //println(todo)
      todo = todo-1
      /*
      if (controller.getTheory(theoryPath).getIncludesWithoutMeta.isEmpty) {
        /*no dependencies*/
        orderedTheories += theoryPath
        sorted += theoryPath
      }
      else
      */
      try {
        controller.getTheory(theoryPath)
        if (controller.depstore.querySet(theoryPath, api.ontology.DependsOn).subsetOf(sorted.asInstanceOf[scala.collection.GenSet[Path]])) {
          /*dependencies already in sorted*/
          orderedTheories += theoryPath
          sorted += theoryPath
        }
        else {
          /*dependencies not yet in sorted*/
          unsorted += theoryPath
        }
      } catch {case _ : Error => Console.err.println("Error: while sorting " + theoryPath + " (skipped)")}
    }

    /* insert rest until sorted */
    var change = true
    while (!unsorted.equals(HashSet.empty) && change) {
      change = false
      for (theoryPath <- unsorted) {
        /*cycle through unsorted until theory is found with all dependencies sorted*/
        if (controller.depstore.querySet(theoryPath, api.ontology.DependsOn).subsetOf(sorted.asInstanceOf[scala.collection.GenSet[Path]])) {
          orderedTheories += theoryPath
          unsorted -= theoryPath
          sorted += theoryPath
          change = true
        }
      }
    }

    /*this sort is using dependencies that may become outdated, but requirements will only become less strict through replacements*/

    /* find replacements */
    for (theoryPath <- sorted) {
      try {
        /* remove unused includes */
        var replacement = findUnusedIncludeReplacements(theoryPath : MPath, replacements : HashMap[MPath, HashMap[Path, HashSet[MPath]]])
        /* remove redundant includes */
        for (redundant <- findRedundantIncludes(theoryPath, replacements)) {
          replacement.put(redundant, HashSet[MPath]())
        }
        /*add to return map*/
        replacements.put(theoryPath, replacement)
      } catch { case _ : Error => {
          Console.err.println("Error: while optimizing " + theoryPath + " (skipped)")
          replacements.put(theoryPath, HashMap[Path, HashSet[MPath]]())
        }
      }
    }
    replacements
  }

  def allToXML(map : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    for (theoryPath <- map.keySet) {
      sb ++= replaceTheoryToXML(theoryPath, map)
    }
    return sb.toString
  }

  def replaceTheoryToXML(theoryPath : MPath, map : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    if (map.get(theoryPath).get.keySet.isEmpty) return ""
    sb ++= "<theory MPath=" ++= theoryPath.toString ++= ">\n"
    sb ++= replaceInclusionToXML(map.get(theoryPath).get)
    sb ++= "</theory>\n"
    return sb.toString
  }

  def replaceInclusionToXML(map : HashMap[Path, HashSet[MPath]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    for (path <- map.keySet) {
      if (map.get(path).get.isEmpty)
        sb ++= "\t<removeInclusion Path=" ++= path.toString ++= ">\n"
      else {
        sb ++= "\t<replaceInclusion Path=" ++= path.toString ++= ">\n"
        for (theoryPath <- map.get(path).get) sb ++= "\t\t<replacement MPath=" ++= theoryPath.toString ++= ">\n"
        sb ++= "\t<replaceInclusion>"
      }
    }
    return sb.toString
  }
}