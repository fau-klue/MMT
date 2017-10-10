package info.kwarc.mmt.got

import java.awt.event.{ActionEvent, ActionListener}
import java.awt.{BorderLayout, ComponentOrientation, Container, Dimension, FlowLayout}
import javax.swing._

import info.kwarc.mmt.api
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.modules.DeclaredTheory
import info.kwarc.mmt.api.objects.{Context, OMID, Term, Traverser}
import info.kwarc.mmt.api.ontology.RelationalReader
import info.kwarc.mmt.api.symbols.{Constant, Declaration, PlainInclude}

import scala.collection.mutable
import scala.collection.mutable.{HashMap, HashSet, ListBuffer, StringBuilder}

/**
  * Created by michael on 15.05.17.
  */
class GraphOptimizationTool extends Extension {
  var printErrors = true      //print Errors on error stream, otherwise not at all
  var predictFuture = true    //declarations used in future lite code are counted as used by optimization
  var ignoreUnion = true      //Unions are not optimized if true

  /*variable for interactive mode*/
  var command : String = ""
  val dialogue = new Dialogue(this)

  /**
    * This method is used to make sure the onthologies are loaded when starting the extension
    * @param args not used here
    */
  override def start(args: List[String]): Unit = {
    val ret = super.start(args)
    if (controller.extman.get(classOf[RelationalReader]).isEmpty) controller.extman.addExtension(new RelationalReader)
    ret
  }

  /**
    * This method returns a theory's inclusions, by looking at its direct inclusions and then being applied recursively to the included theories
    * @param theoryPath This is the path of the theory to be analyzed
    * @param replacementmap This is a map containing inclusion replacements for each theory
    * @return This is a list of all inclusions, including indirect
    */
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

  /**
    * This method returns a theory's direct inclusions
    * @param theoryPath This is the path of the theory to be analyzed
    * @param replacementmap This is a map containing inclusion replacements for each theory
    * @return This is a list of all direct inclusions
    */
  def directIncludes (theoryPath : MPath, replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : List[MPath] = {
    var ret = ListBuffer[MPath]()
    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    try {
      val replacement = replacementmap.get(theoryPath).get
      for (declaration <- theory.getPrimitiveDeclarations) {
        declaration match {
          case PlainInclude(from, _) =>
            if (!replacement.contains(from)) {
              ret += from
            }
            else {
              ret ++= replacement.get(from).get
            }
          case _ => Unit
        }
      }
    } catch {
      case _ : java.util.NoSuchElementException =>
        for (declaration <- theory.getPrimitiveDeclarations) {
          declaration match {
            case PlainInclude(from, _) =>
              ret += from
            case _ => Unit
          }
        }
    }
    ret.toList
  }

  /**
    * Sort theories topologically
    * @param theories This is an Iterable of theories to be sorted
    * @return This is a sorted List of theories
    */
  def sortTheories (theories: Iterable[MPath]) : List[MPath] = {
    /*set of already sorted theories for quick check*/
    var sorted = HashSet[MPath]()
    /*actually sorted list*/
    var orderedTheories = mutable.ListBuffer[MPath]()
    /*set of theories still to be sorted*/
    var unsorted = HashSet[MPath]()
    unsorted ++= theories
    var todo : Int = controller.depstore.getInds(api.ontology.IsTheory).length
    /* insert until sorted */
    var change = true
    while (!unsorted.equals(HashSet.empty) && change) {
      change = false
      for (theoryPath <- unsorted) {
        /*cycle through unsorted until theory is found with all dependencies (in optimization scope) sorted*/
        if (controller.depstore.querySet(theoryPath, api.ontology.Includes).asInstanceOf[HashSet[MPath]].intersect(unsorted).isEmpty) {
          orderedTheories += theoryPath
          unsorted -= theoryPath
          sorted += theoryPath
          change = true
        }
      }
    }
    return orderedTheories.toList
  }

  def transitiveClosure(theories : Iterable[MPath]): HashSet[MPath] = {
    var closure = HashSet[MPath]()
    for (theoryPath <- theories) {
      closure += theoryPath
      closure ++= controller.depstore.querySet(theoryPath, -api.ontology.Includes).asInstanceOf[HashSet[MPath]]
    }
    return closure
  }

  /**
    * This object is a traverser and searches a theory for all theories that are used
    */
  object FindUsedTheories extends Traverser[HashSet[MPath]] {
    /**
      * Traverses over terms
      * @param t This is the current subterm
      * @param con This is the current context
      * @param state This is the traverser's state
      * @return
      */
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

    /**
      * Searches a Declaration for its used theories, adds them to state
      * @param decl This is the Declaration to be searched
      * @param state This is the traverser's state
      */
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

    /**
      * Searches a DeclaredTheory for its used theories, adds them to state
      * @param dt This is the DeclaredTheory to be searched
      * @return This is a Set of used theories (as MPaths)
      */
    def apply(dt: DeclaredTheory): State = {
      val state: State = HashSet[MPath]()
      for (decl <- dt.getDeclarations) {
        FindUsedTheories(decl, state)
      }
      state
    }
  }

  /**
    * This method finds inclusions that are redundant, since they are already part of a different inclusion
    * @param theoryPath This is the path of the theory to be optimized
    * @param replacementmap This is a map containing inclusion replacements for each theory
    * @return This is a list containing the suggested removals for the theory
    */
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

  /**
    * This method optimizes a theory by reducing its inclusions to those used inside the theory
    * @param theoryPath This is the path of the theory to be optimized
    * @param replacementmap This is a map containing inclusion replacements for each theory
    * @return This is a map containing the suggested replacements for the theory
    */
  def findUnusedIncludeReplacements(theoryPath : MPath,
                                    replacementmap : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = HashMap[MPath, HashMap[Path, HashSet[MPath]]](),
                                    futureUse : HashMap[MPath, HashSet[MPath]]
                                   ) : HashMap[Path, HashSet[MPath]] = {
    /* replacements will map the replacement suggestions for each optimization candidate
    *  theory inclusions that can be removed entirely will receive an empty set*/
    var replacements : HashMap[Path, HashSet[MPath]] = new HashMap[Path, HashSet[MPath]]

    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    var usedTheories : HashSet[MPath] = FindUsedTheories(theory)
    if (ignoreUnion && usedTheories.isEmpty) return replacements
    if (predictFuture) usedTheories ++= futureUse.get(theoryPath).get

    /* Find candidates for optimization.
    *  Every directly included theory from which there is no used symbol can be optimized in at least some way.*/
    var optimizationCandidates = HashSet[MPath]()
    optimizationCandidates ++= directIncludes(theoryPath, replacementmap)
    optimizationCandidates --= usedTheories

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
        transitiveUsedIncludes += usedDirectInclude
        transitiveUsedIncludes ++= controller.get(usedDirectInclude).asInstanceOf[DeclaredTheory].getIncludes
      }

      if (candidateIncludes.subsetOf(transitiveUsedIncludes)) {
        replacements.put(optimizationCandidate, new HashSet[MPath]())
      }
      else {
        var replacementIncludes = (HashSet[MPath]() ++=candidateIncludes)--=transitiveUsedIncludes
        var transitiveReplacementIncludes = HashSet[MPath]()
        for (replacementInclude <- replacementIncludes) {
          transitiveReplacementIncludes ++= controller.get(replacementInclude).asInstanceOf[DeclaredTheory].getIncludes
        }
        replacementIncludes --= transitiveReplacementIncludes
        replacements.put(optimizationCandidate, replacementIncludes)
      }
    }
    replacements
  }

  /**
    * This method optimizes all given theories
    * @param theories Theories to be optimized as Iterable[MPath]
    * @return This is a map containing the suggested replacements for all analyzed theories
    */
  def findReplacements(theories: Iterable[MPath], interactive : Boolean) : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = {
    var replacements = HashMap[MPath, HashMap[Path, HashSet[MPath]]]()
    var preserve = HashSet[MPath]()
    var futureUse = HashMap[MPath, HashSet[MPath]]()
    var missingFuture = HashSet[MPath]()
    var futureLight = sortTheories(transitiveClosure(theories))

    /*start interactive window*/
    if (interactive) {
      dialogue.showWindow()
    }

    /*Search future lite code for used theories*/
    for (theoryPath <- futureLight.reverse) {
      try {
        futureUse.put(theoryPath, FindUsedTheories(controller.getTheory(theoryPath)))
      } catch {
        case _: Error => {
          if (printErrors) Console.err.println("Error: while looking into Future " + theoryPath + "(skipped)")
          futureUse.put(theoryPath, HashSet[MPath]())
          missingFuture += theoryPath
        }
      }
    }
    for (theoryPath <- theories) {
      for (futurePath <- controller.depstore.querySet(theoryPath, -api.ontology.Includes).asInstanceOf[HashSet[MPath]]) {
        if (missingFuture.contains(futurePath)) missingFuture += theoryPath
        else futureUse.get(theoryPath).get ++= futureUse.get(futurePath).get
      }
    }

    /* find replacements */
    for (theoryPath <- sortTheories(theories)) {
      try {
        /* remove unused includes */
        if (!interactive) replacements.put(theoryPath, findUnusedIncludeReplacements(theoryPath , replacements, futureUse))
        else {
          replacements.put(theoryPath, HashMap[Path, HashSet[MPath]]())
          var suggestions = findUnusedIncludeReplacements(theoryPath, replacements, futureUse)
          for (key <- suggestions.keySet) {
            command = "waiting"
            dialogue.suggest(theoryPath, key, suggestions.get(key).get)
            while (command == "waiting")
              synchronized {
                wait()
              }

            if (command == "yes") {
              replacements.get(theoryPath).get.put(key, suggestions.get(key).get)
              //TODO apply change to source
            }
            if (command == "never") preserve += key.asInstanceOf[MPath]
          }
        }
        /* remove redundant includes */
        for (redundant <- findRedundantIncludes(theoryPath, replacements)) {
          if (!interactive) replacements.get(theoryPath).get.put(redundant, HashSet[MPath]())
          else {
            command = "waiting"
            dialogue.suggest(theoryPath, redundant, HashSet[MPath]())
            while (command == "waiting")
              synchronized {
                wait()
              }

            if (command == "yes") {
              replacements.get(theoryPath).get.put(redundant, HashSet[MPath]())
              //TODO apply change to source
            }
            if (command == "never") preserve += redundant.asInstanceOf[MPath]
          }
        }
      } catch { case _ : Error => {
          if (printErrors) Console.err.println("Error: while optimizing " + theoryPath + " (skipped)")
          replacements.put(theoryPath, HashMap[Path, HashSet[MPath]]())
        }
      }
    }
    /*stop interactive window*/
    if (interactive) {
      dialogue.done()
    }
    replacements
  }

  /**
    * This method optimizes all theories inside the onthology
    * @return This is a map containing the suggested replacements for all analyzed theories
    */
  def findReplacements(interactive : Boolean = false) : HashMap[MPath, HashMap[Path, HashSet[MPath]]] = {
    val theories = controller.depstore.getInds(api.ontology.IsTheory).asInstanceOf[Iterator[MPath]].toIterable
    return findReplacements(theories, interactive)
  }

  /**
    * This method converts a given mapping as generated by findReplacements to an XML representation
    * @param map This is a map containing inclusion replacements for each theory
    * @return XML-String
    */
  def allToXML(map : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    for (theoryPath <- map.keySet) {
      sb ++= replaceTheoryToXML(theoryPath, map)
    }
    return sb.toString
  }

  /**
    * This method is a subroutine of allToXML
    * @param theoryPath
    * @param map This is a map containing inclusion replacements for each theory
    * @return XML-String, or empty if mapping is
    */
  def replaceTheoryToXML(theoryPath : MPath, map : HashMap[MPath, HashMap[Path, HashSet[MPath]]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    if (map.get(theoryPath).get.keySet.isEmpty) return ""
    sb ++= "<theory MPath=" ++= theoryPath.toString ++= ">\n"
    sb ++= replaceInclusionToXML(map.get(theoryPath).get)
    sb ++= "</theory>\n"
    return sb.toString
  }

  /**
    * This method converts a given mapping of replacements for a single theory to an XML representation
    * @param map This is a map containing inclusion replacements for one theory
    * @return XML-String
    */
  def replaceInclusionToXML(map : HashMap[Path, HashSet[MPath]]) : String = {
    var sb : StringBuilder = new StringBuilder()
    for (path <- map.keySet) {
      if (map.get(path).get.isEmpty)
        sb ++= "\t<removeInclusion Path=" ++= path.toString ++= ">\n"
      else {
        sb ++= "\t<replaceInclusion Path=" ++= path.toString ++= ">\n"
        for (theoryPath <- map.get(path).get) sb ++= "\t\t<replacement MPath=" ++= theoryPath.toString ++= ">\n"
        sb ++= "\t<replaceInclusion>\n"
      }
    }
    return sb.toString
  }

  class Dialogue(parent : GraphOptimizationTool) extends JFrame("Style") {
    val got = parent
    /*panels*/
    val suggestionPanel = new JScrollPane()
    val controls = new JPanel()

    /*text label for displaying suggested changes*/
    val suggestionBox = new JLabel()

    /*control buttons*/
    val yesButton = new JButton("yes")
    yesButton.addActionListener(new ActionListener(){
      def actionPerformed(e : ActionEvent){
        got.synchronized {
          got.command="yes"
          got.notify()
        }
      }
    })
    val noButton = new JButton("no")
    noButton.addActionListener(new ActionListener(){
      def actionPerformed(e : ActionEvent){
        got.synchronized {
          got.command="no"
          got.notify()
        }
      }
    })
    val laterButton = new JButton("later")
    laterButton.addActionListener(new ActionListener(){
      def actionPerformed(e : ActionEvent){
        got.synchronized {
          got.command="later"
          got.notify()
        }
      }
    })
    val neverButton = new JButton("never")
    neverButton.addActionListener(new ActionListener(){
      def actionPerformed(e : ActionEvent){
        got.synchronized {
          got.command="never"
          got.notify()
        }
      }
    })

    addComponentsToPane(getContentPane())
    disableButtons()

    def addComponentsToPane(panel : Container) : Unit = {
      suggestionPanel.setLayout(new ScrollPaneLayout())
      controls.setLayout(new FlowLayout())

      //add suggestionBox
      suggestionBox.setPreferredSize(new Dimension(300, 500))
      suggestionPanel.add(suggestionBox)

      //Add buttons
      controls.add(yesButton)
      controls.add(noButton)
      controls.add(neverButton)
      controls.add(laterButton)

      //Left to right component orientation is selected by default
      suggestionPanel.setComponentOrientation(ComponentOrientation.LEFT_TO_RIGHT)

      //TODO add button actions

      //add panels
      panel.add(suggestionBox, BorderLayout.CENTER)
      panel.add(controls,BorderLayout.SOUTH)
    }

    def showWindow() : Unit = {
      //display the window
      pack()
      setVisible(true)
    }

    def disableButtons() : Unit = {
      yesButton.setEnabled(false)
      noButton.setEnabled(false)
      neverButton.setEnabled(false)
      laterButton.setEnabled(false)
    }


    def done() : Unit = {
      disableButtons()
      setVisible(false)
    }

    def suggest(in : MPath, theoryPath : Path, replacements : HashSet[MPath]) : Unit = {
      /*display suggestion*/
      var sb = new StringBuilder()
      sb ++= "<html>"
      sb ++= "in:<br>"
      sb ++= in.toString ++= "<br>"
      if (replacements.isEmpty) {
        sb ++= "remove:<br>" ++= theoryPath.toString
      }
      else {
        sb ++= "replace:<br>" ++= theoryPath.toString
        sb ++= "<br>"
        sb ++= "with:"
        for (replacement <- replacements) {
          sb ++= "<br>" ++= replacement.toString
        }
      }
      sb ++= "</html>"
      suggestionBox.setText(sb.toString())

      /*enable buttons*/
      yesButton.setEnabled(true)
      noButton.setEnabled(true)
      neverButton.setEnabled(true)
      laterButton.setEnabled(true)

      /*resize window*/
      pack()
    }
  }
}