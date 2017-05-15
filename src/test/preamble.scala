import info.kwarc.mmt.api
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend.Run
import info.kwarc.mmt.api.ontology.{DeclarationTreeExporter, DependencyGraphExporter, JsonGraphExporter, PathGraphExporter}
import info.kwarc.mmt.api.modules.DeclaredTheory
import info.kwarc.mmt.api.symbols.PlainInclude

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/** An abstract class for test methods. Instantiates a controller, sets the mathpath for archives,
  * loads the AlignmentsServer (so you can run a Server without getting an error message.
  *
  * You just need to give archivepath and instantiate the run method with your own arbitrary code
  *
  * @param archivepath    : the path to your archives
  * @param logprefixes    : A list of logprefixes to log
  * @param alignmentspath : the path to .align files (doesn't need to be set, therefore defaults to
  *                         empty string)
  * @param serverport     : Optional port to start a server. If None, no server is started
  * @param gotoshell      : if true, it will drop to the MMT shell afterwards
  * @param logfile        : If defined, will log into file
  */
abstract class Test(archivepath : String,
                    logprefixes : List[String] = Nil,
                    alignmentspath : String = "",
                    serverport : Option[Int] = None,
                    gotoshell : Boolean = true,
                    logfile : Option[String] = None) {
  val controller = Run.controller

  // If you want to log additional stuff, just put it in this list

  controller.handleLine("log console")
  if (logfile.isDefined) controller.handleLine("log html " + logfile.get)// /home/raupi/lmh/mmtlog.txt")
  logprefixes foreach (s => controller.handleLine("log+ " + s))
  controller.handleLine("extension info.kwarc.mmt.lf.Plugin")
  controller.handleLine("extension info.kwarc.mmt.LFX.Plugin")
  controller.handleLine("extension info.kwarc.mmt.odk.Plugin")
  controller.handleLine("extension info.kwarc.mmt.pvs.Plugin")
  // controller.handleLine("extension info.kwarc.mmt.metamath.Plugin")
  controller.handleLine("mathpath archive " + archivepath)
  controller.handleLine("extension info.kwarc.mmt.api.ontology.AlignmentsServer " + alignmentspath)


  def doFirst : Unit = {}

  def run : Unit

  def main(args: Array[String]): Unit = try {

    controller.extman.addExtension(new DependencyGraphExporter)
    controller.extman.addExtension(new DeclarationTreeExporter)
    controller.extman.addExtension(new JsonGraphExporter)
    controller.extman.addExtension(new PathGraphExporter)
      doFirst
      if (serverport.isDefined) {
        //controller.handleLine("clear")
        controller.handleLine("server on " + serverport.get)
      }
      run
      if (gotoshell) Run.main(Array())
    } catch {
      case e: api.Error => println(e.toStringLong)
        sys.exit
    }

  def hl(s : String) = controller.handleLine(s)
}

/**
  * As an example, here's my default. All test files of mine just extend this:
  */
abstract class DennisTest(prefixes : String*) extends Test(
  "/home/jazzpirate/work/MathHub",
  prefixes.toList,
  "/home/jazzpirate/work/Stuff/Public",
  Some(8080),
  true,
  Some("/home/jazzpirate/work/mmtlog.html")
) {
}

abstract class TomTest(prefixes : String*) extends Test(
  "/home/twiesing/Projects/KWARC/MathHub/localmh/MathHub",
  prefixes.toList,
  "/home/twiesing/Projects/KWARC/MathHub/localmh/MathHub/alignments/Public",
  Some(8080),
  true,
  None
)

abstract class MichaelTest(prefixes : String*) extends Test(
  "/home/michael/content/",
  prefixes.toList,
  "",
  Some(8080),
  true,
  Some("/home/michael/content/test.log")
)

object RunTom extends TomTest {
  def run : Unit = Unit
}

object RunMichael extends MichaelTest {
  def findRedundancy(theoryPath : MPath) : List[Path] = {
    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    var ret = ListBuffer[Path]()
    var subIncludes = mutable.HashSet[MPath]()
    for (include <- theory.getIncludes) {
      for (subInclude <- controller.get(include).asInstanceOf[DeclaredTheory].getIncludes) {
        subIncludes += subInclude
      }
    }
    for (decl <- theory.getPrimitiveDeclarations) {
      decl match {
        case PlainInclude(from, _) =>
          if (subIncludes.contains(from)) {
            ret+= decl.path
          }
        case _ => Unit
      }
    }
    return ret.toList
  }

  def removeRedundancy(theoryPath : MPath) : Unit = {
    for (redundancy <- findRedundancy(theoryPath)) {
      controller.delete(redundancy)
    }
  }

  def run : Unit = {
    var path : MPath = Path.parseM("http://mydomain.org/myarchive/mmt-example?test_all",NamespaceMap.empty)
    var theory : DeclaredTheory = controller.get(path) match {
      case t : DeclaredTheory => t
      case _ => ???
    }
    var string : String = controller.presenter.asString(theory)
    println(string)
    println("redundant includes:")
    for (redundancy <- findRedundancy(path)) {
      println(controller.presenter.asString(controller.get(redundancy)))
    }
    removeRedundancy(path)
    println("redundant includes after cleanup:")
    for (redundancy <- findRedundancy(path)) {
      println(controller.presenter.asString(controller.get(redundancy)))
    }
  }
}
