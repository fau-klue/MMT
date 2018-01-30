package info.kwarc.mmt.api.frontend.actions

import info.kwarc.mmt.api.frontend.{Controller, actions}
import info.kwarc.mmt.api.utils.{MMTSystem, OS}

import scala.collection.mutable.ListBuffer
import scala.util.Try

/** an action that responds to the user */
private[actions] trait ResponsiveAction extends ActionImpl {
  /** prints a response to the caller */
  def respond(x: Any*)(implicit controller: Controller) = controller.report.apply("user", x.map(_.toString).mkString(", "))
}

/** Shared base class for Actions for printing something */
sealed abstract class PrintAction extends ResponsiveAction {}

case object MMTInfo extends PrintAction {
  def apply(implicit controller: Controller): Unit = {
    respond(s"MMT Version     : ${MMTSystem.version}")
    respond(s"Run Style       : ${MMTSystem.runStyle}")
    respond(s"Operation System: ${OS.detect}")

    respond("use 'show extensions' to show current extensions. ")
    respond("use 'show mathpath' to show loaded content. ")
    respond("use 'show server' to show current server. ")
  }
  def toParseString = "show mmt"
}
object MMTInfoCompanion extends ActionObjectCompanionImpl[MMTInfo.type]("show mmt system information", "show mmt")

case object MMTVersion extends PrintAction {
  def apply(implicit controller: Controller): Unit = {
    respond(MMTSystem.version)
  }
  def toParseString = "show version"
}
object MMTVersionCompanion extends ActionObjectCompanionImpl[MMTInfo.type]("show mmt version information", "show version")

/** print all loaded knowledge items to STDOUT in text syntax */
case object ClearConsole extends PrintAction {
  def apply(implicit controller: Controller): Unit = {
    System.out.print("\033[H\033[2J")
    System.out.flush()
  }
  def toParseString = "clear console"
}
object ClearConsoleCompanion extends ActionObjectCompanionImpl[ClearConsole.type]("clears the console", "clear console")


/** print all loaded knowledge items to STDOUT in text syntax */
case object PrintAll extends PrintAction {
  def apply(implicit controller: Controller): Unit = {
    respond("\n" + controller.library.toString)
  }
  def toParseString = "show knowledge"
}
object PrintAllCompanion extends ActionObjectCompanionImpl[PrintAll.type]("print all loaded knowledge items to STDOUT in text syntax", "show knowledge")

/** print all loaded knowledge items to STDOUT in XML syntax */
case object PrintAllXML extends PrintAction {
  def apply(implicit controller: Controller): Unit = {
    respond("\n" + controller.library.getModules.map(_.toNode).mkString("\n"))
  }
  def toParseString = "show xml"
}
object PrintAllXMLCompanion extends ActionObjectCompanionImpl[PrintAllXML.type]("print all loaded knowledge items to STDOUT in xml syntax", "show xml")

/** print all configuration entries to STDOUT */
case object PrintConfig extends PrintAction {
  def apply(implicit controller: Controller) : Unit = {
    respond(controller.getConfigString())
  }
  def toParseString = "show config"
}
object PrintConfigCompanion extends ActionObjectCompanionImpl[PrintConfig.type]("print all configuration to stdout", "show config")

case class HelpAction(topic: String) extends PrintAction {
  // list of all known help Topics
  private def helpTopics : List[String] = (
    MMTSystem.getResourceList("/help-text/").flatMap({
      case s: String if s.endsWith(".txt") => Some(s.stripSuffix(".txt"))
      case _ => None
    }) ::: ActionCompanion.all.flatMap(_.keywords).distinct ::: List("topics")
    ).sorted

  /** gets dynamically generated help entries */
  private def getDynamicHelp(topic: String) : Option[String] = topic match {
    case "" => getHelpText("help")
    case "topics" =>
      val lines = new ListBuffer[String]()
      lines += "Type 'help <topic>' for more information about a specific topic. "
      lines += ""
      helpTopics.map(lines +=)
      Some(lines.mkString("\n"))
    case _ => None
  }

  /** gets the (static) help text for a given topic or None */
  private def getHelpText(topic: String) : Option[String] = if(topic.matches("[A-Za-z_-]+")) {
    Try(MMTSystem.getResourceAsString("/help-text/" + topic + ".txt")).toOption
  } else {
    None
  }

  /** gets the help text for a given action or None */
  private def getActionHelp(action: String) : Option[String] = {
    val topics = ActionCompanion.find(action)
    if(topics.isEmpty){
      None
    } else {
      Some(topics.distinct.map(ac => ac.mainKeyword + ": " + ac.helpText).mkString("\n"))
    }
  }


  def apply(implicit controller: Controller): Unit = {
    val topicActual = topic.trim
    // try and get a string that represents help
    getDynamicHelp(topicActual).getOrElse(getHelpText(topicActual).getOrElse(getActionHelp(topicActual).getOrElse(""))) match {
      case "" => respond(s"No help on '$topic' available")
      case s: String => logGroup {
        respond(s)
      }
    }
  }
  def toParseString: String = s"show help $topic".trim
}
object HelpActionCompanion extends ActionCompanionImpl[HelpAction]("print help about a given topic", "show help", "help") {
  import Action._
  override def parserActual(implicit state: ActionState): actions.Action.Parser[HelpAction] = (strMaybeQuoted *) ^^ { s => HelpAction(s.mkString(" ")) }
}

/** utility methods for handling [[PrintAction]]s */
trait PrintActionHandling {
  self: Controller =>

  /** returns a string expressing the current configuration */
  def getConfigString(): String = state.config.toString
}
