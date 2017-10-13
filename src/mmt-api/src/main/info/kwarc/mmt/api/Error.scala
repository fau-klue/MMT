package info.kwarc.mmt.api

import Level.Level
import info.kwarc.mmt.api.building.BuildTarget
import parser.SourceRef
import utils._

import scala.xml._

/** The superclass of all Errors generated by MMT
  *
  * @param shortMsg the error message
  */
abstract class Error(val shortMsg: String) extends java.lang.Exception(shortMsg) {
  /** additional message text, override as needed */
  def extraMessage: String = ""

  /** the severity of the error, override as needed */
  def level: Level = Level.Error

  private var causedBy: Option[Throwable] = None

  /** get the error due to which this error was thrown */
  def setCausedBy(e: Throwable): this.type = {
    causedBy = Some(e)
    this
  }

  protected def causedByToNode = causedBy match {
    case Some(e: Error) => e.toNode
    case Some(e) => <cause type={e.getClass.getName} shortMsg={e.getMessage}>{Stacktrace.asNode(e)}</cause>
    case None => Nil
  }

  protected def causedByToString = causedBy match {
    case None => ""
    case Some(e: Error) => "\n\ncaused by\n" + e.toStringLong
    case Some(e) => "\n\ncaused by\n" + e.getClass + ": " + e.getMessage + e.getStackTrace.map(_.toString).mkString("\n", "\n", "")
  }

  override def toString = shortMsg

  def toStringLong: String = {
    shortMsg + "\n" + extraMessage + "\ndetected at\n" + Stacktrace.asString(this) + causedByToString
  }

  def toNode: Elem =
      <error type={getClass.getName} shortMsg={shortMsg} level={level.toString}>
         {if (extraMessage.isEmpty) Nil else extraMessage}
         {Stacktrace.asNode(this)}
         {causedByToNode}
      </error>

  def toHTML: String = HTML.build { h => import h._
    def trace(t: Throwable) {
      div("stacktrace") {
        Stacktrace.asStringList(t).foreach { s =>
          div("stacktraceline") {
            span {
              text {
                s
              }
            }
          }
        }
      }
    }
    div("error") {
      div {
        span("name") {
          text(this.getClass.getName)
        }
        text(" of level ")
        span("level") {
          text(level.toString)
        }
      }
      div("message") {
        text(shortMsg)
      }
      if (!extraMessage.isEmpty) div {
        text {
          extraMessage
        }
      }
      trace(this)
      causedBy.foreach {e =>
        div {text {"caused by"}}
        div("cause") {
          e match {
            case e: Error => div {
              literal(e.toHTML)
            }
            case e: Throwable => div {
              text {
                e.getClass + " : " + e.getMessage
              }
              trace(e)
            }
          }
        }
      }
    }
  }
}

object Error {
  /** converts java exception to MMT error */
  def apply(e: Exception): Error = e match {
    case e: Error => e
    case e: Exception => GeneralError("unknown error").setCausedBy(e)
  }
}

/** auxiliary functions for handling Java stack traces */
object Stacktrace {
  def asStringList(e: Throwable): List[String] = e.getStackTrace.map(_.toString).toList

  def asString(e: Throwable): String = asStringList(e).mkString("", "\n", "")

  def asNode(e: Throwable): Seq[Node] with Serializable = asStringList(e) match {
    case Nil => Nil
    case st => <stacktrace>{st.map(s => <element>{s}</element>)}</stacktrace>
  }
}

/** error levels, see [[Error]]
  *
  * even fatal errors can be ignored (by comparison)
  */
object Level {
  type Level = Int
  val Force = -1
  val Info = 0
  val Warning = 1
  val Error = 2
  val Fatal = 3
  val Ignore = 4

  def parse(s: String): Level = s match {
    case "0" => Info
    case "1" => Warning
    case "" | "2" => Error
    case "3" => Fatal
    case _ => throw ParseError("unknown error level: " + s)
  }

  def toString(l: Level): String = l match {
    case -1 => "force"
    case 0 => "info"
    case 1 => "warn"
    case 2 => "error"
    case 3 => "fatal"
    case 4 => "ignore"
    case _ => "unknown" + l
  }
}

/** other errors that occur during parsing */
case class ParseError(s: String) extends Error("parse error: " + s)

/** errors that occur when parsing a knowledge item */
case class SourceError(origin: String, ref: SourceRef, mainMessage: String, extraMessages: List[String] = Nil,
                       override val level: Level = Level.Error) extends Error(mainMessage) {
  override def extraMessage: String = s"source error ($origin) at " + ref.toString + extraMessages.mkString("\n", "\n", "\n")

  override def toNode: Elem = xml.addAttr(xml.addAttr(super.toNode, "sref", ref.toString), "target", origin)
}

/** errors that occur during compiling */
object CompilerError {
  def apply(key: String, ref: SourceRef, messageList: List[String], level: Level): SourceError =
    SourceError(key, ref, messageList.head, messageList.tail, level)
}

/** errors that occur when checking a knowledge item (generated by the Checker classes) */
abstract class Invalid(s: String) extends Error(s)

/** errors that occur when structural elements are invalid */
case class InvalidElement(elem: StructuralElement, s: String) extends Invalid("invalid element: " + s + ": " + elem.path.toPath)

/** errors that occur when objects are invalid */
case class InvalidObject(obj: objects.Obj, s: String) extends Invalid("invalid object (" + s + "): " + obj)

/** errors that occur when judgements do not hold */
case class InvalidUnit(unit: checking.CheckingUnit, history: checking.History, msg: String) extends Invalid("invalid unit: " + msg)

/** run time error thrown by executing invalid program */
case class ExecutionError(msg: String) extends Error(msg)

/** other errors */
case class GeneralError(s: String) extends Error("general error: " + s)

/** errors that occur when adding a knowledge item */
case class AddError(s: String) extends Error("add error: " + s)

/** errors that occur when updating a knowledge item */
case class UpdateError(s: String) extends Error("update error: " + s)

/** errors that occur when deleting a knowledge item */
case class DeleteError(s: String) extends Error("delete error: " + s)

/** errors that occur when retrieving a knowledge item */
case class GetError(s: String) extends Error("get error: " + s)

/** errors that occur when the backend believes it should find an applicable resource but cannot */
case class BackendError(s: String, p: Path) extends Error("Cannot find resource " + p.toString + ": " + s)

/** errors that occur when a configuration entry is missing */
case class ConfigurationError(id: String) extends Error(s"no entry for $id in current configuration")

/** errors that occur when presenting a knowledge item */
case class PresentationError(s: String) extends Error(s)

/** errors that occur when registering extensions  */
case class RegistrationError(s: String) extends Error(s)

/** errors that are not supposed to occur, e.g., when input violates the precondition of a method */
case class ImplementationError(s: String) extends Error("implementation error: " + s)

/** errors that occur during substitution with name of the variable for which the substitution is defined */
case class SubstitutionUndefined(name: LocalName, m: String) extends Error("Substitution undefined at " + name.toString + "; " + m)

case class LookupError(name: LocalName, context: objects.Context) extends Error("variable " + name.toString + " not declared in context " + context)

case class HeapLookupError(name: LocalName) extends Error("variable " + name.toString + " not declared")

/** base class for errors that are thrown by an extension */
abstract class ExtensionError(prefix: String, s: String) extends Error(prefix + ": " + s)

/** the type of continuation functions for error handling
  *
  * An ErrorHandler is passed in most situations in which a component (in particular [[BuildTarget]]s)
  * might produce a non-fatal error.
  */
abstract class ErrorHandler {
  /** the global indicator for errors that is not reset by mark */
  private var newErrors = false
  private var assumeNoErrors = true

  def mark {
    assumeNoErrors = true
  }

  /** true if errors occurred since ~creation~ last reset */
  def hasNewErrors: Boolean = newErrors

  /** true if no new errors occurred since the last call to mark */
  def noErrorsAdded: Boolean = assumeNoErrors

  /** registers an error
    *
    * This should be called exactly once on every error, usually in the order in which they are found.
    */
  def apply(e: Error) {
    if (e.level > 1) {
      newErrors = true
      assumeNoErrors = false
    }
    addError(e)
  }

  /** convenience for apply */
  def <<(e: Error) {
    apply(e)
  }

  /** evaluates a command with this class as the exception handler */
  def catchIn(a: => Unit) {
    try {
      a
    } catch {
      case e: Error => addError(e)
    }
  }

  protected def addError(e: Error)
}


/** Filters errors before passing them to the another error handler */
class FilteringErrorHandler(handler : ErrorHandler, filter : Error => Boolean) extends ErrorHandler {
  override def mark = handler.mark
  override def hasNewErrors = handler.hasNewErrors
  override def catchIn(a: => Unit) = handler.catchIn(a)
  override def apply(e: Error) = if (filter(e)) handler.apply(e) //otherwise ignore
  def addError(e : Error) = {} //nothing to do here, not called
}


/** an error handler that needs opening and closing */
abstract class OpenCloseHandler extends ErrorHandler {
  def open: Unit
  def close: Unit
}

/** combines the actions of multiple handlers */
class MultipleErrorHandler(handlers: List[ErrorHandler]) extends OpenCloseHandler {
  def addError(e: Error) {
    handlers.foreach(_.apply(e))
  }
  def open {
    handlers.foreach {
      case h: OpenCloseHandler => h.open
      case _ =>
    }
  }
  def close {
    handlers.foreach {
      case h: OpenCloseHandler => h.open
      case _ =>
    }
  }
}

/** stores errors in a list */
class ErrorContainer(report: Option[frontend.Report]) extends ErrorHandler {
  private var errors: List[Error] = Nil

  protected def addError(e: Error) {
    this.synchronized {
      errors ::= e
    }
    report.foreach(_ (e))
  }

  def isEmpty: Boolean = errors.isEmpty

  override def reset() {
    errors = Nil
  }


  def getErrors: List[Error] = errors.reverse
}

/** writes errors to a file in XML syntax
  *
  * @param fileName the file to write the errors into (convention: file ending 'err')
  * @param report if given, errors are also reported
  *
  */
class ErrorWriter(fileName: File, report: Option[frontend.Report]) extends OpenCloseHandler {
  private var file: StandardPrintWriter = null

  protected def addError(e: Error) {
    report.foreach(_ (e))
    file.write(new PrettyPrinter(240, 2).format(e.toNode) + "\n")
  }

  def open {
    file = File.Writer(fileName)
    file.write("<errors>\n")
  }
  /** closes the file */
  def close {
    file.write("</errors>\n")
    file.close()
  }
}

/** reports errors */
class ErrorLogger(report: frontend.Report) extends ErrorHandler {
  protected def addError(e: Error) {
    report(e)
  }
}

/** throws errors */
object ErrorThrower extends ErrorHandler {
  protected def addError(e: Error) {
    throw e
  }
}
