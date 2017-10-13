package info.kwarc.mmt.api.building

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.archives.Archive
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.archives._
import info.kwarc.mmt.api.modules.{DeclaredTheory, DeclaredView}
import info.kwarc.mmt.api.utils._

import scala.util.Try

/** auxiliary type to represent the parameters and result of building a file/directory
  *
  * this is no case class due to a state-dependent error continuation
  *
  * @param inFile    the input file
  * @param inPath    the path of the input file inside the archive, relative to the input dimension
  * @param children  the build tasks of the children if this task refers to a directory
  * @param outFile   the intended output file
  * @param errorCont BuildTargets should report errors here (instead of directly writing to errFile)
  */
class BuildTask(val key: String, val archive: Archive, val inFile: File, val children: Option[List[BuildTask]],
                val inPath: FilePath, val outFile: File, val errorCont: OpenCloseHandler,
                val target : TraversingBuildTarget, val policy : QueuePolicy = QueuePolicy.default) extends MMTTask {
  /** build targets should set this to true if they skipped the file so that it is not passed on to the parent directory */
  var skipped = false
  /** the narration-base of the containing archive */
  val base = archive.narrationBase

  /** the MPath corresponding to the inFile if inFile is a file in a content-structured dimension */
  def contentMPath: MPath = Archive.ContentPathToMMTPath(inPath)

  /** the DPath corresponding to the inFile if inFile is a folder in a content-structured dimension */
  def contentDPath: DPath = Archive.ContentPathToDPath(inPath)

  /** (possibly shorter) output file name to be shown in user messages */
  def outPath: FilePath = outFile.toFilePath

  /** the DPath corresponding to the inFile if inFile is in a narration-structured dimension */
  def narrationDPath: DPath = DPath(base / inPath.segments)

  def isDir = children.isDefined

  def isEmptyDir = children.isDefined && children.get.isEmpty

  /** the name of the folder if inFile is a folder */
  def dirName: String = outFile.toFilePath.dirPath.name

  def asDependency: BuildDependency = children match {
    case Some(ch) => DirBuildDependency(key, archive, inPath, ch)
    case None => FileBuildDependency(key, archive, inPath)
  }

  /** task should be queued at end */
  // var lowPriority: Boolean = true

  // def highPriority = !lowPriority

  /** task was not requested directly but added as dependency of some other task */
  // var dependencyClosure: Boolean = false

  /** task was eventually run despite being blocked due to missing dependencies */
  // var forceRun: List[Dependency] = Nil

  // private val estRes = target.estimateResult(task)

  /** dependencies that are needed for an up-to-date check */
  var neededDeps: List[Dependency] = Nil // estRes.used

  /** dependencies that will be used but are not available */
  var missingDeps: List[Dependency] = Nil // estRes.used
  /** resources that will be provided once successfully built */
  var willProvide: List[ResourceDependency] = Nil // estRes.provided
  /** update policy */
  // var updatePolicy = Update(Level.Force)

  def toJString: String = {
    val str =inPath.toString
    (if (str.isEmpty) archive.id else str) + " (" + key + ")" +
      missingDeps.map(_.toJString).mkString(" [", ", ", "]")
  }

  def toJson: JSONString = JSONString(toJString)

  /*
  def merge(qt: QueuedTask): Unit = {
    updatePolicy = updatePolicy.merge(qt.updatePolicy)
    lowPriority = lowPriority && qt.lowPriority
    dependencyClosure = dependencyClosure && qt.dependencyClosure
    // not sure if missingDeps and willProvide should be merged
  }
  */
}


/** */
sealed abstract class BuildResult {
  /**
    * resources that were used during building
    */
  def used: List[Dependency]

  /** resources that have been built successfully */
  def provided: List[ResourceDependency]

  def toJson: JSON

  def toJsonPart: List[(String, JSON)] =
    List(("needed", JSONArray()),
      ("used", JSONArray(used.map(_.toJson): _*)),
      ("provided", JSONArray(provided.map(_.toJson): _*)))
}

object BuildResult {
  def empty: BuildSuccess = BuildSuccess(Nil, Nil)
  /** convenience method to create the result of successfully importing a (typically) externally checked document */
  def fromImportedDocument(doc: documents.Document, success : Boolean)(controller : Controller) = {
    val modules = doc.getModulesResolved(controller.globalLookup)
    val provided = modules.map(_.path) map LogicalDependency

    val used = modules.flatMap {
      case th : DeclaredTheory => th.meta.toList ::: th.getIncludes ::: th.getNamedStructures.map(_.from.toMPath)
      case v : DeclaredView => v.from.toMPath :: v.to.toMPath :: v.getIncludes
    }.distinct.map(LogicalDependency) // TODO this is an ugly hack and should be replaced by a precise method. Requires some planning though; in the
    // TODO meantime it's better than nothing
    val missing = used.collect {
      case ld if Try(controller.getO(ld.mpath)).toOption.flatten.isEmpty => ld
    }
    if (missing.nonEmpty) {
      MissingDependency(missing,provided,used)
    } else if (!success)
      BuildFailure(used, provided)
    else
      BuildSuccess(used, provided)
    /*
    val provs = doc.getDeclarations collect {
      case r: documents.MRef => LogicalDependency(r.target)
    }
    BuildSuccess(Nil, provs)
    */
  }
}

case class BuildEmpty(str: String) extends BuildResult {
  def used: List[Dependency] = Nil

  def provided: List[ResourceDependency] = Nil

  def toJson: JSON = JSONObject(("result", JSONString(str)) :: toJsonPart: _*)
}

/** successful build */
case class BuildSuccess(used: List[Dependency], provided: List[ResourceDependency]) extends BuildResult {
  def toJson: JSON = JSONObject(("result", JSONString("success")) :: toJsonPart: _*)
}

/** unrecoverable failure */
case class BuildFailure(used: List[Dependency], provided: List[ResourceDependency]) extends BuildResult {
  def toJson: JSON = JSONObject(("result", JSONString("failure")) :: toJsonPart: _*)
}

/** recoverable failure: build should be retried after building a missing dependency */
case class MissingDependency(needed: List[Dependency], provided: List[ResourceDependency], used : List[Dependency]) extends BuildResult {

  def toJson: JSON = JSONObject(("result", JSONString("failed")) ::
    ("needed", JSONArray(needed.map(_.toJson): _*)) :: toJsonPart.tail: _*)
}

/** dependency of a [[BuildTask]] */
sealed abstract class Dependency {
  /** convert to a string for toJson */
  def toJString: String

  def toJson: JSONString = JSONString(toJString)
}

sealed abstract class BuildDependency extends Dependency {
  def key: String

  def archive: Archive

  def inPath: FilePath

  def getTarget(controller: Controller): TraversingBuildTarget =
    controller.extman.getOrAddExtension(classOf[TraversingBuildTarget], key).getOrElse {
      throw RegistrationError("build target not found: " + key)
    }

  def getErrorFile(controller: Controller): File
}

/** dependency on another [[BuildTask]]
  *
  * @param inPath path to file (without inDim)
  */
case class FileBuildDependency(key: String, archive: Archive, inPath: FilePath) extends BuildDependency {
  def toJString: String = inPath.toString + " (" + key + ")"

  def getErrorFile(controller: Controller): File = (archive / errors / key / inPath).addExtension("err")
}

/** like [[FileBuildDependency]] but for a directory
  *
  * @param inPath path to file (without inDim)
  */
case class DirBuildDependency(key: String, archive: Archive, inPath: FilePath, children: List[BuildTask])
  extends BuildDependency {
  def toJString: String = archive.id + "/" + inPath.toString +
    " (" + key + ") " + children.map(bt => bt.inPath).mkString("[", ", ", "]")

  def getErrorFile(controller: Controller): File = getTarget(controller).getFolderErrorFile(archive, inPath)
}

sealed abstract class ResourceDependency extends Dependency

/** a dependency on a physical resource
  */
case class PhysicalDependency(file: File) extends ResourceDependency {
  def toJString: String = file.toString
}

/** a dependency on an MMT module that must be provided by building some other [[BuildTask]]
  *
  * providing the dependency typically requires some catalog to determine the appropriate [[BuildTask]]
  */
case class LogicalDependency(mpath: MPath) extends ResourceDependency {
  def toJString: String = mpath.toString
}