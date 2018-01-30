package info.kwarc.mmt.api.utils

import java.net.URLDecoder
import java.util.jar.JarFile

import info.kwarc.mmt.api._

object MMTSystem {
  /** information about how MMT was run, needed to access resources */
  sealed abstract class RunStyle
  /** run from expected folder structure */
  sealed abstract class DeployRunStyle extends RunStyle {
    /** the deploy folder */
    def deploy: File
  }
  /** run from self-contained mmt.jar */
  sealed trait IsFat {
    def jar: File
  }
  /** run from installed fat jar */
  case class FatJar(jar: File) extends DeployRunStyle with IsFat {
    def deploy = jar.up
  }
  /** run from a fat jar that is not part of the expected file structure */
  case class DownloadedFatJar(jar: File) extends RunStyle with IsFat
  /** run from mmt-api.jar in deploy folder */
  case class ThinJars(deploy: File) extends DeployRunStyle
  /** run from classes in src/mmt-api folder */
  case class Classes(classFolder: File) extends DeployRunStyle {
     val root = {
       var src = classFolder.up
       while (!src.isRoot && src.name != "src") src = src.up
       src.up
     }
     def deploy = root / "deploy"
     def api = root / "src" / "mmt-api"
     def projectFolder(name: String) = api.up / name
     def resources = api / "resources"
   }
  /** run in unknown way, in particular as part of jedit */
  case object OtherStyle extends RunStyle

  /** the [[RunStyle]] of the current run */
  lazy val runStyle = {
     val location = getClass.getProtectionDomain.getCodeSource.getLocation
     if (location == null)
        OtherStyle
     else {
       val classFolder = File(location.getPath)
       if (classFolder.isFile) {
         if (classFolder.name == "mmt.jar") {
           if (classFolder.up.name == "deploy")
              FatJar(classFolder)
           else
              DownloadedFatJar(classFolder)
         } else
           ThinJars(classFolder.up.up)
      } else {
         Classes(classFolder)
      }
     }
   }

  /** the version of MMT being used */
  lazy val version: String = {
    Option(this.getClass.getPackage.getImplementationVersion).getOrElse(getResourceAsString("versioning/system.txt") + "--localchanges")
  }

   /** expected location of the user's mmtrc file */
   val userConfigFile = {
      OS.detect match {
         case Windows => OS.settingsFolder / "mmt" / "mmtrc"
         case MacOS => OS.settingsFolder / "mmt" / ".mmtrc"
         case _ => OS.settingsFolder / ".mmtrc"
      }
   }

   /** retrieves a resource from the jar or the resource folder depending on the [[RunStyle]], may be null */
   def getResource(path: String): java.io.InputStream = {
      if(!path.startsWith("/")){ return getResource("/" + path) } // make sure that the st
      runStyle match {
        case _:IsFat | _:ThinJars | OtherStyle =>
          getClass.getResourceAsStream(path) // the file inside the JAR
        case rs: Classes =>
          val file = rs.resources / path
          if (file.exists)
             new java.io.FileInputStream(file)
          else
             null
      }
   }
   def getResourceAsString(path: String): String = Option(getResource(path)) match {
     case Some(r) => utils.readFullStream(r)
     case None => throw GeneralError(s"cannot find resource $path (run style is $runStyle)")
   }

  /** return a list of available resources at the given path */
  def getResourceList(path: String) : List[String] = runStyle match {
      // running from jar
      case _:IsFat | _:ThinJars | OtherStyle =>

        // find the path to the current jar
        val classPath = getClass.getName.replace(".", "/") + ".class"
        val myPath = getClass.getClassLoader.getResource(classPath)
        val jarPath = myPath.getPath.substring(5, myPath.getPath.indexOf("!"))

        // open the jar and find all files in it
        import scala.collection.JavaConverters._
        val entries = new JarFile(URLDecoder.decode(jarPath, "UTF-8")).entries.asScala.map(e => "/" + e.getName)

        // find all the resources within the given path, then remove the prefix
        entries.filter(e => e.startsWith(path) && !e.endsWith("/")).map(_.stripPrefix(path)).toList

      // running from classes, list the source directory
      case rs: Classes =>
        val base = (rs.resources / path).toJava
        base.listFiles.map(f => { File(base).relativize(f).toString }).toList
    }
}
