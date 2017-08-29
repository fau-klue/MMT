import java.io.{BufferedWriter, FileWriter}
import java.nio.file.Files
import java.nio.file.StandardCopyOption._

import sbt.Keys.packageBin
import sbt._

object PostProcessApi {
  /**
    * pacakges the compiled binaries and copies to deploy
    */
  def deployPackage(name: String): Def.Initialize[Task[Unit]] =
    packageBin in Compile map { jar => deployTo(name)(jar) }

  /*
   * copies files to deploy folder
   */
  def deployTo(name: String)(jar: sbt.File): Unit = {
    val tar = Utils.deploy / name
    Files.copy(jar.toPath, tar.toPath, REPLACE_EXISTING)
    println("copied file: " + jar)
    println("to file: " + tar)
  }

  def delRecursive(log: Logger, path: File): Unit = {
    def delRecursive(path: File): Unit = {
      path.listFiles foreach { f =>
        if (f.isDirectory) delRecursive(f)
        else {
          f.delete()
          log.debug("deleted file: " + path)
        }
      }
      path.delete()
      log.debug("deleted directory: " + path)
    }

    if (path.exists && path.isDirectory) delRecursive(path)
    else log.warn("ignoring missing directory: " + path)
  }

  def postProcess(log: Logger) = {
    val mmtFolder = File(System.getProperty("user.dir")).getParentFile
    val oldPrefix = "file:/" + mmtFolder.toString

    def doFolder(path: File): Unit = {
      log.debug("processing: " + path)
      path.list foreach { e =>
        if (!e.startsWith(".")) {
          val f = path / e
          if (f.isDirectory)
            doFolder(f)
          else if (e.endsWith(".html") && !e.startsWith("index")) {
            val s = io.Source.fromFile(f).getLines().mkString("", "\n", "\n")
            if (s.indexOf(oldPrefix) >= 0) {
              val w = new BufferedWriter(new FileWriter(f))
              log.debug("rewrote: " + f)
              w.write(s.replace(oldPrefix, "https://github.com/UniFormal/MMT/blob/master"))
              w.close()
            } else
              log.debug("skipping: " + f)
          }
        }
      }
    }

    val apiDir = mmtFolder / "apidoc"
    if (apiDir.exists && apiDir.isDirectory) doFolder(apiDir)
    else log.error("missing api directory: " + apiDir)
  }
}
