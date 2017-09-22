package info.kwarc.mmt.api.backend

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend._
import info.kwarc.mmt.api.utils._

/** builds git commands */
abstract class Git {
   /** the path to git, defaults to "git" */
   val gitPath = "git"
   /**
    * @param args the git commands (excluding "git")
    */
   def apply(args: String*): List[String]
}

/** prepends the path to git to the git commands */
object UnixGit extends Git {
   def apply(args: String*) = gitPath :: args.toList
}

/**
 * git behaves rather weirdly under windows, especially if authentication is needed
 *
 * this runs the [[UnixGit]] commands in the bash shell that comes with windows git
 *
 * @param sh the path to git's bash (may contain spaces), defaults to "sh"
 */
class WindowsGit(sh: String = "sh") extends Git {
   def apply(args: String*) = List(sh, "--login", "-c", UnixGit(args:_*).mkString("\"", " ", "\""))
}

/** client for repository managers (such as GitHub)
 *  each repository is considered as an one archive, identified by a string (usually of the form GROUP/NAME as in GitHub)
 */
abstract class ArchiveHub {
   val root: File
   def localPath(id: String) = {
     val ret = (root / id).canonical
     // make sure dots in id do not cause trouble 
     if (!(root <= ret)) throw GeneralError("local path escapes root path: " + ret)
     ret
   }
   /** create a new archive */
   def init(id: String): Unit
   /** clones a repository */
   def clone(id: String): Option[File]
   /** @return all locally available repositories */
   def localArchiveIDs: List[String]
   /** @return the directories of locally available repositories, i.e., grandchild directories of root */ 
   def localPaths = localArchiveIDs map localPath
   /** @return all remotely available repositories (unimplemented) */
   def remoteArchiveIDs: List[String] = Nil //TODO
   /** updates the local working copy of a repository */
   def pull(id: String): Unit
   /** pulls all local repositories */
   def pullAll {
     localArchiveIDs map pull
   }
   /** commits/pushes all changes to the remote server */
   def push(id: String): Unit
   /** pushes all local repositories */
   def pushAll {
     localArchiveIDs map push
   }
   /** downloads a remote repository as a zip file */
   def download(id: String): Option[File]
}

/**
 * wraps around a git shell client to repositories holdings MMT archives
 *
 * git is called as follows
 *  - on Windows: sh --login -c "git"
 *  - on other OS's: git
 * Users must make sure their shell interprets these commands properly.
 *
 * @param root the directory in which clones are created
 * @param report for logging
 * @param https toggle between https and ssh for remote URLs (see below) 
 * 
 * https URLs are good for anonymous cloning. ssh URLs are good for key-based authentication when pushing.
 * Fresh users should use https first and typically want to switch to ssh eventually.
 */
class MathHub(val uri: URI, val root: File, https : Boolean, val report: Report) extends ArchiveHub with Logger {
   val logPrefix = "oaf"
   /** choose UnixGit or WindowsGit depending on OS */
   private val gitCommand = OS.detect match {case Windows => new WindowsGit() case _ => UnixGit}
   private def git(dir: File, args: String*): Boolean = {
      val command = gitCommand(args:_*)
      log(command.mkString(" ") + " in " + dir.toString)
      val result = ShellCommand.runIn(dir, command :_*)
      result match {
         case Some(m) =>
            logError(m)
            false
         case None =>
            true
      }
   }
   /** the remote URL of the repository to be used for init and clone */
   private object Remote {
      private def sshurl(pathS: String) = "git@" + uri.authority.getOrElse("") + ":" + pathS + ".git"
      private def httpsurl(pathS: String) = "https://" + uri.authority.getOrElse("") + "/" + pathS + ".git"
      def url(pathS: String) = if (https) httpsurl(pathS) else sshurl(pathS)
   }
   
   /** initializes a repository */
   def init(pathS: String) {
      val path = utils.stringToList(pathS, "/")
      val repos = root / path
      val readme = "README.txt"
      val mf = "MANIFEST.MF"
      repos.mkdirs
      git(repos, "init")
      File.write(repos / "source" / readme, "commit your sources in this folder")
      git(repos, "add", s"source/$readme")
      File.WriteLineWise(repos / mf, List(s"id: $pathS", s"narration-base: http://mathhub.info/$pathS"))
      git(repos, "add", mf)
      git(repos, "commit", "-m", "\"automatically created by MMT\"")
      git(repos, "remote", "add", "origin", Remote.url(pathS))
      git(repos, "push", "origin", "master")
   }
   /** clones a repository */
   def clone(path: String): Option[File] = {
      val lp = localPath(path)
      if (lp.exists) {
         log("target directory exists, skipping")
      } else {
         val success = git(root, "clone", Remote.url(path), path)
         if (!success) {
           if (lp.exists) {
              log("git failed, deleting " + lp)
              lp.deleteDir
           }
           return None
         }
      }
      Some(lp)
   }
   /** set all remote URL (practical to switch to upgrade from https to ssh) */
   def setRemoteURL {
     localArchiveIDs map {id =>
       git(localPath(id), "remote", "set-url", "origin", Remote.url(id))
     }
   }
   def localArchiveIDs = root.subdirs.flatMap {g => g.subdirs.map(r => g.name + "/" + r.name)}
   def pull(id: String) {
     git(localPath(id), "pull", "origin", "master")
   }
   def push(id: String) {
     git(localPath(id), "push")
   }
   def download(id: String) = {
     TrustAllX509TrustManager.trustAll // awkward, but gitlab uses certificate from startssl.com, which is not recognized by Java
     val downloadURI = (uri / id / "repository" / "archive.zip") ? "ref=master"
     val target = root/id
     val zip = target.addExtension("zip")
     log("downloading from " + downloadURI)
     try {
       File.download(downloadURI, zip)
       File.unzip(zip, target, skipRootDir = true)
       Some(target)
     } catch {
       case _: Exception => None
     } finally {
       zip.delete
     }
   }
}

object MathHub {
   val defaultURL = URI("http", "gl.mathhub.info")
}
