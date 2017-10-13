package info.kwarc.mmt.api.frontend

import info.kwarc.mmt.api._
import utils._
import archives._
import info.kwarc.mmt.api.building.{BuildTarget, TraversingBuildTarget}

/** a make-like shell extension that calls a build target on a file/folder in an archive
 */
class Make extends ShellExtension("make") {
   def helpText = ":make TARGETS ARCHIVE"
   def run(shell: Shell, args: List[String]): Boolean = {
     if (args.length < 2) {
       println(helpText)
       return true
     }
     val key = args(0)
     val input = controller.getHome resolve args(1)
     // get the archive containing the input file
     val (archRoot, relPath) = controller.backend.resolveAnyPhysical(input).getOrElse {
       println(input + " not found")
       return true
     }
     controller.backend.openArchive(archRoot)
     val arch = controller.backend.getArchive(archRoot).getOrElse {
       println(input + " not found") // should be impossible
       return true
     }
     // get the build target for the given key
     val bt = controller.extman.getOrAddExtension(classOf[BuildTarget], key).getOrElse {
       println("build target " + key + " not found")
       return true
     }
     // strip the dimension from the remaining input path (if any)
     val buildPath = relPath.segments match {
       case Nil => relPath
       case dim::rest => bt match {
         case tbt: TraversingBuildTarget =>
           if (FilePath(dim) == arch.resolveDimension(tbt.inDim))
             FilePath(rest)
           else {
             println(input + " is not an input file for " + key)
             return true
           }
       }
       case _ =>
         println(key + " can only be called on an entire archive")
         return true
     }
     // run the build target
     controller.report.addHandler(ConsoleHandler)
     controller.report.groups += "debug"
     controller.report.groups += "archives"
     controller.report.groups += bt.logPrefix
     bt(Build, arch, buildPath)
     true
   }
}