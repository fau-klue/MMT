package info.kwarc.mmt.api.building

import info.kwarc.mmt.api.Level.Level
import info.kwarc.mmt.api.utils.File

/** builds a folder by concatenating the build results of its children
  *
  * not used yet!
  * */
/*
trait AggregatingBuildTarget extends TraversingBuildTarget {
   override def buildDir(bd: BuildTask, builtChildren: List[BuildTask], level: Level): BuildResult = {
     var res = ""
     builtChildren.foreach {bt =>
       val f = File.read(bt.outFile)
       res += f
     }
     File.write(bd.outFile, res)
     BuildSuccess(Nil, Nil)
   }
}
*/