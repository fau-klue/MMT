package info.kwarc.mmt.got

import info.kwarc.mmt.api.{MPath, Path}
import info.kwarc.mmt.api.checking.ObjectChecker
import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.modules.DeclaredTheory
import info.kwarc.mmt.api.symbols.PlainInclude

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * Created by michael on 15.05.17.
  */
class GraphOptimizationTool extends Extension {

  def findRedundancy(theoryPath : MPath) : List[Path] = {
    val theory : DeclaredTheory = controller.get(theoryPath).asInstanceOf[DeclaredTheory]
    var ret = ListBuffer[Path]()
    var subIncludes = mutable.HashSet[MPath]()
    for (include <- theory.getIncludes) {
      for (subInclude <- controller.get(include).asInstanceOf[DeclaredTheory].getIncludes) {
        subIncludes += subInclude
      }
    }
    for (declaration <- theory.getPrimitiveDeclarations) {
      declaration match {
        case PlainInclude(from, _) =>
          if (subIncludes.contains(from)) {
            ret+= declaration.path
          }
        case _ => Unit
      }
    }
    ret.toList
  }

  def removeRedundancy(theoryPath : MPath) : Unit = {
    for (redundancy <- findRedundancy(theoryPath)) {
      controller.delete(redundancy)
    }
  }

}
