package info.kwarc.mmt.got

import info.kwarc.mmt.api.{ContainerElement, StructuralElement}
import info.kwarc.mmt.api.checking.{Checker, CheckingEnvironment, ObjectChecker}

/**
  * Created by michael on 15.05.17.
  */
class GraphOptimizationTool(objectChecker: ObjectChecker) extends Checker(objectChecker){
  override val id: String = "GOT"

  /** checks the entire StructuralElement */
  override def apply(e: StructuralElement)(implicit env: CheckingEnvironment): Unit = {
    println("test")
  }

  /** checks the header of a StructuralElement, i.e., everything except for its body */
  override def applyElementBegin(e: StructuralElement)(implicit ce: CheckingEnvironment): Unit = {

  }

  /** checks the end of a StructuralElement (e.g., global conditions like totality of a view) */
  override def applyElementEnd(e: ContainerElement[_])(implicit ce: CheckingEnvironment): Unit = {

  }
}
