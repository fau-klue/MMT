package info.kwarc.mmt.tptp

import info.kwarc.mmt.tptp._
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.documents._
import info.kwarc.mmt.api.utils._
import info.kwarc.mmt.api.frontend._
import info.kwarc.mmt.api.backend._
import info.kwarc.mmt.api.symbols._
import info.kwarc.mmt.api.libraries._
import info.kwarc.mmt.api.modules._
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.presentation._

/**
 * TPTP Compiler, translates TPTP sources to OMDoc
 */
object TptpCompiler extends Compiler {

  def isApplicable(src : String) : Boolean = {
    true
  }

  override def compile(in : File, out : File) : List[CompilerError] = {
    println("Compiling " + in.toJava.getName())
    Nil
  }

  override def init(args : List[String] = Nil) {
    println("Initialization...")
//    TptpToMMT.controller.handle(ExecFile(new java.io.File("run.mmt")))
    println("Done")
  }
  
  override def destroy {
    println("Destroying")
  }
  
  def main(args: Array[String]): Unit = {
		TptpCompiler.init()
  }
}