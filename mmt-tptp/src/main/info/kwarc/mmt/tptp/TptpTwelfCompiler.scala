package info.kwarc.mmt.tptp

import tptp._

import info.kwarc.mmt.api._
import documents._
import utils._
import frontend._
import backend._
import symbols._
import libraries._
import modules._
import objects._
import presentation._

//import info.kwarc.mmt.lf.Twelf // maybe don't need this

import scala.sys.process._ // need this to execute shell commands
//import scala.io._ // to write to file
//import java.io._ // *


/**
 * TPTP twelf Compiler, translates TPTP sources to twelf using tptp2x
 */
class TptpTwelfCompiler extends Compiler {
  val key = "tptp-twelf"
  private var tptppath : String = null
  override def start(args: List[String]) {
     tptppath = args(0)     
  }
  
  def includeFile(n: String) : Boolean = n.endsWith(".tptp")
  def buildOne(bf: archives.BuiltFile) {
   // should be  .../TPTP/TPTP2X  
    var tptp2Xpath : String = tptppath.substring(0, tptppath.indexOf("MMT")) + "TPTP2X/"    
    // compiled file name
    var fileName : String = bf.inFile.toString().substring(bf.inFile.toString().lastIndexOf("/"))    
    // output file
    var outFile : String = bf.outFile.toString()      
    // output dir
    var outDir : String = bf.outFile.toString().substring(0,bf.outFile.toString().lastIndexOf("/"))
//    set file extension
    val fileout = bf.outFile.setExtension("elf")
         
    log("running tptp2X script on file " + fileName + " .....")
    log(fileout.toString())
    log(bf.inFile.toString)
    /* 
     * runs tptp2X script
     * 
     * with parameters:
     * 
     *  -flf format twelf
     *  -d- output directory - stdout
     */    
    val tptp2xcomp = "tptp2X"
    val flags : String = "-flf -d- -q2"
    val cmd : String = "tcsh " + tptp2Xpath + tptp2xcomp + " " + flags + " " + bf.inFile.toString()
  
//    log("about to run!!!")
//     check if file already exists, overwrite!  
    // check if output target dir exists, if not, create dirs
    var outf : java.io.File = new java.io.File(outDir.toString())
    if (! outf.exists()) {
      outf.mkdirs()
    }
    
    cmd #> new java.io.File(fileout.toString()) !        
    
    
    log("compiled to " + fileout.toString())
    
    
//    a nice way of dealing with concrete files should be found
//    right now the compiler is called with the same inFile as during the first compilation
//    i.e. .elf is sought even after 
  }
  
}

