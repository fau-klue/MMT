/**
 * This is the main wrapper class for MMT.
 * It imports main MMT class, parses twelf/spec files upon invocation, calls '
 * logic translation->abstract syntax->concrete syntax->Hets style logic definition' 
 *   pipeline
 * 
 * created by Aivaras:
 * a.jakubauskas@jacobs-university.de
 */
package info.kwarc.mmt.hets


import info.kwarc.mmt.api._
import backend._
import utils.File._ //maybe the stuff here is useful

import scala.util.control.Exception._

// for exception handling
import java.io.FileNotFoundException
import java.io.IOException
import utils._
import utils.MyList._
import modules._
import patterns._
import libraries._
import frontend._
import symbols._
import objects._
import objects.Conversions._
import info.kwarc.mmt.api.frontend._ // for report
//import utils.MyList


object SpecTest {
  
   val latinbase = "http://latin.omdoc.org/logics/syntax"
   val foundational = "http://cds.omdoc.org/foundations"  
  
   def main(args: Array[String]) {
     
     if (args.length == 0) {
    	 println("No arguments given. Expecting [flag] [filepath] arguments.\nTerminating.")
    	 return
     } 
     
       try {         
         val flag = args(0)
         println("flag: " + flag)
         val filename = args(1) // take first argument - file name of the source
         
         //TODO make global
         val controller = new frontend.Controller
         val uri = new utils.URI(None,None,List(foundational + "?" + filename))
         controller.handleLine("archive add /home/aivaras/TPTP/MMT/theories")
         val fl = File(new java.io.File(filename))
         if (!(new java.io.File(filename).exists())) {
           println("File " + filename + " does not exist!")
           return
         }

         val argl = args.toList
         
         if (argl contains "-readSpec") {        	
           // parse logic spec
           println("reading logic specification")
           println("\t\t..from file " + filename)
           val source = scala.io.Source.fromFile(new java.io.File(filename),"UTF-8")       
           val (doc, err) = controller.textReader.readDocument(source, DPath(uri))(controller.termParser.apply(_))
           source.close()           
           if (!err.isEmpty) {
        	   println("errors while reading " + filename + " encountered:")
        	   err map println
        	   return
           } else {
             println("no errors while reading")
             doc.getModulesResolved(controller.localLookup) foreach {
             	case t:DeclaredTheory => println(t.toString())
             }           
           }
         } else if (argl contains "-t") {
           println(".... test test ....")
           val source = scala.io.Source.fromFile(new java.io.File(filename),"UTF-8")       
           val (doc, err) = controller.textReader.readDocument(source, DPath(uri))(controller.termParser.apply(_))
           source.close()           
           if (!err.isEmpty) {
        	   println("errors while reading " + filename + " encountered:")
        	   err map println
        	   return
           } else {
             println("spec test")
             println("no errors while reading")
             println(doc.toString())
           }
           doc.getModulesResolved(controller.localLookup) foreach {
             case t:DeclaredTheory => println(t.toString())
           }
         }
         
         
       } // <------------ end of main
      catch {
        case e : java.lang.ArrayIndexOutOfBoundsException => println("Error: array index out of bounds")
        													e.printStackTrace()
        													
        case e : java.lang.OutOfMemoryError => println("ran out of memory!") 
        										e.printStackTrace()
//
//        case e : FileNotFoundException => println("no such file: " + args(0) + ", check spelling")
//        case e : IOException => println("IO exception")
//        case e => println("unknown error:")
//        				throw e
//        				e.printStackTrace()
      }
       
     
     
   }
}