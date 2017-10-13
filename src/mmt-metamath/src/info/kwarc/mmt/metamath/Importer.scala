package info.kwarc.mmt.metamath

import scala.collection.mutable.{HashMap, HashSet, ListBuffer, MutableList, Stack}
import info.kwarc.mmt.api._
import documents._
import archives._
import info.kwarc.mmt.api.parser.Reader
import info.kwarc.mmt.api.utils.{File, Unparsed}
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.frontend.Controller

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.combinator.RegexParsers
import org.metamath.scala._
import java.io.FileReader

import info.kwarc.mmt.api.building.{BuildResult, BuildTask}

class Importer extends archives.Importer {
  val key = "mm-omdoc"
  def inExts = List("mm")
  override def inDim = RedirectableDimension("mm")

  def importDocument(bf: BuildTask, index: Document => Unit): BuildResult = {
    log("Reading " + bf.inFile)
    val parser = new MMParser(new FileReader(bf.inFile))
    val e = try {
      log("File parsing...")
      val db = parser.parse
      log("Add to library...")
      val conv = new LFTranslator(controller, bf, index)
      val doc = conv.addDatabase(db)
      index(doc)
    } catch {
      case e : Exception => throw LocalError("error while translating").setCausedBy(e)
    }

    BuildResult.empty
  }

}
