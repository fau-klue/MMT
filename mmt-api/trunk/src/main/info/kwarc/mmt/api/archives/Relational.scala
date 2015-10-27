package info.kwarc.mmt.api.archives

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend._
import info.kwarc.mmt.api.parser._
import info.kwarc.mmt.api.utils._

/** a build target for computing mmt structure dependencies */
class Relational extends TraversingBuildTarget {
  /** source by default, may be overridden */
  def inDim = source

  def key = "mmt-deps"

  /** relational */
  val outDim = source

  val parser = new RelKeywordBasedParser

  override val outExt = "mmt"

  override def start(_args: List[String]) {
    controller.extman.addExtension(parser)
  }

  def includeFile(s: String) = s.endsWith(".mmt")

  private def getDocDPath(bt: BuildTask): DPath = {
    val inPathOMDoc = bt.inPath.toFile.setExtension("omdoc").filepath
    DPath(bt.base / inPathOMDoc.segments)
  }

  def buildFile(bf: BuildTask): Unit = {
    val ps = new ParsingStream(bf.base / bf.inPath.segments, getDocDPath(bf),
      bf.archive.namespaceMap, "mmt", File.Reader(bf.inFile))
    val doc = parser(ps)(bf.errorCont)
    storeRel(doc)
    doc.getModulesResolved(controller.localLookup) foreach indexModule
  }

  override def buildDir(bd: BuildTask, builtChildren: List[BuildTask]): Unit = {
    /* here we clean memory to avoid conflicts with subsequent builds.
     * without it nat.mmt results in several "error: invalid unit:" */
    controller.memory.content.clear()
    controller.memory.narration.clear
    // TODO: avoid memory usage and add dependencies (to be computed) directly in StructureParser
  }

  /** extract and store the relational information about a knowledge item */
  private def storeRel(se: StructuralElement): Unit = {
    controller.relman.extract(se) { r =>
      controller.depstore += r
    }
  }

  /** index a module */
  private def indexModule(mod: StructuralElement): Unit = {
    storeRel(mod)
  }

  // no history can be checked therefore simply rebuild on update
  override def update(a: Archive, up: Update, in: FilePath = EmptyPath): Unit = build(a, in)
}

/** dependency on relative file path (without inDim) in archive processed by target */
case class Dependency(archive: Archive, filePath: FilePath, target: String)

trait Dependencies {
  // override this method
  def getSingleDeps(controller: Controller, a: Archive, fp: FilePath): Set[Dependency] =
    Set.empty

  def getSingleDeps(controller: Controller, key: String, dep: Dependency): Set[Dependency] =
    if (dep.target == key)
      getSingleDeps(controller, dep.archive, dep.filePath)
    else controller.getOrAddBuildTarget(dep.target) match {
      case Some(bt) => bt.getSingleDeps(controller, dep.archive, dep.filePath)
      case None => Set.empty
    }

  def getDeps(controller: Controller, key: String, args: Set[Dependency]): List[Dependency] = {
    var visited: Set[Dependency] = Set.empty
    var unknown = args
    var deps: Map[Dependency, Set[Dependency]] = Map.empty
    while (unknown.nonEmpty) {
      val p = unknown.head
      val ds = getSingleDeps(controller, key, p)
      deps += ((p, ds))
      visited += p
      unknown -= p
      unknown ++= ds.diff(visited)
    }
    Relational.flatTopsort(controller, deps)
  }
}

/** an object to extract dependencies from a controller */
object Relational {
  /** get all archives */
  def getArchives(controller: Controller): List[Archive] =
    controller.backend.getStores.collect { case a: Archive => a }

  def close[A](inMap: Map[A, Set[A]]): Map[A, Set[A]] = {
    var changed = true
    var m = inMap
    while (changed) {
      changed = false
      m = m.map(p => (p._1, {
        val n: Set[A] = p._2.flatMap(m).union(p._2)
        if (n.size != p._2.size) changed = true
        n
      }))
    }
    m.filter(p => p._2.contains(p._1))
  }

  def topsort[A](controller: Controller, m: Map[A, Set[A]]): List[Set[A]] = {
    if (m.isEmpty) Nil
    else {
      val (noDeps, rest) = m.partition(_._2.isEmpty)
      if (noDeps.isEmpty) {
        controller.report(new Error("cyclic deps: " + close(m)) {})
        List(Set.empty, m.keySet)
      }
      else {
        val fst = noDeps.keySet
        fst :: topsort(controller, rest.map(p => (p._1, p._2.diff(fst))))
      }
    }
  }

  def flatTopsort[A](controller: Controller, m: Map[A, Set[A]]): List[A] =
    topsort(controller, m).flatMap(_.toList.sortBy(_.toString))
}
