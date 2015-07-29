import PostProcessApi._
import sbt.Keys._
import sbtunidoc.Plugin.UnidocKeys.unidoc

lazy val postProcessApi =
  taskKey[Unit]("post process generated api documentation wrt to source links.")

postProcessApi := postProcess(streams.value.log)

publish := {}

scalaVersion := "2.11.7"

unidocSettings

scalacOptions in(ScalaUnidoc, unidoc) ++=
  "-diagrams" +:
    Opts.doc.title("MMT") ++:
    Opts.doc.sourceUrl("file:/€{FILE_PATH}.scala")

target in(ScalaUnidoc, unidoc) := file("../doc/api")

lazy val cleandoc =
  taskKey[Unit]("remove api documentation.")

cleandoc := delRecursive(streams.value.log, file("../doc/api"))

lazy val apidoc =
  taskKey[Unit]("generate post processed api documentation.")

apidoc := postProcessApi.value

apidoc <<= apidoc.dependsOn(cleandoc, unidoc in Compile)

val deploy =
  TaskKey[Unit]("deploy", "assembles and copies fat jars to deploy location.")

def commonSettings(nameStr: String) = Seq(
  organization := "info.kwarc.mmt",
  version := "1.0.1",
  scalaVersion := "2.11.7",
  name := nameStr,
  sourcesInBase := false,
  scalaSource in Compile := baseDirectory.value / "src",
  resourceDirectory in Compile := baseDirectory.value / "resources",
  unmanagedBase := baseDirectory.value / "jars",
  isSnapshot := true,
  publishTo := Some(Resolver.file("file", new File("../deploy/main"))),
  exportJars := true,
  autoAPIMappings := true,
  connectInput in run := true,
  fork := true,
  deploy <<= deployPackage("main/" + nameStr + ".jar"),
  test in assembly := {},
  assemblyMergeStrategy in assembly := {
    case PathList("rootdoc.txt") => MergeStrategy.discard
    case x =>
      val oldStrategy = (assemblyMergeStrategy in assembly).value
      oldStrategy(x)
  }
)

lazy val tiscaf = (project in file("tiscaf")).
  settings(commonSettings("tiscaf"): _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src/main/scala",
    deploy <<= deployPackage("lib/tiscaf.jar"),
    libraryDependencies ++= Seq(
      "org.scalatest" % "scalatest_2.11" % "2.2.5" % "test",
      "net.databinder.dispatch" %% "dispatch-core" % "0.11.3" % "test",
      "org.slf4j" % "slf4j-simple" % "1.7.12" % "test"
    )
  )

lazy val api = (project in file("mmt-api/trunk")).
  dependsOn(tiscaf).
  settings(commonSettings("mmt-api"): _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src/main",
    scalaSource in Test := baseDirectory.value / "src/notests",
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value,
      "org.scala-lang" % "scala-reflect" % scalaVersion.value,
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.4")
  )

lazy val lfcatalog = (project in file("lfcatalog/trunk")).
  dependsOn(tiscaf).
  settings(commonSettings("lfcatalog") ++ oneJarSettings: _*).
  settings(
    libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.0.4",
    deploy <<= deployPackage("lfcatalog/lfcatalog.jar")
  )

lazy val lf = (project in file("mmt-lf")).
  dependsOn(api, lfcatalog).
  settings(commonSettings("mmt-lf"): _*).
  settings(
    scalaSource in Test := baseDirectory.value / "test",
    libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.5" % "test"
  )

lazy val tptp = (project in file("mmt-tptp")).
  dependsOn(api, lf).
  settings(commonSettings("mmt-tptp"): _*).
  settings(
    unmanagedJars in Compile += baseDirectory.value / "lib" / "tptp-parser.jar",
    libraryDependencies += "antlr" % "antlr" % "2.7.7"
  )

lazy val owl = (project in file("mmt-owl")).
  dependsOn(api, lf).
  settings(commonSettings("mmt-owl"): _*).
  settings(
    libraryDependencies += "net.sourceforge.owlapi" % "owlapi-apibinding" % "3.5.2"
  )

lazy val lfs = (project in file("mmt-lfs")).
  dependsOn(api, lf).
  settings(commonSettings("mmt-lfs"): _*)

lazy val mizar = (project in file("mmt-mizar/trunk")).
  dependsOn(api, lf, lfs).
  settings(commonSettings("mmt-mizar"): _*)

lazy val frameit = (project in file("frameit-mmt")).
  dependsOn(api, lfcatalog).
  settings(commonSettings("frameit-mmt"): _*)

lazy val pvs = (project in file("mmt-pvs")).
  dependsOn(api).
  settings(commonSettings("mmt-pvs"): _*)

lazy val specware = (project in file("mmt-specware")).
  dependsOn(api).
  settings(commonSettings("mmt-specware"): _*)

lazy val stex = (project in file("mmt-stex")).
  dependsOn(api).
  settings(commonSettings("mmt-stex"): _*)

lazy val webEdit = (project in file("mmt-webEdit")).
  dependsOn(stex).
  settings(commonSettings("mmt-webEdit"): _*)

lazy val planetary = (project in file("planetary-mmt")).
  dependsOn(stex).
  settings(commonSettings("planetary-mmt"): _*)

lazy val oeis = (project in file("mmt-oeis")).
  dependsOn(planetary).
  settings(commonSettings("mmt-oeis"): _*)

lazy val leo = (project in file("mmt-leo")).
  dependsOn(lf, api).
  settings(commonSettings("mmt-leo"): _*).
  settings(
    scalaSource in Test := baseDirectory.value / "test",
    libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.5" % "test"
  )

// just a wrapper project
lazy val mmt = (project in file("mmt-exts")).
  dependsOn(tptp, stex, pvs, specware, webEdit, oeis, leo).
  settings(commonSettings("mmt-exts"): _*).
  settings(
    exportJars := false,
    publish := {},
    deploy <<= assembly in Compile map deployTo("mmt.jar"),
    mainClass in assembly := Some("info.kwarc.mmt.api.frontend.Run"),
    assemblyOption in assembly := (assemblyOption in assembly).value.copy(
      prependShellScript = Some(Seq("#!/bin/bash", """exec /usr/bin/java -Xmx2048m -jar "$0" "$@"""")))
  )

val jeditJars = Seq(
  "Console.jar",
  "ErrorList.jar",
  "Hyperlinks.jar",
  "jedit.jar",
  "SideKick.jar"
)

lazy val jedit = (project in file("jEdit-mmt")).
  dependsOn(mmt).
  settings(commonSettings("jEdit-mmt"): _*).
  settings(
    resourceDirectory in Compile := baseDirectory.value / "src/resources",
    unmanagedJars in Compile ++= jeditJars map (baseDirectory.value / "lib" / _),
    deploy <<= assembly in Compile map
      deployTo("jedit-plugin/plugin/jars/MMTPlugin.jar"),
    assemblyExcludedJars in assembly := {
      val cp = (fullClasspath in assembly).value
      cp filter { j => jeditJars.contains(j.data.getName) }
    }
  )
