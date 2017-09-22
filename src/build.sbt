import PostProcessApi._
import sbt.Keys._
import sbtunidoc.Plugin.UnidocKeys.unidoc

publish := {}

scalaVersion := "2.11.8"

scalacOptions := Seq("-deprecation")

// = generation of API documentation

// configuration of unidoc, used by our apidoc target

unidocSettings

scalacOptions in(ScalaUnidoc, unidoc) ++=
  "-diagrams" +:
    Opts.doc.title("MMT") ++:
    Opts.doc.sourceUrl("file:/€{FILE_PATH}.scala")

target in(ScalaUnidoc, unidoc) := file("../apidoc")

// our targets
// Targets should not use the 'libraryDependencies' setting to register external dependencies to be managed via sbt.
// (Using library dependencies that are only needed for Test targets is acceptable.)
// Instead, they should create a lib folder, place the necessary jars there, and configure them using the 'unmanagedJars' setting.


lazy val postProcessApi =
  taskKey[Unit]("post process generated api documentation wrt to source links.")

postProcessApi := postProcess(streams.value.log)

lazy val cleandoc =
  taskKey[Unit]("remove api documentation.")

cleandoc := Utils.delRecursive(streams.value.log, file("../apidoc"))

lazy val apidoc =
  taskKey[Unit]("generate post processed api documentation.")

apidoc := postProcessApi.value

apidoc := apidoc.dependsOn(cleandoc, unidoc in Compile).value

// definition of our custom, project-specific targets

parallelExecution in ThisBuild := false
javaOptions in ThisBuild ++= Seq("-Xmx1g")
fork in Test := true

// task keys can be used PROJECTNAME/KEY to execute custom tasks as defined in the corresponding setting
val deploy =
  TaskKey[Unit]("deploy", "copies packaged jars for MMT projects to deploy location.")

val deployFull =
  TaskKey[Unit]("deployFull", "copies all (including tiscaf and lfcatalog) packaged jars to deploy location.")


// settings to be reused by all projects
def commonSettings(nameStr: String) = Seq(
  organization := "info.kwarc.mmt",
  version := "1.0.1",
  scalaVersion := "2.11.7",
  name := nameStr,
  sourcesInBase := false,
  libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.5" % "test",
  isSnapshot := true,
  exportJars := true,
  autoAPIMappings := true,
  connectInput in run := true,
  fork := true,
  test in assembly := {},
  assemblyMergeStrategy in assembly := {
    case PathList("rootdoc.txt") => MergeStrategy.discard // 2 versions from from scala jars
	case PathList("META-INF","MANIFEST.MF") => MergeStrategy.discard // should never be merged anyway
    case x => MergeStrategy.singleOrError // work around weird behavior of default strategy, which renames files for no apparent reason
	/*case x => 
	  val oldStrategy = (assemblyMergeStrategy in assembly).value
      oldStrategy(x)*/
  }
)

// settings to be reused for MMT projects (= local projects except tiscaf and lfcatalog)
def mmtProjectsSettings(nameStr: String) = commonSettings(nameStr) ++ Seq(
  scalaSource in Compile := baseDirectory.value / "src",
  scalaSource in Test := baseDirectory.value / "test" / "scala",
  resourceDirectory in Compile := baseDirectory.value / "resources",
  unmanagedBase := baseDirectory.value / "jars",
  publishTo := Some(Resolver.file("file", Utils.deploy.toJava/"main")),
  deploy := Utils.deployPackage("main/" + nameStr + ".jar").value,
  deployFull := Utils.deployPackage("main/" + nameStr + ".jar").value
)

// settings to be reused for MathHub projects
def mathhubProjectsSettings(group: String, name: String) = {
    val nameStr = group + "-" + name
    val folder = Utils.mathhubFolder / group / name
    val jar = folder / (name + ".jar")
	commonSettings(nameStr) ++ Seq(
	  scalaSource in Compile := folder / "scala"
	  //deploy := Utils.deployMathHub(jar).value,
	  //deployFull := Utils.deployMathHub(jar).value
    )
}

// individual projects

// projects that do not depend on mmt-api

lazy val tiscaf = (project in file("tiscaf")).
  settings(commonSettings("tiscaf"): _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src/main/scala",
    libraryDependencies ++= Seq(
        "net.databinder.dispatch" %% "dispatch-core" % "0.11.3" % "test",
        "org.slf4j" % "slf4j-simple" % "1.7.12" % "test"
    ),
    deployFull := Utils.deployPackage("lib/tiscaf.jar").value
  )

lazy val lfcatalog = (project in file("lfcatalog")).
  settings(commonSettings("lfcatalog") ++ oneJarSettings: _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "tiscaf.jar",
  	unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-xml.jar",
    deployFull := Utils.deployPackage("lfcatalog/lfcatalog.jar").value
  )

  
// mmt-api and the projects dependencing on it

lazy val api = (project in file("mmt-api")).
  settings(mmtProjectsSettings("mmt-api"): _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src" / "main",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "tiscaf.jar",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-compiler.jar",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-reflect.jar",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-parser-combinators.jar",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-xml.jar",
    libraryDependencies += "org.scala-lang" % "scala-parser-combinators" % "2.11.0-M4" % "test",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.0-M4" % "test",
    libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.11.0-M4" % "test"
  )


lazy val lf = (project in file("mmt-lf")).
  dependsOn(api % "compile -> compile; test -> test").
  settings(mmtProjectsSettings("mmt-lf"): _*).
  settings(
    unmanagedJars in Compile += Utils.deploy.toJava / "lfcatalog" / "lfcatalog.jar",
    libraryDependencies += "org.scala-lang" % "scala-parser-combinators" % "2.11.0-M4" % "test",
    unmanagedJars in Test += Utils.deploy.toJava / "lib" / "tiscaf.jar"
  )

lazy val leo = (project in file("mmt-leo")).
  dependsOn(lf, api).
  settings(mmtProjectsSettings("mmt-leo"): _*).
  settings(
    libraryDependencies += "com.assembla.scala-incubator" %% "graph-core" % "1.9.4"
  )

lazy val concepts = (project in file("concept-browser")).
  dependsOn(api).
  settings(mmtProjectsSettings("concept-browser"): _*).
  settings(
    libraryDependencies ++= Seq(
        "org.ccil.cowan.tagsoup" % "tagsoup" % "1.2"
    ),
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "tiscaf.jar",
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-xml.jar"
  )

lazy val tptp = (project in file("mmt-tptp")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-tptp"): _*).
  settings(
    unmanagedJars in Compile += baseDirectory.value / "lib" / "leo.jar"
  )

lazy val owl = (project in file("mmt-owl")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-owl"): _*).
  settings(
    unmanagedJars in Compile += baseDirectory.value / "lib" / "owlapi-bin.jar"
  )

lazy val mizar = (project in file("mmt-mizar")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-mizar"): _*)

lazy val frameit = (project in file("frameit-mmt")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("frameit-mmt"): _*)

lazy val mathscheme = (project in file("mmt-mathscheme")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-mathscheme"): _*)

lazy val pvs = (project in file("mmt-pvs")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-pvs"): _*)

lazy val metamath = (project in file("mmt-metamath")).
  dependsOn(api, lf, SourceDeps.mmScala).
  settings(mmtProjectsSettings("mmt-metamath"): _*)

lazy val tps = (project in file("mmt-tps")).
  dependsOn(api,lf).
  settings(mmtProjectsSettings("mmt-tps"): _*)

lazy val imps = (project in file("mmt-imps")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-imps"): _*)

lazy val odk = (project in file("mmt-odk")).
  dependsOn(api, lf).
  settings(mmtProjectsSettings("mmt-odk"): _*)

lazy val specware = (project in file("mmt-specware")).
  dependsOn(api).
  settings(mmtProjectsSettings("mmt-specware"): _*)

lazy val stex = (project in file("mmt-stex")).
  dependsOn(api).
  settings(mmtProjectsSettings("mmt-stex"): _*)

/*
lazy val guidedTours = (project in file("mmt-guidedTours")).
  dependsOn(api).
  settings(mmtProjectsSettings("mmt-guidedTours"): _*)
*/


lazy val webEdit = (project in file("mmt-webEdit")).
  dependsOn(stex).
  settings(mmtProjectsSettings("mmt-webEdit"): _*)

lazy val planetary = (project in file("planetary-mmt")).
  dependsOn(stex).
  settings(mmtProjectsSettings("planetary-mmt"): _*)

lazy val latex = (project in file("latex-mmt")).
  dependsOn(stex).
  settings(mmtProjectsSettings("latex-mmt"): _*)

lazy val openmath = (project in file("mmt-openmath")).
  dependsOn(api).
  settings(mmtProjectsSettings("mmt-openmath"): _*)

lazy val oeis = (project in file("mmt-oeis")).
  dependsOn(planetary).
  settings(mmtProjectsSettings("mmt-oeis"): _*).
  settings(
    unmanagedJars in Compile += Utils.deploy.toJava / "lib" / "scala-parser-combinators.jar"
  )

lazy val repl = (project in file("mmt-repl")).
  dependsOn(api).
  settings(mmtProjectsSettings("mmt-repl")).
  settings(
    libraryDependencies ++= Seq(
      "org.jline" % "jline" % "3.1.2"
    )
  )

// experimental projects that are not part of any tests: marpa-mmt, hets-mmt

// wrapper project that depends on most other projects
// the deployed jar is stand-alone and can be used as a unix shell script
lazy val mmt = (project in file("fatjar")).
  dependsOn(tptp, stex, pvs, specware, webEdit, oeis, odk, jedit, latex, openmath, imps, repl, concepts).
  settings(mmtProjectsSettings("fatjar"): _*).
  settings(
    exportJars := false,
    publish := {},
    deploy := {assembly in Compile map Utils.deployTo(Utils.deploy / "mmt.jar")}.value,
    mainClass in assembly := Some("info.kwarc.mmt.api.frontend.Run"),
    assemblyExcludedJars in assembly := {
      val cp = (fullClasspath in assembly).value
      cp filter {j => jeditJars.contains(j.data.getName)}
    },
    assemblyOption in assembly := (assemblyOption in assembly).value.copy(
      prependShellScript = Some(Seq("#!/bin/bash", """exec /usr/bin/java -Xmx2048m -jar "$0" "$@"""")))
  )

// jars to be used in Compile but not in the fat jar
val jeditJars = Seq(
  "Console.jar",
  "ErrorList.jar",
  "Hyperlinks.jar",
  "jedit.jar",
  "SideKick.jar",
  "jsr.jar"
)

val install =
  TaskKey[Unit]("install", "copies jedit jars to local jedit installation folder.")

lazy val jedit = (project in file("jEdit-mmt")).
  dependsOn(api,lf).
  settings(commonSettings("jEdit-mmt"): _*).
  settings(
    scalaSource in Compile := baseDirectory.value / "src",
    resourceDirectory in Compile := baseDirectory.value / "src/resources",
    unmanagedJars in Compile ++= jeditJars map (baseDirectory.value / "lib" / _),
    deploy := Utils.deployPackage("main/MMTPlugin.jar").value,
    deployFull := Utils.deployPackage("main/MMTPlugin.jar").value,
    install := Utils.installJEditJars
  )

// ************************************************** MathHub projects

// this works in principle but sbt complains about a cyclic dependency involving lfx
// sbt cannot handle project folder outside the root directory, but external source folders are fine; so we use a dummy folder here
/*
lazy val MMTLFX = (project in file("mathhub")).
  dependsOn(api,lf).
  settings(mathhubProjectsSettings("MMT","LFX"):_*)
*/
