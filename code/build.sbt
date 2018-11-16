name := "CoupledSim"

version := "0.1.0"

scalaVersion := "2.11.12"

val scalacOpts = Seq(
  "-Xmax-classfile-name", "140",
  "-feature",
  "-language:implicitConversions",
  "-language:postfixOps",
  "-language:existentials"
)

lazy val web = (project in file("web")).settings(
  scalaVersion := "2.11.12",
  scalaJSProjects := Seq(jsClient),
  isDevMode in scalaJSPipeline := false,
  pipelineStages in Assets := Seq(scalaJSPipeline),
  compile in Compile := ((compile in Compile) dependsOn scalaJSPipeline).value,
  libraryDependencies ++= Seq(
    "org.webjars" % "codemirror" % "5.13",
    "org.webjars" % "jquery" % "2.1.3",
    "org.webjars" % "bootstrap" % "3.3.6"
  )
).enablePlugins(SbtWeb)

lazy val shared = (project in file("shared")).settings(
  scalaVersion := "2.11.12",
  name := "shared",
  scalacOptions ++= scalacOpts,
  test in assembly := {},
  libraryDependencies ++= Seq(
    "org.scalaz" %%% "scalaz-core" % "7.2.26"
  )
)

lazy val jsClient = (project in file("js-client")).settings(
  scalaVersion := "2.11.12",
  name := "coupledsim-client",
  parallelExecution in ThisBuild := false,
  scalacOptions ++= scalacOpts,
  testFrameworks += new TestFramework("utest.runner.Framework"),
  resolvers += sbt.Resolver.bintrayRepo("denigma", "denigma-releases"),
  libraryDependencies ++= Seq(
    "org.scalaz" %%% "scalaz-core" % "7.2.26",
    "com.lihaoyi" %%% "utest" % "0.5.4",
    "org.singlespaced" %%% "scalajs-d3" % "0.3.4",
    "org.denigma" %%% "codemirror-facade" % "5.13.2-0.8",
    "com.github.karasiq" %%% "scalajs-bootstrap" % "2.3.1"
  ),
  artifactPath in (Compile,fastOptJS) :=
      ((target in fastOptJS).value /
        ((moduleName in fastOptJS).value + ".js")),
  artifactPath in (Compile,fullOptJS) := (artifactPath in (Compile,fastOptJS)).value,
  jsDependencies ++= Seq(
    "org.webjars" % "codemirror" % "5.13" / "codemirror.js",
    "org.webjars" % "jquery" % "2.1.3" / "2.1.3/jquery.js",
    "org.webjars" % "bootstrap" % "3.3.7" / "bootstrap.min.js"
  ),
  unmanagedSourceDirectories in Compile +=
      baseDirectory.value / ".." / "shared" / "src" / "main" / "scala-2.11"
).aggregate(shared).dependsOn(shared).enablePlugins(ScalaJSPlugin, ScalaJSWeb)

val flinkVersion = "1.6.1"

val flinkDependencies = Seq(
  "org.apache.flink" %% "flink-scala" % flinkVersion % "provided",
  "org.apache.flink" %% "flink-table" % flinkVersion % "provided",
  "org.apache.flink" %% "flink-streaming-scala" % flinkVersion % "provided",
  "org.apache.flink" %% "flink-gelly-scala" % "1.6.1")

lazy val flink = (project in file("flink")).
  settings(
    scalaVersion := "2.11.12",
    resolvers ++= Seq(
 	   "Apache Development Snapshot Repository" at "https://repository.apache.org/content/repositories/snapshots/",
    	Resolver.mavenLocal
    ),
    libraryDependencies ++= flinkDependencies ++ Seq(
      "org.scalatest" %% "scalatest" % "3.0.5" % "test"
      //,"org.slf4j" % "slf4j-simple" % "1.7.+"
    ),
    //fork in run := true,
    test in assembly := {},
    run in Compile := Defaults.runTask(fullClasspath in Compile,
                                   mainClass in (Compile, run),
                                   runner in (Compile, run)
    ).evaluated
  ).aggregate(shared).dependsOn(shared)

lazy val root = project.in(file(".")).settings(
  name := "coupledsim",
  testFrameworks += new TestFramework("utest.runner.Framework")
  ).aggregate(shared, jsClient, web)
   .dependsOn(jsClient, web)
