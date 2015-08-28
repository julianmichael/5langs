import sbt._
import Keys._

object MyBuild extends Build {
  lazy val fivelangs = Project("fivelangs", file(".")).
    dependsOn(molt % "compile")
  lazy val molt = RootProject( file("lib/molt") )
}