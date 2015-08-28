package object fivelangs {

  def intsFrom(i: Int): Stream[Int] = i #:: intsFrom(i+1)
  val nats = intsFrom(0).map(_.toString)
  val natInts = intsFrom(0)
  // stdlib bug; should just use filterNot when they make lazy again
  def freshVar(prohib: Set[String]) = nats.filter(!prohib(_)).head

  case class TypeError(message: String)

}
