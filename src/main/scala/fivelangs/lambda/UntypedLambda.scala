package fivelangs.lambda
import fivelangs._

object UntypedLambda {
  // for notational convenience
  sealed trait Exp {
    override def toString: String = this match {
      case Var(x) => x
      case Lam(p, t) => s"(\\$p. $t)"
      case App(t1, t2) => s"($t1 $t2)"
    }
  }

  case class Var(name: String) extends Exp
  case class Lam(param: String, t: Exp) extends Exp
  case class App(t1: Exp, t2: Exp) extends Exp

  object SampleExps {
    val id = Lam("x", Var("x"))
    val mock = Lam("x", App(Var("x"), Var("x")))
    val tru = Lam("x", Lam("y", Var("x")))
    val fals = Lam("x", Lam("y", Var("y")))
    def nat(i: Int) = {
      var count = i
      var inside: Exp = Var("x")
      while(count > 0) {
        inside = App(Var("f"), inside)
        count -= 1
      }
      Lam("f", Lam("x", inside))
    }
    val plus = Lam("n", Lam("m", Lam("f", Lam("x", App(Var("m"), App(Var("f"),
                  App(Var("n"), App(Var("f"), Var("x")))))))))
    val times = Lam("n", Lam("m", App(App(Var("m"), App(plus, Var("n"))), nat(0))))

    val abbreviations: Map[String, Exp] = Map(
      "true" -> tru,
      "false" -> fals,
      "id" -> id,
      "+" -> plus,
      "*" -> times
    )
  }

  def isValue(t: Exp): Boolean = t match {
    case App(Var(_), _) => true
    case App(_, _) => false
    case _ => true
  }

  def girth(t: Exp): Int = t match {
    case Var(_) => 1
    case Lam(_, t1) => 1 + girth(t1)
    case App(t1, t2) => 1 + girth(t1) + girth(t2)
  }

  def size(t: Exp): Int = t match {
    case Var(_) => 1
    case Lam(_, t1) => 1 + size(t1)
    case App(t1, t2) => 1 + math.max(girth(t1), girth(t2))
  }

  def freeVars(t: Exp): Set[String] = t match {
    case Var(name) => Set(name)
    case Lam(p, t) => freeVars(t) - p
    case App(t1, t2) => freeVars(t1) ++ freeVars(t2)
  }

  def isClosed(t: Exp): Boolean = freeVars(t).isEmpty

  def alpha(prohib: Set[String], lam: Lam): Lam = lam match {
    case Lam(param, t) if(prohib(param)) => {
      val newVar = freshVar(prohib)
      Lam(newVar, substitute(t, param, Var(newVar)))
    }
    case x => x
  }

  // substitute `sub` for `name` in `target`
  def substitute(sub: Exp, name: String, target: Exp): Exp = target match {
    case Var(y) if y == name => sub
    case v@Var(_) => v
    case l@Lam(_, _) => {
      val Lam(newP, newT) = alpha(freeVars(sub) ++ freeVars(l), l)
      val subbedTerm = substitute(sub, name, newT)
      Lam(newP, subbedTerm)
    }
    case App(t1, t2) => {
      val newT1 = substitute(sub, name, t1)
      val newT2 = substitute(sub, name, t2)
      App(newT1, newT2)
    }
  }

  def step(t: Exp): Exp = t match {
    case v if isValue(v) => v
    case App(t1, t2) if !isValue(t1) => App(step(t1), t2)
    case App(v1, t2) if !isValue(t2) => App(v1, step(t2))
    case App(Lam(p, t), v2) => substitute(v2, p, t)
    // otherwise we're stuck (free variable) or looping
  }

  def smallStepEval(t: Exp): Exp = {
    var term = t
    var nextTerm = step(t)
    while(term != nextTerm) {
      term = nextTerm
      nextTerm = step(nextTerm)
    }
    term
  }

  def bigStepEval(t: Exp): Exp = t match {
    case v if isValue(v) => v
    case App(t1, t2) => {
      val v1 = bigStepEval(t1)
      val v2 = bigStepEval(t2)
      (v1: @unchecked) match {
        case Lam(p, t) => {
          println(s"$v1 $v2")
          bigStepEval(substitute(t, p, v2))
        }
        // otherwise we're stuck (free variable) or looping
      }
    }
  }

  def superEval(t: Exp): Exp = t match {
    case v@Var(_) => v
    case l@Lam(p, t1) => Lam(p, superEval(t1))
    case App(t1, t2) => {
      val v1 = superEval(t1)
      val v2 = superEval(t2)
      (v1: @unchecked) match {
        case Lam(p, tt) => superEval(substitute(tt, p, v2))
        case _ => App(v1, v2)
      }
    }
  }

}
