package fivelangs.lambda
import fivelangs._
object SimplyTypedLambda {
  // Simply-typed lambda calculus with functions, products,
  // conditionals, unit, and bools.
  // Call-by-value.
  // ints were too much extra code; should just be included later
  // in the "extensible" variant that is to follow.
  // coproducts require those pesky annotations
  // because we don't have subtyping/Top or type inference
  // so I decided to nix them too.

  sealed trait Exp {
    override def toString: String = this match {
      case Var(x) => x
      case Lam(p, typ, body) => s"(\\$p: $typ. $body)"
      case App(t1, t2) => s"($t1 $t2)"
      case Cond(c, b, ow) => s"if $c then $b else $ow"
      case Pair(t1, t2) => s"($t1, $t2)"
      case Pi1(t) => s"π1 $t"
      case Pi2(t) => s"π2 $t"
      /*
      case Inl(t) => s"inl $t"
      case Inr(t) => s"inr $t"
      case Case(t, lName, lBody, rName, rBody) =>
        s"case $t of (inl $lName => $lBody) (inr $rName => $rBody)"
      */
      case Unit => "()"
      case BoolLiteral(b) => s"$b"
      case And(a, b) => s"$a && $b"
      case Or(a, b) => s"$a || $b"
      /*
      case IntLiteral(i) => s"$i"
      case Plus(a, b) => s"$a + $b"
      case Minus(a, b) => s"$a - $b"
      case Times(a, b) => s"$a * $b"
      case Div(a, b) => s"$a / $b"
      */
    }
  }

  case class Var(name: String) extends Exp
  // functions
  case class Lam(param: String, paramType: Type, body: Exp) extends Exp
  case class App(t1: Exp, t2: Exp) extends Exp
  // conditionals
  case class Cond(cond: Exp, body: Exp, otherwise: Exp) extends Exp
  // products
  case class Pair(t1: Exp, t2: Exp) extends Exp
  case class Pi1(t: Exp) extends Exp
  case class Pi2(t: Exp) extends Exp
  // coproducts
  /*
  case class Inl(t: Exp) extends Exp
  case class Inr(t: Exp) extends Exp
  case class Case(t: Exp, lName: String, lBody: Exp,
                          rName: String, rBody: Exp) extends Exp
  */
  // unit
  case object Unit extends Exp
  // bools
  case class BoolLiteral(b: Boolean) extends Exp
  case class And(a: Exp, b: Exp) extends Exp
  case class Or(a: Exp, b: Exp) extends Exp
  // ints
  /*
  case class IntLiteral(n: Int) extends Exp
  case class Plus(a: Exp, b: Exp) extends Exp
  case class Minus(a: Exp, b: Exp) extends Exp
  case class Times(a: Exp, b: Exp) extends Exp
  case class Div(a: Exp, b: Exp) extends Exp
  */

  object SampleExps {
    val tru = BoolLiteral(true)
    val fals = BoolLiteral(false)
    val unit = Unit
    def id(typ: Type) = Lam("x", typ, Var("x"))
  }

  // the types themselves
  sealed trait Type
  case class TFunc(a: Type, b: Type) extends Type
  case class TProd(a: Type, b: Type) extends Type
  // case class TSum(a: Type, b: Type) extends Type
  case object TUnit extends Type
  case object TBool extends Type
  // case object TInt extends Type

  case class TypeError(message: String)

  def isValue(t: Exp): Boolean = t match {
    case Lam(_, _, _) => true
    case Pair(v1, v2) => isValue(v1) && isValue(v2)
    // case Inl(v) => isValue(v)
    // case Inr(v) => isValue(v)
    case Unit => true
    case BoolLiteral(_) => true
    // case IntLiteral(_) => true
    case _ => false
  }

  /* Implement if I end up needing it
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
  */

  def freeVars(t: Exp): Set[String] = t match {
    case Var(name) => Set(name)
    case Lam(p, _, t) => freeVars(t) - p
    case App(t1, t2) => freeVars(t1) ++ freeVars(t2)
    case Cond(c, b, ow) => freeVars(c) ++ freeVars(b) ++ freeVars(ow)
    case Pair(t1, t2) => freeVars(t1) ++ freeVars(t2)
    case Pi1(t) => freeVars(t)
    case Pi2(t) => freeVars(t)
    /*
    case Inl(t) => freeVars(t)
    case Inr(t) => freeVars(t)
    case Case(t, lName, lBody, rName, rBody) =>
      freeVars(t) ++ freeVars(lBody) ++ freeVars(rBody)
    */
    case And(a, b) => freeVars(a) ++ freeVars(b)
    case Or(a, b) => freeVars(a) ++ freeVars(b)
    /*
    case Plus(a, b) => freeVars(a) ++ freeVars(b)
    case Minus(a, b) => freeVars(a) ++ freeVars(b)
    case Times(a, b) => freeVars(a) ++ freeVars(b)
    case Div(a, b) => freeVars(a) ++ freeVars(b)
    */
    // bool, int literals; unit
    case _ => Set.empty[String]
  }

  def isClosed(t: Exp): Boolean = freeVars(t).isEmpty

  // TODO factor this out better, and possibly use the state monad
  def alpha(prohib: Set[String], lam: Lam): Lam = lam match {
    case Lam(param, typ, t) if(prohib(param)) =>
      val newVar = freshVar(prohib)
      Lam(newVar, typ, substitute(Var(newVar), param, t))
    case x => x
  }
  /*
  def alpha(prohib: Set[String], cas: Case): Case = cas match {
    case Case(t, lName, lBody, rName, rBody) =>
      val newName = freshVar(prohib)
      val (newLName, newLBody) =
        if(prohib(lName)) {
          (newName, substitute(Var(newName), lName, lBody))
        } else {
          (lName, lBody)
        }
      val (newRName, newRBody) =
        if(prohib(rName)) {
          (newName, substitute(Var(newName), rName, rBody))
        } else {
          (rName, rBody)
        }
      Case(t, newLName, newLBody, newRName, newRBody)
  }
  */

  // as of here I stopped trying to implement ints.

  // substitute `sub` for `name` in `target`
  def substitute(sub: Exp, name: String, target: Exp): Exp = {
    def doSub(x: Exp) = substitute(sub, name, x)
    target match {
      case Var(y) if y == name => sub
      case v@Var(_) => v
      case l@Lam(_, _, _) =>
        val Lam(newP, typ, newT) = alpha(freeVars(sub) ++ freeVars(l), l)
        Lam(newP, typ, doSub(newT))
      case App(t1, t2) => App(doSub(t1), doSub(t2))
      case Cond(c, b, ow) => Cond(doSub(c), doSub(b), doSub(ow))
      case Pair(t1, t2) => Pair(doSub(t1), doSub(t2))
      case Pi1(t) => Pi1(doSub(t))
      case Pi2(t) => Pi2(doSub(t))
      /*
      case Inl(t) => Inl(doSub(t))
      case Inr(t) => Inr(doSub(t))
      case c@Case(_, _, _, _, _) =>
        val Case(t, lName, lBody, rName, rBody) =
          alpha(freeVars(sub) ++ freeVars(c), c)
        Case(t, lName, doSub(lBody), rName, doSub(rBody))
      */
      case Unit => Unit
      case b@BoolLiteral(_) => b
      case And(a, b) => And(doSub(a), doSub(b))
      case Or(a, b) => Or(doSub(a), doSub(b))
    }
  }

  type TypeCheck = Either[TypeError, Type]
  type Environment = Map[String, Type]

  // as of here I stopped trying to implement coproducts
  // (because I realized we need the annotations)

  def typeof(t: Exp): TypeCheck = typeWithEnv(Map.empty[String, Type], t)
  def typeWithEnv(env: Environment, t: Exp): TypeCheck = t match {
    case Var(x) => env.get(x) match {
      case Some(typ) => Right(typ)
      case None => Left(TypeError(s"free variable $x"))
    }
    case Lam(p, typ, body) => for {
      returnType <- typeWithEnv(env + (p -> typ), body).right
    } yield TFunc(typ, returnType)
    case App(t1, t2) => for {
      apperType <- typeWithEnv(env, t1).right
      appeeType <- typeWithEnv(env, t2).right
      resultType <- (apperType match {
        case TFunc(ante, consq) if ante == appeeType => Right(consq)
        case x => Left(TypeError(s"tried to apply type $x to $appeeType"))
      }).right
    } yield resultType
    case Cond(cond, body, ow) => for {
      condType <- typeWithEnv(env, cond).right
      _ <- (if(condType == TBool) Right(TBool)
        else Left(TypeError(s"condition $cond not of type Bool"))).right
      bodyType <- typeWithEnv(env, body).right
      elseType <- typeWithEnv(env, ow).right
      resultType <- (if(bodyType == elseType) Right(bodyType)
        else Left(TypeError(s"mismatched types in if-else; $bodyType and $elseType"))).right
    } yield resultType
    case Pair(t1, t2) => for {
      leftType <- typeWithEnv(env, t1).right
      rightType <- typeWithEnv(env, t2).right
    } yield TProd(leftType, rightType)
    case Pi1(t) => for {
      innerType <- typeWithEnv(env, t).right
      resultType <- (innerType match {
        case TProd(l, r) => Right(l)
        case x => Left(TypeError(s"projection π1 operating on type $x"))
      }).right
    } yield resultType
    case Pi2(t) => for {
      innerType <- typeWithEnv(env, t).right
      resultType <- (innerType match {
        case TProd(l, r) => Right(r)
        case x => Left(TypeError(s"projection π2 operating on type $x"))
      }).right
    } yield resultType
    case Unit => Right(TUnit)
    case b@BoolLiteral(_) => Right(TBool)
    case And(l, r) => for {
      leftType <- typeWithEnv(env, l).right
      rightType <- typeWithEnv(env, r).right
      result <- (if(leftType == TBool && rightType == TBool) Right(TBool)
                else Left(TypeError(s"tried to && terms of type $leftType and $rightType"))).right
    } yield result
    case Or(l, r) => for {
      leftType <- typeWithEnv(env, l).right
      rightType <- typeWithEnv(env, r).right
      result <- (if(leftType == TBool && rightType == TBool) Right(TBool)
                else Left(TypeError(s"tried to || terms of type $leftType and $rightType"))).right
    } yield result
  }

  def step(t: Exp): Exp = t match {
    case v if isValue(v) => v
    case App(t1, t2) if !isValue(t1) => App(step(t1), t2)
    case App(v1, t2) if !isValue(t2) => App(v1, step(t2))
    case App(Lam(p, _, t), v2) => substitute(v2, p, t)
    case Cond(cond, body, ow) if !isValue(cond) => Cond(step(cond), body, ow)
    case Cond(BoolLiteral(true), body, ow) => body
    case Cond(BoolLiteral(false), body, ow) => ow
    case Pair(t1, t2) if !isValue(t1) => Pair(step(t1), t2)
    case Pair(v1, t2) if !isValue(t2) => Pair(v1, step(t2))
    case Pi1(t) if !isValue(t) => Pi1(step(t))
    case Pi1(Pair(v1, v2)) => v1
    case Pi2(t) if !isValue(t) => Pi2(step(t))
    case Pi2(Pair(v1, v2)) => v2
    case And(t1, t2) if !isValue(t1) => And(step(t1), t2)
    case And(v1, t2) if !isValue(t2) => And(v1, step(t2))
    case And(BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 && b2)
    case Or(t1, t2) if !isValue(t1) => Or(step(t1), t2)
    case Or(v1, t2) if !isValue(t2) => Or(v1, step(t2))
    case Or(BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 || b2)
    // otherwise we're stuck: this should never happen; all other cases would've had TypeError
  }

  def smallStepEval(t: Exp): Either[TypeError, Exp] = for {
    _ <- typeof(t).right
  } yield {
    var term = t
    var nextTerm = step(t)
    while(term != nextTerm) {
      term = nextTerm
      nextTerm = step(nextTerm)
    }
    term
  }

  /*
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
  */
}
