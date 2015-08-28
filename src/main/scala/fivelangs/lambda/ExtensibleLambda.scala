package fivelangs.lambda
import fivelangs._


object ExtensibleLambda {
  // In this file, I try to solve the Expression Problem.
  // I don't expect it to work.

  import ExtensibleLambdaParsing._
  import molt.syntax.cfg.parsable._
  import molt.syntax.cfg._

  case class GlobalExpSpec(
    expSpecMakers: List[(GlobalExpSpec => ExpSpec)]) {

    lazy val expSpecs: Set[ExpSpec] = {
      val expSpecQueue = collection.mutable.Set.empty[ExpSpec]
      expSpecQueue ++= expSpecMakers.map(_.apply(this))
      val allExpSpecs = collection.mutable.Set.empty[ExpSpec]
      while(!expSpecQueue.isEmpty) {
        val next = expSpecQueue.head
        expSpecQueue -= next
        if(!allExpSpecs(next)) {
          allExpSpecs += next
          expSpecQueue ++= next.dependencies
        }
      }
      allExpSpecs.toSet
    }

    // this crazy thing is to work around the fact that
    // constructors can't have dependent method types
    sealed trait Exp {
      val expSpec: ExpSpec
      val exp: expSpec.E
      override def toString: String = expSpec.toStringExp(exp)
    }
    def makeExp(thisExpSpec: ExpSpec)(thisExp: thisExpSpec.E) = new Exp {
      val expSpec = thisExpSpec
      // compiler couldn't tell that expSpec == thisExpSpec
      // hopefully this will run ok
      val exp = thisExp.asInstanceOf[expSpec.E]
    }

    sealed trait Type {
      val expSpec: ExpSpec
      val typ: expSpec.T
      override def toString: String = expSpec.toStringType(typ)
    }
    def makeType(thisExpSpec: ExpSpec)(thisType: thisExpSpec.T) = new Type {
      val expSpec = thisExpSpec
      val typ = thisType.asInstanceOf[expSpec.T]
    }

    type TypeCheck = Either[TypeError, Type]
    type Environment = Map[String, Type]

    def isValue(e: Exp): Boolean = e.expSpec.isValue(e.exp)
    def freeVars(e: Exp): Set[String] = e.expSpec.freeVars(e.exp)
    def isClosed(t: Exp): Boolean = freeVars(t).isEmpty
    // the unfortunate casts WILL be accurate because of
    // the appropriate things being equal
    def substitute(sub: Exp, name: String, target: Exp): Exp = {
      target.expSpec.substitute(
        sub.asInstanceOf[target.expSpec.g.Exp],
        name,
        target.exp).asInstanceOf[Exp]
    }
    def typeof(t: Exp): TypeCheck = typeWithEnv(Map.empty[String, Type], t)
    def typeWithEnv(env: Environment, t: Exp): TypeCheck =
      t.expSpec.typeWithEnv(
        env.asInstanceOf[t.expSpec.g.Environment],
        t.exp
      ).asInstanceOf[TypeCheck]

    def step(t: Exp): Exp =
      if(isValue(t)) t
      else t.expSpec.step(t.exp).asInstanceOf[Exp]

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

    val expParser: CFGParsable[Exp] = makeExpParser(this)
    val typeParser: CFGParsable[Type] = makeTypeParser(this)
  }

  abstract class ExpSpec(val g: GlobalExpSpec) {
    val dependencies: List[ExpSpec] = Nil

    type E // the type of expressions
    type T // the type of the new types (if any; otherwise g.Type)

    // convenience method
    final def makeExp(e: E): g.Exp = g.makeExp(this)(e)
    final def makeType(t: T): g.Type = g.makeType(this)(t)

    def isValue(e: E): Boolean
    def freeVars(e: E): Set[String]
    def substitute(sub: g.Exp, name: String, target: E): g.Exp

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck

    def step(t: E): g.Exp

    def toStringExp(e: E): String
    def toStringType(t: T): String

    val expParser: CFGParsable[E]
    val typeParser: Option[CFGParsable[T]]
  }

  case class VarSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    case class Var(x: String)
    type E = Var
    type T = g.Type

    def isValue(e: E): Boolean = false

    def freeVars(e: E): Set[String] = e match {
      case Var(name) => Set(name)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = target match {
      case Var(y) if y == name => sub
      case v@Var(_) => g.makeExp(this)(v)
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Var(x) => env.get(x) match {
        case Some(typ) => Right(typ)
        case None => Left(TypeError(s"free variable $x"))
      }
    }

    def step(t: E): g.Exp = ???

    override def toStringExp(e: E): String = e match { case Var(x) => x }
    def toStringType(t: T): String = t.toString

    val expParser: CFGParsable[E] = makeVarExpParser(this)
    val typeParser: Option[CFGParsable[T]] = None
  }

  case class FuncSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    private[this] val innerVarSpec = VarSpec(g)
    override val dependencies = List(innerVarSpec)

    sealed trait FuncTerm
    case class Lam(param: String, paramType: g.Type, body: g.Exp) extends FuncTerm
    case class App(t1: g.Exp, t2: g.Exp) extends FuncTerm

    case class TFunc(a: g.Type, b: g.Type)

    type E = FuncTerm
    type T = TFunc

    def isValue(e: E): Boolean = e match {
      case Lam(_, _, _) => true
      case App(_, _) => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Lam(param, typ, body) => g.freeVars(body) - param
      case App(t1, t2) => g.freeVars(t1) ++ g.freeVars(t2)
    }

    private[this] def alpha(prohib: Set[String], lam: Lam): Lam = lam match {
      case Lam(param, typ, t) if(prohib(param)) =>
        val newVar = freshVar(prohib)
        Lam(newVar, typ,
          g.substitute(g.makeExp(innerVarSpec)(innerVarSpec.Var(newVar)), param, t))
      case x => x
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case l@Lam(_, _, _) =>
          val Lam(newP, typ, newT) = alpha(g.freeVars(sub) ++ freeVars(l), l)
          makeExp(Lam(newP, typ, doSub(newT)))
        case App(t1, t2) => g.makeExp(this)(App(doSub(t1), doSub(t2)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Lam(p, typ, body) => for {
        returnType <- g.typeWithEnv(env + (p -> typ), body).right
      } yield makeType(TFunc(typ, returnType))
      case App(t1, t2) => for {
        apperType <- g.typeWithEnv(env, t1).right
        appeeType <- g.typeWithEnv(env, t2).right
        resultType <- (apperType.typ match {
          case TFunc(ante, consq) if ante.typ == appeeType.typ => Right(consq)
          case x => Left(TypeError(s"tried to apply type $x to $appeeType"))
        }).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case App(t1, t2) if !g.isValue(t1) => makeExp(App(g.step(t1), t2))
      case App(v1, t2) if !g.isValue(t2) => makeExp(App(v1, g.step(t2)))
      case App(v1, v2) => v1.exp match {
        case Lam(p, _, t) => g.substitute(v2, p, t)
      }
    }

    override def toStringExp(e: E): String = e match {
      case Lam(p, typ, body) => s"(\\$p: $typ. $body)"
      case App(t1, t2) => s"($t1 $t2)"
    }
    def toStringType(t: T): String = t match {
      case TFunc(t1, t2) => s"$t1 -> t2"
    }

    val expParser: CFGParsable[E] = makeFuncExpParser(this)
    val typeParser: Some[CFGParsable[T]] = Some(makeFuncTypeParser(this))
  }

  case class BoolSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    sealed trait BoolExp
    case class BoolLiteral(b: Boolean) extends BoolExp
    case class And(a: g.Exp, b: g.Exp) extends BoolExp
    case class Or(a: g.Exp, b: g.Exp) extends BoolExp
    case class Not(t: g.Exp) extends BoolExp

    object TBool

    type E = BoolExp
    type T = TBool.type

    def isValue(e: E): Boolean = e match {
      case BoolLiteral(_) => true
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case BoolLiteral(_) => Set.empty[String]
      case And(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Or(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Not(a) => g.freeVars(a)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case b@BoolLiteral(_) => makeExp(b)
        case And(a, b) => makeExp(And(doSub(a), doSub(b)))
        case Or(a, b) => makeExp(Or(doSub(a), doSub(b)))
        case Not(a) => makeExp(Not(doSub(a)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case b@BoolLiteral(_) => Right(makeType(TBool))
      case And(l, r) => for {
        leftType <- g.typeWithEnv(env, l).right
        rightType <- g.typeWithEnv(env, r).right
        result <- (if(leftType.typ == TBool && rightType.typ == TBool) Right(makeType(TBool))
                  else Left(TypeError(s"tried to && terms of type $leftType and $rightType"))).right
      } yield result
      case Or(l, r) => for {
        leftType <- g.typeWithEnv(env, l).right
        rightType <- g.typeWithEnv(env, r).right
        result <- (if(leftType.typ == TBool && rightType.typ == TBool) Right(makeType(TBool))
                  else Left(TypeError(s"tried to || terms of type $leftType and $rightType"))).right
      } yield result
      case Not(t) => for {
        innerType <- g.typeWithEnv(env, t).right
        result <- (if(innerType.typ == TBool) Right(makeType(TBool))
                  else Left(TypeError(s"tried to ! term of type $innerType"))).right
      } yield result
    }

    def step(t: E): g.Exp = makeExp(t match {
      case And(t1, t2) if !g.isValue(t1) => And(g.step(t1), t2)
      case And(v1, t2) if !g.isValue(t2) => And(v1, g.step(t2))
      case And(v1, v2) => (v1.exp, v2.exp) match {
        case (BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 && b2)
      }
      case Or(t1, t2) if !g.isValue(t1) => Or(g.step(t1), t2)
      case Or(v1, t2) if !g.isValue(t2) => Or(v1, g.step(t2))
      case Or(v1, v2) => (v1.exp, v2.exp) match {
        case (BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 || b2)
      }
      case Not(t) if !g.isValue(t) => Not(g.step(t))
      case Not(v) => v.exp match {
        case BoolLiteral(b) => BoolLiteral(!b)
      }
    })

    def toStringExp(e: E): String = e match {
      case BoolLiteral(false) => "False"
      case BoolLiteral(true) => "True"
      case And(a, b) => s"$a && $b"
      case Or(a, b) => s"$a || $b"
      case Not(t) => s"!$t"
    }
    def toStringType(t: T): String = "Bool"

    val expParser: CFGParsable[E] = makeBoolExpParser(this)
    val typeParser: Option[CFGParsable[T]] = Some(makeBoolTypeParser(this))
  }

  case class CondSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    private[this] val innerBoolSpec = BoolSpec(g)
    override val dependencies = List(innerBoolSpec)

    case class Cond(cond: g.Exp, body: g.Exp, otherwise: g.Exp)

    type E = Cond
    type T = g.Type

    def isValue(e: E): Boolean = false

    def freeVars(e: E): Set[String] = e match {
      case Cond(c, b, ow) => g.freeVars(c) ++ g.freeVars(b) ++ g.freeVars(ow)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match { case Cond(c, b, ow) =>
        makeExp(Cond(doSub(c), doSub(b), doSub(ow)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Cond(cond, body, ow) => for {
        condType <- g.typeWithEnv(env, cond).right
        _ <- (if(condType.typ == innerBoolSpec.TBool) Right(condType)
          else Left(TypeError(s"condition $cond not of type Bool"))).right
        bodyType <- g.typeWithEnv(env, body).right
        elseType <- g.typeWithEnv(env, ow).right
        resultType <- (if(bodyType == elseType) Right(bodyType)
          else Left(TypeError(s"mismatched types in if-else: $bodyType and $elseType"))).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case Cond(cond, body, ow) if !g.isValue(cond) =>
        makeExp(Cond(g.step(cond), body, ow))
      case Cond(v, body, ow) => v.exp match {
        case innerBoolSpec.BoolLiteral(true) => body
        case innerBoolSpec.BoolLiteral(false) => ow
      }
    }

    def toStringExp(e: E): String = e match {
      case Cond(c, b, ow) => s"if $c then $b else $ow"
    }
    def toStringType(t: T): String = t.toString

    val expParser: CFGParsable[E] = makeCondExpParser(this)
    val typeParser: Option[CFGParsable[T]] = None
  }

  case class UnitSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    case object Unit
    case object TUnit

    type E = Unit.type
    type T = TUnit.type

    def isValue(e: E): Boolean = true
    def freeVars(e: E): Set[String] = Set.empty[String]
    def substitute(sub: g.Exp, name: String, target: E): g.Exp = makeExp(Unit)

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = Right(makeType(TUnit))

    def step(t: E): g.Exp = ???

    def toStringExp(e: E): String = "()"
    def toStringType(t: T): String = "Unit"

    val expParser: CFGParsable[E] = makeUnitExpParser(this)
    val typeParser: Some[CFGParsable[T]] = Some(makeUnitTypeParser(this))
  }

  case class ProdSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    sealed trait ProdExp
    case class Pair(t1: g.Exp, t2: g.Exp) extends ProdExp
    case class Pi1(t: g.Exp) extends ProdExp
    case class Pi2(t: g.Exp) extends ProdExp

    case class TProd(l: g.Type, r: g.Type)

    type E = ProdExp
    type T = TProd

    def isValue(e: E): Boolean = e match {
      case Pair(v1, v2) => g.isValue(v1) && g.isValue(v2)
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Pair(t1, t2) => g.freeVars(t1) ++ g.freeVars(t2)
      case Pi1(t) => g.freeVars(t)
      case Pi2(t) => g.freeVars(t)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case Pair(t1, t2) => makeExp(Pair(doSub(t1), doSub(t2)))
        case Pi1(t) => makeExp(Pi1(doSub(t)))
        case Pi2(t) => makeExp(Pi2(doSub(t)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Pair(t1, t2) => for {
        leftType <- g.typeWithEnv(env, t1).right
        rightType <- g.typeWithEnv(env, t2).right
      } yield makeType(TProd(leftType, rightType))
      case Pi1(t) => for {
        innerType <- g.typeWithEnv(env, t).right
        resultType <- (innerType.typ match {
          case TProd(l, r) => Right(l)
          case x => Left(TypeError(s"projection π1 operating on type $x"))
        }).right
      } yield resultType
      case Pi2(t) => for {
        innerType <- g.typeWithEnv(env, t).right
        resultType <- (innerType.typ match {
          case TProd(l, r) => Right(r)
          case x => Left(TypeError(s"projection π2 operating on type $x"))
        }).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case Pair(t1, t2) if !g.isValue(t1) => makeExp(Pair(g.step(t1), t2))
      case Pair(v1, t2) if !g.isValue(t2) => makeExp(Pair(v1, g.step(t2)))
      case Pi1(t) if !g.isValue(t) => makeExp(Pi1(g.step(t)))
      case Pi1(v) => v.exp match { case Pair(v1, v2) => v1 }
      case Pi2(t) if !g.isValue(t) => makeExp(Pi2(g.step(t)))
      case Pi2(v) => v.exp match { case Pair(v1, v2) => v2 }
    }

    def toStringExp(e: E): String = e match {
      case Pair(t1, t2) => s"($t1, $t2)"
      case Pi1(t) => s"π1 $t"
      case Pi2(t) => s"π2 $t"
    }
    def toStringType(t: T): String = t match {
      case TProd(t1, t2) => s"$t1 x t2"
    }

    val expParser: CFGParsable[E] = makeProdExpParser(this)
    val typeParser: Option[CFGParsable[T]] = Some(makeProdTypeParser(this))
  }

  case class CoprodSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    private[this] val innerVarSpec = VarSpec(g)
    override val dependencies = List(innerVarSpec)

    sealed trait CoprodExp
    case class Inl(t: g.Exp, rType: g.Type) extends CoprodExp
    case class Inr(t: g.Exp, lType: g.Type) extends CoprodExp
    case class Case(t: g.Exp, lName: String, lBody: g.Exp,
                          rName: String, rBody: g.Exp) extends CoprodExp

    case class TCoprod(t1: g.Type, t2: g.Type)

    type E = CoprodExp
    type T = TCoprod

    def isValue(e: E): Boolean = e match {
      case Inl(v, _) => g.isValue(v)
      case Inr(v, _) => g.isValue(v)
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Inl(t, _) => g.freeVars(t)
      case Inr(t, _) => g.freeVars(t)
      case Case(t, lName, lBody, rName, rBody) =>
        g.freeVars(t) ++ (g.freeVars(lBody) - lName) ++ (g.freeVars(rBody) - rName)
    }

    private[this] def alpha(prohib: Set[String], cas: Case): Case = cas match {
      case Case(t, lName, lBody, rName, rBody) =>
        val newName = freshVar(prohib)
        val (newLName, newLBody) =
          if(prohib(lName)) {
            (newName,
             g.substitute(
               innerVarSpec.makeExp(innerVarSpec.Var(newName)).asInstanceOf[g.Exp],
               lName,
               lBody))
          } else {
            (lName, lBody)
          }
        val (newRName, newRBody) =
          if(prohib(rName)) {
            (newName,
             g.substitute(
               innerVarSpec.makeExp(innerVarSpec.Var(newName)).asInstanceOf[g.Exp],
               rName,
               rBody))
          } else {
            (rName, rBody)
          }
        Case(t, newLName, newLBody, newRName, newRBody)
    }


    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case Inl(t, rType) => makeExp(Inl(doSub(t), rType))
        case Inr(t, lType) => makeExp(Inr(doSub(t), lType))
        case c@Case(_, _, _, _, _) =>
          val Case(t, lName, lBody, rName, rBody) =
            alpha(g.freeVars(sub) ++ freeVars(c), c)
          makeExp(Case(t, lName, doSub(lBody), rName, doSub(rBody)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Inl(t, rType) => for {
        lType <- g.typeWithEnv(env, t).right
      } yield makeType(TCoprod(lType, rType))
      case Inr(t, lType) => for {
        rType <- g.typeWithEnv(env, t).right
      } yield makeType(TCoprod(lType, rType))
      case Case(t, lName, lBody, rName, rBody) => for {
        termType <- g.typeWithEnv(env, t).right
        typePair <- (termType.typ match {
          case TCoprod(lType, rType) => Right((lType, rType))
          case x => Left(TypeError(s"cannot take case of type $x"))
        }).right
        lBodyType <- g.typeWithEnv(env + (lName -> typePair._1), lBody).right
        rBodyType <- g.typeWithEnv(env + (rName -> typePair._2), rBody).right
        _ <- (if(lBodyType == rBodyType) Right(lBodyType)
             else Left(TypeError(
               s"cases (${lBodyType.typ} and ${rBodyType.typ}) do not match"))).right
      } yield lBodyType
    }

    def step(e: E): g.Exp = e match {
      case Inl(t, rType) if !g.isValue(t) => makeExp(Inl(g.step(t), rType))
      case Inr(t, lType) if !g.isValue(t) => makeExp(Inr(g.step(t), lType))
      case Case(t, lName, lBody, rName, rBody) if !g.isValue(t) =>
        makeExp(Case(g.step(t), lName, lBody, rName, rBody))
      case Case(v, lName, lBody, rName, rBody) => v.exp match {
        case Inl(t, _) => g.substitute(t, lName, lBody)
        case Inr(t, _) => g.substitute(t, rName, rBody)
      }
    }

    def toStringExp(e: E): String = e match {
      case Inl(t, rType) => s"inl $t: (_ + $rType)"
      case Inr(t, lType) => s"inr $t: ($lType + _)"
      case Case(t, lName, lBody, rName, rBody) =>
        s"case $t of (inl $lName => $lBody) (inr $rName => $rBody)"
    }
    def toStringType(t: T): String = t match {
      case TCoprod(t1, t2) => s"$t1 + t2"
    }

    val expParser: CFGParsable[E] = makeCoprodExpParser(this)
    val typeParser: Option[CFGParsable[T]] = Some(makeCoprodTypeParser(this))
  }

  case class IntSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {

    sealed trait IntExp
    case class IntLiteral(n: Int) extends IntExp
    case class Plus(a: g.Exp, b: g.Exp) extends IntExp
    case class Minus(a: g.Exp, b: g.Exp) extends IntExp
    case class Times(a: g.Exp, b: g.Exp) extends IntExp
    case class Div(a: g.Exp, b: g.Exp) extends IntExp

    case object TInt

    type E = IntExp
    type T = TInt.type

    def isValue(e: E): Boolean = e match {
      case IntLiteral(_) => true
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Plus(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Minus(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Times(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Div(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case _ => Set.empty[String]
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case Plus(a, b) => makeExp(Plus(doSub(a), doSub(b)))
        case Minus(a, b) => makeExp(Minus(doSub(a), doSub(b)))
        case Times(a, b) => makeExp(Times(doSub(a), doSub(b)))
        case Div(a, b) => makeExp(Div(doSub(a), doSub(b)))
        case i@IntLiteral(_) => makeExp(i)
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = {
      def opType(a: g.Exp, b: g.Exp, s: String): g.TypeCheck = for {
        aType <- g.typeWithEnv(env, a).right
        bType <- g.typeWithEnv(env, b).right
        result <- (if(this == aType.expSpec && this == bType.expSpec) {
          Right(makeType(TInt))
        } else {
          Left(TypeError(s"cannot $s ${aType.typ} and ${bType.typ}"))
        }).right
      } yield result

      t match {
        case IntLiteral(_) => Right(makeType(TInt))
        case Plus(a, b) => opType(a, b, "add")
        case Minus(a, b) => opType(a, b, "subtract")
        case Times(a, b) => opType(a, b, "multiply")
        case Div(a, b) => opType(a, b, "divide")
      }
    }

    def step(t: E): g.Exp = t match {
      case Plus(t1, t2) if !g.isValue(t1) => makeExp(Plus(g.step(t1), t2))
      case Plus(v1, t2) if !g.isValue(t2) => makeExp(Plus(v1, g.step(t2)))
      case Plus(v1, v2) => (v1.exp, v2.exp) match {
        case (IntLiteral(i), IntLiteral(j)) => makeExp(IntLiteral(i + j))
      }
      case Minus(t1, t2) if !g.isValue(t1) => makeExp(Minus(g.step(t1), t2))
      case Minus(v1, t2) if !g.isValue(t2) => makeExp(Minus(v1, g.step(t2)))
      case Minus(v1, v2) => (v1.exp, v2.exp) match {
        case (IntLiteral(i), IntLiteral(j)) => makeExp(IntLiteral(i - j))
      }
      case Times(t1, t2) if !g.isValue(t1) => makeExp(Times(g.step(t1), t2))
      case Times(v1, t2) if !g.isValue(t2) => makeExp(Times(v1, g.step(t2)))
      case Times(v1, v2) => (v1.exp, v2.exp) match {
        case (IntLiteral(i), IntLiteral(j)) => makeExp(IntLiteral(i * j))
      }
      case Div(t1, t2) if !g.isValue(t1) => makeExp(Div(g.step(t1), t2))
      case Div(v1, t2) if !g.isValue(t2) => makeExp(Div(v1, g.step(t2)))
      case Div(v1, v2) => (v1.exp, v2.exp) match {
        case (IntLiteral(i), IntLiteral(j)) => makeExp(IntLiteral(i / j))
      }
    }

    def toStringExp(e: E): String = e match {
      case IntLiteral(i) => s"$i"
      case Plus(a, b) => s"$a + $b"
      case Minus(a, b) => s"$a - $b"
      case Times(a, b) => s"$a * $b"
      case Div(a, b) => s"$a / $b"
    }
    def toStringType(t: T): String = "Int"

    val expParser: CFGParsable[E] = makeIntExpParser(this)
    val typeParser: Option[CFGParsable[T]] = Some(makeIntTypeParser(this))
  }

  case class FixSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    val innerFuncSpec = FuncSpec(g)
    override val dependencies: List[ExpSpec] = List(innerFuncSpec)

    case class Fix(e: g.Exp)

    type E = Fix
    type T = g.Exp

    def isValue(e: E): Boolean = false

    def freeVars(e: E): Set[String] = e match {
      case Fix(t) => g.freeVars(t)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = target match {
      case Fix(t) => makeExp(Fix(g.substitute(sub, name, t)))
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Fix(e) => for {
        typ <- g.typeWithEnv(env, e).right
        innerType <- (typ.typ match {
          case innerFuncSpec.TFunc(t1, t2) if t1 == t2 => Right(t1)
          case x => Left(TypeError(
            "can only get fixed point of functions T1 -> T1; found type $x"))
        }).right
      } yield innerType.asInstanceOf[g.Type]
    }

    def step(t: E): g.Exp = t match {
      case Fix(t1) if !g.isValue(t1) => makeExp(Fix(g.step(t1)))
      case Fix(v1) => v1.exp match {
        case innerFuncSpec.Lam(x, _, body) =>
          g.substitute(makeExp(t), x, body.asInstanceOf[g.Exp])
      }
    }

    def toStringExp(e: E): String = s"Fix $e"
    def toStringType(t: T): String = t.toString

    val expParser: CFGParsable[E] = ???
    val typeParser: Option[CFGParsable[T]] = ???
  }

}
