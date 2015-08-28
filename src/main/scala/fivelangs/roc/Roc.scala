package fivelangs.roc
import fivelangs._

object Roc {

  import RocParsing._
  import molt.syntax.cfg.parsable._
  import molt.syntax.cfg._

  import scalaz._
  import scalaz.syntax._
  import Scalaz._

  case class GlobalExpSpec(
    expSpecMakers: List[(GlobalExpSpec => ExpSpec)]) {

    type IdInfo = (Set[Int], Map[Int, Obj])
    type CheckT[M[+_], A] = StateT[M, IdInfo, A]
    type CheckValidate[+A] = \/[String, A]
    type Check[A] = CheckT[CheckValidate, A]

    def freshId: Check[Int] = for {
      st <- get[IdInfo].lift[CheckValidate]
      (ids, mapping) = st
      id = natInts.filter(x => !ids.contains(x)).head
      _ <- put((ids + id, mapping)).lift[CheckValidate]
    } yield id

    def addMapping(id: Int, obj: Obj): Check[Unit] = for {
      st <- get[IdInfo].lift[CheckValidate]
      (ids, mapping) = st
      _ <- put((ids, mapping + (id -> obj))).lift[CheckValidate]
    } yield ()

    def getObj(id: Int): Check[Obj] = for {
      st <- get[IdInfo].lift[CheckValidate]
      (_, mapping) = st
      obj <- mapping.get(id) match {
        case Some(o) => o.point[Check]
        case None => "variable referenced object that does not exist. cry".left.liftM[CheckT]
      }
    } yield obj

    sealed trait ObjExp
    case class Access(obj: Exp, field: String) extends ObjExp
    case class Obj(id: Int, fields: Map[String, Exp]) extends ObjExp
    case class Mix(left: Exp, right: Exp) extends ObjExp

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
      // compiler can't tell that expSpec == thisExpSpec
      val exp = thisExp.asInstanceOf[expSpec.E]
    }

    def isValue(e: Exp): Boolean = e.expSpec.isValue(e.exp)

    def areEqual(e1: Exp, e2: Exp): Boolean =
      e1.expSpec == e2.expSpec && e1.expSpec.areEqual(e1.exp, e2.exp.asInstanceOf[e1.expSpec.E])

    def resolveScoping(t: Exp): Check[Exp] = resolveScopingWithParentScopes(Nil, t)
    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: Exp): Check[Exp] = for {
      scoped <- t.expSpec.resolveScopingWithParentScopes(parentScopes, t.exp).asInstanceOf[Check[t.expSpec.E]]
    } yield makeExp(t.expSpec)(scoped).asInstanceOf[Exp]

    def updateReferences(t: Exp, old: Int, sub: Int): Exp =
      makeExp(t.expSpec)(t.expSpec.updateReferences(t.exp, old, sub))

    def eval(t: Exp): Check[Exp] =
      if(isValue(t)) t.point[Check]
      else t.expSpec.eval(t.exp).asInstanceOf[Check[Exp]]

    def fullEval(t: Exp): CheckValidate[Exp] = (for {
      scoped <- resolveScoping(t)
      result <- eval(scoped)
    } yield result).eval((Set.empty[Int], Map.empty[Int, Obj]))

    val expParser: CFGParsable[Exp] = makeExpParser(this)
  }

  abstract class ExpSpec(val g: GlobalExpSpec) {
    val dependencies: List[ExpSpec] = Nil

    type E // the type of expressions

    type Check[A] = g.Check[A]
    type Exp = g.Exp
    def error[A](msg: String): Check[A] = msg.left[A].liftM[g.CheckT]

    // convenience method
    final def makeExp(e: E): Exp = g.makeExp(this)(e)

    def isValue(e: E): Boolean

    def areEqual(e1: E, e2: E): Boolean

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E]

    def updateReferences(term: E, old: Int, sub: Int): E

    def eval(t: E): Check[Exp]

    def toStringExp(e: E): String

    val expParser: CFGParsable[E]
  }

  case class EqSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    private[this] val innerBoolSpec = BoolSpec(g)
    override val dependencies = List(innerBoolSpec)

    case class Eq(e1: Exp, e2: Exp)

    type E = Eq

    def isValue(e: E): Boolean = false

    def areEqual(e1: E, e2: E): Boolean = ???

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case Eq(e1, e2) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, e1)
        y <- g.resolveScopingWithParentScopes(parentScopes, e2)
      } yield Eq(x, y)
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case Eq(e1, e2) => Eq(g.updateReferences(e1, old, sub), g.updateReferences(e2, old, sub))
    }

    def eval(t: E): Check[Exp] = t match {
      case Eq(e1, e2) => for {
        v1 <- g.eval(e1)
        v2 <- g.eval(e2)
      } yield innerBoolSpec.makeExp(innerBoolSpec.BoolLiteral(g.areEqual(v1, v2))).asInstanceOf[Exp]
    }

    override def toStringExp(e: E): String = e match { case Eq(e1, e2) => s"($e1 == $e2)" }

    val expParser: CFGParsable[E] = makeEqExpParser(this)

  }

  case class VarSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {

    case class Var(name: String, scopeId: Int)

    type E = Var

    def isValue(e: E): Boolean = false

    def areEqual(e1: E, e2: E): Boolean = ???

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case v@Var(name, _) =>
        parentScopes.find(_._2.contains(name)) match {
          case None => error[E](s"free variable $name")
          case Some((id, _)) =>
            Var(name, id).point[Check]
        }
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case Var(name, oldId) if oldId == old => Var(name, sub)
      case x@Var(_, _) => x
    }

    def eval(t: E): Check[Exp] = t match {
      case v@Var(name, id) => for {
        obj <- g.getObj(id)
        g.Obj(_, fields) = obj
        result <- g.eval(fields(name))
      } yield result
    }

    override def toStringExp(e: E): String = e match { case Var(x, p) => s"($x <- ${p.hashCode})" }

    val expParser: CFGParsable[E] = makeVarExpParser(this)
  }

  case class ObjSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    import g.{Obj,Access,Mix,ObjExp}

    type E = ObjExp

    def isValue(e: E): Boolean = e match {
      case Access(_, _) => false
      case Obj(_, _) => true
      case Mix(_, _) => false
    }

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case Access(obj, field) => for {
        newObj <- g.resolveScopingWithParentScopes(parentScopes, obj)
      } yield Access(newObj, field)
      case o@Obj(_, fields) => for {
        newId <- g.freshId
        newScope = (newId, fields.map(_._1).toSet)
        newScopes = newScope :: parentScopes
        newFields <- fields.foldLeft(Map.empty[String, Exp].point[Check]) {
          case (acc, (name, term)) => for {
            prev <- acc
            newTerm <- g.resolveScopingWithParentScopes(newScopes, term)
          } yield prev + (name -> newTerm)
        }
        newObj = Obj(newId, newFields)
        _ <- g.addMapping(newId, newObj)
      } yield newObj
      case Mix(l, r) => for {
        newL <- g.resolveScopingWithParentScopes(parentScopes, l)
        newR <- g.resolveScopingWithParentScopes(parentScopes, r)
      } yield Mix(newL, newR)
    }

    def areEqual(e1: E, e2: E): Boolean = (e1, e2) match {
      case (Obj(_, f1), Obj(_, f2)) => f1 == f2
    }

    def eval(t: E): Check[Exp] = t match {
      case Access(obj, field) => for {
        objVal <- g.eval(obj)
        result <- objVal.exp match {
          case Obj(parent, fields) if fields.contains(field) =>
            g.eval(fields(field))
          case Obj(parent, fields) =>
            error[Exp](s"object $obj ($objVal) has no field $field")
          case other =>
            error[Exp](s"term $obj ($objVal) is not an object")
        }
      } yield result

      case Mix(l, r) => for {
        leftVal <- g.eval(l)
        rightVal <- g.eval(r)
        newId <- g.freshId
        result <- (leftVal.exp, rightVal.exp) match {
          case (Obj(lId, lFields), Obj(rId, rFields)) =>
            val lFieldsToKeep = (for {
              (name, term) <- lFields
              if !rFields.contains(name)
            } yield (name, g.updateReferences(term, lId, newId))).toMap
            val rFieldsToKeep = rFields.map {
              case (name, term) => (name, g.updateReferences(term, rId, newId))
            }
            val newObj = Obj(newId, lFieldsToKeep ++ rFieldsToKeep)
            newObj.point[Check]
          case (x, y) => error[Obj](s"cannot mix $x and $y")
        }
        _ <- g.addMapping(newId, result)
      } yield makeExp(result)
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case Access(obj, field) =>
        Access(g.updateReferences(obj, old, sub), field)
      case Obj(id, fields) =>
        val newFields = fields.map {
          case (name, field) => (name, g.updateReferences(field, old, sub))
        }.toMap
        Obj(id, newFields)
      case Mix(l, r) =>
        Mix(g.updateReferences(l, old, sub), g.updateReferences(r, old, sub))
    }

    override def toStringExp(e: E): String = e match {
      case Access(obj, field) => s"$obj.$field"
      case Obj(id, fields) =>
        val fieldString = fields.map {
          case (k, v) => s"$k: $v"
        }.mkString(", ")
        s"{$id; $fieldString }"
      case Mix(l, r) => s"$l $r"
    }

    val expParser: CFGParsable[E] = makeObjExpParser(this)
  }

  case class BoolSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    sealed trait BoolExp
    case class BoolLiteral(b: Boolean) extends BoolExp
    case class And(a: Exp, b: Exp) extends BoolExp
    case class Or(a: Exp, b: Exp) extends BoolExp
    case class Not(t: Exp) extends BoolExp

    object TBool

    type E = BoolExp
    type T = TBool.type

    def isValue(e: E): Boolean = e match {
      case BoolLiteral(_) => true
      case _ => false
    }

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case b@BoolLiteral(_) => (b: E).point[Check]
      case And(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield And(x, y)
      case Or(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield Or(x, y)
      case Not(t) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, t)
      } yield Not(x)
    }

    def areEqual(e1: E, e2: E): Boolean = (e1, e2) match {
      case (BoolLiteral(b1), BoolLiteral(b2)) => b1 == b2
    }

    private[this] def getBool(e: Exp): Check[Boolean] = g.eval(e).flatMap(t => t.exp match {
      case BoolLiteral(b) => b.point[Check]
      case other => error[Boolean](s"expected boolean; instead got $t ($other)")
    })

    def eval(t: E): Check[Exp] = t match {
      case And(t1, t2) => for {
        b1 <- getBool(t1)
        b2 <- getBool(t2)
      } yield makeExp(BoolLiteral(b1 && b2))
      case Or(t1, t2) => for {
        b1 <- getBool(t1)
        b2 <- getBool(t2)
      } yield makeExp(BoolLiteral(b1 || b2))
      case Not(t) => for {
        b <- getBool(t)
      } yield makeExp(BoolLiteral(!b))
    }

    def toStringExp(e: E): String = e match {
      case BoolLiteral(false) => "False"
      case BoolLiteral(true) => "True"
      case And(a, b) => s"$a && $b"
      case Or(a, b) => s"$a || $b"
      case Not(t) => s"!$t"
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case b@BoolLiteral(_) => b
      case And(a, b) =>
        And(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
      case Or(a, b) =>
        Or(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
      case Not(t) =>
        Not(g.updateReferences(t, old, sub))
    }

    val expParser: CFGParsable[E] = makeBoolExpParser(this)
  }

  case class CondSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    private[this] val innerBoolSpec = BoolSpec(g)
    override val dependencies = List(innerBoolSpec)

    case class Cond(cond: Exp, body: Exp, otherwise: Exp)

    type E = Cond

    def isValue(e: E): Boolean = false

    def areEqual(e1: E, e2: E): Boolean = ???

    private[this] def getBool(e: Exp): Check[Boolean] = g.eval(e).flatMap(t => t.exp match {
      case innerBoolSpec.BoolLiteral(b) => b.point[Check]
      case other => error[Boolean](s"expected boolean; instead got $t ($other)")
    })

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case Cond(cond, body, ow) => for {
        newCond <- g.resolveScopingWithParentScopes(parentScopes, cond)
        newBody <- g.resolveScopingWithParentScopes(parentScopes, body)
        newOw <- g.resolveScopingWithParentScopes(parentScopes, ow)
      } yield Cond(newCond, newBody, newOw)
    }

    def eval(t: E): Check[Exp] = t match {
      case Cond(cond, body, ow) => for {
        c <- getBool(cond)
        bod <- g.eval(body)
        els <- g.eval(ow)
      } yield if(c) bod else els
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case Cond(cond, body, ow) =>
        Cond(g.updateReferences(cond, old, sub),
             g.updateReferences(body, old, sub),
             g.updateReferences(ow, old, sub))
    }

    def toStringExp(e: E): String = e match {
      case Cond(c, b, ow) => s"if $c then $b else $ow"
    }

    val expParser: CFGParsable[E] = makeCondExpParser(this)
  }

  case class UnitSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    case object Unit

    type E = Unit.type

    def isValue(e: E): Boolean = true

    def areEqual(e1: E, e2: E): Boolean = true

    def eval(t: E): Check[Exp] = makeExp(Unit).point[Check]

    def updateReferences(term: E, old: Int, sub: Int): E = Unit

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = Unit.point[Check]

    def toStringExp(e: E): String = "()"

    val expParser: CFGParsable[E] = makeUnitExpParser(this)
  }

  case class IntSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {

    sealed trait IntExp
    case class IntLiteral(n: Int) extends IntExp
    case class Plus(a: Exp, b: Exp) extends IntExp
    case class Minus(a: Exp, b: Exp) extends IntExp
    case class Times(a: Exp, b: Exp) extends IntExp
    case class Div(a: Exp, b: Exp) extends IntExp

    case object TInt

    type E = IntExp
    type T = TInt.type

    def isValue(e: E): Boolean = e match {
      case IntLiteral(_) => true
      case _ => false
    }

    def areEqual(e1: E, e2: E): Boolean = (e1, e2) match {
      case (IntLiteral(i1), IntLiteral(i2)) => i1 == i2
    }

    def resolveScopingWithParentScopes(parentScopes: List[(Int, Set[String])], t: E): Check[E] = t match {
      case v@IntLiteral(_) => (v: E).point[Check]
      case Plus(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield Plus(x, y)
      case Minus(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield Minus(x, y)
      case Times(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield Times(x, y)
      case Div(a, b) => for {
        x <- g.resolveScopingWithParentScopes(parentScopes, a)
        y <- g.resolveScopingWithParentScopes(parentScopes, b)
      } yield Div(x, y)
    }

    private[this] def getInt(e: Exp): Check[Int] = g.eval(e).flatMap(t => t.exp match {
      case IntLiteral(b) => b.point[Check]
      case other => error[Int](s"expected int; instead got $t ($other)")
    })

    def eval(t: E): Check[Exp] = t match {
      case v@IntLiteral(i) => makeExp(v).point[Check]
      case Plus(a, b) => for {
        v1 <- getInt(a)
        v2 <- getInt(b)
      } yield makeExp(IntLiteral(v1 + v2))
      case Minus(a, b) => for {
        v1 <- getInt(a)
        v2 <- getInt(b)
      } yield makeExp(IntLiteral(v1 - v2))
      case Times(a, b) => for {
        v1 <- getInt(a)
        v2 <- getInt(b)
      } yield makeExp(IntLiteral(v1 * v2))
      case Div(a, b) => for {
        v1 <- getInt(a)
        v2 <- getInt(b)
      } yield makeExp(IntLiteral(v1 / v2))
    }

    def toStringExp(e: E): String = e match {
      case IntLiteral(i) => s"$i"
      case Plus(a, b) => s"$a + $b"
      case Minus(a, b) => s"$a - $b"
      case Times(a, b) => s"$a * $b"
      case Div(a, b) => s"$a / $b"
    }

    def updateReferences(term: E, old: Int, sub: Int): E = term match {
      case i@IntLiteral(_) => i
      case Plus(a, b) =>
        Plus(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
      case Minus(a, b) =>
        Minus(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
      case Times(a, b) =>
        Times(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
      case Div(a, b) =>
        Div(g.updateReferences(a, old, sub), g.updateReferences(b, old, sub))
    }

    val expParser: CFGParsable[E] = makeIntExpParser(this)
  }
}

object RocTestItems {
    import Roc._
    import molt.syntax.cfg.parsable.ParseCommands._

    val g = GlobalExpSpec(List(
      VarSpec,
      UnitSpec,
      BoolSpec,
      IntSpec,
      CondSpec,
      ObjSpec,
      EqSpec
    ))

    implicit val parser = g.expParser
    type Exp = g.Exp
    val e1 = parseForced[Exp]("""
    {
      addone = {
        a = (),
        ret = a + 1
      },

      ret = (addone { a = 4 }).ret
    }.ret
    """
    )

    val fibExps = parse[Exp]("""
    {
      n = (),
      ret = {
        m = n,
        ret = if n == 0 then 1
              else (if n == 1 then 1
              else ((fib { n = m - 1 }).ret + (fib { n = m - 2 }).ret))
    }
    """
    )
    val fibExp = fibExps.head

    val objSpec = ObjSpec(g)
    import molt.syntax.cfg.parsable.CFGParsable
    implicit val assignmentParser =
      RocParsing.makeAssignmentParser(objSpec).asInstanceOf[CFGParsable[(String, objSpec.g.Exp)]]
    implicit val expParser = objSpec.g.expParser

    val fib = objSpec.g.Obj(-1, Map("fib" -> fibExp.asInstanceOf[objSpec.g.Exp]))

    def repl: Unit = {
      var fields = Map.empty[String, objSpec.g.Exp]
      val in = io.Source.stdin
      var inc = 0
      def evalLine(name: String, exp: objSpec.g.Exp): Unit = {
          val globalObj = objSpec.g.makeExp(objSpec)(objSpec.g.Obj(-1, fields + (name -> exp)))
          val result = g.fullEval(g.makeExp(objSpec)(objSpec.g.Access(globalObj, name)))
          import scalaz.{\/-, -\/}
          result match {
            case -\/(msg) => println(s"Error: $msg")
            case \/-(e) =>
              fields = fields + (name -> exp)
              println(s"$name = $e")
          }
      }
      for(line <- in.getLines) {
        println(s"> $line")
        parseUnique[objSpec.g.Exp](line) match {
          case None => parseUnique[(String, objSpec.g.Exp)](line) match {
            case None => println("syntax error")
            case Some((name, exp)) => evalLine(name, exp)
          }
          case Some(exp) =>
            val nextName = s"var$inc"
            inc = inc + 1
            evalLine(nextName, exp)
        }
      }
    }

}
