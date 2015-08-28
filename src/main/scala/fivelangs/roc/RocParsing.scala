package fivelangs.roc
import fivelangs._

import molt.syntax.cfg.parsable._
import molt.syntax.cfg._
import CFGParserHelpers._


object RocParsing {
  import Roc._
  object VarCategory extends RegexLexicalCategory("[a-z][a-zA-Z0-9]*")
  object IntCategory extends RegexLexicalCategory("[0-9]+")

  def makeExpParser(g: GlobalExpSpec): ComplexCFGParsable[g.Exp] = {

    def expProductionForSpec(spec: ExpSpec): (List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])) = (
      List(spec.expParser) -> (c => for {
        e <- spec.expParser.fromAST(c(0))
      } yield g.makeExp(spec)(e)))

    val globalExpParser = new ComplexCFGParsable[g.Exp] {
      final override lazy val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])] = Map(
        List(Parenthesize(this)) -> ((c: List[AST[CFGParsable[_]]]) => for {
            t <- Parenthesize(this).fromAST(c(0))
          } yield t)
      ) ++ (for (spec <- g.expSpecs) yield expProductionForSpec(spec))
    }

    globalExpParser
  }

  def makeEqExpParser(spec: EqSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(spec.g.expParser, Terminal("=="), spec.g.expParser) -> (c => for {
        e1 <- spec.g.expParser.fromAST(c(0))
        e2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Eq(e1, e2))
    )
  }

  def makeVarExpParser(spec: VarSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(VarCategory) -> (c => for {
        v <- VarCategory.fromAST(c(0))
      } yield spec.Var(v, -1))
    )
  }

  def makeUnitExpParser(spec: UnitSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("()")) -> (c => for {
        v <- Terminal("()").fromAST(c(0))
      } yield spec.Unit)
    )
  }


  def makeAssignmentParser(spec: ObjSpec) = new ComplexCFGParsable[(String, spec.g.Exp)] {
      final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[(String, spec.g.Exp)])] = Map(
        List(VarCategory, Terminal("="), spec.g.expParser) -> (c => for {
          name <- VarCategory.fromAST(c(0))
          body <- spec.g.expParser.fromAST(c(2))
        } yield (name, body))
      )
    }

  def makeObjExpParser(spec: ObjSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {

    val assignmentParser = makeAssignmentParser(spec)
    val assignmentsParser = DelimitedList(",", assignmentParser)

    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("{"), assignmentsParser, Terminal("}")) -> (c => for {
        fields <- assignmentsParser.fromAST(c(1))
      } yield spec.g.Obj(-1, fields.toMap)),
      List(spec.g.expParser, spec.g.expParser) -> (c => for {
        left <- spec.g.expParser.fromAST(c(0))
        right <- spec.g.expParser.fromAST(c(1))
      } yield spec.g.Mix(left, right)),
      List(spec.g.expParser, Terminal("."), VarCategory) -> (c => for {
        obj <- spec.g.expParser.fromAST(c(0))
        field <- VarCategory.fromAST(c(2))
      } yield spec.g.Access(obj, field))
    )
  }

  def makeBoolExpParser(spec: BoolSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("False")) -> (c => for {
        _ <- Terminal("False").fromAST(c(0))
      } yield spec.BoolLiteral(false)),
      List(Terminal("True")) -> (c => for {
        _ <- Terminal("True").fromAST(c(0))
      } yield spec.BoolLiteral(true)),
      List(spec.g.expParser, Terminal("&&"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("&&").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.And(t1, t2)),
      List(spec.g.expParser, Terminal("||"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("||").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Or(t1, t2)),
      List(Terminal("!"), spec.g.expParser) -> (c => for {
        _ <- Terminal("!").fromAST(c(0))
        t <- spec.g.expParser.fromAST(c(1))
      } yield spec.Not(t))
    )
  }

  def makeIntExpParser(spec: IntSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Numeric) -> (c => for {
        is <- Numeric.fromAST(c(0))
      } yield spec.IntLiteral(is.toInt)),
      List(Terminal("-"), spec.g.expParser) -> (c => for {
        _ <- Terminal("-").fromAST(c(0))
        is <- Numeric.fromAST(c(1))
      } yield spec.IntLiteral(is.toInt * -1)),
      List(spec.g.expParser, Terminal("+"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("+").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Plus(t1, t2)),
      List(spec.g.expParser, Terminal("-"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("-").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Minus(t1, t2)),
      List(spec.g.expParser, Terminal("*"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("*").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Times(t1, t2)),
      List(spec.g.expParser, Terminal("/"), spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        _ <- Terminal("/").fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(2))
      } yield spec.Div(t1, t2))
    )
  }

  def makeCondExpParser(spec: CondSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("if"), spec.g.expParser,
        Terminal("then"), spec.g.expParser,
        Terminal("else"), spec.g.expParser) -> (c => for {
        cond <- spec.g.expParser.fromAST(c(1))
        ifSo <- spec.g.expParser.fromAST(c(3))
        ifElse <- spec.g.expParser.fromAST(c(5))
      } yield spec.Cond(cond, ifSo, ifElse))
    )
  }

}