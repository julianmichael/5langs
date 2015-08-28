package fivelangs.lambda
import fivelangs._

import molt.syntax.cfg.parsable._
import molt.syntax.cfg._
import CFGParserHelpers._


object ExtensibleLambdaParsing {
  import ExtensibleLambda._
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

  def makeTypeParser(g: GlobalExpSpec): ComplexCFGParsable[g.Type] = {

    def typeProductionForSpec(spec: ExpSpec): Option[(List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Type]))] = spec.typeParser map { tParser =>
      List(tParser) -> ((c: List[AST[CFGParsable[_]]]) => for {
        e <- tParser.fromAST(c(0))
      } yield g.makeType(spec)(e))
    }

    val globalTypeParser = new ComplexCFGParsable[g.Type] {
      final override lazy val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Type])] = Map(
        List(Parenthesize(this)) -> ((c: List[AST[CFGParsable[_]]]) => for {
            t <- Parenthesize(this).fromAST(c(0))
          } yield t)
      ) ++ (for {
        spec <- g.expSpecs
        prod <- typeProductionForSpec(spec)
      } yield prod)
    }
    globalTypeParser
  }

  def makeVarExpParser(spec: VarSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(VarCategory) -> (c => for {
        v <- VarCategory.fromAST(c(0))
      } yield spec.Var(v))
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

  def makeUnitTypeParser(spec: UnitSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(Terminal("Unit")) -> (c => for {
        v <- Terminal("Unit").fromAST(c(0))
      } yield spec.TUnit)
    )
  }


  def makeFuncExpParser(spec: FuncSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("\\"), VarCategory, Terminal(":"), spec.g.typeParser, Terminal("."), spec.g.expParser) -> (c => for {
        p <- VarCategory.fromAST(c(1))
        typ <- spec.g.typeParser.fromAST(c(3))
        t <- spec.g.expParser.fromAST(c(5))
      } yield spec.Lam(p, typ, t)),
      List(spec.g.expParser, spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        t2 <- spec.g.expParser.fromAST(c(1))
      } yield spec.App(t1, t2))
    )
  }

  def makeFuncTypeParser(spec: FuncSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(spec.g.typeParser, Terminal("->"), spec.g.typeParser) -> (c => for {
        t1 <- spec.g.typeParser.fromAST(c(0))
        t2 <- spec.g.typeParser.fromAST(c(2))
      } yield spec.TFunc(t1,t2))
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

  def makeBoolTypeParser(spec: BoolSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(Terminal("Bool")) -> (c => for {
        v <- Terminal("Bool").fromAST(c(0))
      } yield spec.TBool)
    )
  }

  def makeProdExpParser(spec: ProdSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("("), spec.g.expParser, Terminal(","), spec.g.expParser, Terminal(")")) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(1))
        t2 <- spec.g.expParser.fromAST(c(3))
      } yield spec.Pair(t1, t2)),
      List(Terminal("π1"), spec.g.expParser) -> (c => for {
        t <- spec.g.expParser.fromAST(c(1))
      } yield spec.Pi1(t)),
      List(Terminal("π2"), spec.g.expParser) -> (c => for {
        t <- spec.g.expParser.fromAST(c(1))
      } yield spec.Pi2(t))
    )
  }

  def makeProdTypeParser(spec: ProdSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(spec.g.typeParser, Terminal("x"), spec.g.typeParser) -> (c => for {
        t1 <- spec.g.typeParser.fromAST(c(0))
        t2 <- spec.g.typeParser.fromAST(c(2))
      } yield spec.TProd(t1,t2))
    )
  }

  def makeCoprodExpParser(spec: CoprodSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("inl"), spec.g.expParser, Terminal(":"), Terminal("_"), Terminal("+"), spec.g.typeParser) -> (c => for {
        term <- spec.g.expParser.fromAST(c(1))
        rType <- spec.g.typeParser.fromAST(c(5))
      } yield spec.Inl(term, rType)),
      List(Terminal("inr"), spec.g.expParser, Terminal(":"), Terminal("_"), Terminal("+"), spec.g.typeParser) -> (c => for {
        term <- spec.g.expParser.fromAST(c(1))
        lType <- spec.g.typeParser.fromAST(c(5))
      } yield spec.Inr(term, lType)),
      List(Terminal("case"), spec.g.expParser, Terminal("of"),
        Terminal("("), Terminal("inl"), VarCategory,
        Terminal("=>"), spec.g.expParser, Terminal(")"),
        Terminal("("), Terminal("inr"), VarCategory,
        Terminal("=>"), spec.g.expParser, Terminal(")")) -> (c => for {
        term <- spec.g.expParser.fromAST(c(1))
        lName <- VarCategory.fromAST(c(5))
        lBody <- spec.g.expParser.fromAST(c(7))
        rName <- VarCategory.fromAST(c(11))
        rBody <- spec.g.expParser.fromAST(c(13))
      } yield spec.Case(term, lName, lBody, rName, rBody))
    )
  }

  def makeCoprodTypeParser(spec: CoprodSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(spec.g.typeParser, Terminal("+"), spec.g.typeParser) -> (c => for {
        t1 <- spec.g.typeParser.fromAST(c(0))
        t2 <- spec.g.typeParser.fromAST(c(2))
      } yield spec.TCoprod(t1,t2))
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

  def makeIntTypeParser(spec: IntSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(Terminal("Int")) -> (c => for {
        v <- Terminal("Int").fromAST(c(0))
      } yield spec.TInt)
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