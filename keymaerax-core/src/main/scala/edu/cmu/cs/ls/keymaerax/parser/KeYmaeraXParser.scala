/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.annotation.{switch, tailrec}
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * KeYmaera X parser items on the parser stack.
  *
  * @author Andre Platzer
 */
private[parser] sealed trait Item
/** Tokens are terminals occurring at a given location in the input. */
private[parser] case class Token(tok: Terminal, loc: Location = UnknownLocation) extends Item {
  override def toString = tok.toString
}
object UnknownToken extends Token(PSEUDO, UnknownLocation)
/** Expressions that are partially parsed on the parser item stack. */
private[parser] case class Expr(expr: Expression) extends Item {
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = KeYmaeraXPrettyPrinter.stringify(expr)
}
/** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
private[parser] case class RecognizedQuant(v: Expression) extends Item {
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = "Rec(" + KeYmaeraXPrettyPrinter.stringify(v) +")"
}
/** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
private[parser] case class RecognizedModal(ltok: Token, program: Program, rtok: Token) extends Item {
  require(ltok.tok==LBOX && rtok.tok==RBOX || ltok.tok==LDIA && rtok.tok==RDIA, "Compatible modality tokens required " + this)
  /** The region that this recognized item spans. */
  def loc: Location = ltok.loc--rtok.loc
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = "Rec" + ltok.tok.img + KeYmaeraXPrettyPrinter.stringify(program) + rtok.tok.img
}
///** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
//private[parser] case class RecognizedAnnotation(program: Program) extends Item {
//  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
//  override def toString: String = "Rec(" + KeYmaeraXPrettyPrinter.stringify(program) + "@)"
//}
private[parser] trait FinalItem extends Item
/** Parser items representing expressions that are accepted by the parser. */
private[parser] case class Accept(expr: Expression) extends FinalItem
/** Parser items representing erroneous ill-formed input. */
private[parser] case class Error(msg: String, loc: Location, st: String) extends FinalItem

/** Expected inputs */
private[parser] trait Expected
object Expected {
  /** Terminal input expected */
  private[parser] implicit class ExpectTerminal(tok: Terminal) extends Expected {
    override def toString: String = ParseException.tokenDescription(tok)
  }
}
/** Nonterminal or pseudo-nonterminal input expected */
private[parser] case class ExpectNonterminal(nonterm: String) extends Expected {
  override def toString: String = nonterm
}
object BINARYTERMOP extends ExpectNonterminal("<BinaryTermOp>")
object BINARYFORMULAOP extends ExpectNonterminal("<BinaryFormulaOp>")
object BINARYPROGRAMOP extends ExpectNonterminal("<BinaryProgramOp>")
object FIRSTTERM extends ExpectNonterminal("<BeginningOfTerm>")
object FIRSTFORMULA extends ExpectNonterminal("<BeginningOfFormula>")
object FIRSTPROGRAM extends ExpectNonterminal("<BeginningOfProgram>")
object FIRSTEXPRESSION extends ExpectNonterminal("<BeginningOfExpression>")
object FOLLOWSTERM extends ExpectNonterminal("<FollowsTerm>")
object FOLLOWSFORMULA extends ExpectNonterminal("<FollowsFormula>")
object FOLLOWSPROGRAM extends ExpectNonterminal("<FollowsProgram>")
object FOLLOWSEXPRESSION extends ExpectNonterminal("<FollowsExpression>")
object FOLLOWSIDENT extends ExpectNonterminal("<FollowsIdentifier>")
/** Pseudo-nonterminal encoding that there's other possible expectations beyond what's listed */
object MORE extends ExpectNonterminal("<more>") {override def toString = "..."}

/**
 * KeYmaera X parser reads input strings in the concrete syntax of differential dynamic logic of KeYmaera X.
  *
  * @example
 * Parsing formulas from strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]:
 * {{{
 * val parser = KeYmaeraXParser
 * val fml0 = parser("x!=5")
 * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 * }}}
  * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.parser]]
 * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 */
object KeYmaeraXParser extends Parser {
  import OpSpec.statementSemicolon

  /** This default parser. */
  val parser = this

  /** Lax mode where the parser is a little flexible about accepting input. */
  private[parser] val LAX = System.getProperty("LAX", "true")=="true"

  private val DEBUG = System.getProperty("DEBUG", "true")=="true"

  private val parseErrorsAsExceptions = true

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String): Expression = {
    val tokenStream = KeYmaeraXLexer.inMode(input, ExpressionMode())
    try { parse(tokenStream) }
    catch {case e: ParseException => throw e.inInput(input, Some(tokenStream))}
  }

  def printer: KeYmaeraXPrettyPrinter.type = KeYmaeraXPrettyPrinter

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Parser state consisting of expected syntactic kind to parse currently, the item stack, and remaining input. */
  private[parser] sealed case class ParseState(stack: Stack[Item], input: TokenStream) {
    /** Lookahead location of this parser state */
    private[parser] def location: Location = input.head.loc
    /** Lookahead token of this parser state */
    private[parser] def la: Token = input.head
    override def toString: String = "ParseState(" + stack + "  <|>  " + input.mkString(", ") +")"
    /** Explanation of the top few items on the parser stack */
    def topString: String = stack.take(5).fold("")((s, e) => s + " " + e)
  }

  private val PSEUDOTOK = UnknownToken
  override def termParser: (String => Term) =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, TermKind, apply(input)) match {
      case t: Term => t
      case e@_ => throw ParseException("Input does not parse as a term but as " + e.kind, e).inInput(input)
    }

  override def formulaParser: (String => Formula) =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, FormulaKind, apply(input)) match {
      case f: Formula => f
      case e@_ => throw ParseException("Input does not parse as a formula but as " + e.kind, e).inInput(input)
    }

  /** Parse the input token stream in the concrete syntax as a differential dynamic logic formula */
  private[parser] def formulaTokenParser: (TokenStream => Formula) =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, FormulaKind, parse(input)) match {
      case f: Formula => f
      case e@_ => throw ParseException("Input does not parse as a formula but as " + e.kind, e).inInput("<unknown>", Some(input))
    }

  override def programParser: (String => Program) =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, ProgramKind, apply(input)) match {
      case p: Program => p
      case e@_ => throw ParseException("Input does not parse as a program but as " + e.kind, e).inInput(input)
    }

  override def differentialProgramParser: (String => DifferentialProgram) =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, DifferentialProgramKind, apply(input)) match {
      case p: DifferentialProgram => p
      case e@_ => throw ParseException("Input does not parse as a program but as " + e.kind, e).inInput(input)
    }

  private val eofState = ParseState(Bottom, List(Token(EOF, UnknownLocation)))

  private[parser] def parse(input: TokenStream): Expression = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    val parse = parseLoop(ParseState(Bottom, input)).stack match {
      case Bottom :+ Accept(e) => e
      case context :+ Error(msg, loc, st) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st)
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
    }
    semanticAnalysis(parse) match {
      case None => parse
      case Some(error) => if (LAX) {if (false) println("WARNING: " + "Semantic analysis" + "\nin " + "parsed: " + printer.stringify(parse) + "\n" + error); parse}
      else throw ParseException("Semantic analysis error " + error, parse).inInput("<unknown>", Some(input))
    }
  }

  /** Repeatedly perform parseStep until a final parser item is produced. */
  @tailrec
  private def parseLoop(st: ParseState): ParseState = st.stack match {
    case _ :+ (result: FinalItem) => st
    case _ => parseLoop(parseStep(st))
  }

  /** Semantic analysis of expressions after parsing, returning errors if any or None. */
  def semanticAnalysis(e: Expression): Option[String] = {
    val symbols = StaticSemantics.symbols(e)
    val names = symbols.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
    assert(!DEBUG || (names.size == symbols.size) == (symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).distinct.length == symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).length), "equivalent ways of checking uniqueness via set conversion or list distinctness")
    //@NOTE Stringify avoids infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
    if (names.size == symbols.size) None
    else {
      val namesList = symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
      val duplicateNames = namesList.diff(namesList.distinct)
      val duplicates = symbols.filter(s => duplicateNames.contains((s.name, s.index, s.isInstanceOf[DifferentialSymbol])))
      Some("semantics: Expect unique names_index that identify a unique type." +
         "\nambiguous: " + duplicates.toList.map(s => s.fullString).mkString(" and ") +
         "\nsymbols:   " + symbols.mkString(", ") /*+ if (DEBUG) "\nin expression: " + printer.stringify(e)*/)
    }
  }

  // elaboration based on expected types

  /** Elaborate `e` to the expected `kind` of a part of op by lifting defaulted types as needed or return None. */
  private def elaboratable(kind: Kind, e: Expression): Option[Expression] = if (e.kind==kind) Some(e) else e match {
    // lift misclassified defaulted function application to predicate application when required by context type.
    case FuncOf(f, t) if kind==FormulaKind => Some(PredOf(Function(f.name,f.index,f.domain,Bool), t))
    // lift misclassified defaulted predicate application to function application when required by context type.
    case PredOf(f, t) if kind==TermKind => Some(FuncOf(Function(f.name,f.index,f.domain,Real), t))
    // lift misclassified defaulted differential program constant
    case x: Variable if kind==DifferentialProgramKind && x.index==None => Some(DifferentialProgramConst(x.name))
    // lift misclassified defaulted program constant
    case x: Variable if kind==ProgramKind && x.index==None => Some(ProgramConst(x.name))
    // lift misclassified defaulted term (p(x))' to formula as needed.
    case Differential(t) if kind==FormulaKind => elaboratable(kind, t) match {
      case Some(f:Formula) => Some(DifferentialFormula(f))
      case None => None
    }
    // lift misclassified defaulted formula (f(x))' to term as needed.
    case DifferentialFormula(f) if kind==TermKind => elaboratable(kind, f) match {
      case Some(t:Term) => Some(Differential(t))
      case None => None
    }
    // lift misclassified defaulted differential equation
    case Equal(xp:DifferentialSymbol, e) if kind==DifferentialProgramKind && !StaticSemantics.isDifferential(e) => Some(AtomicODE(xp, e))
    // lift misclassified defaulted differential equation
    case Equal(xp:DifferentialSymbol, e) if kind==ProgramKind && !StaticSemantics.isDifferential(e) => Some(ODESystem(AtomicODE(xp, e)))
    //@todo And(And(x'=5,x>0),x<12)) is not lifted yet
    // lift misclassified defaulted differential equation
    case And(Equal(xp:DifferentialSymbol, e), h)
      if (kind==DifferentialProgramKind || kind==ProgramKind) && !StaticSemantics.isDifferential(h) => Some(ODESystem(AtomicODE(xp, e), h))
    case ode: ODESystem if kind==ProgramKind => Some(ode)
    // whether ODESystem is classified as ProgramKind or DifferentialProgramKind
    case ode: ODESystem if kind==ProgramKind || kind==DifferentialProgramKind => Some(ode)
    // lift differential equations without evolution domain constraints to ODESystems
    case ode: DifferentialProgram if ode.kind==DifferentialProgramKind && kind==ProgramKind => assert(!ode.isInstanceOf[ODESystem], "wrong kind"); Some(ODESystem(ode))
    case _ => None
  }

  /** Elaborate `e` to the expected `kind` of a part of operator `op` at token `tok` by lifting defaulted types as needed or throw exception. */
  private def elaborate(st: ParseState, optok: Token, op: OpSpec, kind: Kind, e: Expression): Expression = elaboratable(kind, e) match {
    case Some(e) => e
      //@todo locations are a little off in error reporting here. Would need original operator token.
    case None => throw ParseException("Impossible elaboration: Operator " + op.op + " expects a " + kind + " as argument but got the " + e.kind + " "  + e.prettyString,
      st, optok, kind.toString)
  }

  /** Elaborate e to the expected kind of a part of op by lifting defaulted types as needed or leave as is. */
  private def possibleElaborate(kind: Kind, e: Expression): Expression = elaboratable(kind, e) match {
    case Some(e) => e
    case None => e
  }

  /** Elaborate the composition op(e) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Token, op: UnaryOpSpec[Expression], e: Expression): Expression =
    op.const(tok.tok.img, elaborate(st, tok, op, op.kind, e))

  /** Elaborate the composition op(e1, e2) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Token, op: BinaryOpSpec[Expression], e1: Expression, e2: Expression): Expression =
    op.const(tok.tok.img, elaborate(st, tok, op, op.kind._1, e1), elaborate(st, tok, op, op.kind._2, e2))

  private[parser] var annotationListener: ((Program,Formula) => Unit) =
  {(p,inv) => println("Annotation: " + p + " @invariant(" + inv + ")")}
  /**
   * Register a listener for @annotations during the parse.
    *
    * @todo this design is suboptimal.
   */
  def setAnnotationListener(listener: (Program,Formula) => Unit): Unit =
    this.annotationListener = listener

  /** Report an @invariant @annotation to interested parties */
  private def reportAnnotation(p: Program, invariant: Formula): Unit = annotationListener(p,invariant)

  /** Whether p is compatible with @annotation */
  private def isAnnotable(p: Program): Boolean =
  //@note DifferentialProgramKind will ultimately be elaborated to ODESystem
    p.isInstanceOf[Loop] || p.isInstanceOf[ODESystem] || p.kind==DifferentialProgramKind


  // parsing

  private def parseStep(st: ParseState): ParseState = {
    val ParseState(s, input@(Token(la,_) :: rest)) = st
    //@note This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // nonproductive: help KeYmaeraXLexer recognize := * with whitespaces as ASSIGNANY
      case r :+ Token(ASSIGN,loc1) :+ Token(STAR,loc2) =>
        reduce(st, 2, Bottom :+ Token(ASSIGNANY, loc1--loc2), r)

      // nonproductive: special notation for annotations
      case r :+ Expr(p:Program) :+ (tok@Token(INVARIANT,_)) :+ Token(LPAREN,_) :+ Expr(f1: Formula) :+ Token(RPAREN,_) if isAnnotable(p) =>
        //@note elaborate DifferentialProgramKind to ODESystem to make sure annotations are stored on top-level
        reportAnnotation(elaborate(st, tok, OpSpec.sNone, ProgramKind, p).asInstanceOf[Program], f1)
        reduce(st, 4, Bottom, r :+ Expr(p))
      case r :+ Expr(p:Program) :+ Token(INVARIANT,_) :+ Token(LPAREN,_) :+ Expr(f1: Formula) if isAnnotable(p) =>
        if (la==RPAREN || formulaBinOp(la)) shift(st) else error(st, List(RPAREN, BINARYFORMULAOP))
      case r :+ Expr(p:Program) :+ Token(INVARIANT,_) =>
        if (isAnnotable(p)) {
          if (la == LPAREN) shift(st) else error(st, List(LPAREN))
        } else errormsg(st, "requires an operator that supports annotation")


      // special quantifier notation
      case r :+ (tok1@Token(FORALL,_)) :+ RecognizedQuant(v1:Variable) :+ Expr(f1:Formula) =>
        reduce(st, 3, OpSpec.sForall.const(tok1.tok.img, v1, f1), r)

      case r :+ (tok1@Token(EXISTS,_)) :+ RecognizedQuant(v1:Variable) :+ Expr(f1:Formula) =>
        reduce(st, 3, OpSpec.sExists.const(tok1.tok.img, v1, f1), r)

      // special case typing to force elaboration of quantifiers at the end
      case r :+ (tok1@Token(FORALL|EXISTS,_)) :+ (tok2@RecognizedQuant(_:Variable)) :+ Expr(e1)
        if (la==EOF || la==RPAREN || la==RBRACE || formulaBinOp(la)) && e1.kind!=FormulaKind =>
        //@todo assert(!formulaBinOp(la) || quantifier binds stronger than la)
        reduce(st, 1, elaborate(st, tok1, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ tok2 )

      // ordinary identifiers disambiguate quantifiers versus predicate/function/predicational versus variable
      case r :+ (tok1@Token(FORALL|EXISTS,_)) :+ Token(IDENT(name,idx),_) =>
        //@note Recognized(Variable()) instead of IDENT to avoid item overlap IDENT LPAREN with function/predicate symbols
        //@note Recognized(Variable()) instead of Variable to avoid detecting lookup confusion with Variable PLUS ... too late
        //@note Recognized should also generalize better to block quantifiers and multi-sorted quantifiers
        if (firstFormula(la)) shift(reduce(st, 1, Bottom :+ RecognizedQuant(Variable(name,idx,Real)), r :+ tok1)) else error(st, List(FIRSTFORMULA))

      case r :+ (tok1@Token(FORALL|EXISTS,_)) =>
        if (la.isInstanceOf[IDENT]) shift(st) else error(st, List(IDENT("IDENT")))


      // special cases for early prime conversion
      case r :+ Token(IDENT(name,idx),_) :+ Token(PRIME,_) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, Variable(name,idx,Real)), r)

//      // special cases for early prime conversion, possibly redundant
//      case r :+ Expr(x1:Variable) :+ Token(PRIME,_) =>
//        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      // ordinary identifiers outside quantifiers disambiguate to predicate/function/predicational versus variable
      case r :+ Token(IDENT(name,idx),_) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        if (la==LPAREN || la==LBRACE || la==PRIME) shift(st) else reduce(st, 1, Variable(name,idx,Real), r)

      // function/predicate symbols arity 0
      case r :+ Token(tok:IDENT,_) :+ Token(LPAREN,_) :+ Token(RPAREN,_)  =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 3, tok, Nothing, r)

      // function/predicate symbols of argument ANYTHING
      case r :+ Token(tok:IDENT,_) :+ Token(LPAREN,_) :+ Token(ANYTHING,_) :+ Token(RPAREN,_)  =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 4, tok, Anything, r)

      // function/predicate symbols arity>0
      case r :+ Token(tok:IDENT,_) :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 4, tok, t1, r)

      // function/predicate symbols arity>0: special elaboration case for misclassified t() as formula
      case r :+ Token(tok:IDENT,_) :+ (optok@Token(LPAREN,_)) :+ Expr(t1:Formula) :+ Token(RPAREN,_) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 4, tok, elaborate(st, optok, OpSpec.sFuncOf, TermKind, t1).asInstanceOf[Term], r)

      // predicational symbols arity>0
      case r :+ Token(IDENT(name,idx),_) :+ Token(LBRACE,_) :+ Expr(f1:Formula) :+ Token(RBRACE,_) =>
        if (followsFormula(la)) reduce(st, 4, PredicationalOf(Function(name, idx, Bool, Bool), f1), r)
        else error(st, List(FOLLOWSFORMULA))

      // predicational symbols arity>0: special elaboration case for misclassified t() as formula
      case r :+ Token(IDENT(name,idx),_) :+ (optok@Token(LBRACE,_)) :+ Expr(f1:Term) :+ Token(RBRACE,_) =>
        if (followsFormula(la)) reduce(st, 4, PredicationalOf(Function(name, idx, Bool, Bool), elaborate(st, optok, OpSpec.sPredOf, FormulaKind, f1).asInstanceOf[Formula]), r)
        else error(st, List(FOLLOWSFORMULA))

      case r :+ Token(tok:IDENT,_) :+ Token(LPAREN,_) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above")
        if (firstTerm(la) || firstFormula(la) || la==RPAREN || la==ANYTHING) shift(st) else error(st, List(FIRSTTERM,FIRSTFORMULA,RPAREN,ANYTHING))

      case r :+ Token(tok:IDENT,_) :+ Token(LBRACE,_) =>
        //assert(isNoQuantifier(r), "Quantifier stack items handled above")
        if (firstFormula(la)) shift(st) else error(st, List(FIRSTFORMULA))


      // special case for negative numbers to turn lexer's MINUS, NUMBER("5") again into NUMBER("-5")
      case r :+ Token(MINUS,loc1) :+ Token(NUMBER(n),loc) if OpSpec.negativeNumber && !n.startsWith("-") && !isNotPrefix(st) &&
        loc1.adjacentTo(loc) =>
        assert(r.isEmpty || !r.top.isInstanceOf[Expr], "Can no longer have an expression on the stack, which would cause a binary operator")
        if (la==LPAREN || la==LBRACE) error(st, List(FOLLOWSTERM))
        else reduce(st, 2, Number(BigDecimal("-" + n)), r)

      case r :+ Token(NUMBER(value),_) =>
        if (la==LPAREN || la==LBRACE) error(st, List(FOLLOWSTERM))
        else reduce(st, 1, Number(BigDecimal(value)), r)


        // PERIOD to DOT conversion for convenience
      case r :+ Token(PERIOD,loc) =>
        reduce(st, 1, Bottom :+ Token(DOT,loc), r)
      case r :+ Token(tok@(DOT|PLACE|NOTHING|ANYTHING | TRUE|FALSE),_) =>
        reduce(st, 1, op(st, tok, List()).asInstanceOf[UnitOpSpec].const(tok.img), r)

      // differentials

      case r :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case r :+ Token(LPAREN,_) :+ Expr(f1:Formula) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)

      // special notation for loops
      case r :+ Token(LBRACE,_) :+ Expr(t1:DifferentialProgram) :+ Token(RBRACE,_) :+ (tok@Token(STAR,_)) =>
        // special elaboration for not-yet-ODESystem Programs
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==INVARIANT) shift(reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, elaborate(st, tok, OpSpec.sNone, ProgramKind, t1).asInstanceOf[Program]), r))
        else reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, elaborate(st, tok, OpSpec.sNone, ProgramKind, t1).asInstanceOf[Program]), r)
      case r :+ Token(LBRACE,_) :+ Expr(t1:Program) :+ Token(RBRACE,_) :+ (tok@Token(STAR,_)) =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==INVARIANT) shift(reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, t1), r))
        else reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, t1), r)

      // parentheses for grouping
      case r :+ Token(LPAREN,_) :+ Expr(t1) :+ Token(RPAREN,_) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        assert(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case r :+ Token(LBRACE,_) :+ Expr(t1:Program) :+ Token(RBRACE,_) =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==STAR) shift(st) else reduce(st, 3, t1, r)


      ///////

      // modalities
      case r :+ (ltok@Token(LBOX,_)) :+ Expr(t1:Program) :+ (rtok@Token(RBOX,_)) =>
        if (firstFormula(la)) shift(reduce(st, 3, RecognizedModal(ltok, elaborate(st, ltok, OpSpec.sBox, ProgramKind, t1).asInstanceOf[Program], rtok), r))
        else error(st, List(FIRSTFORMULA))

      case r :+ (ltok@Token(LDIA,_)) :+ Expr(t1:Program) :+ (rtok@Token(RDIA,_)) =>
        //@note convert to RecognizedMoal to avoid subsequent item confusion with t1 > la
        if (firstFormula(la)) shift(reduce(st, 3, RecognizedModal(ltok, elaborate(st, ltok, OpSpec.sDiamond, ProgramKind, t1).asInstanceOf[Program], rtok), r))
        else error(st, List(FIRSTFORMULA))

      // modal formulas bind tight
      //case r :+ Token(LBOX,_) :+ Expr(p1:Program) :+ Token(RBOX,_) :+ Expr(f1:Formula) =>
      case r :+ RecognizedModal(tok@Token(LBOX,_), p1:Program, Token(RBOX,_)) :+ Expr(f1:Formula) =>
        //@todo assert(modality binds tight)
        reduce(st, 4-2, elaborate(st, tok, OpSpec.sBox, p1, f1), r)

        //@todo could turn the first 3 into Recognized to stash for later and disambiguate
      //case r :+ Token(LDIA,_) :+ Expr(p1:Program) :+ Token(RDIA,_) :+ Expr(f1:Formula) =>
      case r :+ RecognizedModal(tok@Token(LDIA,_), p1:Program, Token(RDIA,_)) :+ Expr(f1:Formula) =>
        //@todo assert(modality binds tight)
        reduce(st, 4-2, elaborate(st, tok, OpSpec.sDiamond, p1, f1), r)

      // special case to force elaboration of modalities at the end
      //case r :+ (tok1@Token(LBOX,_)) :+ Expr(p1:Program) :+ (tok3@Token(RBOX,_)) :+ Expr(e1)
      case r :+ (mod:RecognizedModal) :+ Expr(e1)
        if (la==EOF || la==RPAREN || la==RBRACE || formulaBinOp(la)) && e1.kind!=FormulaKind
          || (if (statementSemicolon) la==SEMI else programOp(la)) =>
        reduce(st, 1, elaborate(st, mod.rtok, OpSpec.sNone,  FormulaKind, e1), r :+ mod)

//      // special case to force elaboration of modalities at the end
//      case r :+ (tok1@Token(LDIA,_)) :+ Expr(p1:Program) :+ (tok3@Token(RDIA,_)) :+ Expr(e1)
//        if (la==EOF || la==RPAREN || la==RBRACE || formulaBinOp(la)) && e1.kind!=FormulaKind =>
//        reduce(st, 1, elaborate(st, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ Expr(p1) :+ tok3)

      // special case to force elaboration to DifferentialProgramConst {c} and {c,...} and {c&...}
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(e1:Variable) if la==AMP || la==COMMA || la==RBRACE =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "IDENT stack for predicationals has already been handled")
        reduce(st, 1, elaborate(st, tok1, OpSpec.sNone, DifferentialProgramKind, e1), r :+ tok1)

      // differential equation system special notation
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(p1:DifferentialProgram) :+ (tok2@Token(AMP,_)) :+ Expr(f1:Formula) :+ (tok3@Token(RBRACE,_)) =>
        reduce(st, 5, elaborate(st, tok2, OpSpec.sODESystem, p1, f1), r)

      // elaboration special pattern case
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@Equal(_:DifferentialSymbol,_)) =>
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, tok1, OpSpec.sODESystem, DifferentialProgramKind, t1)), r)

      // elaboration special pattern case
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@And(Equal(_:DifferentialSymbol,_),_)) =>
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, tok1, OpSpec.sODESystem, DifferentialProgramKind, t1)), r)



      // special case for sCompose in case statementSemicolon
      //@todo review
      case r :+ Expr(p1: Program) :+ Expr(p2: Program) if statementSemicolon =>
        if (la==LPAREN || !statementSemicolon&&la==LBRACE) error(st, if (statementSemicolon) List(LPAREN) else List(LPAREN,LBRACE))
        val optok = OpSpec.sCompose
        assume(optok.assoc==RightAssociative)
        //@todo op(st, la) : Potential problem: st is not the right parser state for la
        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
          || (la == RDIA/* || la == RDIA*/) && (p1.kind == ProgramKind || p1.kind == DifferentialProgramKind)
          || la!=LBRACE && (optok < op(st, la, List(p2.kind,ExpressionKind)) || optok <= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == LeftAssociative))
          reduce(st, 2, elaborate(st, Token(SEMI, UnknownLocation), op(st, SEMI, List(p1.kind,p2.kind)).asInstanceOf[BinaryOpSpec[Expression]], p1, p2), r)
        else if (statementSemicolon&&la==LBRACE || optok > op(st, la, List(p2.kind,ExpressionKind)) || optok >= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == RightAssociative)
          shift(st)
        else {assert(statementSemicolon); error(st, List(EOF,RPAREN,RBRACE,RBOX,RDIA, LBRACE))}

//      // lax accepts optional or possibly even extra SEMI between the two programs for sequential composition
//      case r :+ Expr(p1: Program) :+ (tok@Token(SEMI,_)) :+ Expr(p2: Program) if statementSemicolon && LAX =>
//        if (la==LPAREN || !statementSemicolon&&la==LBRACE) error(st)
//        val optok = OpSpec.sCompose
//        assume(optok.assoc==RightAssociative)
//        //@todo op(st, la) : Potential problem: st is not the right parser state for la
//        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
//          || (la == RDIA || la == RDIA) && (p1.kind == ProgramKind || p1.kind == DifferentialProgramKind)
//          || la!=LBRACE && (optok < op(st, la, List(p2.kind,ExpressionKind)) || optok <= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == LeftAssociative))
//          reduce(st, 3, op(st, tok.tok, List(p1.kind,p2.kind)).asInstanceOf[BinaryOpSpec[Program]].const(tok.tok.img, p1, p2), r)
//        else if (statementSemicolon&&la==LBRACE || optok > op(st, la, List(p2.kind,ExpressionKind)) || optok >= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == RightAssociative)
//          shift(st)
//        else error(st)

      // generic operators

      // binary operators with precedence
      //@todo review
      //@todo should really tok!=COMMA and handle that one separately to enforce (x,y) notation but only allow p(x,y) without p((x,y)) sillyness
      case r :+ Expr(t1) :+ (optok1@Token(tok:OPERATOR,_)) :+ Expr(t2) if !((t1.kind==ProgramKind||t1.kind==DifferentialProgramKind) && tok==RDIA) &&
        tok!=TEST =>
        // pass t1,t2 kinds so that op/2 can disambiguate based on kinds
        val optok = op(st, tok, List(t1.kind,t2.kind))
        if (optok==OpSpec.sNoneUnfinished && la!=EOF) shift(st)
        else {
          assume(optok.isInstanceOf[BinaryOpSpec[_]], "binary operator expected for " + optok + " since others should have been reduced\nin " + s)
          if (la==LPAREN || !statementSemicolon && la==LBRACE) error(st, List(LPAREN, LBRACE))
          else {
            //@todo op(st, la) : Potential problem: st is not the right parser state for la
            //@todo if statementSemicolon then the missing SEMI causes incorrect predictions of operator precedence ++ versus ;
            if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
              || (la==RDIA /*|| la==RDIA*/) && (t1.kind == ProgramKind || t1.kind == DifferentialProgramKind)
              || la!=LBRACE &&
                (optok<op(st, la, List(t2.kind, ExpressionKind))
                  || optok<=op(st, la, List(t2.kind, ExpressionKind)) && optok.assoc==LeftAssociative && op(st, la, List(t2.kind, ExpressionKind)).assoc==LeftAssociative)) {
              //println("\tGOT: " + tok + "\t" + "LA: " + la + "\tAfter: " + s + "\tRemaining: " + input)
              val result = elaborate(st, optok1, optok.asInstanceOf[BinaryOpSpec[Expression]], t1, t2)
              if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
                if (la==SEMI) reduce(shift(st), 4, result, r)
                else if (result.isInstanceOf[DifferentialProgram] || result.isInstanceOf[ODESystem]) reduce(st, 3, result, r) // optional SEMI
                else error(st, List(SEMI))
              } else reduce(st, 3, result, r)
            } else if (statementSemicolon && la==LBRACE
              || optok>op(st, la, List(t2.kind, ExpressionKind))
              || optok>=op(st, la, List(t2.kind, ExpressionKind)) && optok.assoc==RightAssociative && op(st, la, List(t2.kind, ExpressionKind)).assoc==RightAssociative)
              shift(st)
            else error(st, List(LPAREN, EOF, RPAREN, RBRACE, RBOX, RDIA, LBRACE, MORE))
          }
        }

      // unary prefix operators with precedence
      //@todo review
      case r :+ (optok1@Token(tok:OPERATOR,_)) :+ Expr(t1) if op(st, tok, List(t1.kind)).assoc==PrefixFormat =>
        assume(op(st, tok, List(t1.kind)).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        val optok = op(st, tok, List(t1.kind))
        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
          || (la == RDIA || la == RDIA) && (t1.kind == ProgramKind || t1.kind == DifferentialProgramKind)
          || optok <= op(st, la, List(t1.kind,ExpressionKind))) {
          //|| followsTerm(la))
          //@note By operator precedence, will only elaborate if need be, i.e. unless lookahead says shifting will get the right type
          val result = elaborate(st, optok1, op(st, tok, List(t1.kind)).asInstanceOf[UnaryOpSpec[Expression]], t1)
          if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
            if (la == SEMI) reduce(shift(st), 3, result, r)
            else error(st, List(SEMI))
          } else reduce(st, 2, result, r)
        } else if (optok > op(st, la, List(t1.kind,ExpressionKind))) shift(st)
        else error(st, List(MORE))

      case _ :+ Token(tok:OPERATOR,_) if op(st, tok, List(ExpressionKind)).assoc==PrefixFormat || tok==MINUS =>
        //@note MINUS will always have to be shifted before reduction, whether binary infix or unary prefix
        assert(op(st, tok, List(ExpressionKind)).isInstanceOf[UnaryOpSpec[_]] || tok==MINUS, "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st)
        else error(st, List(FIRSTEXPRESSION))

      // unary postfix operator
      case r :+ Expr(t1) :+ (optok@Token(tok:OPERATOR,_)) if op(st, tok, List(t1.kind)).assoc==PostfixFormat && tok!=STAR =>
        //@note STAR from sLoop needs explicit braces
        assert(op(st, tok, List(t1.kind)).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have postfix format\nin " + s)
        val result = elaborate(st, optok, op(st, tok, List(t1.kind)).asInstanceOf[UnaryOpSpec[Expression]], t1)
        if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
          if (la == SEMI) reduce(shift(st), 3, result, r)
          else error(st, List(SEMI))
        } else reduce(st, 2, result, r)

      // special case for elaboration to a;
      case r :+ Expr(t1:Variable) :+ (optok@Token(SEMI,_)) if statementSemicolon =>
        assert(r.isEmpty || !r.top.isInstanceOf[Token] || !(r.top.asInstanceOf[Token].tok==ASSIGN || r.top.asInstanceOf[Token].tok==EQ || r.top.asInstanceOf[Token].tok==TEST), "Would have recognized as atomic statement already or would not even have shifted to SEMI")
        //@todo assert r.top is not formula or term operator or assignment or test
        //@note should not have gone to SEMI if there would have been another reduction to an atomic program already.
        reduce(st, 2, elaborate(st, optok, OpSpec.sProgramConst, ProgramKind, t1), r)

      case _ :+ Expr(t1) :+ (tok@Token(STAR,_)) =>
        if (firstTerm(la) && la!=EOF) shift(st) else error(st, List(FIRSTTERM))
      //@note explicit braces around loops so can't happen:
//        if (firstExpression(la) ||
//          t1.isInstanceOf[Program] && followsProgram((la))) shift(st) else error(st)

      case _ :+ Expr(t1) :+ (tok@Token(op:OPERATOR,_)) if op != PRIME =>
        if (firstExpression(la) && la!=EOF) shift(st) else error(st, List(FIRSTEXPRESSION))


      case _ :+ (tok@Token(LPAREN,_)) :+ Expr(t1) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (followsExpression(t1, la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)
        else error(st, List(FOLLOWSEXPRESSION))

      case _ :+ (tok@Token(LBRACE,_)) :+ Expr(t1:Program) =>
        if (followsProgram(la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)
        else error(st, List(FOLLOWSPROGRAM))

      case _ :+ (tok@Token(LBOX,_)) :+ Expr(t1) =>
        if (t1.isInstanceOf[Program] && followsProgram(la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Unmatched modality", tok, st)
        else if ((t1.isInstanceOf[Variable] || t1.isInstanceOf[DifferentialSymbol]) && followsIdentifier(la)) shift(st)
        else if ((elaboratable(ProgramKind, t1)!=None || elaboratable(DifferentialProgramKind, t1)!=None) && followsProgram(la)) shift(st)
        else error(st, List(FOLLOWSPROGRAM, FOLLOWSIDENT))

      case _ :+ (tok@Token(LDIA,_)) :+ Expr(t1)  =>
        if (followsExpression(t1, la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Unmatched suspected modality", tok, st)
        else if ((t1.isInstanceOf[Variable] || t1.isInstanceOf[DifferentialSymbol]) && followsIdentifier(la)) shift(st)
        else if ((elaboratable(ProgramKind, t1)!=None || elaboratable(DifferentialProgramKind, t1)!=None) && followsProgram(la)) shift(st)
        else error(st, List(FOLLOWSEXPRESSION, FOLLOWSIDENT))

      case _ :+ Token(LPAREN,_) =>
        if (firstFormula(la) /*|| firstTerm(la)*/ || la==RPAREN || la==ANYTHING) shift(st)
        else error(st, List(FIRSTFORMULA, RPAREN, ANYTHING))

      case _ :+ Token(LBRACE,_) =>
        if (firstProgram(la) || firstFormula(la) /*for predicationals*/) shift(st)
        else error(st, List(FIRSTPROGRAM, FIRSTFORMULA))

      case _ :+ Token(LBOX,_) =>
        if (firstProgram(la)) shift(st)
        else error(st, List(FIRSTPROGRAM))

      case _ :+ Token(LDIA,_) =>
        if (firstProgram(la) || firstTerm(la)) shift(st)
        else error(st, List(FIRSTPROGRAM, FIRSTTERM))

      // non-accepting expression
      case _ :+ _ :+ Expr(t) =>
        if (followsExpression(t, la) && la!=EOF) shift(st)
        else error(st, List(FOLLOWSEXPRESSION))

      // small stack cases
      case Bottom :+ Expr(t) =>
        if (la == EOF) accept(st, t)
        else if (followsExpression(t, la) && la!=EOF) shift(st)
        else error(st, List(EOF, FOLLOWSEXPRESSION))

      case Bottom =>
        if (firstExpression(la)) shift(st)
        else if (la==EOF) throw ParseException("Empty input is not a well-formed expression ", st, List(FIRSTEXPRESSION)) else error(st, List(FIRSTEXPRESSION))

      case rest :+ (tok@Token(RPAREN,_)) if !rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LPAREN).isDefined =>
        throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)

      case rest :+ (tok@Token(RBRACE,_)) if !rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LBRACE).isDefined =>
        throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)

      case rest :+ (tok@Token(RBOX,_)) if !rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LBOX).isDefined =>
        throw ParseException.imbalancedError("Unmatched modality", tok, st)

      case rest :+ (tok@Token(RDIA,_)) if !rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LDIA).isDefined =>
        throw ParseException.imbalancedError("Syntax error or unmatched modality", tok, st)

      case _ => {
        //Try to make a good error message.
        goodErrorMessage(st) match {
          case Some(msg) => throw ParseException(s"${msg}", st)
          case None => throw ParseException(s"Syntax error (or incomplete parser missing an item).\nWe could not generate a nice error message for stack: ${st.stack}", st)
        }
        //@todo cases should be completed to complete the parser items, but it's easier to catch-all and report legible parse error.

        //throw new AssertionError("Incomplete parser missing an item, so does not yet know how to handle case.\nFound: " + la + "\nAfter: " + s)
      }
    }
  }

  private def goodErrorMessage(st : ParseState) : Option[String] = st.stack.top match {
    case Token(edu.cmu.cs.ls.keymaerax.parser.RBOX, _) => Some("Syntax error. Perhaps the program contained in your box modality is ill-formed or incomplete?")
    case _ => None
  }

  // stack helper

    /**
     * Reduce consuming items in the parse state st to function/predicate name applied to argument arg,
     * while automatically disambiguating between function and predicate symbols based on lookahead
     * and parser state of stack items.
      *
      * @NOTE Needs to be able to disambiguate early in [x:=q()]f()->r()+c(x)>0
     */
  private def reduceFuncOrPredOf(st: ParseState, consuming: Int, name: IDENT, arg: Term, remainder: Stack[Item]): ParseState = {
    val ParseState(s, input@(Token(la, _) :: rest)) = st
    if (termBinOp(la) || isTerm(st) && followsTerm(la))
      reduce(st, consuming, FuncOf(Function(name.name, name.index, arg.sort, Real), arg), remainder)
    else if (formulaBinOp(la) || isFormula(st) && followsFormula(la))
      reduce(st, consuming, PredOf(Function(name.name, name.index, arg.sort, Bool), arg), remainder)
    else if (followsFormula(la))
      reduce(st, consuming, PredOf(Function(name.name, name.index, arg.sort, Bool), arg), remainder)
    else if (followsTerm(la))
      reduce(st, consuming, FuncOf(Function(name.name, name.index, arg.sort, Real), arg), remainder)
    else if (la == RPAREN) shift(st)
    else error(st, List(BINARYTERMOP,BINARYFORMULAOP,RPAREN,MORE))
  }

  /** Top terminal token from stack or EOF if the top item is not a token or the stack is empty. */
  private def stackToken(s: Stack[Item]): Terminal =
    if (!s.isEmpty && s.top.isInstanceOf[Token]) s.top.asInstanceOf[Token].tok else EOF

  // FIRST lookahead sets

  /** Is la the beginning of a new expression? */
  private def firstExpression(la: Terminal): Boolean = firstFormula(la) || firstProgram(la) /*|| firstTerm(la) */

  /** First(Term): Is la the beginning of a new term? */
  private def firstTerm(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] ||
    la==MINUS || la==LPAREN || la==DOT ||
    la==PERIOD      // from DotTerm

  /** First(Formula): Is la the beginning of a new formula? */
  private def firstFormula(la: Terminal): Boolean = firstTerm(la) || /*la.isInstanceOf[IDENT] ||*/
    la==NOT || la==FORALL || la==EXISTS || la==LBOX || la==LDIA || la==TRUE || la==FALSE || la==PLACE /*|| la==LPAREN */

  /** First(Program): Is la the beginning of a new program? */
  private def firstProgram(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la==TEST || la==LBRACE

  // FOLLOW sets

  /** Follow(Formula): Can la follow after a formula? */
  private def followsFormula(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV || la==RPAREN ||
    la==RBRACE /* from predicationals */ ||
    la==PRIME || la==EOF

  /** Is la a (binary) operator that only works for formulas? */
  private def formulaBinOp(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV

  /** Is la a (unary/binary) operator that only works for programs? */
  private def programOp(la: Terminal): Boolean = la==SEMI || la==CHOICE || la==DUAL

  /** Follow(Term): Can la follow after a term? */
  private def followsTerm(la: Terminal): Boolean = la==RPAREN ||
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
    la==EQ || la==NOTEQ || la==GREATEREQ || la==RDIA || la==LESSEQ || la==LDIA || // from T in formulas
    followsFormula(la) ||
    (if (statementSemicolon) la==SEMI || la==RBRACE || la==AMP
    else la==SEMI || la==CHOICE || la==STAR || la==RBRACE || la==COMMA) || // from T in programs
    la == COMMA || // from T in ODE systems
    la==PRIME || la==EOF

  /** Is la a (binary) operator that only works for terms? */
  private def termBinOp(la: Terminal): Boolean =
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
    la==EQ || la==NOTEQ || la==GREATEREQ || la==LESSEQ // from T in formulas
  //|| la==RDIA || la==LDIA // from T in formulas but also possibly as modalities

  /** Follow(Program): Can la follow after a program? */
  private def followsProgram(la: Terminal): Boolean = la==RBRACE || la==CHOICE || la==STAR/**/ ||
    (if (statementSemicolon) firstProgram(la) || /*Not sure:*/ la==SEMI else la==SEMI)  ||
    la==RBOX || la==RDIA ||  // from P in programs
    la==COMMA || la==AMP ||  // from D in differential programs
    la==EOF ||
    la==DUAL ||              // from P in hybrid games
    la==INVARIANT            // extra: additional @annotations

  /** Follow(kind(expr)): Can la follow an expression of the kind of expr? */
  private def followsExpression(expr: Expression, la: Terminal): Boolean = expr match {
    case _: Variable => followsIdentifier(la) || /*if elaborated to program*/ followsProgram(la)
    case _: DifferentialSymbol => followsTerm(la) || la==ASSIGN
    case FuncOf(_,_) => followsTerm(la) || /*elaboratable(FormulaKind, t)!=None &&*/ followsFormula(la) //@todo line irrelevant since followsTerm subsumes followsFormula
    case _: Term => followsTerm(la)
    case And(Equal(_:DifferentialSymbol, _), _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case Equal(_:DifferentialSymbol, _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case f: Formula => followsFormula(la) || elaboratable(TermKind, f)!=None && followsTerm(la)
    case _: Program => followsProgram(la)
    case _ => ???
  }

  /** Follow(Identifier): Can la follow after an identifier? */
  private def followsIdentifier(la: Terminal): Boolean = followsTerm(la) ||
    la==LPAREN || la==PRIME ||
    la==ASSIGN || la==ASSIGNANY || la==EOF || firstFormula(la) /* from \exists x ... */


  // parser actions

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val ParseState(s, (la :: rest)) = st
    if (parseErrorsAsExceptions && la.tok == EOF) throw ParseException("Unfinished input. Parser cannot shift past end of file", st)
    else require(la.tok != EOF, "Cannot shift past end of file")
    ParseState(s :+ la, rest)
  }

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
    *
    * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Item, remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) :+ reduced, input)
  } ensuring(r => r.stack.tail == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  private def reduce(st: ParseState, consuming: Int, reduced: Expression, remainder: Stack[Item]): ParseState = reduce(st, consuming, Expr(reduced), remainder)

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
    *
    * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack[Item], remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) ++ reduced, input)
  } ensuring(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val ParseState(s, input) = st
    require(input == List(Token(EOF)), "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(Bottom :+ Accept(result), input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState, expect: List[Expected]): ParseState = {
    if (parseErrorsAsExceptions) throw ParseException("Unexpected token cannot be parsed", st, expect)
    else {
      val ParseState(s, input@(la :: rest)) = st
      ParseState(s :+ Error("Unexpected token cannot be parsed\nFound: " + la + "\nExpected: " + expect, la.loc, st.toString), input)
    }
  }

    /** Error parsing the next input token la when in parser stack s.*/
  private def errormsg(st: ParseState, expect: String): ParseState = {
    val ParseState(s, input@(la :: rest)) = st
    if (parseErrorsAsExceptions) throw ParseException("Unexpected token cannot be parsed", st, expect)
    else ParseState(s :+ Error("Unexpected token cannot be parsed\nFound: " + la + "\nExpected: " + expect, la.loc, st.toString), input)
  }

  /** Drop next input token la from consideration without shifting it to the parser stack s. */
  private def drop(st: ParseState): ParseState = {
    val ParseState(s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot drop end of file")
    ParseState(s, rest)
  }


  // state lookup based on parser state

  /** Checks that stack does not start with a quantifier directly on top */
  private def isNoQuantifier(stack: Stack[Item]): Boolean =
    stack.isEmpty || !(stack.top.isInstanceOf[Token] && (stack.top.asInstanceOf[Token].tok==FORALL || stack.top.asInstanceOf[Token].tok==EXISTS))

  /** If the stack starts with an expr item, so has been reduced already, it can't be a prefix operator */
  private def isNotPrefix(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_) :+ Token(_:OPERATOR, _)  :+ _ => true
    case _ => false
  }

  /** If the stack starts with something that is guaranteed to be a formula item */
  private def isFormula(st: ParseState): Boolean = (st.stack match {
    case _ :+ Token(op:OPERATOR,_) => formulaBinOp(op)
    case _ :+ Token(op:OPERATOR,_) :+ Expr(_) => formulaBinOp(op)
    case _ :+ Expr(_:Formula) => true
    case _ => false
  })

  /** If the stack starts with something that is guaranteed to be a term item */
  private def isTerm(st: ParseState): Boolean = (st.stack match {
    case _ :+ Token(op:OPERATOR,_) => termBinOp(op)
    case _ :+ Token(op:OPERATOR,_) :+ Expr(_) => termBinOp(op)
    case _ :+ Expr(_:Term) => true
    case _ => false
  })

  // this is a terrible approximation
  private def isProgram(st: ParseState): Boolean = (st.stack match {
    case _ :+ Expr(_:Program) => true
    case _ :+ Token(LBRACE,_) => true
    case _ :+ Token(LBOX,_) => true
    case _ :+ Token(LBRACE,_) :+ _ => true
    case _ :+ Token(LBOX,_) :+ _ => true
    case _ :+ Expr(_:Program) :+ _ => true
    case _ => false
  })

  private def isVariable(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:Variable) => true
    case _ => false
  }

  private def isDifferentialSymbol(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:DifferentialSymbol) => true
    case _ :+ Expr(_:DifferentialSymbol) :+ Token(ASSIGN,_) :+ Expr(_) => true
    case _ => false
  }

  // operator precedence lookup based on parser state

  import OpSpec._

  /**
   * The operator notation of the top-level operator of expr with opcode, precedence and associativity.
   * Main responsibility is to disambiguate different operators with the same notation based on kinds and parse state.
   */
  private[parser] def op(st: ParseState, tok: Terminal, kinds: List[Kind]): OpSpec = {
   // println("\top(" + tok +" " + kinds)
    (tok: @switch) match {
      //@note could almost(!) replace by reflection to search through all OpSpec and check their images.
      // terms
      case sDotTerm.op => sDotTerm
      case sNothing.op => sNothing
      case sAnything.op => sAnything
      case s:IDENT/*sVariable.op*/ => sVariable //@todo could also be FuncOf/PredOf if la==LPAREN but does not really change precedence
      case s:NUMBER/*sNumber.op*/ => sNumber
      //case t: FuncOf => sFuncOf
      case sDifferential.op => if (isVariable(st)) sDifferential else if (isFormula(st)) sDifferentialFormula else sDifferential
      case sPair.op => if (!kinds.isEmpty && kinds(0)!=TermKind) sDifferentialProduct else sPair
      case sMinus.op => if (kinds==List(TermKind,TermKind)||kinds==List(TermKind,ExpressionKind)) sMinus else if (kinds==List(TermKind)) sNeg
        else if (isNotPrefix(st)) sMinus else sNeg
      case sPower.op => sPower
      case sTimes.op => if (kinds==List(ProgramKind) || kinds==List(ExpressionKind))/*if (isProgram(st))*/ sLoop else sTimes
      case sDivide.op => sDivide
      case sPlus.op => sPlus

      // formulas
      case sDotFormula.op => sDotFormula
      case sTrue.op => sTrue
      case sFalse.op => sFalse
      //case f: PredOf => sPredOf
      //case f: PredicationalOf => sPredicationalOf
      //case f: DifferentialFormula => sDifferentialFormula
      case sEqual.op => if (isProgram(st)) sAtomicODE else sEqual
      case sNotEqual.op => sNotEqual
      case sGreaterEqual.op => sGreaterEqual
      case sGreater.op => if (!kinds.isEmpty && kinds(0)==ProgramKind) sNoneDone else sGreater   // 1/2 sDiamond
      case sLessEqual.op => sLessEqual
      case sLess.op => if (kinds.length>=2 && kinds(1)==ProgramKind) sNone else sLess    // 1/2 sDiamond
      case sForall.op => sForall
      case sExists.op => sExists
      //      case f: Box => sBox
      //      case f: Diamond => sDiamond
      case sNot.op => sNot
      case sAnd.op => if (!kinds.isEmpty && (kinds(0)==ProgramKind||kinds(0)==DifferentialProgramKind))/*if (isProgram(st))*/ sNoneUnfinished/*sODESystem*/ else sAnd
      case sOr.op => sOr
      case sImply.op => sImply
      case sRevImply.op => sRevImply
      case sEquiv.op => sEquiv

      // programs
      //case p: ProgramConst => sProgramConst
      //case p: DifferentialProgramConst => sDifferentialProgramConst
      case sAssign.op => if (isDifferentialSymbol(st)) sDiffAssign else sAssign
      case sAssignAny.op => sAssignAny
      case sTest.op => sTest
      //      case p: ODESystem => sODESystem
      //      case p: AtomicODE => sAtomicODE
      case sDifferentialProduct.op => sDifferentialProduct
      //      case sLoop.op => sLoop
      case sDual.op => sDual
      case sCompose.op => sCompose
      case sChoice.op => sChoice


      case INVARIANT => sNone
      //case
      case sEOF.op => sEOF
    }
  } ensuring(r => r.op == tok && r.opcode == tok.img || r==sNone || r==sNoneDone || tok.isInstanceOf[IDENT] || tok.isInstanceOf[NUMBER], "OpSpec's opcode coincides with expected token " + tok)


}
