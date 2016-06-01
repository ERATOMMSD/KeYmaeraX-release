/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
 * to Mathematica Expr objects.
 * @author Nathan Fulton
 */
class KeYmaeraToMathematica {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  //@todo Code Review contract: convert back is identity, ask converse converter
  def fromKeYmaera(e: KExpr): MExpr = e match {
    case t: Term =>
      require(disjointNames(StaticSemantics.symbols(t)), "Disjoint names required for Mathematica conversion")
      convertTerm(t)
    case f: Formula =>
      require(disjointNames(StaticSemantics.symbols(f)), "Disjoint names required for Mathematica conversion")
      convertFormula(f)
    case fn: Function =>
      //@todo Code Review: prefixed name must be disjoint from other names in the containing term/formula -> Mathematica namespace `constFn`
      MathematicaNameConversion.toMathematica(
        new Function(MathematicaNameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
  }

  private def disjointNames(symbols: Set[NamedSymbol]): Boolean = {
    val names = symbols.map(x=>(x.name,x.index)).toList
    names.distinct.length == names.length
  }

  /**
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  protected def convertTerm(t : Term): MExpr = {
    /** Convert tuples to list of sorts */
    def flattenSort(s: Sort): List[Sort] = s match {
      case Tuple(ls, rs) => flattenSort(ls) ++ flattenSort(rs)
      case _ => s :: Nil
    }

    require(t.sort == Real || t.sort == Unit || flattenSort(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      //@todo Code Review: clean up FuncOf conversion into two cases here
      case FuncOf(fn, child) => convertFnApply(fn, child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case Plus(l, r) =>
        new MExpr(MathematicaSymbols.PLUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Minus(l, r) =>
        new MExpr(MathematicaSymbols.MINUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Times(l, r) =>
        new MExpr(MathematicaSymbols.MULT, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Divide(l, r) =>
        new MExpr(MathematicaSymbols.DIV, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Power(l, r) =>
        new MExpr(MathematicaSymbols.EXP, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) =>
        //@note converts nested pairs into nested lists
        new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))

      case t: Variable => MathematicaNameConversion.toMathematica(t)
    }
  }

  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  protected def convertFormula(f : Formula): MExpr = f match {
    case And(l,r)   => new MExpr(MathematicaSymbols.AND, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equiv(l,r) => new MExpr(MathematicaSymbols.BIIMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Imply(l,r) => new MExpr(MathematicaSymbols.IMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Or(l,r)    => new MExpr(MathematicaSymbols.OR, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equal(l,r) => new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case NotEqual(l,r) => new MExpr(MathematicaSymbols.UNEQUAL, Array[MExpr](convertTerm(l), convertTerm(r)))
    case LessEqual(l,r) => new MExpr(MathematicaSymbols.LESS_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Less(l,r)   => new MExpr(MathematicaSymbols.LESS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case GreaterEqual(l,r) => new MExpr(MathematicaSymbols.GREATER_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Greater(l,r) => new MExpr(MathematicaSymbols.GREATER, Array[MExpr](convertTerm(l), convertTerm(r)))
    case False => MathematicaSymbols.FALSE
    case True => MathematicaSymbols.TRUE
    case Not(phi) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(phi)))
    case Exists(vs, phi) => convertExists(vs,phi)
    case Forall(vs, phi) => convertForall(vs,phi)
    case _ => throw new ProverException("Don't know how to convert " + f + " of class " + f.getClass)
  }

  protected def convertFnApply(fn: Function, child: Term): MExpr = child match {
    //@todo Code Review: avoid duplicate code, see fromKeYmaera
    case Nothing => MathematicaNameConversion.toMathematica(new Function(MathematicaNameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
    case _ =>
      //@note single-argument Apply[f, {x}] == f[x] vs. Pair arguments turn into list arguments Apply[f, {{x,y}}] == f[{x,y}]
      //@note Pairs will be transformed into nested lists, which makes f[{x, {y,z}] different from f[{{x,y},z}] and would require list arguments (instead of argument lists) when using the functions in Mathematica. Unproblematic for QE, since converted in the same fashion every time
      val args = Array[MExpr](MathematicaNameConversion.toMathematica(fn), new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(child))))
      new MExpr(MathematicaSymbols.APPLY, args)
  }

  //@todo Code Review: Forall+Exists could be 1 conversion
  /** Convert block of exists quantifiers into a single exists quantifier block */
  protected def convertExists(vs:Seq[NamedSymbol],f:Formula): MExpr = {
    val (vars, formula) = collectVarsExists(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(MathematicaNameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.EXISTS, Array[MExpr](variables, convertFormula(formula)))
  }
  /** Recursively converts sequences of quantifiers into a single block quantifier */
  private def collectVarsExists(vsSoFar:Seq[NamedSymbol],candidate:Formula): (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextf) =>  collectVarsExists(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  /** Convert block of forall quantifiers into a single forall quantifier block */
  protected def convertForall(vs:Seq[NamedSymbol],f:Formula): MExpr = {
    val (vars, formula) = collectVarsForall(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(MathematicaNameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.FORALL, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsForall(vsSoFar:Seq[NamedSymbol],candidate:Formula): (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextf) =>  collectVarsForall(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  protected def keyExn(e: KExpr): Exception =
    new ConversionException("conversion not defined for KeYmaera expr: " + PrettyPrinter.printer(e))
}

