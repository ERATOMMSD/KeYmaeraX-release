/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
 * Uniform Renaming for KeYmaera X
 * @author Andre Platzer
 * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
 * @note Code Review: 2016-03-09
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

/**
  * Uniformly rename all occurrences of `what` and `what'` to `repl` and `repl'` and vice versa.
  * Uniformly rename all occurrences of variable `what` (and its associated DifferentialSymbol `what'`) to
  * `repl` (and its associated DifferentialSymbol `repl'`) everywhere
  * and vice versa uniformly rename all occurrences of variable `repl` (and its associated DifferentialSymbol) to `what` (and `what'`).
  * @param what What variable to replace (along with its associated DifferentialSymbol).
  * @param repl The target variable to replace `what` with and vice versa.
  * @author Andre Platzer
  * @author smitsch
  * @see [[UniformRenaming]]
  */
final case class URename(what: Variable, repl: Variable) extends Renaming {
  /** Whether to allow semantic renaming, i.e., renaming within ProgramConst etc that do not have a syntactic representation of `what`. */
  private[core] override val semanticRenaming: Boolean = true
}

/**
  * Uniformly rename all occurrences of `what` and `what'` to `repl` and `repl'` and vice versa.
  * Uniformly rename all occurrences of variable `what` (and its associated DifferentialSymbol `what'`) to
  * `repl` (and its associated DifferentialSymbol `repl'`) everywhere
  * and vice versa uniformly rename all occurrences of variable `repl` (and its associated DifferentialSymbol) to `what` (and `what'`).
  * @param what What variable to replace (along with its associated DifferentialSymbol).
  * @param repl The target variable to replace `what` with and vice versa.
  * @author Andre Platzer
  * @author smitsch
  * @see [[BoundRenaming]]
  */
final case class SyntacticURename(what: Variable, repl: Variable) extends Renaming {
  /** Whether to allow semantic renaming, i.e., renaming within ProgramConst etc that do not have a syntactic representation of `what`. */
  //@note for bound renaming purposes this absolutely has to be false
  private[core] override val semanticRenaming: Boolean = false
}

/**
  * Uniformly rename all occurrences of `what` and `what'` to `repl` and `repl'` and vice versa.
  * Uniformly rename all occurrences of variable `what` (and its associated DifferentialSymbol `what'`) to
  * `repl` (and its associated DifferentialSymbol `repl'`) everywhere
  * and vice versa uniformly rename all occurrences of variable `repl` (and its associated DifferentialSymbol) to `what` (and `what'`).
  * @author Andre Platzer
  * @author smitsch
 */
sealed trait Renaming extends (Expression => Expression) {
  insist(what.sort == repl.sort, "Uniform renaming only to variables of the same sort")
  /** What variable to replace (along with its associated DifferentialSymbol). */
  val what: Variable
  /** The target variable to replace `what` with and vice versa */
  val repl: Variable
//  /** The variables that are not allowed to occur initially */
//  private val taboo: Set[NamedSymbol] = if (repl.sort == Real) Set(repl,DifferentialSymbol(repl)) else Set(repl)
//  /** The variables that are affected and should be gone finally */
//  private val affected: Set[NamedSymbol] = if (what.sort == Real) Set(what,DifferentialSymbol(what)) else Set(what)

  /** Whether to allow semantic renaming, i.e., renaming within ProgramConst etc that do not have a syntactic representation of `what`. */
  private[core] val semanticRenaming: Boolean
  /** `true` for transpositions (replace `what` by `repl` and `what'` by `repl'` and, vice versa, `repl` by `what` etc) or `false` to clash upon occurrences of `repl` or `repl'`. */
  private[core] val TRANSPOSITION: Boolean = true

  override def toString: String = "URename{" + what.asString + "~>" + repl.asString + "}"


  /** apply this uniform renaming everywhere in an expression, resulting in an expression of the same kind. */
  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: Program => apply(p)
  }

  /** apply this uniform renaming everywhere in a term */
  def apply(t: Term): Term = try rename(t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }
    /*ensuring(r => StaticSemantics.symbols(t).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + t
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")*/

  /** apply this uniform renaming everywhere in a formula */
  def apply(f: Formula): Formula = try rename(f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }
   /*ensuring(r => StaticSemantics.symbols(f).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + f
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")*/

  /** apply this uniform renaming everywhere in a program */
  def apply(p: DifferentialProgram): DifferentialProgram = try renameODE(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /** apply this uniform renaming everywhere in a program */
  def apply(p: Program): Program = try rename(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
  /* ensuring(r => StaticSemantics.symbols(p).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + p
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")*/

  /**
   * Apply uniform renaming everywhere in the sequent.
   */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensuring contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch { case ex: ProverException => throw ex.inContext(s.toString) }

  // implementation

  /** Rename a variable (that occurs in the given context for error reporting purposes) */
  private def renameVar(x: Variable, context: Expression): Variable =
    if (x==what) repl
    else if (x==repl) if (TRANSPOSITION) what else throw new RenamingClashException("Replacement name " + repl.asString + " already occurs originally", this.toString, x.asString, context.prettyString)
    else x


  private def rename(term: Term): Term = term match {
    case x: Variable                      => renameVar(x, term)
    case DifferentialSymbol(x)            => DifferentialSymbol(renameVar(x, term))
    case n: Number                        => n
    case FuncOf(f:Function, theta)        => FuncOf(f, rename(theta))
    case Anything | Nothing | DotTerm     => term
    // homomorphic cases
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeTerm => f.reapply(rename(f.left), rename(f.right))
    case Neg(e)       => Neg(rename(e))
    case Plus(l, r)   => Plus(rename(l),   rename(r))
    case Minus(l, r)  => Minus(rename(l),  rename(r))
    case Times(l, r)  => Times(rename(l),  rename(r))
    case Divide(l, r) => Divide(rename(l), rename(r))
    case Power(l, r)  => Power(rename(l),  rename(r))
    case Differential(e) =>  Differential(rename(e))
    // unofficial
    case Pair(l, r)   => Pair(rename(l),   rename(r))
  }

  private def rename(formula: Formula): Formula = formula match {
    case PredOf(p, theta)   => PredOf(p, rename(theta))
    case PredicationalOf(c, fml) => throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case DotFormula         => if (semanticRenaming) DotFormula else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case True | False       => formula

    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeFormula => f.reapply(rename(f.left), rename(f.right))

    // pseudo-homomorphic base cases
    case Equal(l, r)        => Equal(rename(l),        rename(r))
    case NotEqual(l, r)     => NotEqual(rename(l),     rename(r))
    case GreaterEqual(l, r) => GreaterEqual(rename(l), rename(r))
    case Greater(l, r)      => Greater(rename(l),      rename(r))
    case LessEqual(l, r)    => LessEqual(rename(l),    rename(r))
    case Less(l, r)         => Less(rename(l),         rename(r))

    // homomorphic cases
    case Not(g)      => Not(rename(g))
    case And(l, r)   => And(rename(l),   rename(r))
    case Or(l, r)    => Or(rename(l),    rename(r))
    case Imply(l, r) => Imply(rename(l), rename(r))
    case Equiv(l, r) => Equiv(rename(l), rename(r))

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => DifferentialFormula(rename(g))

    case Forall(vars, g) => Forall(vars.map(x => renameVar(x,formula)), rename(g))
    case Exists(vars, g) => Exists(vars.map(x => renameVar(x,formula)), rename(g))

    case Box(p, g)       => Box(rename(p), rename(g))
    case Diamond(p, g)   => Diamond(rename(p), rename(g))
  }

  private def rename(program: Program): Program = program match {
    case a: ProgramConst             => if (semanticRenaming) a else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: ProgramConstant " + a, this.toString, program.toString)
    case Assign(x, e)                => Assign(renameVar(x,program), rename(e))
    case DiffAssign(DifferentialSymbol(x), e) => DiffAssign(DifferentialSymbol(renameVar(x,program)), rename(e))
    case AssignAny(x)                => AssignAny(renameVar(x,program))
    case Test(f)                     => Test(rename(f))
    case ODESystem(a, h)             => ODESystem(renameODE(a), rename(h))
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case ode: DifferentialProgram    => renameODE(ode)
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeProgram => f.reapply(rename(f.left), rename(f.right))
    case Choice(a, b)                => Choice(rename(a), rename(b))
    case Compose(a, b)               => Compose(rename(a), rename(b))
    case Loop(a)                     => Loop(rename(a))
    case Dual(a)                     => Dual(rename(a))
  }

  private def renameODE(ode: DifferentialProgram): DifferentialProgram = ode match {
    case AtomicODE(DifferentialSymbol(x), e) => AtomicODE(DifferentialSymbol(renameVar(x,ode)), rename(e))
    case c: DifferentialProgramConst => if (semanticRenaming) c else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: DifferentialProgramConstant " + c, this.toString, ode.toString)      // homomorphic cases
    case DifferentialProduct(a, b)   => DifferentialProduct(renameODE(a), renameODE(b))
  }
}