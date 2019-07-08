package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable._


sealed abstract class RelationalProofRule() extends RightRule {

  def checkOrder(mainODE: Program, sharpODE: Program, exitCond: Formula) : Boolean = {
    val Equal(g, gs) = exitCond

    StaticSemantics.vars(g).intersect(StaticSemantics.boundVars(sharpODE)).isEmpty &&
      StaticSemantics.vars(gs).intersect(StaticSemantics.boundVars(mainODE)).isEmpty
  }

  def decomposeODE(ode: DifferentialProgram) : List[AtomicODE] = {
    ode match {
      case AtomicODE(d, t) => List[AtomicODE](AtomicODE(d, t))
      case DifferentialProduct(a, b) => decomposeODE(a) ++ decomposeODE(b)
    }
  }

  def composeODE(ode: List[AtomicODE]) : DifferentialProgram = {
    if (ode.size == 1) {
      ode.head
    }
    else {
      DifferentialProduct(ode.head, composeODE(ode.tail))
    }
  }

  def computeTimeStretchFunction(mainODE : Program, sharpODE : Program, exitCond : Formula) : (Term, Program) = {
    require(StaticSemantics.boundVars(mainODE).intersect(StaticSemantics.vars(sharpODE)).isEmpty, "Time Stretch requires disjoint dynamics.")
    require(StaticSemantics.vars(mainODE).intersect(StaticSemantics.boundVars(sharpODE)).isEmpty, "Time Stretch requires disjoint dynamics.")

    val ODESystem(d, q) = mainODE
    val ODESystem(ds, qs) = sharpODE
    val Equal(g, gs) = exitCond

    require(g.isInstanceOf[Variable], "Time Stretch only handles single variable exit conditions.") //TEMP
    require(gs.isInstanceOf[Variable], "Time Stretch only handles single variable exit conditions.") //TEMP

    val equations = decomposeODE(d)
    val sharpEquations = decomposeODE(ds)
    val matchingOrder = checkOrder(mainODE, sharpODE, exitCond)

    val dg = (if (matchingOrder) equations else sharpEquations)
      .find(a => StaticSemantics.vars(g).subsetOf(StaticSemantics.boundVars(a))) match {
      case Some(AtomicODE(_, dg_)) => dg_
      case None => Number(0)
    }
    val dgs = (if (matchingOrder) sharpEquations else equations)
      .find(a => StaticSemantics.vars(gs).subsetOf(StaticSemantics.boundVars(a))) match {
      case Some(AtomicODE(_, dgs_)) => dgs_
      case None => Number(0)
    }

    val tsf = if (matchingOrder) Divide(dg, dgs) else Divide(dgs, dg)

    (tsf, ODESystem(DifferentialProduct(d, composeODE(sharpEquations.map(a => {
        val AtomicODE(dt, t) = a
        AtomicODE(dt, Times(t, tsf))
      }))), And(q, qs)))
  }

}

/**
  * Implements Proof Rules for Relational Reasoning.
  *
  * Created by Juraj Kolcak on 24/06/19.
  * @see [[https://arxiv.org/abs/1903.00153 Relational Differential Dynamic Logic]].
  */

/**
  * Time Stretch: Synchronise two dynamics along a time stretch function.
  * {{{
  * G |- a=b, [D;E] a/b>0, [DE] c
  * -------------
  * G |- [D;E; ?a=b] c
  * }}}
  */
// TS Time Stretch
case class TimeStretch(pos: SuccPos) extends RelationalProofRule {
  val name: String = "TimeStretch"

  def apply(s: Sequent): immutable.List[Sequent] = {
    val (o, os, e, b) = s(pos) match {
      case Box(Compose(o_, Compose(os_, Test(e_))), b_) => (o_, os_, e_, b_)
      case Box(Compose(Compose(o_, os_), Test(e_)), b_) => (o_, os_, e_, b_)
      case Box(Compose(o_, os_), Box(Test(e_), b_)) => (o_, os_, e_, b_)
      case Box(o_, Box(Compose(os_, Test(e_)), b_)) => (o_, os_, e_, b_)
      case Box(o_, Box(os_, Box(Test(e_), b_))) => (o_, os_, e_, b_)
      case _ => throw new MatchError("Time stretch requires two parallel dynamics, but found: " + s(pos))
    }

    val (tsf, nd) = computeTimeStretchFunction(o, os, e)
    val ODESystem(_, q) = nd

    immutable.List(s.updated(pos, Box(Test(q), e)),
      s.updated(pos, Box(Compose(o, os), Greater(tsf, Number(0)))),
      s.updated(pos, Box(nd, b)))
  }
}

/**
  * Differential Inductive Invariant: invariant reasoning on first (n) derivatives.
  * {{{
  * G,Q |- p>=0, G |- [x'=f(x)&Q&p>=0] p'>0
  * -------------
  * G |- [x'=f(x)&Q] p>=0
  * }}}
  */
// DII Differential Inductive Invariant
case class DifferentialInductiveInvariant(pos: SuccPos) extends RightRule {
  val name: String = "DifferentialInductiveInvariant"

  def apply(s: Sequent): immutable.List[Sequent] = {
    val Box(ODESystem(d, q), p) = s(pos)

    val zero = Number(0)
    //For now, we only use first order derivative, i.e. DII_1
    val derivative = p match {
      case Greater(g, Number(z)) => Greater(Differential(g), zero).ensuring(z == 0)
      case Greater(Number(z), g) => Greater(zero, Differential(g)).ensuring(z == 0)
      case Less(g, Number(z)) => Less(Differential(g), zero).ensuring(z == 0)
      case Less(Number(z), g) => Less(zero, Differential(g)).ensuring(z == 0)
      case GreaterEqual(g, Number(z)) => Greater(Differential(g), zero).ensuring(z == 0)
      case GreaterEqual(Number(z), g) => Greater(zero, Differential(g)).ensuring(z == 0)
      case LessEqual(g, Number(z)) => Less(Differential(g), zero).ensuring(z == 0)
      case LessEqual(Number(z), g) => Less(zero, Differential(g)).ensuring(z == 0)
      case Equal(g, Number(z)) => Equal(Differential(g), zero).ensuring(z == 0)
      case Equal(Number(z), g) => Equal(zero, Differential(g)).ensuring(z == 0)
      case _ => throw new MatchError("The postcondition: " + p.toString + " does not match the required comparison with 0.")
    }

    immutable.List(s.updated(pos, Imply(q, p)),
      s.updated(pos, Box(ODESystem(d,And(q,p)), derivative)))
  }
}

/**
  * Partial Time Stretch: Split and dynamics and synchronise with first part of the second dynamics along a custom time stretch function
  * {{{
  * G |- [?Q&R]g(x)=h(y), [{x'=f(x)&Q}{y'=d(y)&R}]g'/h'>0, [x'=f(x),y'=d(y)&Q&R;?B(x)]C(y), [x'=f(x)&Q]g'>=0&[?B(x);x'=e(x)&P]g'>=0
  * G(\x,\y),g(x)=h(y),B(x),C(y) |- [x'=e(x)&P;y'=d(y)&R;?g(x)=h(y)] A
  * -------------
  * G |- [x'=f(x)&Q;?B(x);x'=e(x)&P;y'=d(y)&R;?g(x)=h(y)] A
  * }}}
  */
// PTS Partial Time Stretch
case class PartialTimeStretch(splitPoint: Formula, pos: SuccPos) extends RelationalProofRule {
  val name: String = "PartialTimeStretch"

  def parseExitCondition(program: Program, post: Formula) : (Program, Formula, Formula) = {
    program match {
      case Compose(Compose(left, right), Test(e)) => (Compose(left, right), e, post) //The Compose is technical - we need it to not mistake Test(p) for Test(e)
      case Compose(left, Compose(right, Test(e))) => (Compose(left, right), e, post)
      case Compose(left, Compose(center, Compose(right, Test(e)))) => (Compose(left, Compose(center, right)), e, post)
      case Compose(odea, Compose(p, Compose(odeb, Compose(odes, Test(e))))) => (Compose(odea, Compose(p, Compose(odeb, odes))), e, post)
      case _ =>
        val Box(program_, post_) = post
        parseExitCondition(Compose(program, program_), post_)
    }
  }

  def parseDynamics(program: Program) : (Program, Program, Program, Formula) = {
    program match {
      case Compose(Compose(Compose(odea, Test(p)), odeb), odes) => (odea, odeb, odes, p)
      case Compose(Compose(odea, Compose(Test(p), odeb)), odes) => (odea, odeb, odes, p)
      case Compose(odea, Compose(Compose(Test(p), odeb), odes)) => (odea, odeb, odes, p)
      case Compose(odea, Compose(Test(p), Compose(odeb, odes))) => (odea, odeb, odes, p)
      case Compose(Compose(odea, Test(p)), Compose(odeb, odes)) => (odea, odeb, odes, p)
      case _ => throw new MatchError("Partial Time Stretch expects differential dynamics with a split point followed by a parallel differential dynamics, but found: " + program)
    }
  }

  def parse(f: Formula) : (Program, Program, Program, Formula, Formula, Formula) = {
    val Box(program, post) = f

    val (dynamics, e, b) = parseExitCondition(program, post)
    val (odea, odeb, odes, p) = parseDynamics(dynamics)

    (odea, odeb, odes, p, e, b)
  }

  def apply(s: Sequent): immutable.List[Sequent] = {
    val (odea, odeb, odes, p, e, b) = parse(s(pos))

    require(StaticSemantics.boundVars(odea).intersect(StaticSemantics.vars(odes)).isEmpty)
    require(StaticSemantics.vars(odea).intersect(StaticSemantics.boundVars(odes)).isEmpty)
    require(StaticSemantics.boundVars(odeb).intersect(StaticSemantics.vars(odes)).isEmpty)
    require(StaticSemantics.vars(odeb).intersect(StaticSemantics.boundVars(odes)).isEmpty)
    require(StaticSemantics.vars(p).intersect(StaticSemantics.boundVars(odes)).isEmpty)

    val Equal(g, gs) = e
    val monoCond = GreaterEqual(Differential(if (checkOrder(odea, odes, e)) g else gs), Number(0))

    val ts = TimeStretch(pos)
    ts.apply(s.updated(pos, Box(Compose(Compose(odea, odes), Test(e)), Box(Test(p), splitPoint)))) ++
    immutable.List(
      s.updated(pos, Box(odea, And(monoCond, Box(Compose(Test(p), odeb), monoCond)))),
      Sequent(IndexedSeq(And(e, And(p, splitPoint))), IndexedSeq(Box(Compose(odeb, Compose(odes, Test(e))), b))))
  }
}

