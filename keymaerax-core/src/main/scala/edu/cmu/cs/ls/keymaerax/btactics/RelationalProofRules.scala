package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable._

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
case class TimeStretch(pos: SuccPos) extends RightRule {
  val name: String = "TimeStretch"

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

  def apply(s: Sequent): immutable.List[Sequent] = {
    val (d, ds, q, qs, x, xs, b) = s(pos) match {
      case Box(ODESystem(d, q), Box(ODESystem(ds, qs), Box(Test(Equal(x, xs)), b))) => (d, ds, q, qs, x, xs, b)
      case Box(ODESystem(d, q), Box(Compose(ODESystem(ds, qs), Test(Equal(x, xs))), b)) => (d, ds, q, qs, x, xs, b)
      case Box(Compose(ODESystem(d, q), ODESystem(ds, qs)), Box(Test(Equal(x, xs)), b)) => (d, ds, q, qs, x, xs, b)
      case Box(Compose(ODESystem(d, q), Compose(ODESystem(ds, qs), Test(Equal(x, xs)))), b) => (d, ds, q, qs, x, xs, b)
      case Box(Compose(Compose(ODESystem(d, q), ODESystem(ds, qs)), Test(Equal(x, xs))), b) => (d, ds, q, qs, x, xs, b)
      case _ => throw new MatchError(s(pos))
    }

    require(x.isInstanceOf[Variable], "Time Stretch only handles single variable exit conditions.") //TEMP
    require(xs.isInstanceOf[Variable], "Time Stretch only handles single variable exit conditions.") //TEMP
    require((StaticSemantics.vars(d) ++ StaticSemantics.vars(q))
      .intersect(StaticSemantics.vars(ds) ++ StaticSemantics.vars(qs)).isEmpty, "Time Stretch requires disjoint dynamics.")

    val ode = decomposeODE(d)
    val odes = decomposeODE(ds)
    var matchingOrder = StaticSemantics.vars(x).subsetOf(StaticSemantics.boundVars(d)) &&
      StaticSemantics.vars(xs).subsetOf(StaticSemantics.boundVars(ds))

    val g = (if (matchingOrder) ode else odes).find(a => StaticSemantics.vars(x).subsetOf(StaticSemantics.boundVars(a))) match {
      case Some(AtomicODE(_, g_)) => g_
      case None => Number(0)
    }
    val gs = (if (matchingOrder) odes else ode).find(a => StaticSemantics.vars(xs).subsetOf(StaticSemantics.boundVars(a))) match {
      case Some(AtomicODE(_, gs_)) => gs_
      case None => Number(0)
    }

    val timeStretchFunction = if (matchingOrder) Divide(g, gs) else Divide(gs, g)

    immutable.List(s.updated(pos, Box(Test(And(q, qs)), Equal(x, xs))),
      s.updated(pos, Box(Compose(ODESystem(d,q), ODESystem(ds, qs)), Greater(timeStretchFunction, Number(0)))),
      s.updated(pos, Box(ODESystem(DifferentialProduct(d, composeODE(odes.map(a => {
        val AtomicODE(dt, t) = a
        AtomicODE(dt, Times(t, timeStretchFunction))
      }))), And(q, qs)), b)))
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
      case _ => throw new MatchError("The postcondition: " + p.toString + " does not match the required inequality with 0.")
    }

    immutable.List(s.updated(pos, Imply(q, p)),
      s.updated(pos, Box(ODESystem(d,And(q,p)), derivative)))
  }
}
