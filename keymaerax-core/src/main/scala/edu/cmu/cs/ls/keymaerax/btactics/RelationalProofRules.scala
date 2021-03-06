package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
//import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3

import scala.collection.immutable
import scala.collection.immutable._

/**
  * Implements Proof Rules for Relational Reasoning.
  *
  * Created by Juraj Kolcak on 24/06/19.
  * @see [[https://arxiv.org/abs/1903.00153 Relational Differential Dynamic Logic]].
  */
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

  def computeTimeStretchFunction(mainODE : Program, sharpODE : Program, syncCond : Formula) : (Term, Program) = {
    require(StaticSemantics.boundVars(mainODE).intersect(StaticSemantics.vars(sharpODE)).isEmpty, "Time Stretch requires disjoint dynamics.")
    require(StaticSemantics.vars(mainODE).intersect(StaticSemantics.boundVars(sharpODE)).isEmpty, "Time Stretch requires disjoint dynamics.")

    val ODESystem(d, q) = mainODE
    val ODESystem(ds, qs) = sharpODE
    val Equal(g, gs) = syncCond

    require(StaticSemantics.vars(g).intersect(StaticSemantics.boundVars(mainODE)).isEmpty || StaticSemantics.vars(g).intersect(StaticSemantics.boundVars(sharpODE)).isEmpty, "Exit Condition does not allow mixing variables")
    require(StaticSemantics.vars(gs).intersect(StaticSemantics.boundVars(mainODE)).isEmpty || StaticSemantics.vars(gs).intersect(StaticSemantics.boundVars(sharpODE)).isEmpty, "Exit Condition does not allow mixing variables")

    val equations = decomposeODE(d)
    val sharpEquations = decomposeODE(ds)
    val matchingOrder = checkOrder(mainODE, sharpODE, syncCond)

    val dg = (if (matchingOrder) DifferentialHelper.lieDerivative(d,g) else DifferentialHelper.lieDerivative(ds,g))
    val dgs = (if (matchingOrder) DifferentialHelper.lieDerivative(ds,gs) else DifferentialHelper.lieDerivative(d,gs))

    val tsf = if (matchingOrder) Divide(dg, dgs) else Divide(dgs, dg)

    (tsf, ODESystem(DifferentialProduct(d, composeODE(sharpEquations.map(a => {
        val AtomicODE(dt, t) = a
        AtomicODE(dt, Times(t, tsf))
      }))), And(And(And(q, qs),Greater(dg,Number(0))),Greater(dgs,Number(0)))))
  }
}

/**
  * Generalised Synchronisation: Synchronise two normal programs along an equality relation.
  * {{{
  * G |- g=h, [a;b;?E]g=h, D(N(a),g), D(N(b),h)
  * -------------
  * G |- [a;b;?E]A <=> [N(a)*N(b);?E]A
  * }}}
  */
// gSync Generalised Synchronisation
case class GeneralisedSynchronisation(sync: Formula, pos: SuccPos) extends RelationalProofRule {
  val name: String = "GeneralisedSynchronisation"

  def parseProgram(program: Program): immutable.List[Program] = {
    program match {
      case Compose(prog1, prog2) => parseProgram(prog1) ++ parseProgram(prog2)
      case _ => immutable.List(program)
    }
  }

  def composeInstructionList(instructionList: immutable.List[Program]): Program = {
    if (instructionList.length <= 1) {
      instructionList.head
    }
    else if (instructionList.length == 2) {
      Compose(instructionList.head, instructionList.last)
    }
    else {
      Compose(instructionList.head, composeInstructionList(instructionList.tail))
    }
  }

  def parseFormula(formula: Formula): (Program, immutable.List[Program], Test, Formula) = {
    val (program, postcondition) = formula match {
      case Box(prog, pc) => (prog, pc)
      case _ => throw new MatchError("Generalised Synchronisation expects the formula to start with a box modality, but found: " + formula)
    }

    val instructionList = parseProgram(program)

    val exitCondition = instructionList.last match {
      case ec@Test(_) => ec
      case _ => throw new MatchError("Generalised Synchronisation expects the programs to end with an exit condition in the form of test, but found: " + instructionList.last)
    }

    if (instructionList.length - 1 < 2) {
      throw new MatchError("Generalised Synchronisation requires at least two hybrid programs in box modality, but found " + (instructionList.length - 1))
    }

    (program, instructionList.init, exitCondition, postcondition)
  }

  def inferBoundVariableSets(instructionList: immutable.List[Program]):
    (SetLattice[Variable], SetLattice[Variable], Term, Term) = {
    val (syncTop, syncBottom) = sync match {
      case Equal(left, right) => (left, right)
      case _ => throw new MatchError("Generalised Synchronisation expects synchronisation condition in the form of equality, but found: " + sync)
    }

    var topVariables: SetLattice[Variable] = null
    var bottomVariables: SetLattice[Variable] = null

    var newTopVariables = StaticSemantics.vars(syncTop)
    var newBottomVariables = StaticSemantics.vars(syncBottom)

    if (newTopVariables.isEmpty) {
      throw new MatchError("Generalised Synchronisation expects non-constant synchronisation condition, but found: " + syncTop)
    }
    if (newBottomVariables.isEmpty) {
      throw new MatchError("Generalised Synchronisation expects non-constant synchronisation condition, but found: " + syncBottom)
    }

    while (topVariables != newTopVariables || bottomVariables != newBottomVariables)
    {
      topVariables = newTopVariables
      bottomVariables = newBottomVariables

      instructionList.foreach(program => {
        if (!StaticSemantics.boundVars(program).intersect(topVariables).isEmpty) {
          newTopVariables = newTopVariables ++ StaticSemantics.boundVars(program)
        }

        if (!StaticSemantics.boundVars(program).intersect(bottomVariables).isEmpty) {
          newBottomVariables = newBottomVariables ++ StaticSemantics.boundVars(program)
        }
      })
    }

    (topVariables, bottomVariables, syncTop, syncBottom)
  }

  def constructMonotonicityFormula(programs: immutable.List[Program], sync: Term): Formula = {
    var monotonicityFormula: Formula = True

    programs.reverse.foreach {
      case dynamics@ODESystem(ode, _) => monotonicityFormula = Box(dynamics, And(Greater(DifferentialHelper.lieDerivative(ode,sync), Number(0)), monotonicityFormula))
//       match{
//         case Some(derivative) => monotonicityFormula = Box(dynamics, And(Greater(derivative, Number(0)), monotonicityFormula))
//         case None => return False
//       }
      case Choice(left, right) =>
        if (monotonicityFormula == True) {
          monotonicityFormula = And(constructMonotonicityFormula(parseProgram(left), sync),
            constructMonotonicityFormula(parseProgram(right), sync))
        }
        else {
          monotonicityFormula = And(constructMonotonicityFormula(parseProgram(left), sync),
            And(constructMonotonicityFormula(parseProgram(right), sync),
              Box(Choice(left, right), monotonicityFormula)))
        }
      case Test(cond) =>
        if (monotonicityFormula != True){
          monotonicityFormula = Imply(cond, monotonicityFormula)
        }
    }

    SimplifierV3.formulaSimp(monotonicityFormula,SimplifierV3.emptyCtx,SimplifierV3.defaultFaxs,SimplifierV3.defaultTaxs)._1
  }

  def synchronisePrograms(topPrograms: immutable.List[Program], bottomPrograms: immutable.List[Program]): Program = {
    (topPrograms.headOption, bottomPrograms.headOption) match {
      case (Some(test@Test(_)), _) =>
        val remainderSynchronisation = synchronisePrograms(topPrograms.tail, bottomPrograms)

        if (remainderSynchronisation == null) {
          test
        }
        else {
          Compose(test, remainderSynchronisation)
        }
      case (Some(Choice(left, right)), _) => Choice(
        synchronisePrograms(immutable.List[Program](left) ++ topPrograms.tail, bottomPrograms),
        synchronisePrograms(immutable.List[Program](right) ++ topPrograms.tail, bottomPrograms))
      case (_, Some(test@Test(_))) =>
        val remainderSynchronisation = synchronisePrograms(topPrograms, bottomPrograms.tail)

        if (remainderSynchronisation == null) {
          test
        }
        else {
          Compose(test, remainderSynchronisation)
        }
      case (_, Some(Choice(left, right))) => Choice(
        synchronisePrograms(topPrograms, immutable.List[Program](left) ++ bottomPrograms.tail),
        synchronisePrograms(topPrograms, immutable.List[Program](right) ++ bottomPrograms.tail))
      case (Some(ODESystem(_, constraint)), None) =>
        val remainderSynchronisation = synchronisePrograms(topPrograms.tail, bottomPrograms)

        if (remainderSynchronisation == null){
          Test(constraint)
        }
        else {
          Compose(Test(constraint), remainderSynchronisation)
        }
      case (None, Some(ODESystem(_, constraint))) =>
        val remainderSynchronisation = synchronisePrograms(topPrograms, bottomPrograms.tail)

        if (remainderSynchronisation == null) {
          Test(constraint)
        }
        else {
          Compose(Test(constraint), remainderSynchronisation)
        }
      case (Some(topDynamics@ODESystem(_, _)), Some(bottomDynamics@ODESystem(_, _))) => {
        val (_, synchronisedDynamics) = computeTimeStretchFunction(topDynamics, bottomDynamics, sync)

        if (topPrograms.length < 2) {
          if (bottomPrograms.length < 2) {
            synchronisedDynamics
          }
          else {
            Compose(synchronisedDynamics, synchronisePrograms(topPrograms, bottomPrograms.tail))
          }
        }
        else {
          if (bottomPrograms.length < 2) {
            Compose(synchronisedDynamics, synchronisePrograms(topPrograms.tail, bottomPrograms))
          }
          else {
            Choice(Compose(synchronisedDynamics, synchronisePrograms(topPrograms, bottomPrograms.tail)),
              Compose(synchronisedDynamics, synchronisePrograms(topPrograms.tail, bottomPrograms)))
          }
        }
      }
      case (None, None) => null
    }
  }

  def apply(s: Sequent): immutable.List[Sequent] = {
    //Parsing
    val (originalProgram, instructionList, exitCondition, postcondition) = parseFormula(s(pos))

    //Check For Assignments/Loops
    instructionList.foreach {
      case program@Assign(_, _) => throw new MatchError("Generalised Synchronisation expects no assignments in the program to be synchronised, but found: " + program)
      case program@Loop(_) => throw new MatchError("Generalised Synchronisation expects no loops in the program to be synchronised, but found: " + program)
      case _ =>
    }

    //Split Programs
    val (topVariables, bottomVariables, topSync, bottomSync) = inferBoundVariableSets(instructionList)

    val topPrograms = instructionList.filter(program => !StaticSemantics.vars(program).intersect(topVariables).isEmpty)
    val bottomPrograms = instructionList.filter(program => !StaticSemantics.vars(program).intersect(bottomVariables).isEmpty)
    val independentPrograms = instructionList.filter(program => StaticSemantics.vars(program).intersect(topVariables).isEmpty &&
      StaticSemantics.vars(program).intersect(bottomVariables).isEmpty)

    //Check program independence
    topPrograms.foreach(program =>
      require(StaticSemantics.vars(program).intersect(bottomVariables).isEmpty, "Generalised Synchronisation requires independent programs, but " +
        program + " depends on " + StaticSemantics.vars(program).intersect(bottomVariables)))
    bottomPrograms.foreach(program =>
      require(StaticSemantics.vars(program).intersect(topVariables).isEmpty, "Generalised Synchronisation requires independent programs, but " +
        program + " depends on " + StaticSemantics.vars(program).intersect(topVariables)))

    //Compute monotonicity formulae
    val topProgramMonotonicity = constructMonotonicityFormula(topPrograms, topSync)
    val bottomProgramMonotonicity = constructMonotonicityFormula(bottomPrograms, bottomSync)

    //Compute Actual Synchronisation
    val synchronisedProgram = synchronisePrograms(topPrograms, bottomPrograms)

    //Deal with independent programs
    val extendedExitCondition = if (independentPrograms.isEmpty) {
      exitCondition
    }
    else {
      Compose(composeInstructionList(independentPrograms), exitCondition)
    }

    immutable.List(s.updated(pos, sync),
      s.updated(pos, Box(originalProgram, sync)),
      s.updated(pos, topProgramMonotonicity),
      s.updated(pos, bottomProgramMonotonicity),
      s.updated(pos, Box(Compose(synchronisedProgram, extendedExitCondition), postcondition)))
  }
}

/**
  * Time Stretch: Synchronise two dynamics along a time stretch function.
  * {{{
  * G |- a=b, [D;E] a/b>0, [DE] c
  * -------------
  * G |- [D;E; ?a=b] c
  * }}}
  */
// TS Time Stretch
case class TimeStretch(sync: Formula, pos: SuccPos) extends RelationalProofRule {
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

    val (tsf, nd) = computeTimeStretchFunction(o, os, sync)
    val ODESystem(_,q1) = o
    val ODESystem(_,q2) = os
    val ODESystem(_, q) = nd
    val Divide(dg, dgs) = tsf

    immutable.List(s.updated(pos, Box(Test(And(q1,q2)), sync)),
      s.updated(pos, Box(Compose(Compose(o, os), Test(e)), sync)),
      s.updated(pos, Box(o, Greater(dg, Number(0)))),
      s.updated(pos, Box(os, Greater(dgs, Number(0)))),
      s.updated(pos, Box(Compose(nd, Test(e)), b)))
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

    val derivative = p match {
      case Greater(g, Number(z)) => Greater(DifferentialHelper.lieDerivative(d,g), zero).ensuring(z == 0)
      case Greater(Number(z), g) => Greater(zero, DifferentialHelper.lieDerivative(d,g)).ensuring(z == 0)
      case Less(g, Number(z)) => Less(DifferentialHelper.lieDerivative(d,g), zero).ensuring(z == 0)
      case Less(Number(z), g) => Less(zero, DifferentialHelper.lieDerivative(d,g)).ensuring(z == 0)
      case GreaterEqual(g, Number(z)) => Greater(DifferentialHelper.lieDerivative(d,g), zero).ensuring(z == 0)
      case GreaterEqual(Number(z), g) => Greater(zero, DifferentialHelper.lieDerivative(d,g)).ensuring(z == 0)
      case LessEqual(g, Number(z)) => Less(DifferentialHelper.lieDerivative(d,g), zero).ensuring(z == 0)
      case LessEqual(Number(z), g) => Less(zero, DifferentialHelper.lieDerivative(d,g)).ensuring(z == 0)
      case Equal(g, Number(z)) => Equal(DifferentialHelper.lieDerivative(d,g), zero).ensuring(z == 0)
      case Equal(Number(z), g) => Equal(zero, DifferentialHelper.lieDerivative(d,g)).ensuring(z == 0)
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

    val ts = TimeStretch(e, pos)
    val originalTS = ts.apply(s.updated(pos, Box(Compose(Compose(odea, odes), Test(e)), Box(Test(p), splitPoint))))
    originalTS.take(1) ++ originalTS.drop(2) ++ immutable.List(
      s.updated(pos, Box(odea, And(monoCond, Box(Compose(Test(p), odeb), monoCond)))),
      Sequent(IndexedSeq(And(e, And(p, splitPoint))), IndexedSeq(Box(Compose(odeb, Compose(odes, Test(e))), b))))
  }
}

/**
  * Monotonic Condition Swap: Swap the exit condition and postcondition of a relational formula, provided they are monotonic.
  * {{{
  * G |- [?Q&P]g(x)<=h(y), [x'=f(x)&Q]g'>0, [x'=f(x)&Q]j'>=0, [y'=e(y)&P]k'>=0, [x'=f(x)&Q;y'=e(y)&P;?j(x)=k(y)] g(x)>=h(y)
  * -------------
  * G |- [x'=f(x)&Q;y'=e(y)&P;?g(x)=h(y)] j(x)<=k(y)
  * }}}
  */
// MCS Monotonic Condition Swap
case class MonotonicConditionSwap(pos: SuccPos) extends RelationalProofRule {
  val name: String = "MonotonicConditionSwap"

  def apply(s: Sequent): immutable.List[Sequent] = {
    val (o, os, e, b) = s(pos) match {
      case Box(Compose(o_, Compose(os_, Test(e_))), b_) => (o_, os_, e_, b_)
      case Box(Compose(Compose(o_, os_), Test(e_)), b_) => (o_, os_, e_, b_)
      case Box(Compose(o_, os_), Box(Test(e_), b_)) => (o_, os_, e_, b_)
      case Box(o_, Box(Compose(os_, Test(e_)), b_)) => (o_, os_, e_, b_)
      case Box(o_, Box(os_, Box(Test(e_), b_))) => (o_, os_, e_, b_)
      case _ => throw new MatchError("Monotonic Condition Swap requires two parallel dynamics, but found: " + s(pos))
    }

    require(StaticSemantics.boundVars(o).intersect(StaticSemantics.vars(os)).isEmpty)
    require(StaticSemantics.vars(o).intersect(StaticSemantics.boundVars(os)).isEmpty)

    val exitConditionOrder = checkOrder(o, os, e)
    val Equal(g, h) = e
    val (j, k, postconditionOrder, greater) = b match {
      case GreaterEqual(j_, k_) => (j_, k_, checkOrder(o, os, Equal(j_, k_)), true)
      case LessEqual(j_, k_) => (j_, k_, checkOrder(o, os, Equal(j_, k_)), false)
      case _ => throw new MatchError("Monotonic Condition Swap requires inequality in postcondition but found: " + b)
    }

    require(StaticSemantics.boundVars(o).intersect(StaticSemantics.vars(if (exitConditionOrder) h else g)).isEmpty)
    require(StaticSemantics.boundVars(os).intersect(StaticSemantics.vars(if (exitConditionOrder) g else h)).isEmpty)
    require(StaticSemantics.boundVars(o).intersect(StaticSemantics.vars(if (postconditionOrder) k else j)).isEmpty)
    require(StaticSemantics.boundVars(os).intersect(StaticSemantics.vars(if (postconditionOrder) j else k)).isEmpty)

    val ODESystem(_, q) = o
    val ODESystem(_, qs) = os

    immutable.List(s.updated(pos, Box(Test(And(q, qs)), b)),
      s.updated(pos, Box(o, Greater(Differential(if (exitConditionOrder) g else h), Number(0)))),
      s.updated(pos, Box(o, GreaterEqual(Differential(if (postconditionOrder) j else k), Number(0)))),
      s.updated(pos, Box(os, GreaterEqual(Differential(if (postconditionOrder) k else j), Number(0)))),
      s.updated(pos, Box(Compose(Compose(o, os), Test(Equal(j, k))), if (greater ^ postconditionOrder) GreaterEqual(g, h) else LessEqual(g, h))))
  }
}

