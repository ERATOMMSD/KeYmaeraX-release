package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TimeStretch
import edu.cmu.cs.ls.keymaerax.core.{And, Assign, AtomicODE, Box, DifferentialProduct, DifferentialSymbol, Except, ODESystem, PrettyPrinter, Real, Rule, SeqPos, Sequent, SuccPos, Test, UnitPredicational, Variable}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.immutable.{IndexedSeq, List}

/**
  * Created by Juraj Kolcak on 24/06/19.
  */
class RelationalTests extends FlatSpec with Matchers {
  val listener = new IOListener() {
    override def begin(input: BelleValue, expr: BelleExpr) : Unit = {
      println(expr.getClass)
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, BelleThrowable]): Unit= {
    }
    override def kill():Unit = ()

  }

  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)

  def testRule(rule: Rule, in: Sequent, out: List[Sequent]) {
    println("\tCheck " + rule)
    val pn = ProvableSig.startProof(in)
    val resList = pn.apply(rule, 0).subgoals
    println("\tResult\t" + resList)
    println("\tExpected\t" + out)
    if (resList != out) println("Unexpected")
    resList.length should be (out.length)
    val res = resList
    for((s,t) <- res zip out) {
      s.ante.length should be (t.ante.length)
      for((f,g) <- s.ante zip t.ante)
        f should be (g)

      s.succ.length should be (t.succ.length)
      for((f,g) <- s.succ zip t.succ)
        f should be (g)
    }
  }

  def testRule(rule: Rule, in: Sequent) = ProvableSig.startProof(in).apply(rule, 0).subgoals

  val pos = SeqPos(1).asInstanceOf[SuccPos]

  "Time Stretch Rule" should "Successfully merge dynamics for a toy example" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?x<8&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}]1/2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&x<8&true}]x+y>0".asFormula))
    )

    testRule(TimeStretch(pos), sequent, result)
  }

  it should "Successfully merge dynamics for a toy example with inverse exit condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&true}{y'=2&2*y>=2}?y=x;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?true&2*y>=2;}]y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&true}{y'=2&2*y>=2}]1/2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&true&2*y>=2}]x+y>0".asFormula))
    )

    testRule(TimeStretch(pos), sequent, result)
  }

  it should "Successfully merge dynamics for the linear acceleration example" in {
    val antecedent = IndexedSeq("x=0&y=0&v>0&w=v&A()>0&B()>A()".asFormula)
    val sequent = Sequent(antecedent,
      IndexedSeq("[{x'=v,v'=A()&true}{y'=w,w'=B()&true}?x=y;]v<=w".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?true&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=A()&true}{y'=w,w'=B()&true}]v/w>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=A(),y'=w*(v/w),w'=B()*(v/w)&true&true}]v<=w".asFormula))
    )

    testRule(TimeStretch(pos), sequent, result)
  }

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val v = Variable("v", None, Real)
  val w = Variable("w", None, Real)
  val q = UnitPredicational("q",Except(y))
  val p = UnitPredicational("p",Except(x))
  val c = ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),"v".asTerm),
    AtomicODE(DifferentialSymbol(v), "a".asTerm)), q)
  val d = ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), "w".asTerm),
    AtomicODE(DifferentialSymbol(w), "b".asTerm)), p)
  val ante = IndexedSeq("x=y".asFormula)
  val s = Sequent(ante, IndexedSeq(Box(c, Box(d, Box(Test("x=y".asFormula), "v <= w".asFormula)))))

  it should "complain about being applied to formulas of the wrong shape" in {
    val singleDynamics = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(Test("x=y".asFormula), "v <= w".asFormula))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), singleDynamics)

    val threeDynamics = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(c, Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), threeDynamics)

    val noExitCondition = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, "v <= w".asFormula))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), noExitCondition)

    val notEqualityExitCondition = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Test("x<y".asFormula), "v <= w".asFormula)))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), notEqualityExitCondition)

    val propositionalPrefix = Sequent(IndexedSeq(), IndexedSeq(And("x=y".asFormula,
      Box(c, Box(d, Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), propositionalPrefix)

    val discretePrefix = Sequent(IndexedSeq(), IndexedSeq(Box(Assign(x, "y".asTerm),
      Box(c, Box(d, Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), discretePrefix)

    val propositionalInfixDynamics = Sequent(IndexedSeq(), IndexedSeq(Box(c, And("x=y".asFormula,
      Box(d, Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), propositionalInfixDynamics)

    val discreteInfixDynamics = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(Test("x=y".asFormula),
      Box(d, Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), discreteInfixDynamics)

    val propositionalInfixTest = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, And("x=y".asFormula,
      Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), propositionalInfixTest)

    val discreteInfixTest = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Assign(x, "y".asTerm),
      Box(Test("x=y".asFormula), "v <= w".asFormula))))))
    an [MatchError] should be thrownBy testRule(TimeStretch(pos), discreteInfixTest)
  }

  it should "complain about variable mish-mash in dynamics and exit condition" in {
    //The first two are temporary - we do not compute derivatives with chain rule so we use a simplified TS rule for single variable exit conditions.
    val complexExitCondition = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Test("v*x=y".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), complexExitCondition)

    val complexExitCondition2 = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Test("x=y-2".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), complexExitCondition2)

    val nonRelationalExitCondition = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Test("x=3".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), nonRelationalExitCondition)

    val mixedExitCondition = Sequent(IndexedSeq(), IndexedSeq(Box(c, Box(d, Box(Test("x*y=w".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), mixedExitCondition)

    val overlappingDynamics = Sequent(IndexedSeq(), IndexedSeq(Box(c,
      Box(ODESystem(AtomicODE(DifferentialSymbol(x), "w".asTerm), p), Box(Test("x=y".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), overlappingDynamics)

    val overlappingDomains = Sequent(IndexedSeq(), IndexedSeq(Box(c,
      Box(ODESystem(AtomicODE(DifferentialSymbol(y), "w".asTerm), "y=x".asFormula), Box(Test("x=y".asFormula), "v <= w".asFormula)))))
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos), overlappingDomains)
  }

  it should "complain about being applied to non-existent position" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(TimeStretch(SeqPos(5).asInstanceOf[SuccPos]), s)
  }
}
