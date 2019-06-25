package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{DifferentialInductiveInvariant, TimeStretch}
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


  //Time Stretch
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

  it should "throw an exception when applied to a formula with single differential dynamics" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with three differential dynamics" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}{r'=2&r>8}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula without exit condition" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with exit condition which is not equality" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x<=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y&[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y|[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y->[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[x:=y;{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[?x=y;{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamics nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y&[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y|[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y->[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamcis nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][x:=y;{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][?x=y;{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][{{y'=w,w'=b&true}?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y&[?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y|[?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y->[?x=y;]v<=w)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}x:=y;?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}{?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to an exit condition which is not a relation" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=3;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?10=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to an exit condition which mixes variables from the two dynamics" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y*v;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?w+x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a differential (LHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b,x'=7&true}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a,y'=1&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a definition (RHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w+x,w'=b&true}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a*(y+1)&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a variable in evolution domain constraints" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&x<=y}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&2+y>3*v}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a position which does not exist" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(TimeStretch(SeqPos(5).asInstanceOf[SuccPos]),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }


  //Differential Inductive Invariant
  "Differential Inductive Invariant" should "perform successfully on a toy example with strict inequality" in {
    val antecedent = IndexedSeq("x<0&y<0".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=-1&true}]0>x+y".asFormula))
    val result = List[Sequent](
      Sequent(IndexedSeq("x<0&y<0".asFormula), IndexedSeq("true->0>x+y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=-1&true&0>x+y}]0>(x+y)'".asFormula))
    )

    testRule(DifferentialInductiveInvariant(pos), sequent, result)
  }

  it should "perform successfully on a toy example with non-strict inequality" in {
    val antecedent = IndexedSeq("x>=0".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&true}]x>=0".asFormula))
    val result = List[Sequent](
      Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("true->x>=0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&true&x>=0}](x)'>0".asFormula))
    )

    testRule(DifferentialInductiveInvariant(pos), sequent, result)
  }

  it should "throw an exception when applied to a formula without differential dynamics" in {
    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y->x>0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[x:=y;]x>0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[?x=y;]x>0".asFormula)))
  }

  it should "throw an exception when applied to a formula with differential dynamics nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=0&[{x'=v,v'=a&true}]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=0|[{x'=v,v'=a&true}]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("x=0->[{x'=v,v'=a&true}]x>=0".asFormula)))
  }

  it should "throw an exception when applied to a formula with differential dynamics nested in a hybrid program" in {
    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[x:=y;{x'=v,v'=a&true}]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[?x=y;{x'=v,v'=a&true}]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{{x'=v,v'=a&true}}*]x>=0".asFormula)))
  }

  it should "throw an exception when applied to a formula with postcondition which is not inequality" in {
    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}]x=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](y=0&x>=0)".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](y=0|x>=0)".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](y=0->x>=0)".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}?x=y;]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}x:=y;]x>=0".asFormula)))

    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=1&true}]x>=0".asFormula)))
  }

  it should "throw an exception when applied to a formula with inequality postcondition which does not compare against zero" in {
    an [MatchError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}]x>y".asFormula)))

    an [AssertionError] should be thrownBy testRule(DifferentialInductiveInvariant(pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}]x<=2".asFormula)))
  }

  it should "throw an exception when applied to a position which does not exist" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(DifferentialInductiveInvariant(SeqPos(5).asInstanceOf[SuccPos]),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}]x>=0".asFormula)))
  }
}
