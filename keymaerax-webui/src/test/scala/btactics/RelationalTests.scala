package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{DifferentialInductiveInvariant, GeneralisedSynchronisation, PartialTimeStretch, TacticTestBase, TimeStretch}
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter, Rule, SeqPos, Sequent, SuccPos}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.immutable.{IndexedSeq, List}

/**
  * Created by Juraj Kolcak on 24/06/19.
  */
class RelationalTests extends TacticTestBase with Matchers {
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


  //Generalised Synchronisation
  "Generalised Synchronisation Rule" should "Successfully merge two normal programs with only dynamics" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((x<8&true) & 1>0) & 2>0}?x=y;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge two normal programs with tests and dynamics" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}?x>5;{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}?x>5;{y'=2&true}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1,y'=2*(1/2)&((x<8&true) & 1>0) & 2>0}?x>5;?true;}?x=y;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge two normal programs with nondeterministic choices and dynamics" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{{y'=2&true} ++ {y'=A()&y<3}}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{{y'=2&true} ++ {y'=A()&y<3}}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0 & [{y'=A()&y<3}]A()>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1,y'=2*(1/2)&((x<8&true) & 1>0) & 2>0} ++ {x'=1,y'=A()*(1/A())&((x<8&y<3) & 1>0) & A()>0}}?x=y;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in a toy example with switched sync condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2,x'=1*(2/1)&((true & x<8) & 2>0) & 1>0}?x=y;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("y=x".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in a toy example with box in postcondition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;][x:=y+4;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((x<8&true) & 1>0) & 2>0}?x=y;][x:=y+4;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics with extra programs and include them with the exit condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{z'=A()&true}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{z'=A()&true}{y'=2&true}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((x<8&true) & 1>0) & 2>0}{z'=A()&true}?x=y;]x+y>0".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in abstraction example" in {
    val antecedent = IndexedSeq("A()>0&V()>0&x=0&y=0&0<v&v=w".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}?v=V();{x'=v,v'=(A()*V())/v&true}{y'=w,w'=A()&true}?x=y;]v<=w".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}?v=V();{x'=v,v'=(A()*V())/v&true}{y'=w,w'=A()&true}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}](v>0 & (v=V() -> [{x'=v,v'=(A()*V())/v&true}]v>0))".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=w,w'=A()&true}]w>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=v,v'=a,y'=w*(v/w),w'=A()*(v/w)&((v<=V()&true) & v>0) & w>0}?v=V();{x'=v,v'=(A()*V())/v,y'=w*(v/w),w'=A()*(v/w)&((true&true) &v>0)& w>0}}?x=y;]v<=w".asFormula))
    )

    testRule(GeneralisedSynchronisation("x=y".asFormula, pos), sequent, result)
  }

  it should "throw an exception when applied to a formula without programs to synchronise" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula without exit condition" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;{z'=u,u'=c&true}]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y&[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y|[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y->[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with assignments in the hybrid program" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}x:=8;{y'=2&true}?x=y;]x+y>0".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}y:=8;?x=y;]x+y>0".asFormula)))
  }

  it should "throw an exception when applied to a formula with loops in the hybrid program" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{{y'=2&true}}*?x=y;]x+y>0".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{{x'=1&x<8}{y'=2&true}}*?x=y;]x+y>0".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}](x=y&[?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}](x=y|[?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}](x=y->[?x=y;]x<=y)".asFormula)))
  }

  it should "throw an exception when the synchronisation condition is not a relation" in {
    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("x=8".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(GeneralisedSynchronisation("0=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when the synchronisation condition mixes variables from the two hybrid programs" in {
    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("x=y*v".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("w-x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to two hybrid programs sharing a bound variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&true}{y'=v,v'=b&true}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=w,w'=a&true}{y'=w,w'=b&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to two hybrid programs sharing a variable bound in only one of them" in {
    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&true}{y'=v&true}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a*y&true}{y'=w,w'=b&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a position which does not exist" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(GeneralisedSynchronisation("x=y".asFormula, SeqPos(5).asInstanceOf[SuccPos]),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula)))
  }

  //Time Stretch
  "Time Stretch Rule" should "Successfully merge dynamics for a toy example" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?x<8&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1&x<8}{y'=2&true}}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&(((x<8&true)&1>0)&2>0)}?x=y;]x+y>0".asFormula))
    )

    testRule(TimeStretch("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge dynamics for a toy example with inverse sync condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&true}{y'=2&2*y>=2}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?true&2*y>=2;}]y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1&true}{y'=2&2*y>=2}}?x=y;]y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&true}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&2*y>=2}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((true&2*y>=2)&2>0)&1>0}?x=y;]x+y>0".asFormula))
    )

    testRule(TimeStretch("y=x".asFormula, pos), sequent, result)
  }

  it should "Successfully merge dynamics for a toy example with box in postcondition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;][x:=y*2;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?x<8&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1&x<8}{y'=2&true}}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((x<8&true)&1>0)&2>0}?x=y;][x:=y*2;]x+y>0".asFormula))
    )

    testRule(TimeStretch("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge dynamics for a toy example with sync condition different from exit condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x*y>=8;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?x<8&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1&x<8}{y'=2&true}}?x*y>=8;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]2>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/2)&((x<8&true)&1>0)&2>0}?x*y>=8;]x+y>0".asFormula))
    )

    testRule(TimeStretch("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge dynamics for the linear acceleration example" in {
    val antecedent = IndexedSeq("x=0&y=0&v>0&w=v&A()>0&B()>A()".asFormula)
    val sequent = Sequent(antecedent,
      IndexedSeq("[{x'=v,v'=A()&true}{y'=w,w'=B()&true}?x=y;]v<=w".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?true&true;}]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=v,v'=A()&true}{y'=w,w'=B()&true}}?x=y;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=A()&true}]v>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=w,w'=B()&true}]w>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=A(),y'=w*(v/w),w'=B()*(v/w)&((true&true)&v>0)&w>0}?x=y;]v<=w".asFormula))
    )

    testRule(TimeStretch("x=y".asFormula, pos), sequent, result)
  }

  it should "Successfully merge dynamics even when synchronisation condition is not a relation" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&x<8}{y'=2&true}?x=y;]x+y>0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[{?x<8&true;}]x=3".asFormula)),
      Sequent(antecedent, IndexedSeq("[{{x'=1&x<8}{y'=2&true}}?x=y;]x=3".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&x<8}]1>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=2&true}]0>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1,y'=2*(1/0)&(((x<8&true)&1>0)&0>0)}?x=y;]x+y>0".asFormula))
    )

    testRule(TimeStretch("x=3".asFormula, pos), sequent, result)
  }

  it should "throw an exception when applied to a formula with single differential dynamics" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with three differential dynamics" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}{r'=2&r>8}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula without exit condition" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y&[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y|[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("x=y->[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[x:=y;{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[?x=y;{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamics nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y&[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y|[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}](x=y->[{y'=w,w'=b&true}?x=y;]v<=w)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamcis nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][x:=y;{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][?x=y;{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}][{{y'=w,w'=b&true}?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y&[?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y|[?x=y;]v<=w)".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}](x=y->[?x=y;]v<=w)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}x:=y;?x=y;]v<=w".asFormula)))

    an [MatchError] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}{?x=y;}*]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a formula with sync condition which is not equality" in {
    an [MatchError] should be thrownBy testRule(TimeStretch("x<=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a sync condition which mixes variables from the two dynamics" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y*v".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("w+x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a differential (LHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b,x'=7&true}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a,y'=1&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a definition (RHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w+x,w'=b&true}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a*(y+1)&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a variable in evolution domain constraints" in {
    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&x<=y}?x=y;]v<=w".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(TimeStretch("x=y".asFormula, pos),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&2+y>3*v}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }

  it should "throw an exception when applied to a position which does not exist" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(TimeStretch("x=y".asFormula, SeqPos(5).asInstanceOf[SuccPos]),
      Sequent(IndexedSeq(), IndexedSeq("[{x'=v,v'=a&true}{y'=w,w'=b&true}?x=y;]v<=w".asFormula)))
  }


  //Differential Inductive Invariant
  "Differential Inductive Invariant" should "perform successfully on a toy example with strict inequality" in {
    val antecedent = IndexedSeq("x<0&y<0".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=-1&true}]0>x+y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("true->0>x+y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=-1&true&0>x+y}]0>-1+y'".asFormula))
    )

    testRule(DifferentialInductiveInvariant(pos), sequent, result)
  }

  it should "perform successfully on a toy example with non-strict inequality" in {
    val antecedent = IndexedSeq("x>=0".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=1&true}]x>=0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("true->x>=0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=1&true&x>=0}]1>0".asFormula))
    )

    testRule(DifferentialInductiveInvariant(pos), sequent, result)
  }

  it should "perform successfully on a toy example with equality" in {
    val antecedent = IndexedSeq("x=0".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=0&true}]x=0".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("true->x=0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=0&true&x=0}]0=0".asFormula))
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

  it should "throw an exception when applied to a formula with postcondition which is not comparison" in {
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


  //Partial Time Stretch
  "Partial Time Stretch" should "successfully merge dynamics in a toy example" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?x<=X()&true;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]a>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=3&true}]3>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a,y'=3*(a/3)&((x<=X()&true) & a>0) & 3>0}?x=y;][?x=X();]y=X()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]((x)'>=0&[?x=X();{x'=a-4&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("x=y&x=X()&y=X()".asFormula), IndexedSeq("[{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula))
    )

    testRule(PartialTimeStretch("y=X()".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in a toy example with switched sync condition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?y=x;]x<=y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?x<=X()&true;]y=x".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]a>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=3&true}]3>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a,y'=3*(a/3)&((x<=X()&true) & 3>0) & a>0}?y=x;][?x=X();]y=X()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]((x)'>=0&[?x=X();{x'=a-4&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("y=x&x=X()&y=X()".asFormula), IndexedSeq("[{x'=a-4&true}{y'=3&true}?y=x;]x<=y".asFormula))
    )

    testRule(PartialTimeStretch("y=X()".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in a toy example with box in postcondition" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;][x:=y-5;]x<=y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?x<=X()&true;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]a>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=3&true}]3>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a,y'=3*(a/3)&((x<=X()&true) & a>0) & 3>0}?x=y;][?x=X();]y=X()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]((x)'>=0&[?x=X();{x'=a-4&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("x=y&x=X()&y=X()".asFormula), IndexedSeq("[{x'=a-4&true}{y'=3&true}?x=y;][x:=y-5;]x<=y".asFormula))
    )

    testRule(PartialTimeStretch("y=X()".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in a toy example given as nested modalities" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}][?x=X();][{x'=a-4&true}][{y'=3&true}][?x=y;][x:=y-5;]x<=y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?x<=X()&true;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]a>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=3&true}]3>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a,y'=3*(a/3)&((x<=X()&true) & a>0) & 3>0}?x=y;][?x=X();]y=X()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]((x)'>=0&[?x=X();{x'=a-4&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("x=y&x=X()&y=X()".asFormula), IndexedSeq("[{x'=a-4&true}{y'=3&true}?x=y;][x:=y-5;]x<=y".asFormula))
    )

    testRule(PartialTimeStretch("y=X()".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics in abstraction example" in {
    val antecedent = IndexedSeq("A()>0&V()>0&x=0&y=0&0<v&v=w".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}?v=V();{x'=v,v'=(A()*V())/v&true}{y'=w,w'=A()&true}?x=y;]v<=w".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?v<=V()&true;]x=y".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}]v>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=w,w'=A()&true}]w>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=a,y'=w*(v/w),w'=A()*(v/w)&((v<=V()&true) & v>0) & w>0}?x=y;][?v=V();]w=V()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=v,v'=a&v<=V()}]((x)'>=0&[?v=V();{x'=v,v'=(A()*V())/v&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("x=y&v=V()&w=V()".asFormula), IndexedSeq("[{x'=v,v'=(A()*V())/v&true}{y'=w,w'=A()&true}?x=y;]v<=w".asFormula))
    )

    testRule(PartialTimeStretch("w=V()".asFormula, pos), sequent, result)
  }

  it should "successfully merge dynamics even when synchronisation condition is not relation" in {
    val antecedent = IndexedSeq("x=y".asFormula)
    val sequent = Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=0;]x<=y".asFormula))
    val result = List[Sequent](
      Sequent(antecedent, IndexedSeq("[?x<=X()&true;]x=0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]a>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{y'=3&true}]0>0".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a,y'=3*(a/0)&((x<=X()&true) & a>0) & 0>0}?x=0;][?x=X();]y=X()".asFormula)),
      Sequent(antecedent, IndexedSeq("[{x'=a&x<=X()}]((x)'>=0&[?x=X();{x'=a-4&true}](x)'>=0)".asFormula)),
      Sequent(IndexedSeq("x=0&x=X()&y=X()".asFormula), IndexedSeq("[{x'=a-4&true}{y'=3&true}?x=0;]x<=y".asFormula))
    )

    testRule(PartialTimeStretch("y=X()".asFormula, pos), sequent, result)
  }

  it should "throw an exception when applied to a formula with single split differential dynamics" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with single differential dynamics" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with three differential dynamics" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}{z'=a&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula without split dynamics" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with two split differential dynamics" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?y'=Y();{y'=a&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula without exit condition" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with exit condition which is not equality" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x>0;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with differential dynamics in the wrong order" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{y'=3&true}{x'=a-4&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}{y'=3&true}?x=X();{x'=a-4&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{y'=3&true}{x'=a&x<=X()}?x=X();{x'=a-4&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("x=y&[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("x=y|[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("x=y->[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[x:=y;{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[?x=y;{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;}*]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamics nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}](x=y&[{y'=3&true}?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}](x=y|[{y'=3&true}?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}](x=y->[{y'=3&true}?x=y;]x<=y)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the second dynamcis nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}x:=y;{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}?x=y;{y'=3&true}?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{{y'=3&true}?x=y;}*]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a propositional formula" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}](x=y&[?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}](x=y|[?x=y;]x<=y)".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}](x=y->[?x=y;]x<=y)".asFormula)))
  }

  it should "throw an exception when applied to a formula with the exit condition nested in a discrete program" in {
    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}x:=y;?x=y;]x<=y".asFormula)))

    an [MatchError] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}{?x=y;}*]x<=y".asFormula)))
  }

  it should "throw an exception when applied to an exit condition which mixes variables from the two dynamics" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&x<=X()}?x=X();{x'=a-4&true}{y'=w,w'=a&true}?x=y*v;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=v,v'=a&x<=X()}?x=X();{x'=a-4&true}{y'=w,w'=a&true}?w+x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a differential (LHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3,x'=a-2&true}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4,y'=12&true}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a definition (RHS) variable" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=x&true}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-y&true}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to two differential dynamics sharing a variable in evolution domain constraints" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&y<=x}?x=y;]x<=y".asFormula)))

    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&x+12>y*3}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to dynamics with split using variable from the second dynamics" in {
    an [IllegalArgumentException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, pos),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X()+y;{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))
  }

  it should "throw an exception when applied to a position which does not exist" in {
    an [IndexOutOfBoundsException] should be thrownBy testRule(PartialTimeStretch("y=X()".asFormula, SeqPos(5).asInstanceOf[SuccPos]),
      Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=a&x<=X()}?x=X();{x'=a-4&true}{y'=3&true}?x=y;]x<=y".asFormula)))
  }
}
