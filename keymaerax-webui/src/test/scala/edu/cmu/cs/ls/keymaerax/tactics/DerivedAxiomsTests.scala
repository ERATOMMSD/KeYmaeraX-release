/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.tactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, CheckinTest}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags.{OptimisticTest, CheckinTest}
import testHelper.KeYmaeraXTestTags
import edu.cmu.cs.ls.keymaerax.tags.ObsoleteTest

import scala.collection.immutable._

/**
 * Tests provability of the derived axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 * @todo add a reflection-based test at the end that checks all lazy val in DerivedAxioms, even if that does not fail separately it gives exhaustiveness.
 */
/*@CheckinTest*/
/*@SummaryTest*/
@ObsoleteTest
class DerivedAxiomsTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    if(!(new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "lemmadb")).exists()) {
      DerivedAxioms.prepopulateDerivedLemmaDatabase()
    }
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }


  private def check(lemma: Lemma): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact.isProved shouldBe true
    useToClose(lemma)
    lemma.fact.conclusion
  }

  private def useToClose(lemma: Lemma): Unit = {
    val rootNode = Provable.startProof(lemma.fact.conclusion)
    rootNode(lemma.fact, 0).isProved shouldBe true
  }

  private def check(lem: Any /*lem: ApplyRule[LookupLemma]*/): Sequent = ??? /*{
    val lemma = lem.rule.lemma
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact.isProved shouldBe true
    useToClose(lem)
    lemma.fact.conclusion
  }*/

  private def useToClose(lem: Any /*lem: ApplyRule[LookupLemma]*/): Unit = ??? /*{
    val rootNode = new RootNode(lem.rule.lemma.fact.conclusion)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(lem, rootNode))
    rootNode.isClosed() shouldBe true
    rootNode.isProved() shouldBe true
  }*/

  "The DerivedAxioms prepopulation procedure" should "not crash" /*taggedAs(KeYmaeraXTestTags.CheckinTest)*/ in {
    LemmaDBFactory.lemmaDB.deleteDatabase() //necessary. Perhaps we should add optional copy-and-recover.
    DerivedAxioms.prepopulateDerivedLemmaDatabase()
  }


  "Derived Axioms" should "prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "prove !!" in {check(doubleNegationAxiom)}
  it should "prove exists dual" in {check(existsDualAxiom)}
  ignore should "prove all eliminate" /*taggedAs(OptimisticTest)*/ in {check(allEliminateAxiom)}
  ignore should "prove exists eliminate" /*taggedAs(OptimisticTest)*/ in {check(existsEliminate)}
  it should "prove !exists" in {check(notExists)}
  it should "prove !all" in {check(notAll)}
  it should "prove ![]" in {check(notBox)}
  it should "prove !<>" in {check(notDiamond)}
  it should "prove all distribute" in {check(allDistributeAxiom)}
  it should "prove box dual" in {check(boxDualAxiom)}
  it should "prove K1" in {check(K1)}
  it should "prove K2" in {check(K2)}
  it should "prove box split" in {check(boxSplit)}
  it should "prove box split left" in {check(boxSplitLeft)}
  it should "prove box split right" in {check(boxSplitRight)}
  it should "prove <> split" in {check(diamondSplit)}
  it should "prove diamond split left" in {check(diamondSplitLeft)}
  it should "prove []~><> propagation" in {check{boxDiamondPropagation}}
  it should "prove <:=> assign" in {check(assigndAxiom)}
  it should "prove <:=> assign v" in {check(dummyassigndVvariant)}
  it should "prove := assign dual" in {check(assignDualAxiom)}
  it should "prove all substitute" in {check(allSubstitute)}
  it should "prove [:=] equational" in {check(assignbEquationalAxiom)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbAxiom)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndAxiom)}
  it should "prove <':=> differential assign" in {check(assignDAxiom)}
  it should "prove <:*> assign nondet" in {check(nondetassigndAxiom)}
  it should "prove <?> test" in {check(testdAxiom)}
  it should "prove <++> choice" in {check(choicedAxiom)}
  it should "prove <;> compose" in {check(composedAxiom)}
  it should "prove <*> iterate" in {check(iteratedAxiom)}
  it should "prove <*> approx" in {check(loopApproxd)}
  it should "prove exists generalize" in {check(existsGeneralize)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom)}
  it should "prove & commute" in {check(andCommute)}
  it should "prove & assoc" in {check(andAssoc)}
  it should "prove !& deMorgan" in {check(notAnd)}
  it should "prove !| deMorgan" in {check(notOr)}
  it should "prove !-> deMorgan" in {check(notImply)}
  it should "prove !<-> deMorgan" in {check(notEquiv)}
  it should "prove domain commute" in {check(domainCommute)}
  it should "prove -> expand" in {check(implyExpand)}
  it should "prove PC1" in {check(PC1)}
  it should "prove PC2" in {check(PC2)}
  it should "prove PC3" in {check(PC3)}
  it should "prove -> tautology" in {check{implyTautology}}
  it should "prove ->'" in {check(Dimply)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom)}
  it should "prove DW differential weakening" in {check(DWeakening)}
  it should "prove DS no domain" in {check(DSnodomain)}
  it should "prove DSol no domain" in {check(DSdnodomain)}
  it should "prove Dsol& differential equation solution" in {check(DSddomain)}
//  it should "prove x' derive var" in {check(Dvar)}
  it should "prove x' derive variable" in {check(Dvariable)}
  it should "prove 'linear" in {check(Dlinear)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(Dskipd)}
  it should "prove = reflexive" in {check(equalReflex)}
  it should "prove = commute" in {check(equalCommute)}
  it should "prove <=" in {check(lessEqual)}
  it should "prove = negate" in {check(notNotEqual)}
  it should "prove < negate" in {check(notGreaterEqual)}
  it should "prove >= flip" in {check(flipGreaterEqual)}
  it should "prove > flip" in {check(flipGreater)}
  it should "prove + associative" in {check(plusAssociative)}
  it should "prove * associative" in {check(timesAssociative)}
  it should "prove + commutative" in {check(plusCommutative)}
  it should "prove * commutative" in {check(timesCommutative)}
  it should "prove distributive" in {check(distributive)}
  it should "prove + identity" in {check(plusIdentity)}
  it should "prove * identity" in {check(timesIdentity)}
  it should "prove + inverse" in {check(plusInverse)}
  it should "prove * inverse" in {check(timesInverse)}
  it should "prove positivity" in {check(positivity)}
  it should "prove + closed" in {check(plusClosed)}
  it should "prove * closed" in {check(timesClosed)}
  it should "prove <" in {check(less)}
  it should "prove >" in {check(greater)}
  it should "prove abs" in {check(absDef)}
  it should "prove min" in {check(minDef)}
  it should "prove max" in {check(maxDef)}
  it should "prove y-variant of all dual" in {check(dummyallDualAxiom)}
  it should "prove y-variant of all dual 2" in {check(dummyallDualAxiom2)}
  it should "prove y-variant of exists dual" in {check(dummyexistsDualAxiom)}
  it should "prove +0' dummy" in {check(dummyDplus0)}
  it should "prove +*' reduce dummy" in {check(dummyDplustimesreduceAxiom)}
  it should "prove +*' expand dummy" in {check(dummyDplustimesexpandAxiom)}
  it should "prove ^' consequence dummy" in {check(dummyDpowerconsequence)}

  "Derived Axiom Tactics" should "prove <-> reflexive" in {check(equivReflexiveT)}
  it should "prove !!" in {check(doubleNegationT)}
  it should "prove exists dual" in {check(existsDualT)}
  ignore should "prove all eliminate" /*taggedAs(OptimisticTest)*/ in {check(allEliminateT)}
  ignore should "prove exists eliminate" /*taggedAs(OptimisticTest)*/ in {check(existsEliminateT)}
  it should "prove all distribute" in {check(allDistributeT)}
  it should "prove box dual" in {check(boxDualT)}
  it should "prove <:=> assign" in {check(assigndT)}
  it should "prove [:=] equational" in {check(assignbEquationalT)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbT)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndT)}
  it should "prove <':=> differential assign" in {check(assignDT)}
  it should "prove <++> choice" in {check(choicedT)}
  it should "prove <;> compose" in {check(composedT)}
  it should "prove <*> iterate" in {check(iteratedT)}
  it should "prove exists generalize" in {check(existsGeneralizeT)}
  it should "prove = reflexive" in {check(equalReflexiveT)}
  it should "prove = commute" in {check(equalCommuteT)}
  it should "prove <=" in {check(lessEqualT)}
  it should "prove = negate" in {check(notNotEqualT)}
  it should "prove < negate" in {check(notGreaterEqualT)}
  it should "prove >= flip" in {check(flipGreaterEqualT)}
  it should "prove > flip" in {check(flipGreaterT)}
  it should "prove all substitute" in {check(allSubstituteT)}
  it should "prove vacuous exists" in {check(vacuousExistsT)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetT)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetT)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsT)}
  it should "prove DG differential pre-ghost" in {check(DGpreghostT)}
  it should "prove DW differential weakening" in {check(DWeakeningT)}
  it should "prove abs" in {check(absT)}
  it should "prove min" in {check(minT)}
  it should "prove max" in {check(maxT)}


  lazy val dummyassigndVvariant = derivedAxiom("<:=> assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=t();>p(v) <-> p(t())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val dummyexistsDualAxiom = derivedAxiom("exists dual dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\forall y (!p(y))) <-> \\exists y p(y)".asFormula)),
    useAt("all dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val dummyallDualAxiom = derivedAxiom("all dual dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\exists y (!p(y))) <-> \\forall y p(y)".asFormula)),
    byUS("all dual")
  )

  lazy val dummyallDualAxiom2 = derivedAxiom("all dual dummy 2",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\exists y (!q(y))) <-> \\forall y q(y)".asFormula)),
    byUS("all dual")
  )

  lazy val dummyDplus0 = derivedAxiom("+id' dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + 0)' = (f(??)') + (0')".asFormula)),
    useAt("+' derive sum", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      byUS("= reflexive")
  )

  lazy val dummyDplustimesreduceAxiom = derivedAxiom("+*' reduce dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + (g(??)*h(??)))' = (f(??)') + ((g(??)')*h(??) + g(??)*(h(??)'))".asFormula)),
    useAt("*' derive product", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      useAt("+' derive sum", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      byUS("= reflexive")
  )

  lazy val dummyDplustimesexpandAxiom = derivedAxiom("+*' expand dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + (g(??)*h(??)))' = (f(??)') + ((g(??)')*h(??) + g(??)*(h(??)'))".asFormula)),
    useAt("+' derive sum")(SuccPosition(0, 0::Nil)) &
    useAt("*' derive product")(SuccPosition(0, 0::1::Nil)) &
      byUS("= reflexive")
  )

  lazy val dummyDpowerconsequence = derivedAxiom("^' dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(x^3)' = (3*x^(3-1))*(x)'".asFormula)),
    useAt("^' derive power",PosInExpr(1::0::Nil))(SuccPosition(0, 0::Nil)) &
      byUS("= reflexive")
  )

  def check(axiom: String, base: Formula, expAnte: Option[Formula], expSucc: Option[Formula], where: Position, in: PosInExpr = PosInExpr(0::Nil)) = {
    val helper = new ProvabilityTestHelper((x) => println(x))
    val s =
      if (where.isAnte) Sequent(Nil, IndexedSeq(base), IndexedSeq())
      else Sequent(Nil, IndexedSeq(), IndexedSeq(base))
    val result = helper.runTactic(useAt(axiom, in)(where), new RootNode(s))

    result.openGoals() should have size 1
    expAnte match {
      case Some(f) => result.openGoals().head.sequent.ante should contain only f
      case None => result.openGoals().head.sequent.ante shouldBe empty
    }
    expSucc match {
      case Some(f) => result.openGoals().head.sequent.succ should contain only f
      case None => result.openGoals().head.sequent.succ shouldBe empty
    }
  }

  "Use at" should "all instantiate" in {check("all instantiate", "\\forall x p(x)".asFormula, Some("p(t())".asFormula), None, AntePosition(0))}
  it should "exists generalize" in {check("exists generalize", "\\exists x p(x)".asFormula, None, Some("p(t())".asFormula), SuccPosition(0), PosInExpr(1::Nil))}
}
