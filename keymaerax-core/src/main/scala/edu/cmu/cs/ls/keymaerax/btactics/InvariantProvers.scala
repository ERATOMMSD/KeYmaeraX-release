/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, _}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticIndex.TacticRecursors
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import org.apache.logging.log4j.scala.Logger

import scala.collection.immutable.Seq
import scala.collection.immutable.List
import util.control.Breaks._

/**
  * Created by aplatzer on 5/17/18.
  *
  * @author Andre Platzer
  */
object InvariantProvers {
  import Generator.Generator
  import TactixLibrary._

  private val logger = Logger(getClass) //@note instead of "with Logging" to avoid cyclic dependencies

  /** loopSR: cleverly prove a property of a loop automatically by induction, trying hard to generate loop invariants.
    * Uses [[SearchAndRescueAgain]] to avoid repetitive proving.
    * @see [[loopauto]]
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    *      Example 32. */
  def loopSR(gen: Generator[Formula]): DependentPositionTactic = "loopSR" by ((pos:Position,seq:Sequent) => Augmentors.SequentAugmentor(seq)(pos) match {
    case loopfml@Box(prog, post) =>
      val cand: Iterator[Formula] = gen(seq, pos)
      val bounds: List[Variable] =
        if (StaticSemantics.freeVars(post).toSet.exists( v => v.isInstanceOf[DifferentialSymbol] ) )
          StaticSemantics.boundVars(loopfml).toSet.toList
        else DependencyAnalysis.dependencies(prog, DependencyAnalysis.freeVars(post))._1.toList
      var i = -1
      val subst: USubst = if (bounds.length==1)
        USubst(Seq(SubstitutionPair(DotTerm(), bounds.head)))
      else
        USubst(bounds.map(xi=> {i=i+1; SubstitutionPair(DotTerm(Real,Some(i)), xi)}))
      val jj: Formula = KeYmaeraXParser.formulaParser("jjl(" + subst.subsDefsInput.map(sp=>sp.what.prettyString).mkString(",") + ")")
      SearchAndRescueAgain(jj,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil, chase(pos) & OnAll(chase(pos ++ PosInExpr(1::Nil)) | skip)),
        feedOneAfterTheOther(cand),
        //@todo switch to quickstop mode
        OnAll(master()) & done
      )
    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

  private def feedOneAfterTheOther[A<:Expression](gen: Iterator[A]) : (ProvableSig,ProverException)=>Expression = {
    (_,e) => logger.debug("SnR loop status " + e)
      if (gen.hasNext)
        gen.next()
      else
        throw new BelleThrowable("loopSR ran out of loop invariant candidates")
  }

  def loopPostMaster(gen: Generator[Formula]): DependentPositionTactic = "loopPostMaster" by ((pos:Position,seq:Sequent) => Augmentors.SequentAugmentor(seq)(pos) match {
    case loopfml@Box(prog, post) =>
      val initialCond = seq.ante.reduceRightOption(And).getOrElse(True)
      //val cand: Iterator[Formula] = gen(seq, pos)
      val bounds: List[Variable] =
        if (StaticSemantics.freeVars(post).toSet.exists(v => v.isInstanceOf[DifferentialSymbol]))
          StaticSemantics.boundVars(loopfml).toSet.toList
        else DependencyAnalysis.dependencies(prog, DependencyAnalysis.freeVars(post))._1.toList
      var i = -1
      val subst: USubst = if (bounds.length == 1)
        USubst(Seq(SubstitutionPair(DotTerm(), bounds.head)))
      else
        USubst(bounds.map(xi => {
          i = i + 1; SubstitutionPair(DotTerm(Real, Some(i)), xi)
        }))
      val jj: Formula = KeYmaeraXParser.formulaParser("jjl(" + subst.subsDefsInput.map(sp => sp.what.prettyString).mkString(",") + ")")
      val jjl: Formula = KeYmaeraXParser.formulaParser("jjl(" + subst.subsDefsInput.map(sp => sp.repl.prettyString).mkString(",") + ")")
      val jja: Formula = KeYmaeraXParser.formulaParser("jja()")

      /* stateful mutable candidate used in generateOnTheFly and the pass-through later since usubst end tactic not present yet */
      var candidate: Formula = initialCond

      val finishOff: BelleExpr =
      //@todo switch to quickstop mode
        OnAll(ifThenElse(DifferentialTactics.isODE, ODEInvariance.sAIclosedPlus()(pos), QE())(pos)) & done


      def generateOnTheFly[A <: Expression](initialCond: Formula, pos: Position, initialCandidate: Formula): (ProvableSig, ProverException) => Expression = {
        import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.ExpressionAugmentor
        println/*logger.info*/("loopPostMaster initial " + candidate)
        return {
          (pr, e) => {
            var progress: Boolean = false
              breakable {
                for (seq <- pr.subgoals) {
                  seq.sub(pos) match {
                    case Some(Box(sys: ODESystem, post)) =>
                      println("loopPostMaster subst " + USubst(Seq(jjl ~>> candidate, jja ~> True)))
                      // plug in true for jja, commit if succeeded. Else plug in init for jja and generate
                      val wouldBeSeq = USubst(Seq(jjl ~>> candidate, jja ~> True))(seq)
                      lazy val wouldBeSubgoals = USubst(Seq(jjl ~>> candidate, jja ~> True))(pr)
                      println("loopPostMaster looks at\n" + wouldBeSeq)
                      //@note first check induction step; then lazily check all subgoals (candidate may not be true initially or not strong enough)
                      if (proveBy(wouldBeSeq, ?(finishOff)).isProved && proveBy(wouldBeSubgoals, ?(finishOff)).isProved) {
                        // proof will work so no need to change candidate
                        println("Proof will work " + wouldBeSubgoals.prettyString)
                        //@todo continuation still fails since doesn't know about jja ~> True substitution
                      } else {
                        println("loopPostMaster progressing")
                        val assumeMoreSeq = USubst(Seq(jjl ~>> candidate, jja ~> initialCond))(seq)
                        candidate = gen(assumeMoreSeq, pos).next()
                        progress = true
                        println/*logger.info*/("loopPostMaster next    " + candidate)
                        break
                      }
                    case _ =>
                    // ignore branches that are not about ODEs
                  }
                }
              }
            if (progress) {
              println/*logger.info*/("loopPostMaster cand    " + candidate)
              candidate
            } else {
              candidate = False
              throw new BelleThrowable("loopPostMaster: No more progress for lack of ODEs in the loop\n" + pr.prettyString)
            }
          }
        }
      }


      SearchAndRescueAgain(jj,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil,
          cut(jja) <(
            /* use jja() |- */
            chase(pos) & OnAll(propChase) & OnAll(?(chase(pos ++ PosInExpr(1::Nil))) & ?(QE()))
            ,
            /* show postponed |- jja() */
            hide(pos)
            //@todo cohide(Find.FindR(0, Some(jja)))
            )
          ),
        generateOnTheFly(initialCond, pos, post)
        ,
        finishOff
      ) | (
        // pass-through rescue phase
        DebuggingTactics.print("loopPostMaster commits " + candidate) &
        loop(candidate)(pos) < (master(), master(),
          chase(pos) & OnAll(propChase) & OnAll((chase(pos ++ PosInExpr(1::Nil)) | skip) & (QE() | skip))
          ) & finishOff
        )

    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

  //@todo this is a suboptimal emulation for propositional chase on (1)
  def propChase = normalize

}
