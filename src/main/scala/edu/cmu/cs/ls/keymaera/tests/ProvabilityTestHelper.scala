package edu.cmu.cs.ls.keymaera.tests

import java.util.concurrent.TimeoutException

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary, TacticWrapper, Tactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, Tactic}
import org.joda.time.DateTimeUtils.MillisProvider

import scala.concurrent.duration.{FiniteDuration, DurationConversions, Duration}
import scala.concurrent.{Future, Await}

/**
 * These are helper functions for writing tactic tests.
 * Created by nfulton on 12/6/14.
 */
object ProvabilityTestHelper {
  val tool = new Mathematica()

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Utility Functions
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Parses a string to an expression. Free variables may occur.
   * @param s
   * @return result of parse on success, or None
   */
  def parse(s:String) : Option[Expr] = new KeYmaeraParser().parseBareExpression(s)

  /**
   *
   * @param formula
   * @return a proof node containing the formula.
   */
  def formulaToNode(formula : Formula) = {
    val sequent = new Sequent(Nil, scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(formula))
    new RootNode(sequent)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Begin Abbreviations

  /**
   *
   * @param tactic
   * @param rootNode
   * @return true just in case the tactic closes the rootNode.
   */
  def tacticClosesProof(tactic : Tactic, rootNode : ProofNode):Boolean = runTactic(tactic, rootNode).isClosed()

  /**
   *
   * @param tactic
   * @param rootNode
   * @return true just in case the tactic does not apply at the node.
   */
  def tacticDoesNotApply(tactic : Tactic, rootNode : ProofNode):Boolean = !tactic.applicable(rootNode)

  /**
   * Converts a position tactic to a tactic by finding an applicable position. Use with care; you might want to find the
   * position yourself using the location tactics in the TacticsLibrary.
   * @param positionTactic
   * @return tactic at an applicable position, or ?
   */
  def positionTacticToTactic(positionTactic : PositionTactic):Tactic = {
    TacticLibrary.locateSuccAnte(positionTactic)
  }

  //Begin Substance.

  /**
   * Runs tactic at rootNode, and then blocks while the tactic runs.
   * @param tactic
   * @param rootNode
   * @param mustApply If true, an exception is thrown if the tactic does not apply. Default: false.
   * @param verbose If true, start/end messages are printed, which can be useful for diagnosing diverging tactics. Default: false.
   * @return the rootNode after tactic application completes.
   */
  def runTactic(tactic : Tactic, rootNode : ProofNode, mustApply:Boolean=false, verbose:Boolean=false):ProofNode = {
    if(!tactic.applicable(rootNode)) {
      throw new Exception("runTactic was called on tactic " + tactic.name + ", but is not applicable on the node.")
    }

    //Dispatching the tactic.
    println("Dispatching tactic " + tactic.name)
    tactic.apply(tool, rootNode)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))

    println("beginning wait sequence for " + tactic.name)
    tactic.synchronized {
      tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll));
      tactic.wait();
      tactic.unregister;
    }

    println("Ending wait sequence for " + tactic.name)
    println("Proof is closed: " + rootNode.isClosed())

    rootNode
  }

  /**
   *
   * @param timeoutMs Milliseconds.
   * @param tactic @see runTactic
   * @param rootNode @see runTactic
   * @param mustApply @see runTactic
   * @param verbose @see runTactic
   * @return Some[node] if the tactic finishes in time, where node is the rootNode passed in.
   *         If the tactic does not end in time, returns None.
   */
  def runTacticWithTimeout(timeoutMs : Long, tactic : Tactic, rootNode : ProofNode,
                           mustApply:Boolean=false, verbose:Boolean=false) : Option[ProofNode] = {
    val future = Future { runTactic(tactic, rootNode, mustApply, verbose) }
    eliminateFutureOrTimeout(future, timeoutMs)
  }

  /**
   *
   * @param x
   * @param timeoutMs
   * @tparam T
   * @return Some(result of x) if x completes in timeoutMs milliseconds, or None if not.
   *         Any exception which is not a TimeoutException is propagated.
   */
  private def eliminateFutureOrTimeout[T](x : Future[T], timeoutMs : Long) : Option[T] = {
    try {
      val result : T = Await.result(x, Duration(timeoutMs, "millis"));
      Some(result)
    }
    catch {
      case e : TimeoutException => None
      case e : Exception => throw e
    }
  }


}
