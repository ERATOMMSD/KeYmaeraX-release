package edu.cmu.cs.ls.keymaerax.hydra

import java.util.concurrent.{Callable, FutureTask, ExecutorService, Executors}

import _root_.edu.cmu.cs.ls.keymaerax.bellerophon.{IOListener, Interpreter, SequentialInterpreter}
import _root_.edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, BelleValue, BelleExpr, Interpreter}
import scala.collection.mutable.Map

/**
  * Scheduler for Bellerophon tactics
  * @author Nathan Fulton
  */
object BellerophonTacticExecutor {
  val defaultSize = 10
  val defaultExecutor = new BellerophonTacticExecutor(SequentialInterpreter, defaultSize)
}

case class ListenerFuture[T] (userId: String, listeners: List[IOListener], callable: Callable[T]) extends FutureTask[T] (callable) {
  override def cancel(mayInterruptIfRunning:Boolean): Boolean = {
    listeners.foreach(_.kill)
    super.cancel(mayInterruptIfRunning)
  }
}

class BellerophonTacticExecutor(interpreter : List[IOListener] => Interpreter, poolSize: Int) {
  require(poolSize > 0, "At least one thread is needed.")
  private val pool : ExecutorService = Executors.newFixedThreadPool(poolSize)

  /**
    * [[scheduledTactics]] could be at any state of execution, included finished.
    * Tactics are never removed from the [[scheduledTactics]] mapping unless explicitly via .remove()
    */
  private val scheduledTactics : scala.collection.mutable.Map[String, ListenerFuture[Either[BelleValue, BelleThrowable]]] = Map()

  def tasksForUser(userId: String):List[String] = {
    scheduledTactics.flatMap{case (task, future) =>
      if (userId == future.userId)
        List(task)
      else
        Nil
    }.toList
  }

  /**
    *
    * @param tactic The tactic to run
    * @param value The value to apply the tactic to
    * @return The ID that [[BellerophonTacticExecutor]] uses to identify this tactic.
    */
  def schedule(userId: String, tactic: BelleExpr, value: BelleValue, listeners: List[IOListener] = Nil) : String = {
    val id = java.util.UUID.randomUUID().toString
    assert(!scheduledTactics.contains(id), "All running tactic IDs should be unique.")
    val future = makeFuture(userId, tactic, value, listeners)
    pool.submit(future)
    scheduledTactics += ((id, future))
    id
  }

  def isDone(id: String) = scheduledTactics.get(id) match {
    case Some(future) => future.isDone
    case None         => throw new Exception("This tactic does not exist in the list.")
  }

  def contains(id: String) = scheduledTactics.contains(id)

  /** Returns the result of the tactic, or None if the tactic is not done running. */
  def getResult(id: String) : Option[Either[BelleValue, BelleThrowable]] =
    synchronized {
      if (isDone(id))
        Some(scheduledTactics(id).get())
      else None
    }

  /**
    *
    * @param id The schedule id of the tactic to remove.
    * @param force If true, then the tactic can be removed even if it is currently running.
    *              In that case, the tactic execution is halted first. Defaults to false.
    */
  def tryRemove(id: String, force: Boolean = false): Unit =
    synchronized {
      if (!scheduledTactics.contains(id))
        return
      if (isDone(id)) {
        scheduledTactics.remove(id)
      }
      else if (force) {
        scheduledTactics.get(id).foreach(_.cancel(true))
        scheduledTactics.remove(id)
      }
      else {
        //@note if you want to remove a tactic even if it's still running, then call remove(id, true).
        throw new Exception("Attempted to remove a tactic from scheduledTactics, but that tactic is not yet finished executing.")
      }
  } ensuring(!scheduledTactics.contains(id))

  /**
    *
    * @param id The schedule id of the tactic to remove.
    * @param force If true, then the tactic can be removed even if it is currently running.
    *              In that case, the tactic execution is halted first. Defaults to false.
    */
  def remove(id: String, force: Boolean = false) = {
    require(scheduledTactics.contains(id), "Cannot remove a tactic whose ID is not in the key set of scheduledTactics.")
    tryRemove(id, force)
  }

  /**
    * @param id The schedule id of the tactic to wait on
    * @param millis The duration in milliseconds to sleep between polling attempts
    */
  def wait(id: String, millis:Int = 10): Option[Either[BelleValue, BelleThrowable]] = {
    try {
      while(!isDone(id)) {
        Thread.sleep(millis)
      }
      getResult(id)
    } catch {
      // If the tactic execution is cancelled
      case e:Exception => None
    }
  }

  private def makeFuture(userId: String, tactic: BelleExpr, value: BelleValue, listeners: List[IOListener]) = {
    new ListenerFuture[Either[BelleValue, BelleThrowable]](userId, listeners, new Callable[Either[BelleValue, BelleThrowable]]() {
      override def call(): Either[BelleValue, BelleThrowable] = {
        try {
          Left(interpreter(listeners)(tactic, value))
        }
        catch {
          case e : BelleThrowable     => Right(e)
          case thrown : Throwable => Right(new BelleThrowable("Unknown throwable thrown during tactic execution", thrown))
        }
      }
    })
  }
}