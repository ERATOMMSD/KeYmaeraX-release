/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.util.{GregorianCalendar, Date}

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal
import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr

import scala.collection.immutable

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used syncrhonously or asychronously.
 * Each MathematicaLink 
 * Multiple MathematicaLinks may be created by instantiating multiple copies
 * of implementing classes.
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
trait MathematicaLink extends QETool with DiffSolutionTool with CounterExampleTool with SimulationTool with DerivativeTool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type MExpr = com.wolfram.jlink.Expr

  def runUnchecked(cmd : String) : (String, KExpr)
  def run(cmd : MExpr) : (String, KExpr)

  //@todo Code Review: should probably be removed from the interface
  /**
   * @return true if the job is finished, false if it is still running.
   */
  def ready: Boolean

  /** Cancels the current request.
    *
    * @return True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel(): Boolean
}

/**
 * A link to Mathematica using the JLink interface.
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class JLinkMathematicaLink extends MathematicaLink {
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"
  private val TIMEOUT = 10

  //@todo really should be private -> fix SpiralGenerator
  private[keymaerax] var ml: KernelLink = null
  private var linkName: String = null
  private var jlinkLibDir: Option[String] = None

  private val mathematicaExecutor: ToolExecutor[(String, KExpr)] = ToolExecutor.defaultExecutor()

  private var queryIndex: Long = 0

  private val fetchMessagesCmd = "$MessageList"
  private val checkedMessages = (("Reduce", "nsmet") :: ("Reduce", "ratnz") :: Nil).map({ case (s, t) =>
    new MExpr(new MExpr(Expr.SYMBOL, "MessageName"), Array(new MExpr(Expr.SYMBOL, s), new MExpr(t))) })
  private val checkedMessagesExpr = new MExpr(Expr.SYM_LIST, checkedMessages.toArray)

  private val defaultK2MConverter = new KeYmaeraToMathematica

  /**
   * Initializes the connection to Mathematica.
    *
    * @param linkName The name of the link to use (platform-dependent, see Mathematica documentation)
   * @return true if initialization was successful
   * @note Must be called before first use of ml
   */
  def init(linkName : String, jlinkLibDir : Option[String]): Boolean = {
    this.linkName = linkName
    this.jlinkLibDir = jlinkLibDir
    if (jlinkLibDir.isDefined) {
      System.setProperty("com.wolfram.jlink.libdir", jlinkLibDir.get) //e.g., "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink"
    }
    try {
      ml = MathLinkFactory.createKernelLink(Array[String](
        "-linkmode", "launch",
        "-linkname", linkName + " -mathlink"))
      ml.discardAnswer()
      isActivated match {
        case Some(true) => isComputing match {
          case Some(true) => true // everything ok
          case Some(false) => throw new IllegalStateException("Test computation in Mathematica failed.\n Please start a standalone Mathematica notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
          case None => if (DEBUG) println("Unable to determine state of Mathematica, Mathematica may not be working.\n Restart KeYmaera X if you experience problems using arithmetic tactics."); true
        }
        case Some(false) => throw new IllegalStateException("Mathematica is not activated or Mathematica license is expired.\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\n Please renew your Mathematica license and restart KeYmaera X.")
        case None => if (DEBUG) println("Mathematica may not be activated or Mathematica license might be expired.\\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\\n Please check your Mathematica license manually."); true
      }
    } catch {
      case e:UnsatisfiedLinkError =>
        val message = "Mathematica J/Link native library was not found in:\n" + System.getProperty("com.wolfram.jlink.libdir", "(undefined)") +
          "\nOr this path did not contain the native library compatible with " + System.getProperties.getProperty("sun.arch.data.model") + "-bit " + System.getProperties.getProperty("os.name") + " " + System.getProperties.getProperty("os.version") +
          diagnostic
        println(message)
        throw e.initCause(new Error(message))
      case e:MathLinkException => println("Mathematica J/Link errored " + e); throw e
    }
  }

  /**
   * Closes the connection to Mathematica.
   */
  def shutdown() = {
    if (ml == null) println("No need to shut down MathKernel if no link has been initialized")
    //if (ml == null) throw new IllegalStateException("Cannot shut down if no MathKernel has been initialized")
    else {
      println("Shutting down Mathematica...")
      val l: KernelLink = ml
      ml = null
      l.terminateKernel()
      l.close()
      mathematicaExecutor.shutdown()
      println("...Done")
    }
  }

  /** Restarts the Mathematica connection */
  def restart() = {
    val l: KernelLink = ml
    ml = null
    l.terminateKernel()
    init(linkName, jlinkLibDir)
    l.close()
  }

  def toMathematica(expr : KExpr): MExpr = defaultK2MConverter.fromKeYmaera(expr)

  def toKeYmaera(expr : MExpr): KExpr = MathematicaToKeYmaera.fromMathematica(expr)

  /**
   * Runs the command and then halts program execution until answer is returned.
   */
  def runUnchecked(cmd: String): (String, KExpr) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.synchronized {
      ml.evaluate(cmd)
      ml.waitForAnswer()
      val res = ml.getExpr
      val keymaeraResult = MathematicaToKeYmaera.fromMathematica(res)
      // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
      (res.toString, keymaeraResult)
    }
  }

  def run(cmd: MExpr): (String, KExpr) = run(cmd, mathematicaExecutor, MathematicaToKeYmaera.fromMathematica)

  private def run[T](cmd: MExpr, executor: ToolExecutor[(String, T)], converter: MExpr=>T): (String, T) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    //@todo Code Review: querIndex increment should be synchronized
    queryIndex += 1
    val indexedCmd = new MExpr(Expr.SYM_LIST, Array(new MExpr(queryIndex), cmd))
    // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
    val checkErrorMsgCmd = new MExpr(MathematicaSymbols.CHECK, Array(indexedCmd, MathematicaSymbols.EXCEPTION /*, checkedMessagesExpr*/))
    if (DEBUG) println("Sending to Mathematica " + checkErrorMsgCmd)

    val taskId = executor.schedule(_ => {
      dispatch(checkErrorMsgCmd.toString)
      getAnswer(indexedCmd, queryIndex, converter)
    })

    executor.wait(taskId) match {
      case Some(Left(result)) => result
      case Some(Right(throwable)) => throwable match {
        case ex: MathematicaComputationAbortedException =>
          executor.remove(taskId)
          throw ex
        case ex: Throwable =>
          executor.remove(taskId, force = true)
          throw new ToolException("Error executing Mathematica " + checkErrorMsgCmd, throwable)
      }
      case None =>
        //@note Thread is interrupted by another thread (e.g., UI button 'stop')
        cancel()
        executor.remove(taskId, force = true)
        if (DEBUG) println("Initiated aborting Mathematica " + checkErrorMsgCmd)
        throw new MathematicaComputationAbortedException(checkErrorMsgCmd)
    }
  }

  private def dispatch(cmd: String) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.evaluate(cmd)
  }

  /**
   * blocks and returns the answer.
   */
  private def getAnswer[T](input: MExpr, cmdIdx: Long, converter: MExpr=>T): (String, T) = {
    //@todo Properly dispose input in caller
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.waitForAnswer()
    val res = ml.getExpr
    if (res == MathematicaSymbols.ABORTED) {
      res.dispose()
      //@todo Code Review do not hand MExpr to exceptions
      throw new MathematicaComputationAbortedException(input)
    } else if (res == MathematicaSymbols.EXCEPTION) {
      res.dispose()
      // an exception occurred
      ml.evaluate(fetchMessagesCmd)
      ml.waitForAnswer()
      val msg = ml.getExpr
      val txtMsg = msg.toString
      // msg.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
      throw new IllegalArgumentException("Input " + input + " cannot be evaluated: " + txtMsg)
    } else {
      val head = res.head
      if (head.equals(MathematicaSymbols.CHECK)) {
        val txtMsg = res.toString
        // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
        throw new IllegalStateException("Mathematica returned input as answer: " + txtMsg)
      } else if (res.head == Expr.SYM_LIST && res.args().length == 2 && res.args.head.asInt() == cmdIdx) {
        val theResult = res.args.last
        if (theResult == MathematicaSymbols.ABORTED) {
          res.dispose()
          throw new MathematicaComputationAbortedException(input)
        } else {
          val keymaeraResult = converter(theResult)
          val txtResult = theResult.toString
          // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
          (txtResult, keymaeraResult)
        }
      } else {
        val txtResult = res.toString
        // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
        throw new IllegalStateException("Mathematica returned a stale answer for " + txtResult)
      }
    }
  }

  def ready = ???

  def cancel(): Boolean = {
    ml.abortEvaluation()
    true
  }

  def qeEvidence(f : Formula) : (Formula, Evidence) = {
    val input = new MExpr(MathematicaSymbols.REDUCE,
      Array(toMathematica(f), new MExpr(MathematicaSymbols.LIST, new Array[MExpr](0)), MathematicaSymbols.REALS))
    val (output, result) = run(input)
    result match {
      case f : Formula =>
        if (DEBUG) println("Mathematica QE result: " + f.prettyString)
        (f, new ToolEvidence(immutable.Map("input" -> input.toString, "output" -> output)))
      case _ => throw new ToolException("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }

  private def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }

  def findCounterExample(fml: Formula): Option[Map[NamedSymbol, Term]] = {
    val converter = new KeYmaeraToMathematica() {
      override protected def convertTerm(t: Term): MExpr = t match {
        case Differential(c) =>
          new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
        case DifferentialSymbol(c) =>
          new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
        case _ => super.convertTerm(t)
      }
    }

    val input = new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
      Array(converter.fromKeYmaera(Not(fml)),
        new MExpr(
          MathematicaSymbols.LIST,
          StaticSemantics.symbols(fml).toList.sorted.map(s => converter.fromKeYmaera(s)).toArray),
        new MExpr(Expr.SYMBOL, "Reals")))
    val inputWithTO = new MExpr(new MExpr(Expr.SYMBOL,  "TimeConstrained"), Array(input, toMathematica(Number(TIMEOUT))))

    run(inputWithTO, mathematicaExecutor, nonQEConverter) match {
      case (_, cex: Formula) => cex match {
        case False =>
          if (DEBUG) println("No counterexample, Mathematica returned: " + cex.prettyString)
          None
        case _ =>
          if (DEBUG) println("Counterexample " + cex.prettyString)
          Some(flattenConjunctions(cex).map({
            case Equal(name: NamedSymbol, value) => name -> value
            case Equal(FuncOf(fn, _), value) => fn -> value
          }).toMap)
      }
      case result =>
        if (DEBUG) println("No counterexample, Mathematica returned: " + result)
        None
    }
  }

  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = {
    // init[n_] := Map[List[#]&, FindInstance[a>=..., {a, ...}, Reals, n]] as pure function
    val init = new MExpr(new MExpr(Expr.SYMBOL, "SetDelayed"), Array(
      new MExpr(Expr.SYMBOL, "init"),
        new MExpr(new MExpr(Expr.SYMBOL, "Function"), Array(
          new MExpr(new MExpr(Expr.SYMBOL, "Map"), Array(
            new MExpr(new MExpr(Expr.SYMBOL, "Function"), Array(new MExpr(MathematicaSymbols.LIST, Array(new MExpr(Expr.SYMBOL, "#"))))),
            new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
            Array(toMathematica(initial),
              new MExpr(
                MathematicaSymbols.LIST,
                StaticSemantics.symbols(initial).toList.sorted.map(toMathematica).toArray),
              new MExpr(Expr.SYMBOL, "Reals"),
              new MExpr(Expr.SYMBOL, "#")))))))))
    // step[pre_] := Module[{apre=a/.pre, ...}, FindInstance[apre>=..., {a, ...}, Reals]] as pure function
    val (stepPreVars, stepPostVars) = StaticSemantics.symbols(stateRelation).partition(_.name.startsWith("pre"))
    val pre2post = stepPostVars.filter(_.name != "t_").map(v => Variable("pre" + v.name, v.index, v.sort) -> v).toMap[NamedSymbol, NamedSymbol]
    val stepModuleInit = stepPreVars.toList.sorted.map(s =>
      new MExpr(new MExpr(Expr.SYMBOL, "Set"), Array(
        toMathematica(s),
        new MExpr(new MExpr(Expr.SYMBOL, "ReplaceAll"), Array(
          toMathematica(pre2post.getOrElse(s, throw new IllegalArgumentException("No post variable for " + s.prettyString))),
          new MExpr(Expr.SYMBOL, "#")))))).toArray
    val step = new MExpr(new MExpr(Expr.SYMBOL, "SetDelayed"), Array(
      new MExpr(Expr.SYMBOL, "step"),
        new MExpr(new MExpr(Expr.SYMBOL, "Function"),
          Array(new MExpr(new MExpr(Expr.SYMBOL, "Module"),
            Array(new MExpr(MathematicaSymbols.LIST, stepModuleInit),
              new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
              Array(toMathematica(stateRelation),
                new MExpr(
                  MathematicaSymbols.LIST,
                  stepPostVars.toList.sorted.map(toMathematica).toArray),
                new MExpr(Expr.SYMBOL, "Reals")))))))))
    // Map[N[NestList[step,#,steps]]&, init[n]]
    val exec = new MExpr(new MExpr(Expr.SYMBOL, "Map"), Array(
      new MExpr(new MExpr(Expr.SYMBOL, "Function"),
        Array(new MExpr(new MExpr(Expr.SYMBOL, "N"), Array(new MExpr(new MExpr(Expr.SYMBOL, "NestList"),
          Array(new MExpr(Expr.SYMBOL, "step"), new MExpr(Expr.SYMBOL, "#"), new MExpr(steps))))))),
      new MExpr(new MExpr(Expr.SYMBOL, "Apply"), Array(new MExpr(Expr.SYMBOL, "init"),
        new MExpr(MathematicaSymbols.LIST, Array(new MExpr(n)))))))
    // initial;step;simulate
    val simulate = new MExpr(new MExpr(Expr.SYMBOL, "CompoundExpression"), Array(init, step, exec))

    val executor: ToolExecutor[(String, List[List[Map[NamedSymbol, Number]]])] = ToolExecutor.defaultExecutor()
    def convert(e: MExpr): List[List[Map[NamedSymbol, Number]]] = {
      if (e.listQ() && e.args.forall(_.listQ())) {
        val states: Array[Array[KExpr]] = e.args().map(_.args().map(nonQEConverter))
        states.map(state => {
          val endOfWorld = if (state.contains(False)) state.indexOf(False) else state.length
          state.slice(0, endOfWorld).map({
          case fml: Formula => flattenConjunctions(fml).map({
              case Equal(name: NamedSymbol, value: Number) => name -> value
              case Equal(FuncOf(fn, _), value: Number) => fn -> value
              case s => throw new IllegalArgumentException("Expected state description Equal(...), but got " + s)
            }).toMap
          case s => throw new IllegalArgumentException("Expected state formula, but got " + s)
        }).toList}).toList
      } else throw new IllegalArgumentException("Expected list of simulation states, but got " + e)
    }

    val result = run(simulate, executor, convert)
    executor.shutdown()
    result._2
  }

  def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = ???

  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] =
    diffSol(diffArg, iv, toDiffSys(diffSys, diffArg):_*)

  /** Extends default converter with rule and rule list handling */
  private def nonQEConverter(e: MExpr): KExpr = {
    if (MathematicaToKeYmaera.hasHead(e, MathematicaSymbols.RULE)) convertRule(nonQEConverter)(e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      MathematicaToKeYmaera.hasHead(_, MathematicaSymbols.RULE))))
      convertRuleList(MathematicaToKeYmaera.fromMathematica)(e)
    else MathematicaToKeYmaera.fromMathematica(e)
  }

  /** Converts rules and rule lists, not to be used in QE! */
  private def convertRule(fromMathematica: MExpr=>KExpr)(e: MExpr): Formula = {
    Equal(fromMathematica(e.args()(0)).asInstanceOf[Term], fromMathematica(e.args()(1)).asInstanceOf[Term])
  }
  private def convertRuleList(fromMathematica: MExpr=>KExpr)(e: MExpr): Formula = {
    val convertedRules = e.args().map(_.args().map(r => convertRule(fromMathematica)(r)).reduceLeft((lhs, rhs) => And(lhs, rhs)))
    if (convertedRules.isEmpty) False
    else convertedRules.reduceLeft((lhs, rhs) => Or(lhs, rhs))
  }

  /**
   * Converts a system of differential equations given as DifferentialProgram into list of x'=theta
    *
    * @param diffSys The system of differential equations
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The differential equation system in list form.
   */
  private def toDiffSys(diffSys: DifferentialProgram, diffArg: Variable): List[(Variable, Term)] = {
    var result = List[(Variable, Term)]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case AtomicODE(DifferentialSymbol(x), theta) if x != diffArg => result = result :+ (x, theta); Left(None)
        case AtomicODE(DifferentialSymbol(x), theta) if x == diffArg => Left(None)
        case ODESystem(_, _) => Left(None)
        case DifferentialProduct(_, _) => Left(None)
      }
    }, diffSys)
    result
  }

  /**
   * Computes the symbolic solution of a system of differential equations.
    *
    * @param diffArg The differential argument, i.e., d f(diffArg) / d diffArg.
   * @param diffSys The system of differential equations of the form x' = theta.
   * @return The solution if found; None otherwise
   */
  private def diffSol(diffArg: Variable, iv: Map[Variable, Variable], diffSys: (Variable, Term)*): Option[Formula] = {
    val primedVars = diffSys.map(_._1)
    val functionalizedTerms = diffSys.map{ case (x, theta) => ( x, functionalizeVars(theta, diffArg, primedVars:_*)) }
    val mathTerms = functionalizedTerms.map{case (x, theta) =>
      val diffSymbol = new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](toMathematica(x)))
      (new MExpr(diffSymbol, Array[MExpr](toMathematica(diffArg))), toMathematica(theta))}
    val convertedDiffSys = mathTerms.map{case (x, theta) =>
      new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](x, theta))}

    val functions = diffSys.map(t => toMathematica(functionalizeVars(t._1, diffArg)))

    val initialValues = diffSys.map(t => toMathematica(
      Equal(functionalizeVars(t._1, Number(BigDecimal(0)), primedVars:_*), iv(t._1))))

    val input = new MExpr(new MExpr(Expr.SYMBOL, "DSolve"),
      Array[MExpr](
        new MExpr(Expr.SYM_LIST, (convertedDiffSys ++ initialValues).toArray),
        new MExpr(Expr.SYM_LIST, functions.toArray),
        toMathematica(diffArg)))
    val (_, result) = run(input, mathematicaExecutor, nonQEConverter)
    result match {
      case f: Formula => Some(defunctionalize(f, diffArg, primedVars.map(_.name):_*))
      case _ => None
    }
  }

  /**
   * Replaces all occurrences of variables vars in the specified term t with functions of argument arg.
    *
    * @param t The term.
   * @param arg The function argument.
   * @param vars The variables to functionalize.
   * @return The term with variables replaced by functions.
   */
  private def functionalizeVars(t: Term, arg: Term, vars: Variable*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v@Variable(name, idx, sort) if vars.isEmpty || vars.contains(v) =>
          Right(FuncOf(Function(name, idx, arg.sort, sort), arg))
        case _ => Left(None)
      }
    }, t) match {
    case Some(resultTerm) => resultTerm
    case None => throw new IllegalArgumentException("Unable to functionalize " + t)
  }

  /**
   * Replaces all functions with argument arg in formula f with a variable of the same name.
    *
    * @param f The formula.
   * @param arg The function argument.
   * @return The term with functions replaced by variables.
   */
  private def defunctionalize(f: Formula, arg: Term, fnNames: String*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(Function(name, idx, _, range), fnArg) if arg == fnArg
          && (fnNames.isEmpty || fnNames.contains(name)) => Right(Variable(name, idx, range))
        case _ => Left(None)
      }
    }, f) match {
    case Some(resultF) => resultF
    case None => throw new IllegalArgumentException("Unable to defunctionalize " + f)
  }

  def deriveBy(term: Term, v: Variable): Term = {
    val mathTerm = toMathematica(term)
    val mathVar = toMathematica(v)
    val input = new MExpr(MathematicaSymbols.D, Array[MExpr](mathTerm, mathVar))
    val (_, result) = run(input, mathematicaExecutor, nonQEConverter)
    result match {
      case t: Term => t
    }
  }



  /** Returns the version as (Major, Minor, Release) */
  private def getVersion: (String, String, String) = {
    ml.evaluate("$VersionNumber")
    ml.waitForAnswer()
    val version = ml.getExpr
    ml.evaluate("$ReleaseNumber")
    ml.waitForAnswer()
    val release = ml.getExpr
    //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
    val (major, minor) = { val versionParts = version.toString.split("\\."); (versionParts(0), versionParts(1)) }
    (major, minor, release.toString)
  }

  /** Checks if Mathematica is activated by querying the license expiration date */
  private def isActivated: Option[Boolean] = {
    type MExpr = com.wolfram.jlink.Expr
    val infinity = new MExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))

    ml.evaluate("$LicenseExpirationDate")
    ml.waitForAnswer()
    val licenseExpirationDate = ml.getExpr

    val date: Array[MExpr] = getVersion match {
      case ("9", _, _) => licenseExpirationDate.args
      case ("10", _, _) => licenseExpirationDate.args.head.args
      case (major, minor, _) => if (DEBUG) println("WARNING: Cannot check license expiration date since unknown Mathematica version " + major + "." + minor + ", only version 9.x and 10.x supported. Mathematica requests may fail if license is expired."); null
    }

    if (date == null) None
    else try {
      if (date.length >= 3 && date(0).integerQ() && date(1).integerQ() && date(2).integerQ()) {
        //@note month in calendar is 0-based, in Mathematica it's 1-based
        val expiration = new GregorianCalendar(date(0).asInt(), date(1).asInt() - 1, date(2).asInt())
        val today = new Date()
        Some(expiration.getTime.after(today))
      } else if (date.length >= 1 && date(0).equals(infinity)) {
        Some(true)
      } else {
        None
      }
    } catch {
      case e: ExprFormatException => if (DEBUG) println("WARNING: Unable to determine Mathematica expiration date\n cause: " + e); None
    }
  }

  /** Sends a simple computation to Mathematica to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      ml.evaluate("6*9")
      ml.waitForAnswer()
      val answer = ml.getExpr
      Some(answer.integerQ() && answer.asInt() == 54)
    } catch {
      //@todo need better error reporting, this way it will never show up on UI
      case e: Throwable => if (DEBUG) println("WARNING: Mathematica may not be functional \n cause: " + e); None
    }
  }
}