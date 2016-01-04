/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.HilbertCalculus._

import scala.annotation.switch

/**
 * Axiom Indexing data structures.
 * @note Could be generated automatically, yet better in a precomputation fashion, not on the fly.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object AxiomIndex {

  type AxiomIndex = (PosInExpr, List[PosInExpr])

  /**
   * Return (derived) axiom index with key for matching and list of recursors on other sibling, i.e., after useAt/useFor
   * @see [[UnifyUSCalculus.chase()]]
   * @see [[UnifyUSCalculus.chaseFor()]]
   * @todo copy documentation from chase
   */
  def axiomIndex(axiom: String): AxiomIndex = (axiom: @switch) match {
      //@todo axiom.intern() to @switch?
    case "all instantiate" | "all eliminate"
         | "vacuous all quantifier" | "vacuous exists quantifier"
         | "all dual" | "exists dual" => directReduction
    case "const congruence" | "const formula congruence" => reverseReduction
    // [a] modalities and <a> modalities
    case "<> diamond" | "[] box" => (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)
    case "[:=] assign" | "<:=> assign" | "[':=] differential assign" | "<':=> differential assign" => directReduction
    case "[:=] assign equational" | "<:=> assign equational" => (PosInExpr(0::Nil), PosInExpr(Nil)::PosInExpr(0::1::Nil)::Nil)
    case "[:=] assign update" | "<:=> assign update" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "[:*] assign nondet" | "<:*> assign nondet" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(Nil)::Nil)
    case "[?] test"    | "<?> test"    => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "[++] choice" | "<++> choice" => binaryDefault
    case "[;] compose" | "<;> compose" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "[*] iterate" | "<*> iterate" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)

    case "DW"              => (PosInExpr(Nil), Nil)
    case "DC differential cut" => (PosInExpr(1::0::Nil), PosInExpr(Nil)::Nil)
    case "DE differential effect" | "DE differential effect (system)" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "DI differential invariant" => (PosInExpr(1::Nil), PosInExpr(1::1::Nil)::Nil)
    case "DG differential ghost" => directReduction
    case "DG differential Lipschitz ghost system" => directReduction
    case "DG++ System" => ???
    case "DG++" => ???
    case ", commute" => (PosInExpr(0::Nil), Nil)
    case "DS& differential equation solution" => (PosInExpr(0::Nil), PosInExpr(0::1::1::Nil)::PosInExpr(Nil)::Nil)
    case "DX differential skip" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "DX diamond differential skip" => (PosInExpr(1::Nil), PosInExpr(1::Nil)::Nil)

    // ' recursors for derivative axioms
    case "&' derive and" => binaryDefault
    case "|' derive or" => binaryDefault
    case "->' derive imply" => binaryDefault
    case "forall' derive forall" | "exists' derive exists" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "c()' derive constant fn" => nullaryDefault
    // recursors for derivative formula axioms
    case "=' derive ="   => binaryDefault
    case ">=' derive >=" => binaryDefault
    case ">' derive >"   => binaryDefault
    case "<=' derive <=" => binaryDefault
    case "<' derive <"   => binaryDefault
    case "!=' derive !=" => binaryDefault
    case "-' derive neg"   => unaryDefault
    case "+' derive sum"   => binaryDefault
    case "-' derive minus" => binaryDefault
    case "*' derive product" => (PosInExpr(0::Nil), PosInExpr(0::0::Nil)::PosInExpr(1::1::Nil)::Nil)
    case "/' derive quotient" => (PosInExpr(0::Nil), PosInExpr(0::0::0::Nil)::PosInExpr(0::1::1::Nil)::Nil)
    case "^' derive power" => (PosInExpr(1::0::Nil), PosInExpr(1::Nil)::Nil)
    case "chain rule" => (PosInExpr(1::1::0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "x' derive var"   => nullaryDefault

    /* @todo Adapt for hybrid games */
    case "V vacuous" => assert(Axiom.axioms(axiom)==Imply(PredOf(Function("p", None, Unit, Bool), Nothing), Box(ProgramConst("a"), PredOf(Function("p", None, Unit, Bool), Nothing))))
      (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)
    case "K modal modus ponens" => (PosInExpr(1::1::Nil), PosInExpr(Nil)::Nil)
    case "I induction" => (PosInExpr(1::Nil), /*PosInExpr(0::Nil)::*/PosInExpr(1::1::Nil)::PosInExpr(1::Nil)::Nil)
    // derived
    case "' linear" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "' linear right" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)


    case "DW differential weakening" => (PosInExpr(0::Nil), unknown)
    case "DC differential cut" => (PosInExpr(1::0::Nil), PosInExpr(Nil)::Nil)
    case "DE differential effect" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    //@todo unclear recursor
    case "DE differential effect system" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    //@todo other axioms

      // derived axioms

    case "!& deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!| deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!-> deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!<-> deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::PosInExpr(1::0::Nil)::PosInExpr(1::1::Nil)::Nil)
    case "!all" | "!exists" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(Nil)::Nil)
    case "![]" | "!<>" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)

    case "[] split" | "<> split" => binaryDefault
    case "[] split left" | "[] split right" => directReduction
    case "<*> approx" => (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)
    case "<*> stuck" => (PosInExpr(0::Nil), Nil)
    case "<'> stuck" => (PosInExpr(0::Nil), Nil)

    case "[] post weaken" => (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)

    case "+<= up" | "-<= up" | "<=+ down" | "<=- down" => (PosInExpr(1::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::Nil)

    // default position
    case _ => (PosInExpr(0::Nil), Nil)
  }


  private val nullaryDefault = (PosInExpr(0::Nil), Nil)
  private val unaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)
  private val binaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
  private val directReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)
  private val reverseReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)

  // lookup canonical axioms for an expression (index)

  /** Return the canonical (derived) axiom name that simplifies the expression expr */
  def axiomFor(expr: Expression, pos: Option[Position] = None): Option[String] = {
    axiomsFor(expr, pos).headOption
  }

  private val odeList: List[String] = "DI differential invariant" :: "diffCut" :: "DG differential ghost" :: Nil

  private val unknown = Nil

  def axiomsFor(expr: Expression, pos: Option[Position] = None, sequent: Option[Sequent] = None): List[String] = {
    val isTop = pos.nonEmpty && pos.get.isTopLevel
    val isAnte = pos.nonEmpty && pos.get.isAnte
    expr match {
      case Differential(t) => t match {
        case _: Variable => "x' derive var" :: Nil
        case _: Number => "c()' derive constant fn" :: Nil
        // optimizations
        case t: Term if StaticSemantics.freeVars(t).isEmpty => "c()' derive constant fn" :: Nil
        case _: Neg => "-' derive neg" :: Nil
        case _: Plus => "+' derive sum" :: Nil
        case _: Minus => "-' derive minus" :: Nil
        // optimizations
        case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => "' linear" :: Nil
        case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => "' linear right" :: Nil
        case _: Times => "*' derive product" :: Nil
        case _: Divide => "/' derive quotient" :: Nil
        case _: Power => "^' derive power" :: Nil
        case FuncOf(_, Nothing) => "c()' derive constant fn" :: Nil
        case _ => Nil
      }
      case DifferentialFormula(f) => f match {
        case _: Equal => "=' derive =" :: Nil
        case _: NotEqual => "!=' derive !=" :: Nil
        case _: Greater => ">' derive >" :: Nil
        case _: GreaterEqual => ">=' derive >=" :: Nil
        case _: Less => "<' derive <" :: Nil
        case _: LessEqual => "<=' derive <=" :: Nil
        case _: And => "&' derive and" :: Nil
        case _: Or => "|' derive or" :: Nil
        case _: Imply => "->' derive imply" :: Nil
        case _: Forall => "forall' derive forall" :: Nil
        case _: Exists => "exists' derive exists" :: Nil
        case _ => Nil
      }
      case Box(a, post) =>
        val rules =
          // @todo Better applicability test for V
          if (isTop && sequent.isDefined && sequent.get.ante.isEmpty && sequent.get.succ.length == 1) {"G" :: "V vacuous" :: Nil} else { "V vacuous" :: Nil}
        a match {
        // Note: Using this axiom name to look up a tactic via AxiomInfo actually gives you assignb,
        // which handles several assignment axioms.
        case _: Assign => "[:=] assign" :: rules
        case _: AssignAny => "[:*] assign nondet" :: rules
        case _: DiffAssign => "[':=] differential assign" :: rules
        case _: Test => "[?] test" :: rules
        case _: Compose => "[;] compose" :: rules
        case _: Choice => "[++] choice" :: rules
        case _: Dual => "[^d] dual" :: Nil
        case _: Loop => "loop" :: "[*] iterate" :: rules
        // @todo: This misses the case where differential symbols are not top-level.
        case ODESystem(ode, constraint) if post.isInstanceOf[DifferentialFormula] => ode match {
          case _: AtomicODE => "DE differential effect" :: /*"DW differential weakening" ::*/ Nil
          case _: DifferentialProduct => "DE differential effect (system)" :: /*"DW differential weakening" ::*/ Nil
          case _ => assert(false); ???
        }
        /** Return the (derived) axiom names that simplify the expression expr with simpler ones first */
        case ODESystem(ode, constraint) =>
          val tactics: List[String] = "diffSolve" :: /*"diffInvariant" ::*/ "diffInd" :: Nil
          if (constraint == True)
            tactics ++ odeList ++ rules
          else
            (tactics :+ "DW differential weakening") ++ odeList ++ rules
        case _ => Nil
      }
      case Diamond(a, _) => a match {
        case _: Assign => "<:=> assign" :: Nil
        case _: AssignAny => "<:*> assign nondet" :: Nil
        case _: Test => "<?> test" :: Nil
        case _: Compose => "<;> compose" :: Nil
        case _: Choice => "<++> choice" :: Nil
        case _: Dual => "<^d> dual" :: Nil
        case _: ODESystem => println("AxiomIndex for <ODE> still missing"); unknown
        case _ => Nil
      }
      case Not(f) => f match {
        case Box(_, Not(_)) => "<> diamond" :: Nil
        case _: Box => "![]" :: Nil
        case Diamond(_, Not(_)) => "[] box" :: Nil
        case _: Diamond => "!<>" :: Nil
        case _: Forall => "!all" :: Nil
        case _: Exists => "!exists" :: Nil
        case _: Equal => "! =" :: Nil
        case _: NotEqual => "! !=" :: Nil
        case _: Less => "! <" :: Nil
        case _: LessEqual => "! <=" :: Nil
        case _: Greater => "! >" :: Nil
        case _: GreaterEqual => "! >=" :: Nil
        case _: Not => "!! double negation" :: Nil
        case _: And => "!& deMorgan" :: Nil
        case _: Or => "!| deMorgan" :: Nil
        case _: Imply => "!-> deMorgan" :: Nil
        case _: Equiv => "!<-> deMorgan" :: Nil
        case _ => Nil
      }
      case _ =>
        // Check for axioms vs. rules separately because sometimes we might want to apply these axioms when we don't
        // have positions available (which we need to check rule applicability
        val axioms =
          expr match {
            case (And(True, _)) => "true&" :: Nil
            case (And(_, True)) => "&true" :: Nil
            case (Imply(True, _)) => "true->" :: Nil
            case (Imply(_, True)) => "->true" :: Nil
            case _ => Nil
          }
        if (!isTop) axioms
        else {
          (expr, isAnte) match {
            case (_: Not, true) => "NotL" :: Nil
            case (_: Not, false) => "NotR" :: Nil
            case (_: And, true) => axioms :+ "AndL"
            case (_: And, false) => axioms :+ "AndR"
            case (_: Or, true) => "OrL" :: Nil
            case (_: Or, false) => "OrR" :: Nil
            case (_: Imply, true) => axioms :+ "ImplyL"
            case (_: Imply, false) => axioms :+ "ImplyR"
            case (_: Equiv, true) => "EquivL" :: Nil
            case (_: Equiv, false) => "EquivR" :: Nil
            case (_: Forall, false) => "AllR" :: Nil
            case (_: Exists, true) => "ExistsL" :: Nil
            case _ => Nil
          }
        }
    }
  }
}