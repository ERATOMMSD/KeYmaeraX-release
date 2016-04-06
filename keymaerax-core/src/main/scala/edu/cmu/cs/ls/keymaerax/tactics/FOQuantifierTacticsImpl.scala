/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.btactics.Axiom
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AlphaConversionHelper._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.{boxMonotoneT, diamondMonotoneT}
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.v2vAssignT
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.{getFormula, freshNamedSymbol}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._

import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{TacticHelper, alphaRenamingT, globalAlphaRenamingT}
import PropositionalTacticsImpl.uniformSubstT
import AxiomTactic.axiomT
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.List
import scala.collection.immutable.Seq

/**
 * Implementation of first order quantifier tactics.
 *
 * @author Stefan Mitsch
 */
object FOQuantifierTacticsImpl {

  def universalClosure(f: Formula): Formula = {
    val vars = NameCategorizer.freeVariables(f)
    if(vars.isEmpty) f
    else {
      require(vars.forall(_.isInstanceOf[Variable]),
        "Unable to compute universal closure for formula containing free non-variable symbols: " + f.prettyString)
      vars.foldRight(f)((v, fml) => Forall(v.asInstanceOf[Variable] :: Nil, fml)) //Forall(vars.toList, f)
    }
  }

  def universalClosureT(order: List[NamedSymbol] = Nil): PositionTactic = new PositionTactic("Universal closure") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel &&
      order.toSet.subsetOf(StaticSemantics.freeVars(s(p)).toSet ++ StaticSemantics.signature(s(p)))

    override def apply(p: Position): Tactic = new ConstructionTactic("Universal Closure") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        // fetch non-bound variables and parameterless function symbols
        val varsFns: Set[NamedSymbol] = StaticSemantics.freeVars(node.sequent(p)).toSet ++ StaticSemantics.signature(node.sequent(p))
        require(order.toSet.subsetOf(varsFns), "Order of variables must be a subset of the free symbols+signature, but "
          + (order.toSet -- varsFns) + " is not in the subset")
        // use specified order in reverse, prepend the rest alphabetically
        // @note get both: specified order and compatibility with previous sorting, which resulted in
        //       reverse-alphabetical ordering of quantifiers
        val sorted: List[Term] = ((varsFns -- order).
          filter({ case Variable(_, _, _) => true case Function(_, _, Unit, _) => true case _ => false }).
          // guarantee stable sorting of quantifiers so that Mathematica behavior is predictable - for now: alphabetically
          toList.sortBy(_.name) ++ order.reverse).
          map({ case v@Variable(_, _, _) => v case fn@Function(_, _, Unit, _) => FuncOf(fn, Nothing) case _ => throw new IllegalArgumentException("Should have been filtered") })

        if (sorted.isEmpty) Some(NilT)
        else Some(sorted.map(t => universalGenT(None, t)(p)).reduce(_ & _))
      }
    }
  }

  /**
   * Creates a new tactic for the universal/existential duality axiom.
 *
   * @return The newly created tactic
   */
  def forallDualT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // !(\exists x . (!p(x))) <-> \forall x . p(x)
      case Forall(v, p) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        Equiv(Not(Exists(v, Not(p))), fml)
      case Not(Exists(v, Not(p))) => Equiv(fml, Forall(v, p))
      case _ => False
    }
    uncoverAxiomT("all dual", axiomInstance, _ => forallDualBaseT)
  }
  /** Base tactic for forall duality */
  private def forallDualBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (p, v) = fml match {
        case Equiv(_, Forall(vv, pp)) => (pp, vv)
        case Equiv(Not(Exists(vv, Not(pp))), _) => (pp, vv)
      }
      val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
      SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(v.head, DotTerm)) :: Nil
    }
    axiomLookupBaseT("all dual", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new tactic for the universal/existential duality axiom.
 *
   * @return The newly created tactic
   */
  def existsDualT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // !(\forall x . (!p(x))) <-> \exists x . p(x)
      case Exists(v, p) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        Equiv(Not(Forall(v, Not(p))), fml)
      case Not(Forall(v, Not(p))) => Equiv(fml, Exists(v, p))
      case _ => False
    }
    uncoverAxiomT("exists dual", axiomInstance, _ => existsDualBaseT)
  }
  /** Base tactic for exists duality */
  private def existsDualBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (p, v) = fml match {
        case Equiv(_, Exists(vv, pp)) => (pp, vv)
        case Equiv(Not(Forall(vv, Not(pp))), _) => (pp, vv)
      }
      val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
      SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(v.head, DotTerm)) :: Nil
    }

    val aX = Variable("x")
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(_, Exists(v, _)) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        if (v.head.name == aX.name && v.head.index == aX.index) NilPT
        else new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
            case Equiv(_, Exists(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(v.head, aX))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(_, Exists(v, _)) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        if (v.head.name == aX.name && v.head.index == aX.index) axiom
        else replace(axiom)(aX, v.head)
    }

    axiomLookupBaseT("exists dual", subst, alpha, axiomInstance)
  }

  def allEliminateAlphaT(instantiation : Variable) = new PositionTactic("All eliminate with alpha-renaming") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && p.isTopLevel && (s(p) match {
      case Forall(list, phi) => true // TODO applies is ignored by uncoverAxiomT?
      case _ => false
    })

    override def apply(p: Position): Tactic = {
      val aX = Variable("x", None, Real)

      val renamingTactic = alphaRenamingT(aX, instantiation)

      def axiomInstance(fml: Formula): Formula = fml match {
        case Forall(_, phi) => Imply(fml, phi)
        case _ => False
      }

      renamingTactic(p) & uncoverAxiomT("all eliminate", axiomInstance, _ => allEliminateBaseT)(p)
    }
  }

  /**
   * Creates a new tactic to eliminate a universal quantifier.
 *
   * @return The newly created tactic
   */
  def allEliminateT: PositionTactic = new PositionTactic("All eliminate") {
    // TODO applies is ignored by uncoverAxiomT
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && p.isTopLevel && (s(p) match {
      case Forall(_, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = {
      val aX = Variable("x", None, Real)

      def axiomInstance(fml: Formula): Formula = fml match {
        case Forall(_, phi) => Imply(fml, phi)
        case _ => False
      }

      uncoverAxiomT("all eliminate", axiomInstance, _ => allEliminateBaseT)(p)
    }
  }
  /** Base tactic for all eliminate */
  private def allEliminateBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val p = fml match {
        case Imply(_, q) => q
      }
      val aP = PredOf(Function("p", None, Real, Bool), Anything)
      SubstitutionPair(aP, p) :: Nil
    }
    val aX = Variable("x", None, Real)

    //alpha should rename the bound variable to x.
    def alpha(fml: Formula): PositionTactic = fml match {
      case Imply(Forall(vars, _), _) =>
        assert(vars.length == 1, "Block quantifiers not yet supported")
        val x = vars.head
        if (x.name != aX.name || x.index != aX.index)
//          TacticLibrary.alphaRenamingT(x, aX)
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
              case Imply(Forall(_, _), _) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
                //                Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))
                val succLength = node.sequent.succ.length - 1
                def hasExpectedForm(sequent : Sequent) = sequent(p) match {
                  case Imply(Forall(_,_), _) => true
                  case _ => false
                }
                Some(assertT(hasExpectedForm) & SearchTacticsImpl.locateSubposition(SuccPos(succLength))(TacticLibrary.alphaRenamingT(x, aX)))
              }

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Imply(Forall(vars, _), p) =>
        assert(vars.length == 1, "Block quantifiers not yet supported")
        val x = vars.head
        if (x.name == aX.name && x.index == aX.index) axiom
        else replace(axiom)(aX, x)
    }
    axiomLookupBaseT("all eliminate", subst, alpha, axiomInstance)
  }

  /**
   * Returns a new tactic for universal/existential quantifier instantiation. The tactic performs self-instantiation
   * with the quantified variable.
 *
   * @example{{{
   *           |- x>0
   *         ------------------instantiateT(SuccPosition(0))
   *           |- \exists x x>0
   * }}}
   * @example{{{
   *                     x>0 |-
   *         ------------------instantiateT(AntePosition(0))
   *           \forall x x>0 |-
   * }}}
   * @return The tactic.
   */
  def instantiateT: PositionTactic = new PositionTactic("Quantifier Instantiation") {
    override def applies(s: Sequent, p: Position): Boolean = s(p).subFormulaAt(p.inExpr) match {
      case Some(Forall(_, _)) => p.isAnte
      case Some(Exists(_, _)) => !p.isAnte
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos).subFormulaAt(pos.inExpr) match {
        case Some(Forall(vars, phi)) => Some(vars.map(v => instantiateT(v, v)(pos)).fold(NilT)((a, b) => a & b))
        case Some(Exists(vars, phi)) => Some(vars.map(v => instantiateT(v, v)(pos)).fold(NilT)((a, b) => a & b))
        case _ => None
      }
    }
  }

  /**
   * Creates a tactic which does quantifier instantiation.
 *
   * @param quantified The quantified variable.
   * @param instance The instance.
   * @return The tactic.
   */
  def instantiateT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Quantifier Instantiation") {
    override def applies(s: Sequent, p: Position): Boolean = s(p).subFormulaAt(p.inExpr) match {
      case Some(Forall(vars, _)) => p.isAnte && vars.contains(quantified)
      case Some(Exists(vars, _)) => !p.isAnte && vars.contains(quantified)
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos).subFormulaAt(pos.inExpr) match {
        case Some(Forall(vars, _)) =>
          Some(withStuttering(node.sequent, vars.length > 1, instantiateUniversalQuanT(quantified, instance)(pos)))
        case Some(Exists(vars, _)) =>
          Some(withStuttering(node.sequent, vars.length > 1, instantiateExistentialQuanT(quantified, instance)(pos)))
        case _ => None
      }

      private def withStuttering(s: Sequent, quantStillPresentAfterAround: Boolean, around: Tactic): Tactic = {
        var stutteringAt: Set[PosInExpr] = Set.empty[PosInExpr]

        // HACK don't need stuttering for dummy variable introduced in abstractionT
        // (no longer necessary when we have the correct condition on filtering stutteringAt)
        if (quantified.name != "$abstractiondummy") {
          ExpressionTraversal.traverse(new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
              case Box(prg, _) if /*StaticSemantics(prg).bv.contains(quantified) &&*/ !stutteringAt.exists(_.isPrefixOf(p)) => stutteringAt += p; Left(None)
              case Diamond(prg, _) if /*StaticSemantics(prg).bv.contains(quantified) &&*/ !stutteringAt.exists(_.isPrefixOf(p)) => stutteringAt += p; Left(None)
              case _ => Left(None)
            }
          }, s(pos).subFormulaAt(pos.inExpr).get)
        }

        if (stutteringAt.nonEmpty) {
          val pPos = stutteringAt.map(p => pos.subPos(p))
          val assignPos = stutteringAt.map(p => pos.subPos(PosInExpr(p.pos.tail)))
          val alpha = pPos.foldRight(NilT)((p, r) => r & (alphaRenamingT(quantified, quantified)(p) | NilT))
          val v2v =
            if (quantStillPresentAfterAround) assignPos.foldRight(NilT)((p, r) => r & (v2vAssignT(
              p.topLevel.subPos(PosInExpr(0 :: p.inExpr.pos))) | NilT))
            else assignPos.foldRight(NilT)((p, r) => r & (v2vAssignT(p) | NilT))
          alpha & around & v2v
        } else around

      }
    }
  }

  def instantiateUniversalQuanT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Universal Quantifier Instantiation") {
    val axiomName = "all instantiate"
    val axiom = Axiom.axioms.get(axiomName)
    require(axiom.isDefined)

    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case Forall(vars, _) => vars.contains(quantified)
      case _ => false
    })

    override def apply(pos: Position): Tactic = new ConstructionTactic("Universal Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      def replace(f: Formula)(o: NamedSymbol, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fa) => Right(Forall(v.map(name => if(name == o) n else name ), fa))
          case Exists(v, fa) => Right(Exists(v.map(name => if(name == o) n else name ), fa))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair], (Variable, Variable), (Term, Term))] = f match {
        case Forall(x, qf) if x.contains(quantified) =>
          def forall(h: Formula) = if (x.length > 1) Forall(x.filter(_ != quantified), h) else h
          // construct substitution
          val aX = Variable("x", None, Real)
          val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
          val aP = Function("p", None, Real, Bool)
          val l = List(SubstitutionPair(aT, instance), SubstitutionPair(PredOf(aP, DotTerm),
            forall(SubstitutionHelper.replaceFree(qf)(quantified, DotTerm))))
          // construct axiom instance: \forall x. p(x) -> p(t)
          val g = SubstitutionHelper.replaceFree(qf)(quantified, instance)
          val axiomInstance = Imply(f, forall(g))
          Some(axiomInstance, l, (quantified, aX), (instance, aT))
        case Forall(x, qf) if !x.contains(quantified) => None
        case _ => None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if v.length > 1 => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if v.length > 1 => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

      // since we have an implication, we use modus ponens to get it's consequence
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiom match {
          case Some(a) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
              case Some((axiomInstance, subst, (quant, aX), (inst, aT))) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = modusPonensT(pos, eqPos)
                // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                def repl(f: Formula, v: Variable):Formula = f match {
                  case Imply(Forall(vars, aa), b) =>
                    Imply(
                      decompose(
                        Forall(vars.map(qv => if (qv == v) quantified else qv), SubstitutionHelper.replaceFree(aa)(v, quantified))),
                      b)
                  case _ => throw new IllegalArgumentException("...")
                }

                val (renAxiom, alpha) =
                  if (quantified.name != aX.name || quantified.index != aX.index)
                    (repl(a, aX), alphaRenamingT(quantified, aX)(SuccPosition(0, HereP.first)))
                  else (a, NilT)

                val axInstance = axiomInstance match {
                  case Imply(lhs, rhs) => Imply(decompose(lhs), rhs)
                }

                val replMap = Map[Formula, Formula](axInstance -> renAxiom)
                val branch2Tactic = cohideT(SuccPosition(node.sequent.succ.length)) ~
                  (uniformSubstT(subst, replMap) & alpha & axiomT(axiomName))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => println("Giving up " + this.name); None
            }
          case None => println("Giving up because the axiom does not exist " + this.name); None
        }

    }
  }

  /**
   * Returns a tactic to instantiate an existentially quantified formula that occurs in positive polarity in the
   * succedent or in negative polarity in the antecedent.
 *
   * @example{{{
   *         |- y+2>0
   *         ----------------instantiateExistentialQuanT(Variable("x"), "y+2".asTerm)(SuccPosition(0))
   *         |- \exists x x>0
   * }}}
   * @example{{{
   *                 !(y+2>0) |-
   *         -------------------instantiateExistentialQuanT(Variable("x"), "y+2".asTerm)(AntePosition(0, PosInExpr(0::Nil)))
   *         !(\exists x x>0) |-
   * }}}
   * @example{{{
   *         y>0 -> y>0
   *         -----------------------instantiateExistentialQuanT(Variable("x"), Variable("y"))(AntePosition(0, PosInExpr(0::Nil)))
   *         \exists x x>0 -> y>0 |-
   * }}}
   * @param quantified The variable to instantiate.
   * @param t The instance.
   * @return The tactic which performs the instantiation.
   */
  def instantiateExistentialQuanT(quantified: Variable, t: Term) = new PositionTactic("exists instantiate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, _)) => vars.contains(quantified) &&
        ((p.isAnte && FormulaTools.polarityAt(s(p), p.inExpr) == -1) || (!p.isAnte && FormulaTools.polarityAt(s(p), p.inExpr) == 1))
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p).subFormulaAt(p.inExpr) match {
        case Some(Exists(vars, phi)) =>
          var varPos = List[PosInExpr]()
          ExpressionTraversal.traverse(new ExpressionTraversalFunction {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
              case n: NamedSymbol if vars.contains(n) && !StaticSemanticsTools.boundAt(phi, p).contains(n) =>
                varPos = varPos :+ p
                Left(None)
              case _ => Left(None)
            }
          }, phi)

          val desired = createDesired(node.sequent)
          val cutFrm = Imply(desired, node.sequent(p))
          Some(cutT(Some(cutFrm)) & onBranch(
            (cutUseLbl, lastAnte(assertPT(cutFrm)) & lastAnte(ImplyLeftT) && (hideT(p.topLevel), CloseId ~ errorT("Failed to close!"))),
            (cutShowLbl, lastSucc(assertPT(cutFrm)) & lastSucc(cohideT) & assertT(0, 1) & assertPT(cutFrm)(SuccPosition(0)) &
              ImplyRightT(SuccPosition(0)) & assertT(1, 1) &
              generalize(varPos))
          ))
        case _ => None
      }

      private def createDesired(s: Sequent) = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
          case Exists(_, phi) => Right(replace(phi)(quantified, t))
          case _ => Left(Some(ExpressionTraversal.stop))
        }
      }), s(p)) match {
        case Some(frm) => frm
        case None => throw new IllegalArgumentException(s"Did not find existential quantifier in $s at $p")
      }

      private def generalize(where: List[PosInExpr]) = {
        if (p.isTopLevel) {
          existentialGenPosT(quantified, where)(AntePosition(0)) & CloseId
        } else {
          AxiomaticRuleTactics.propositionalCongruenceT(p.inExpr) &
            lastAnte(existentialGenPosT(quantified, where)) &
            (CloseId | TacticLibrary.debugT("Instantiate existential: axiom close failed"))
        }
      }
    }
  }

  /**
   * Returns a tactic to instantiate an existential quantifier that is known to have an equal substitute.
 *
   * @example{{{
   *           |- z>0 & z=z
   *         --------------------------existSubstitute(1)
   *           |- \exists x (x>0 & x=z)
   * }}}
   * @return The tactic.
   */
  def existSubstitute: PositionTactic = new PositionTactic("Exist Substitute") {
    /** Checks whether this position tactic will be applicable at the indicated position of the given sequent */
    override def applies(s: Sequent, p: Position): Boolean = p.isSucc && (s(p).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, pred)) => vars.size == 1 && equalTermOf(vars.head, pred).isDefined
      case _ => false
    })

    /** Apply this PositionTactic at the indicated Position to obtain a tactic to use at any ProofNode */
    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      /** Returns true if this tactics is applicable to the proof node */
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p).subFormulaAt(p.inExpr) match {
        case Some(Exists(vars, pred)) =>
          assert(vars.size == 1, s"Only quantifiers with 1 variable supported so far, have $vars")
          equalTermOf(vars.head, pred) match {
            case Some(t) => Some(instantiateExistentialQuanT(vars.head, t)(p))
            case None => throw new IllegalArgumentException(s"Formula $pred must contain an equality mentioning variable ${vars.head}")
          }
      }
    }

    /** Returns the first term in formula fml that is found to be equal to the variable v */
    private def equalTermOf(v: Variable, fml: Formula): Option[Term] = {
      var result: Option[Term] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Equal(l, r) if l == v => result = Some(r); Left(Some(ExpressionTraversal.stop))
          case Equal(l, r) if r == v => result = Some(l); Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, fml)
      result
    }
  }

  /**
   * Converse of all instantiate.
 *
   * @param x The universally quantified variable to introduce.
   * @param t The term to generalize.
   * @return The position tactic.
   * @example{{{\forall z \forall x x^2 >= -z^2
   *            ------------------------------- universalGenT(z, f())
   *            \forall x x^2 >= -f()^2
   * }}}
   * @example{{{\forall z \forall x x^2 >= -z^2
   *            ------------------------------- universalGenT(z, y+5)
   *            \forall x x^2 >= -(y+5)^2
   * }}}
   */
  def universalGenT(x: Option[Variable], t: Term): PositionTactic = new PositionTactic("all generalize") {
    override def applies(s: Sequent, p: Position): Boolean = x match {
      case Some(xx) => !StaticSemantics.symbols(s(p)).contains(xx)
      case None => t match {
        case Variable(_, _, _) => true
        case FuncOf(_, _) => true
        case _ => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("all generalize") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val quantified: Variable = x match {
          case Some(xx) => xx
          case None => t match {
            case v: Variable => TacticHelper.freshNamedSymbol(v, node.sequent)
            case FuncOf(fn, _) => val fresh = TacticHelper.freshNamedSymbol(fn, node.sequent); Variable(fresh.name, fresh.index, fresh.sort)
            case _ => throw new IllegalStateException("Disallowed by applies")
          }
        }

        val genFml = Forall(Seq(quantified), SubstitutionHelper.replaceFree(node.sequent(p))(t, quantified))
        Some(cutT(Some(genFml)) & onBranch(
          (cutShowLbl, hideT(p)),
          (cutUseLbl, lastAnte(instantiateT(quantified, t)) & (CloseId | TacticLibrary.debugT("Universal gen: axiom close failed unexpectedly")))
        ))
      }
    }
  }

  /**
   * Tactic for existential quantifier generalization. Generalizes the specified term everywhere in a formula.
 *
   * @example{{{
   *           \exists z z+1 < z+2 |-
   *           -----------------------existentialGenT(Variable("z"), "x+y".asTerm)(AntePosition(0))
   *                 x+y+1 < x+y+2 |-
   * }}}
   * @param x The new existentially quantified variable.
   * @param t The term to generalize.
   * @return The tactic.
   */
  //@todo there's only one usage of this tactic -> replace with existentialGenPosT
  def existentialGenT(x: Variable, t: Term): PositionTactic = {
    // construct axiom instance: p(t) -> \exists x. p(x)
    def axiomInstance(fml: Formula): Formula = Imply(fml, Exists(x :: Nil, SubstitutionHelper.replaceFree(fml)(t, x)))
    uncoverAxiomT("exists generalize", axiomInstance, _ => existentialGenBaseT(x, t))
  }
  /** Base tactic for existential generalization */
  private def existentialGenBaseT(x: Variable, t: Term): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(p, Exists(_, _)) =>
        val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
        val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
        SubstitutionPair(aT, t) :: SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(t, DotTerm)) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Imply(_, Exists(_, _)) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(x, aX)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Imply(left, right) = axiom
      if (x.name != aX.name || x.index != aX.index) Imply(left, replaceFree(right)(aX, x))
      else Imply(left, right)
    }

    axiomLookupBaseT("exists generalize", subst, alpha, axiomInstance)
  }

  /**
   * Tactic for existential quantifier generalization. Generalizes only at certain positions. All positions have to
   * refer to the same term.
 *
   * @example{{{
   *           \exists z z=a+b |-
   *           ------------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: Nil)(AntePosition(0))
   *                 a+b = a+b |-
   * }}}
   * @example{{{
   *           \exists z z=z |-
   *           ----------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: PosInExpr(1::Nil) :: Nil)(AntePosition(0))
   *               a+b = a+b |-
   * }}}
   * @param x The new existentially quantified variable.
   * @param where The term to generalize.
   * @return The tactic.
   */
  def existentialGenPosT(x: Variable, where: List[PosInExpr]): PositionTactic = {
    // construct axiom instance: p(t) -> \exists x. p(x)
    def axiomInstance(fml: Formula): Formula = {
      require(where.nonEmpty, "need at least one position to generalize")
      require(where.map(w => TacticHelper.getTerm(fml, w)).toSet.size == 1, "not all positions refer to the same term")
      val t = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (where.contains(p)) Right(x)
          else Left(None)
      }, fml) match {
        case Some(f) => f
        case _ => throw new IllegalArgumentException(s"Position $where is not a term")
      }
      Imply(fml, Exists(x :: Nil, t))
    }
    uncoverAxiomT("exists generalize", axiomInstance, _ => existentialGenPosBaseT(x, where))
  }
  /** Base tactic for existential generalization */
  private def existentialGenPosBaseT(x: Variable, where: List[PosInExpr]): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(p, Exists(_, _)) =>
        assert(where.map(w => TacticHelper.getTerm(p, w)).toSet.size == 1, "not all positions refer to the same term")

        val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
        val aP = PredOf(Function("p", None, Real, Bool), DotTerm)

        val t = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
            if (where.contains(p)) Right(DotTerm)
            else Left(None)
        }, p) match {
          case Some(f) => f
          case _ => throw new IllegalArgumentException(s"Position $where is not a term")
        }

        SubstitutionPair(aT, TacticHelper.getTerm(p, where.head).get) ::
        SubstitutionPair(aP, t) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Imply(_, Exists(_, _)) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(x, aX)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Imply(left, right) = axiom
      if (x.name != aX.name || x.index != aX.index) Imply(left, replaceFree(right)(aX, x))
      else Imply(left, right)
    }

    axiomLookupBaseT("exists generalize", subst, alpha, axiomInstance)
  }

  def vacuousUniversalQuanT(x: Option[Variable]) = vacuousQuantificationT(x, "vacuous all quantifier", Forall.apply)
  def vacuousExistentialQuanT(x: Option[Variable]) = vacuousQuantificationT(x, "vacuous exists quantifier", Exists.apply)

  /**
   * Base class for vacuous quantifier elimination/introduction tactics.
 *
   * @param x The new quantified variable. If None, the tactic eliminates a vacuous quantifier.
   * @param axiomName The name of the axiom.
   * @param quantFactory Creates the quantifier.
   */
  def vacuousQuantificationT(x: Option[Variable], axiomName: String,
                             quantFactory: (Seq[Variable], Formula) => Quantified): PositionTactic = {

    def axiomInstance(fml: Formula): Formula = x match {
      case Some(v) if !StaticSemantics.symbols(fml).contains(v) => Equiv(quantFactory(v :: Nil, fml), fml)
      case _ => fml match {
        case q: Quantified if q.vars.size == 1 && StaticSemantics.symbols(q.child).intersect(q.vars.toSet).isEmpty =>
          Equiv(fml, q.child)
        case _ => False
      }
    }
    uncoverAxiomT(axiomName, axiomInstance, _ => vacuousQuantificationBaseT(x, axiomName, quantFactory))
  }

  private def vacuousQuantificationBaseT(x: Option[Variable], axiomName: String,
                                         quantFactory: (Seq[Variable], Formula) => Quantified): PositionTactic = {

    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(_, p) =>
        val aP = PredOf(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aP, p) :: Nil
    }

    def v(fml: Formula) = x match {
      case Some(vv) => vv
      case None => fml match {
        case Equiv(q: Quantified, _) =>
          require(q.vars.size == 1)
          q.vars.head
      }
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Equiv(_: Quantified, _) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(v(fml), aX)(p.first))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Equiv(left, right) = axiom
      if (v(fml).name == aX.name && v(fml).index == aX.index) Equiv(left, right)
      else Equiv(replaceFree(left)(aX, v(fml)), right)
    }

    axiomLookupBaseT(axiomName, subst, alpha, axiomInstance)
  }

  /**
   * Creates a tactic to decompose quantifiers.
 *
   * @return The tactic.
   */
  @deprecated
  def decomposeQuanT = new PositionTactic("Decompose Quantifiers") {
    override def applies(s: Sequent, pos: Position): Boolean = {
      var res = false
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if(p == pos.inExpr) Left(None) else Right(e)
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Forall(vars, f) if vars.length > 1 => res = true
            case Exists(vars, f) if vars.length > 1 => res = true
            case _ => res = false
          }
          Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos))
      res
    }

    override def apply(p: Position): Tactic = ??? /*new ApplyRule(DecomposeQuantifiers(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }*/
  }

  /**
   * Creates a new tactic for skolemization.
 *
   * @return The skolemization tactic.
   */
  def skolemizeT: PositionTactic = skolemizeT(forceUniquify = false)
  def skolemizeT(forceUniquify: Boolean): PositionTactic = skolemize(forceUniquify, toFunctionSymbol = false)
  def skolemizeToFnT: PositionTactic = skolemizeToFnT(forceUniquify = false)
  def skolemizeToFnT(forceUniquify: Boolean): PositionTactic = skolemize(forceUniquify, toFunctionSymbol = true)

  private def skolemize(forceUniquify: Boolean, toFunctionSymbol: Boolean): PositionTactic =
      new PositionTactic("Skolemize") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case Forall(_, _) => !p.isAnte
      case Exists(_, _) => p.isAnte
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      import BindingAssessment.allNamesExceptAt
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Forall(vars, phi) =>
          val rename =
            if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT

          val substToFn = if (toFunctionSymbol) {
            val futureVars =
              if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) vars.map(v => freshNamedSymbol(v, node.sequent))
              else vars
            val subst = futureVars.map(v => SubstitutionPair(FuncOf(Function(v.name, v.index, Unit, v.sort), Nothing), v)).toList
            val futurePhi =
              if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty)
                vars.foldRight(phi)((a, b) => replace(b)(a.asInstanceOf[Term], freshNamedSymbol(a, node.sequent).asInstanceOf[Term]))
              else phi
            val desiredResult = futureVars.foldRight(futurePhi)((a, b) => replace(b)(a.asInstanceOf[Term], FuncOf(Function(a.name, a.index, Unit, a.sort), Nothing)))
            uniformSubstT(subst, Map(futurePhi -> desiredResult))
          } else NilT

          Some(rename ~ new ApplyRule(new Skolemize(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          } ~ substToFn)
        case Exists(vars, phi) =>
          val rename =
            if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT

          val substToFn = if (toFunctionSymbol) {
            val futureVars =
              if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) vars.map(v => freshNamedSymbol(v, node.sequent))
              else vars
            val subst = futureVars.map(v => SubstitutionPair(FuncOf(Function(v.name, v.index, Unit, v.sort), Nothing), v)).toList
            val futurePhi =
              if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty)
                vars.foldRight(phi)((a, b) => replace(b)(a.asInstanceOf[Term], freshNamedSymbol(a, node.sequent).asInstanceOf[Term]))
              else phi
            val desiredResult = futureVars.foldRight(futurePhi)((a, b) => replace(b)(a.asInstanceOf[Term], FuncOf(Function(a.name, a.index, Unit, a.sort), Nothing)))
            uniformSubstT(subst, Map(futurePhi -> desiredResult))
          } else NilT

          Some(rename ~ new ApplyRule(new Skolemize(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          } ~ substToFn)
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  val uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    def getBoundVariables(s: Sequent, p: Position): Option[Seq[(String, Option[Int])]] = s(p) match {
      case Forall(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case _ => ???
      })
      case Exists(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case _ => ???
      })
      case Box(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case Box(AssignAny(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case Diamond(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case Diamond(AssignAny(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case a => None
    }

    override def applies(s: Sequent, p: Position): Boolean = (p.inExpr == HereP) && getBoundVariables(s, p).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import BindingAssessment.{allNames,allNamesExceptAt}
        getBoundVariables(node.sequent, p) match {
          case Some(s) =>
            var otherVars = allNamesExceptAt(node.sequent, p).map((n: NamedSymbol) => (n.name, n.index)) ++ s.distinct
            val pVars = allNames(node.sequent(p)).map((n: NamedSymbol) => (n.name, n.index))
            val res: Seq[Option[Tactic]] = for((n, idx) <- s.distinct) yield {
              val vars = otherVars.filter(_._1 == n) ++ pVars.filter(_._1 == n)
              //require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
              // we do not have to rename if there are no name clashes
              if (vars.size > 0) {
                val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
                  case Some(a) => i match {
                    case Some(b) => if (a < b) Some(b) else Some(a)
                    case None => Some(a)
                  }
                  case None => i
                })
                val tIdx: Option[Int] = maxIdx match {
                  case None => Some(0)
                  case Some(a) => Some(a + 1)
                }
                otherVars = otherVars ++ Seq((n, tIdx))
                Some(alphaRenamingT(n, idx, n, tIdx)(p))
              } else {
                None
              }
            }
            val tactic = res.flatten.reduceRight(seqT)
            Some(tactic)
          case None => None
        }
      }
    }

  }
}
