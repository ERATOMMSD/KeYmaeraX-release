package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
 * [[DifferentialTactics]] provides tactics for differential equations.
 * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
object DifferentialTactics {

  /**
   * Differential effect: exhaustively extracts differential equations from an atomic ODE or an ODE system into
   * differential assignments.
   * {{{
   *   G |- [{x'=f(??)&H(??)}][x':=f(??);]p(??), D
   *   -------------------------------------------
   *   G |- [{x'=f(??)&H(??)}]p(??), D
   * }}}
   * @example{{{
   *    |- [{x'=1}][x':=1;]x>0
   *    -----------------------DE(1)
   *    |- [{x'=1}]x>0
   * }}}
   * @example{{{
   *    |- [{x'=1, y'=x & x>0}][y':=x;][x':=1;]x>0
   *    -------------------------------------------DE(1)
   *    |- [{x'=1, y'=x & x>0}]x>0
   * }}}
   */
  lazy val DE: DependentPositionTactic = new DependentPositionTactic("DE") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = if (RenUSubst.semanticRenaming) {
        if (isODESystem(sequent, pos)) {
          DESystemStep_SemRen(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          useAt("DE differential effect")(pos)
        }
      } else {
        import ProofRuleTactics.contextualize
        //@todo wrap within a CE to make sure it also works in context
        if (isODESystem(sequent, pos)) {
          if (HilbertCalculus.INTERNAL) TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(sequent, pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          if (HilbertCalculus.INTERNAL) useAt("DE differential effect")(pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)
        }
      }

      private def predictor(fml: Formula): Formula = fml match {
        case Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p) =>
          Box(
            ODESystem(DifferentialProduct(c, AtomicODE(xp, t)), h),
            Box(DiffAssign(xp, t), p)
          )

        case Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p) =>
          Box(
            ODESystem(AtomicODE(xp, t), h),
            Box(DiffAssign(xp, t), p)
          )
        case _ => println("Unsure how to predict DE outcome for " + fml); ???
      }
    }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    // semanticRenaming
    private lazy val DESystemStep_SemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
              Box(DiffAssign(d, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aH = PredOf(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConst("c")
            val aP = PredOf(Function("p", None, Real, Bool), Anything)
            val aX = Variable("x_")

            val subst = USubst(SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) ::
              SubstitutionPair(aH, h) :: Nil)
            val uren = ProofRuleTactics.uniformRenaming(aX, x)
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(s"[{${d.prettyString}=f(??),c&H(??)}]p(??) <-> [{c,${d.prettyString}=f(??)&H(??)}][${d.prettyString}:=f(??);]p(??)".asFormula))

            cutLR(g)(pos) <(
              /* use */ skip,
              //@todo conditional commuting (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) instead?
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) &
              TactixLibrary.US(subst, TactixLibrary.uniformRenameF(aX, x)(AxiomInfo("DE differential effect (system)").provable)))
              //TactixLibrary.US(subst, "DE differential effect (system)"))
        }
      }
    }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    // !semanticRenaming
    private lazy val DESystemStep_NoSemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(xp, t)), h),
              Box(DiffAssign(xp, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aH = PredOf(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConst("c")
            val aP = PredOf(Function("p", None, Real, Bool), Anything)
            val aX = Variable("x_", None, Real)

            val uren = URename(x, aX)

            val subst = USubst(SubstitutionPair(aF, t) :: SubstitutionPair(aC, uren(c)) :: SubstitutionPair(aP, uren(p)) ::
              SubstitutionPair(aH, uren(h)) :: Nil)
            //            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(s"[{${xp.prettyString}=f(??),c&H(??)}]p(??) <-> [{c,${xp.prettyString}=f(??)&H(??)}][${xp.prettyString}:=f(??);]p(??)".asFormula))
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms("DE differential effect (system)")))

            if (true || DEBUG) println("DE: manual " + subst + " above " + uren + " to prove " + sequent.prettyString)

            cutLR(g)(pos) <(
              /* use */ skip,
              /* show */ cohide('Rlast) & equivifyR(1) & (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) &
              ProofRuleTactics.uniformRenaming(x, aX) & US(subst, "DE differential effect (system)"))

          case Some(f@Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p)) =>
            val g = Box(
              ODESystem(AtomicODE(xp, t), h),
              Box(DiffAssign(xp, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aQ = PredOf(Function("q", None, Real, Bool), Anything)
            val aP = PredOf(Function("p", None, Real, Bool), Anything)
            val aX = Variable("x_", None, Real)

            val uren = URename(x, aX)

            val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aP, uren(p)) ::
              SubstitutionPair(aQ, uren(h)) :: Nil
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms("DE differential effect")))

            if (true || DEBUG) println("DE: manual " + USubst(subst) + " above " + uren + " to prove " + sequent.prettyString)

            cutLR(g)(pos) <(
              /* use */ skip,
              /* show */ cohide('Rlast) & equivifyR(1) & (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) &
              ProofRuleTactics.uniformRenaming(x, aX) & ??? /*@todo US(USubst(subst), origin)*/ & byVerbatim("DE differential effect"))

        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
   * @param qeTool Quantifier elimination tool for final QE step of tactic.
   * @param auto One of 'none, 'diffInd, 'full. Whether or not to automatically close and use DE, DW.
   *             'none: behaves as DI rule per cheat sheet
   *                    {{{
   *                      G, q(x) |- p(x), D    G, q(x) |- [x'=f(x)&q(x)](p(x))', D
   *                      ---------------------------------------------------------
   *                                  G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   *             'diffInd: behaves as diffInd rule per cheat sheet
   *                    {{{
   *                      G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p(x')    @note derive on (p(x))' already done
   *                      ----------------------------------------------
   *                                  G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   *             'full: tries to close everything after diffInd rule
   *                    {{{
   *                        *
   *                      --------------------------
   *                      G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   * @example{{{
   *         *
   *    ---------------------diffInd(qeTool, 'full)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
   *    --------------------------------------------diffInd(qeTool, 'diffInd)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5, true |- x>=5    x>=5, true |- [{x'=2}](x>=5)'
   *    ---------------------------------------------------diffInd(qeTool, 'none)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *    -------------------------------------diffInd(qeTool, 'full)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  def diffInd(implicit qeTool: QETool, auto: Symbol = 'full): DependentPositionTactic = new DependentPositionTactic("diffInd") {
    require(auto == 'none || auto == 'diffInd || auto == 'full, "Expected one of ['none, 'diffInd, 'full] automation values, but got " + auto)
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + sequent.sub(pos))
        if (pos.isTopLevel) {
          val t = DI(pos) &
            (implyR(pos) & andR(pos)) <(
              if (auto == 'full) close | QE else skip,
              if (auto != 'none) {
                //@note derive before DE to keep positions easier
                derive(pos + PosInExpr(1 :: Nil)) &
                DE(pos) &
                (if (auto == 'full) Dassignb(pos + PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & (close | QE)
                 else {
                  assert(auto == 'diffInd)
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                  abstractionb(pos) & (allR(pos)*@TheType()) & ?(implyR(pos)) }) partial
              } else skip
              )
          if (auto == 'full) Dconstify(t)(pos)
          else t
        } else {
          val t = DI(pos) &
            (if (auto != 'none) {
              shift(PosInExpr(1 :: 1 :: Nil), new DependentPositionTactic("Shift") {
                override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                  override def computeExpr(sequent: Sequent): BelleExpr = {
                    //@note derive before DE to keep positions easier
                    shift(PosInExpr(1 :: Nil), derive)(pos) &
                      DE(pos) &
                      (if (auto == 'full) shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                        //@note DW after DE to keep positions easier
                        (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                        abstractionb(pos)
                      else abstractionb(pos))
                  }
                }
              }
              )(pos)
            } else ident)
          if (auto == 'full) Dconstify(t)(pos)
          else t
        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
   * @example{{{
   *    x>=5 |- x>=5    x>=5 |- [{x'=2}](x>=5)'
   *    ---------------------------------------DIRule(qeTool)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true->x>=5&[{x'=2}](x>=5)')
   *    ---------------------------------------------DIRule(qeTool)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  lazy val DIRule: DependentPositionTactic = diffInd(null, 'none)
  lazy val diffIndRule: DependentPositionTactic = diffInd(null, 'diffInd)

  /**
   * Differential cut. Use special function old(.) to introduce a ghost for the starting value of a variable that can be
   * used in the evolution domain constraint.
   * @example{{{
   *         x>0 |- [{x'=2&x>0}]x>=0     x>0 |- [{x'=2}]x>0
   *         -----------------------------------------------diffCut("x>0".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, x_0=x |- [{x'=2&x>=x_0}]x>=0     x>0, x_0=x |- [{x'=2}]x>=x_0
   *         -------------------------------------------------------------------diffCut("x>=old(x)".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0&x>=x_0}]x>=0
   *                x>0, v>=0 |- [{x'=v,v'=1}]v>=0
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0}]x>=x_0
   *         --------------------------------------------------diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1)
   *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   * }}}
   * @param formulas The formulas to cut in as evolution domain constraint.
   * @return The tactic.
   */
  def diffCut(formulas: Formula*): DependentPositionTactic = new DependentPositionTactic("diff cut") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = nestDCs(formulas.map(ghostDC(_, pos, sequent)))
    }

    /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
    private def ghostDC(f: Formula, pos: Position, sequent: Sequent): BelleExpr = {
      val ov = oldVars(f)
      if (ov.isEmpty) {
        DC(f)(pos)
      } else {
        val ghosts: Set[((Variable, Variable), BelleExpr)] = ov.map(old => {
          val ghost = TacticHelper.freshNamedSymbol(Variable(old.name), sequent)
          (old -> ghost,
            discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquational(pos))
        })
        ghosts.map(_._2).reduce(_ & _) & DC(replaceOld(f, ghosts.map(_._1).toMap))(pos)
      }
    }

    /** Turns a list of diff cuts (with possible 'old' ghost creation) tactics into nested DCs */
    private def nestDCs(dcs: Seq[BelleExpr]): BelleExpr = {
      dcs.head <(
        /* use */ (if (dcs.tail.nonEmpty) nestDCs(dcs.tail) partial else skip) partial,
        /* show */ skip
        )
    }

    /** Returns a set of variables that are arguments to a special 'old' function */
    private def oldVars(fml: Formula): Set[Variable] = {
      var oldVars = Set[Variable]()
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
          case FuncOf(Function("old", None, Real, Real), v: Variable) => oldVars += v; Left(None)
          case _ => Left(None)
        }
      }, fml)
      oldVars
    }

    /** Replaces any old(.) with . in formula fml */
    private def replaceOld(fml: Formula, ghostsByOld: Map[Variable, Variable]): Formula = {
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
          case FuncOf(Function("old", None, Real, Real), v: Variable) => Right(ghostsByOld(v))
          case _ => Left(None)
        }
      }, fml) match {
        case Some(g) => g
      }
    }
  }

  /**
   * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
   * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
   * formulas are differential invariants. Fails if diffInd cannot prove invariants.
   * @example{{{
   *         x>0 |- [{x'=2&x>0}]x>=0
   *         ------------------------diffInvariant("x>0".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, x_0=x |- [{x'=2&x>x_0}]x>=0
   *         ---------------------------------diffInvariant("x>old(x)".asFormula)(1)
   *                x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1 & v>=0&x>x_0}]x>=0
   *         ---------------------------------------------------diffInvariant("v>=0".asFormula, "x>old(x)".asFormula)(1)
   *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   * }}}
   * @param formulas The differential invariants to cut in as evolution domain constraint.
   * @return The tactic.
   * @see [[diffCut]]
   * @see [[diffInd]]
   */
  def diffInvariant(qeTool: QETool, formulas: Formula*): DependentPositionTactic = new DependentPositionTactic("diff invariant") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        //@note assumes that first subgoal is desired result, see diffCut
        val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd(qeTool)('Rlast))
        diffCut(formulas: _*)(pos) <(diffIndAllButFirst:_*) partial
      }
    }
  }

  /**
   * Turns things that are constant in ODEs into function symbols.
   * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
   * @return The tactic.
   */
  def Dconstify(inner: BelleExpr): DependentPositionTactic = new DependentPositionTactic("IDC introduce differential constants") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Box(ode@ODESystem(_, _), p)) =>
          val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])
          consts.foldLeft[BelleExpr](inner)((tactic, c) =>
            let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
        case Some(Diamond(ode@ODESystem(_, _), p)) =>
          val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])
          consts.foldLeft[BelleExpr](inner)((tactic, c) =>
            let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
      }
    }
  }

  /**
   * Differential ghost. Adds an auxiliary differential equation y'=a*y+b
   * @example{{{
   *         |- \exists y [{x'=2,y'=0*y+1}]x>0
   *         ---------------------------------- DG("y".asVariable, "0".asTerm, "1".asTerm)(1)
   *         |- [{x'=2}]x>0
   * }}}
   * @example{{{
   *         |- \exists y [{x'=2,y'=f()*y+g() & x>=0}]x>0
   *         --------------------------------------------- DG("y".asVariable, "f()".asTerm, "g()".asTerm)(1)
   *         |- [{x'=2 & x>=0}]x>0
   * }}}
   * @param y The differential ghost variable.
   * @param a The linear term in y'=a*y+b.
   * @param b The constant term in y'=a*y+b.
   * @return The tactic.
   */
  def DG(y: Variable, a: Term, b: Term): DependentPositionTactic = "DG" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>
      cutR(Exists(y::Nil, Box(ODESystem(DifferentialProduct(c, AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b))), h), p)))(pos.checkSucc.top) <(
        /* use */ skip,
        /* show */ cohide(pos.top) &
          /* rename first, otherwise byUS fails */ ProofRuleTactics.uniformRenaming("y".asVariable, y) &
          equivifyR('Rlast) & commuteEquivR('Rlast) & byUS("DG differential ghost")
        )
  })

  /**
   * Syntactically derives a differential of a variable to a differential symbol.
   * {{{
   *   G |- x'=f, D
   *   --------------
   *   G |- (x)'=f, D
   * }}}
   * @example{{{
   *   |- x'=1
   *   ----------Dvariable(1, 0::Nil)
   *   |- (x)'=1
   * }}}
   * @example{{{
   *   |- [z':=1;]z'=1
   *   ------------------Dvariable(1, 1::0::Nil)
   *   |- [z':=1;](z)'=1
   * }}}
   * @incontext
   * @todo could probably simplify implementation by picking atomic formula, using "x' derive var" and then embedding this equivalence into context by CE.
    *       Or, rather, by using CE directly on a "x' derive var" provable fact (z)'=1 <-> z'=1.
   */
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("x' derive variable") {
    private val OPTIMIZED = true //@todo true
    private val axiom = AxiomInfo("x' derive var commuted")
    private val (keyCtx:Context[_],keyPart) = axiom.formula.at(PosInExpr(1::Nil))
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {

      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Differential(x: Variable)) =>
          if (OPTIMIZED) {
            if (DEBUG) println("Dvariable " + keyPart + " on " + x)
            val fact = UnificationMatch.apply(keyPart, Differential(x)).toForward(axiom.provable)
            CEat(fact)(pos)
          } else {
            val withxprime: Formula = sequent.replaceAt(pos, DifferentialSymbol(x)).asInstanceOf[Formula]
            val axiom = s"\\forall ${x.prettyString} (${x.prettyString})' = ${x.prettyString}'".asFormula
            cutLR(withxprime)(pos.topLevel) <(
              /* use */ skip,
              /* show */ cohide(pos.top) & CMon(formulaPos(sequent(pos.top), pos.inExpr)) & cut(axiom) <(
              useAt("all eliminate")(-1) & eqL2R(-1)(1) & useAt("-> self")(1) & close,
              cohide('Rlast) & byUS(DerivedAxioms.Dvariable))
              )
          }
        }
      }

    /** Finds the first parent of p in f that is a formula. Returns p if f at p is a formula. */
    private def formulaPos(f: Formula, p: PosInExpr): PosInExpr = {
      f.sub(p) match {
        case Some(_: Formula) => p
        case _ => formulaPos(f, p.parent)
      }
    }
  }

  /**
   * Unpacks the evolution domain of an ODE at time zero. Useful for proofs that rely on contradictions with other
   * conditions at time zero preventing continuous evolution in the ODE.
   * {{{
   *  x<0, x>=0 |- [x'=3,y'=2 & x>=0]y>0
   *  -----------------------------------diffUnpackEvolutionDomainInitially(1)
   *        x<0 |- [x'=3,y'=2 & x>=0]y>0
   * }}}
   */
  lazy val diffUnpackEvolutionDomainInitially: DependentPositionTactic = "diffUnpackEvolDomain" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(ODESystem(_, q), _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffUnpackEvolDomain only at top-level in succedent")
      cut(q) <(
        /* use */ skip,
        /* show */ DI(pos) & implyR(pos) & closeId
        )
  })

  def diffSolve(solution: Option[Formula] = None, preDITactic: BelleExpr = skip)(implicit tool: DiffSolutionTool with QETool): DependentPositionTactic = "diffSolve" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(odes: ODESystem, _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffSolve only at top-level in succedent")

      val time: Variable = TacticHelper.freshNamedSymbol(Variable("t_", None, Real), sequent)
      val introTime =
          DG(time, "0".asTerm, "1".asTerm)(pos) &
            DLBySubst.assignbExists("0".asTerm)(pos) &
            DLBySubst.assignEquational(pos)

      def createTactic(ode: ODESystem, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                       diffEqPos: SeqPos): BelleExpr = {
        val initialGhosts = (primedSymbols(ode.ode) + time).foldLeft(skip)((a, b) =>
          a & (discreteGhost(b)(diffEqPos) & DLBySubst.assignEquational(diffEqPos)))

        // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
        val flatSolution = flattenConjunctions(solution).
          sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)

        diffUnpackEvolutionDomainInitially(diffEqPos) &
          initialGhosts &
          diffInvariant(tool, flatSolution:_*)(diffEqPos) &
          // initial ghosts are at the end of the antecedent
          exhaustiveEqR2L(hide=true)('Llast)*flatSolution.size &
          diffWeaken(diffEqPos)
      }

      // initial values (from only the formula at pos, because allR will increase index of other occurrences elsewhere in the sequent)
      val iv: Map[Variable, Variable] =
        primedSymbols(odes.ode).map(v => v -> TacticHelper.freshNamedSymbol(v, sequent(pos.top))).toMap

      val theSolution = solution match {
        case sol@Some(_) => sol
        case None => tool.diffSol(odes.ode, time, iv)
      }

      val diffEqPos = SuccPos(sequent.succ.length-1) //@note introTime moves ODE to the end of the succedent
      theSolution match {
        // add relation to initial time
        case Some(s) =>
          val sol = And(s, GreaterEqual(time, Number(0)))
          introTime & createTactic(odes, sol, time, iv, diffEqPos)
        case None => throw new BelleError("No solution found")
      }

  })

  /** diffWeaken by diffCut(consts) <(diffWeakenG, V&close) */
  lazy val diffWeaken: DependentPositionTactic = "diffWeaken" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(a, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      def constAnteConditions(sequent: Sequent, taboo: Set[NamedSymbol]): IndexedSeq[Formula] = {
        sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
      }
      val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)

      if (consts.nonEmpty) {
        // andL puts both conjuncts at the end of ante -> andL second-to-last (except first, where there's only 1 formula)
        val dw = diffWeakenG(pos) & implyR(1) & andL(-1) & andLSecondToLast*(consts.size-1) &
          // original evolution domain is in second-to-last ante position
          implyRi(AntePos(consts.size-1), SuccPos(0)) partial

        //@note assumes that first subgoal is desired result, see diffCut
        val vAllButFirst = dw +: Seq.tabulate(consts.length)(_ => V('Rlast) & close)
        //@note cut in reverse so that andL after diffWeakenG turns them into the previous order
        diffCut(consts.reverse: _*)(pos) <(vAllButFirst:_*) partial
      } else {
        diffWeakenG(pos)
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "diffWeakenG" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(1) & G
  })

  /** Helper for diffWeaken: andL the second-to-last formula */
  private lazy val andLSecondToLast: DependentTactic = new SingleGoalDependentTactic("andL-2nd-to-last") {
    override def computeExpr(sequent: Sequent): BelleExpr = andL(-(sequent.ante.length-1))
  }

  private def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }

  private def primedSymbols(ode: DifferentialProgram) = {
    var primedSymbols = Set[Variable]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
        case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
        case _ => Left(None)
      }
    }, ode)
    primedSymbols
  }

  /** Indicates whether there is a proper ODE System at the indicated position of a sequent with >=2 ODEs */
  private val isODESystem: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ODESystem(_:DifferentialProduct,_), _))     => true
      case Some(Diamond(ODESystem(_:DifferentialProduct,_), _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Computes the dimension of ODE at indicated position of a sequent */
  private val getODEDim: (Sequent,Position)=>Int = (sequent,pos) => {
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).symbols.count(_.isInstanceOf[DifferentialSymbol])
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => odeDim(ode)
      case Some(Diamond(ode: ODESystem, _)) => odeDim(ode)
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether the ODE at indicated position of a sequent has a nontrivial domain */
  private val hasODEDomain: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => ode.constraint != True
      case Some(Diamond(ode: ODESystem, _)) => ode.constraint != True
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }
}
