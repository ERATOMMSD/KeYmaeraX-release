package edu.cmu.cs.ls.keymaerax.btactics

import java.math.{MathContext, RoundingMode}

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.requireOneSubgoal

import scala.collection.immutable._

/** Interval Arithmetic
  *
  * @author Fabian Immler
  */
object IntervalArithmeticV2 {

  def mathematicaFriendly(d: BigDecimal) : Term =
    Times(Number(BigDecimal(d.bigDecimal.unscaledValue())), Power(Number(10), Number(-d.scale)))
  def mathematicaFriendly(n: Number) : Term = mathematicaFriendly(n.value)

  private def eval(t: Term) : BigDecimal = BigDecimalQETool.eval(t)

  def round_down(prec: Int)(x: BigDecimal) : BigDecimal = x.round(new MathContext(prec, RoundingMode.FLOOR))
  def round_up(prec: Int)(x: BigDecimal) : BigDecimal = x.round(new MathContext(prec, RoundingMode.CEILING))
  def round_down_term(prec: Int)(x: Term) : Term = mathematicaFriendly(round_down(prec)(eval(x)))
  def round_up_term(prec: Int)(x: Term) : Term = mathematicaFriendly(round_up(prec)(eval(x)))

  private def div_down(prec: Int)(x: BigDecimal, y: BigDecimal) : BigDecimal =
    x.bigDecimal.divide(y.bigDecimal, new MathContext(prec, RoundingMode.FLOOR))
  private def div_up(prec: Int)(x: BigDecimal, y: BigDecimal) : BigDecimal =
    x.bigDecimal.divide(y.bigDecimal, new MathContext(prec, RoundingMode.CEILING))

  private def div_endpoints(prec: Int)(la: BigDecimal, ua: BigDecimal, lb: BigDecimal, ub: BigDecimal) : (BigDecimal, BigDecimal) = {
    val pairs = (List(la, la, ua, ua), List(lb, ub, lb, ub)).zipped
    val lowers = pairs map ((a, b) => div_down(prec)(a, b))
    val uppers = pairs map ((a, b) => div_up(prec)(a, b))
    (lowers.reduceLeft(_.min(_)), uppers.reduceLeft(_.max(_)))
  }

  private def round2(prec: Int)(l: BigDecimal, u: BigDecimal) : (BigDecimal, BigDecimal) =
    (round_down(prec)(l), round_up(prec)(u))
  private def mult_endpoints(prec: Int)(la: BigDecimal, ua: BigDecimal, lb: BigDecimal, ub: BigDecimal) = {
    val endpoints = List(la * lb, la * ub, ua * lb, ua * ub) // not really efficient...
    round2(prec)(endpoints.reduceLeft(_.min(_)), endpoints.reduceLeft(_.max(_)))
  }

  private val t_f = "f_()".asTerm
  private val t_g = "g_()".asTerm
  private val t_h = "h_()".asTerm
  private val t_ff = "ff_()".asTerm
  private val t_gg = "gg_()".asTerm
  private val t_F = "F_()".asTerm
  private val t_G = "G_()".asTerm

  private lazy val leRefl = proveBy("F_() <= F_()".asFormula,
    useAt("<= refl", PosInExpr(0::Nil))(1) & prop & done)
  private lazy val negDownSeq = proveBy("f_()<=F_() & (h_()<=-F_()<->true) ==> h_()<=-f_()".asSequent,
    useAt("<=neg down", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val negUpSeq = proveBy("ff_()<=f_() & (-ff_()<=h_()<->true) ==> -f_()<=h_()".asSequent,
    useAt("neg<= up", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val plusDownSeq = proveBy("(ff_()<=f_() & gg_()<=g_()) & (h_()<=ff_()+gg_()<->true) ==> h_()<=f_()+g_()".asSequent,
    useAt("<=+ down", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val plusUpSeq = proveBy("(f_()<=F_() & g_()<=G_()) & (F_()+G_()<=h_()<->true) ==> f_()+g_()<=h_()".asSequent,
    useAt("+<= up", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val minusDownSeq = proveBy("(ff_()<=f_() & g_()<=G_()) & (h_()<=ff_()-G_()<->true) ==> h_()<=f_()-g_()".asSequent,
    useAt("<=- down", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val minusUpSeq = proveBy("(f_()<=F_() & gg_()<=g_()) & (F_()-gg_()<=h_()<->true) ==> f_()-g_()<=h_()".asSequent,
    useAt("-<= up", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val multUpSeq = proveBy(
    "(((ff_()<=f_() & f_()<=F_()) & gg_()<=g_() & g_()<=G_()) & ((ff_()*gg_()<=h_() & ff_()*G_()<=h_() & F_()*gg_()<=h_() & F_()*G_()<=h_())<->true)) ==> f_()*g_()<=h_()".asSequent,
    useAt("*<= up", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val multDownSeq = proveBy(
    "(((ff_()<=f_() & f_()<=F_()) & gg_()<=g_() & g_()<=G_()) & ((h_()<=ff_()*gg_() & h_()<=ff_()*G_() & h_()<=F_()*gg_() & h_()<=F_()*G_())<->true)) ==> h_()<=f_()*g_()".asSequent,
    useAt("<=* down", PosInExpr(1::Nil))(1) & prop & done)
  private lazy val divideUpSeq = proveBy(
    "((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((((G_()<0 | 0<gg_()) & (ff_()/gg_()<=h_() & ff_()/G_()<=h_() & F_()/gg_()<=h_() & F_()/G_()<=h_())))<->true) ==> f_()/g_()<=h_()".asSequent, QE & done)
  private lazy val divideDownSeq = proveBy(
    "((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((((G_()<0 | 0<gg_()) & (h_()<=ff_()/gg_() & h_()<=ff_()/G_() & h_()<=F_()/gg_() & h_()<=F_()/G_())))<->true) ==> h_()<=f_()/g_()".asSequent, QE & done)
  private val maxPower = 10
  private lazy val powerDownSeq =
    (1 to maxPower/2) flatMap (n =>
      proveBy(("((ff_()<=f_() & f_()<=F_()) & (((h_()<=ff_()^"+(2*n-1)+" & h_()<=F_()^"+(2*n-1)+"))<->true)) ==> h_()<=f_()^"+(2*n-1)+"").asSequent, QE & done)::
        proveBy(("((ff_()<=f_() & f_()<=F_()) & ((((0<=ff_() & h_()<=ff_()^"+(2*n)+") | (F_()<0 & h_()<=F_()^"+(2*n)+")))<->true)) ==> h_()<=f_()^"+(2*n)).asSequent, QE & done)::
        Nil
      )
  private lazy val powerUpSeq =
    (1 to maxPower) map (n =>
      proveBy(("((ff_()<=f_() & f_()<=F_()) & (((ff_()^"+n+" <= h_() & F_()^"+n+" <=h_()))<->true)) ==> f_()^"+n+" <=h_()").asSequent,
        QE & done))

  /*
  fml |- P      G |- fml
  ----------------------
    G |- P
   */
  private def CutHide(fml: Formula)(prv: ProvableSig) = {
    require(prv.subgoals.length == 1)
    require(prv.subgoals(0).succ.length == 1)
    (0 until prv.subgoals(0).ante.length).foldLeft(prv.apply(Cut(fml), 0).apply(HideRight(SuccPos(0)), 1)) {
      (p, _) =>
        p.apply(HideLeft(AntePos(0)), 0)
    }
  }

  /** Proves Bounds on all Subexpressions using Interval Arithmetic.
    *
    * @param prec       decimal precision
    * @param qeTool     Tool for QE, it will only be called on formulas without variables and without quantifiers
    * @param assms      list of closed constraints on variables
    * @param lowers     already computed bounds (can be used for cached results)
    * @param uppers     dito
    * @param t          term whose subexpressions shall be bounded
    * @return bounds on all subexpressions
  * */
  def proveBounds(prec: Int)
                 (qeTool: QETool)
                 (assms: IndexedSeq[Formula])
                 (lowers: HashMap[Term, ProvableSig], uppers: HashMap[Term, ProvableSig])
                 (t: Term): (HashMap[Term, ProvableSig], HashMap[Term, ProvableSig])
  = {
    if (lowers.isDefinedAt(t) && uppers.isDefinedAt(t)) (lowers, uppers)
    else t match {
      case v if PolynomialArith.isVar(v) =>
        val idx = assms.indexWhere(fml => fml match { case LessEqual(_, w) => v == w })
        val newlowers = if (idx >= 0) {
          val seq = Sequent(assms, IndexedSeq(assms(idx)))
          val prv = ProvableSig.startProof(seq).apply(Close(AntePos(idx), SuccPos(0)), 0)
          lowers.updated(t, prv)
        } else {
          throw new RuntimeException ("TODO: implement less/equal implications")
        }
        val IDX = assms.indexWhere(fml => fml match { case LessEqual(w, _) => v == w })
        val newuppers = if (IDX >= 0) {
          val seq = Sequent(assms, IndexedSeq(assms(IDX)))
          val prv = ProvableSig.startProof(seq).apply(Close(AntePos(IDX), SuccPos(0)), 0)
          uppers.updated(t, prv)
        } else {
          throw new RuntimeException ("TODO: implement less/equal implications")
        }
        (newlowers, newuppers)
      case n: Number =>
        val refl = (ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(n, n))))).
          apply(CoHideRight(SuccPos(0)), 0).
          apply(leRefl.apply(USubst(SubstitutionPair(t_F, n) :: Nil)), 0)
        (lowers.updated(n, refl), uppers.updated(n, refl))
      case Neg(a) =>
        val f = a
        val (lowers2, uppers2) = proveBounds(prec)(qeTool)(assms)(lowers, uppers)(f)
        val ff_prv = lowers2(f)
        val F_prv = uppers2(f)
        val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val F_fml = F_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val ff = ff_fml.left
        val F = F_fml.right
        val h = round_down_term(prec)(Neg(F))
        val H = round_up_term(prec)(Neg(ff))
        val negDown = negDownSeq.apply(USubst(
          SubstitutionPair(t_h, h) ::
            SubstitutionPair(t_f, f) ::
            SubstitutionPair(t_F, F) :: Nil))
        val negUp = negUpSeq.apply(USubst(
          SubstitutionPair(t_h, H) ::
            SubstitutionPair(t_f, f) ::
            SubstitutionPair(t_ff, ff) :: Nil))

        val h_le = ProvableSig.proveArithmetic(qeTool, negDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
        val H_le = ProvableSig.proveArithmetic(qeTool, negUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

        val h_prv = (CutHide(negDown.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
          apply(negDown, 0).
          apply(AndRight(SuccPos(0)), 0).
          apply(CoHideRight(SuccPos(0)), 1).
          apply(h_le, 1).
          apply(F_prv, 0)
        val H_prv = (CutHide(negUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
          apply(negUp, 0).
          apply(AndRight(SuccPos(0)), 0).
          apply(CoHideRight(SuccPos(0)), 1).
          apply(H_le, 1).
          apply(ff_prv, 0)
        (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
      case binop: BinaryCompositeTerm =>
        val f = binop.left
        val g = binop.right
        val (lowers1, uppers1) = proveBounds(prec)(qeTool)(assms)(lowers, uppers)(f)
        val (lowers2, uppers2) = proveBounds(prec)(qeTool)(assms)(lowers1, uppers1)(g)
        val ff_prv = lowers2(f)
        val gg_prv = lowers2(g)
        val F_prv = uppers2(f)
        val G_prv = uppers2(g)
        val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val gg_fml = gg_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val F_fml = F_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val G_fml = G_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val ff = ff_fml.left
        val gg = gg_fml.left
        val F = F_fml.right
        val G = G_fml.right
        binop match {
          case _: Plus =>
            val h = round_down_term(prec)(Plus(ff, gg))
            val H = round_up_term(prec)(Plus(F, G))
            val plusDown = plusDownSeq.apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) :: Nil))
            val plusUp = plusUpSeq.apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))

            val h_le = ProvableSig.proveArithmetic(qeTool, plusDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_le = ProvableSig.proveArithmetic(qeTool, plusUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

            val h_prv = (CutHide(plusDown.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(plusDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(gg_prv, 1).  // be stable by operating on last subgoal
              apply(ff_prv, 0)
            val H_prv = (CutHide(plusUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(plusUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(G_prv, 1).
              apply(F_prv, 0)
            (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
          case _: Minus =>
            val h = round_down_term(prec)(Minus(ff, G))
            val H = round_up_term(prec)(Minus(F, gg))
            val minusDown = minusDownSeq.apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_G, G) :: Nil))
            val minusUp = minusUpSeq.apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_gg, gg) :: Nil))

            val h_le = ProvableSig.proveArithmetic(qeTool, minusDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_le = ProvableSig.proveArithmetic(qeTool, minusUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

            val h_prv = (CutHide(minusDown.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(minusDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(G_prv, 1).  // be stable by operating on last subgoal
              apply(ff_prv, 0)
            val H_prv = (CutHide(minusUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(minusUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(gg_prv, 1).
              apply(F_prv, 0)
            (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
          case _: Times =>
            // Bounds
            val bnds = mult_endpoints(prec)(eval(ff), eval(F), eval(gg), eval(G))

            val h = mathematicaFriendly(bnds._1)
            val H = mathematicaFriendly(bnds._2)
            val multDown = multDownSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val h_le = ProvableSig.proveArithmetic(qeTool, multDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val ante = multDown.conclusion.ante(0)
            val ff_f_F_gg_g_G = ProvableSig.startProof(Sequent(assms, IndexedSeq(ante.asInstanceOf[And].left))).
              apply(AndRight(SuccPos(0)), 0).
              apply(AndRight(SuccPos(0)), 1).
              apply(G_prv, 2).
              apply(gg_prv, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            val h_prv = (CutHide(ante)(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(multDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(ff_f_F_gg_g_G, 0)

            val multUp = multUpSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val H_le = ProvableSig.proveArithmetic(qeTool, multUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(multUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(multUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(ff_f_F_gg_g_G, 0)
            (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
          case _: Divide =>
            // Bounds
            val bnds = div_endpoints(prec)(eval(ff), eval(F), eval(gg), eval(G))
            val h = mathematicaFriendly(bnds._1)
            val H = mathematicaFriendly(bnds._2)
            val divideDown = divideDownSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val h_le = ProvableSig.proveArithmetic(qeTool, divideDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val ante = divideDown.conclusion.ante(0)
            val ff_f_F_gg_g_G = ProvableSig.startProof(Sequent(assms, IndexedSeq(ante.asInstanceOf[And].left))).
              apply(AndRight(SuccPos(0)), 0).
              apply(AndRight(SuccPos(0)), 1).
              apply(G_prv, 2).
              apply(gg_prv, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            val h_prv = (CutHide(ante)(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(divideDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(ff_f_F_gg_g_G, 0)

            val divideUp = divideUpSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val H_le = ProvableSig.proveArithmetic(qeTool, divideUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(divideUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(divideUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(ff_f_F_gg_g_G, 0)
            (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
          case _: Power =>
            // Lower Bound
            val n = g.asInstanceOf[Number].value.toIntExact
            val h = round_down_term(prec)(Power(ff, g))
            val powerDown = powerDownSeq(n - 1).apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_F, F) :: Nil))
            val h_le = ProvableSig.proveArithmetic(qeTool, powerDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val h_prv = (CutHide(powerDown.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(powerDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)

            // Upper Bound
            val H = round_up_term(prec)(Power(F, g))
            val powerUp = powerUpSeq(n-1).apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_F, F) :: Nil))
            val H_le = ProvableSig.proveArithmetic(qeTool, powerUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(powerUp.conclusion.ante(0))(ProvableSig.startProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(powerUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            (lowers2.updated(t, h_prv), uppers2.updated(t, H_prv))
          case _ =>
            throw new RuntimeException ("TODO: implement more binary operations: " + t)
        }
      case _ =>
        throw new RuntimeException ("TODO: implement more operations: " + t)
    }
  }

  private def proveBoundsDefault(assms: IndexedSeq[Formula], t: Term) = {
    val (lowers, uppers) = proveBounds(5)(ToolProvider.qeTool().get)(assms)(HashMap(), HashMap())(t)
    (lowers(t), uppers(t))
  }

  def intervalCutTerms(terms: List[Term]) : BuiltInTactic = new BuiltInTactic("intervalCutTerms") {
    override def result(provable: ProvableSig): ProvableSig = {
      requireOneSubgoal(provable, name)
      val sequent = provable.subgoals(0)
      val nantes = sequent.ante.length
      val prec = 5
      val qe = ToolProvider.qeTool().get
      val bnds = terms.foldLeft(HashMap[Term, ProvableSig](), HashMap[Term, ProvableSig]())((a, t: Term) =>
        proveBounds(prec)(qe)(sequent.ante)(a._1, a._2)(t))
      val prvs = terms flatMap (t => List(bnds._1(t), bnds._2(t)))
      (prvs, prvs.indices).zipped.foldLeft(provable) {
        (result, prvi) => prvi match {
          case (prv: ProvableSig, i: Int) =>
            (0 until i).foldLeft(result.apply(Cut(prv.conclusion.succ(0)), 0).apply(HideRight(SuccPos(0)), 1)){
              (res, _) => res.apply(HideLeft(AntePos(nantes)), 1)
            }.apply(prv, 1)
        }
      }
    }
  }

  // TODO: I don't really understand the business with InputTactic...
  def intervalCutTerms(terms: Term*): InputTactic = "intervalCutTerms" byWithInputs (terms.toList, intervalCutTerms(terms.toList))

  def intervalCut : DependentPositionTactic = "intervalCut" by { (pos: Position, seq: Sequent) =>
    seq.sub(pos) match {
      case Some(fml: ComparisonFormula) => intervalCutTerms(List(fml.left, fml.right))
      case Some(t: Term) => intervalCutTerms(List(t))
      case _ => throw new BelleThrowable("intervalCut not on ComparisonFormula or Term")
    }
  }

}
