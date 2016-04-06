/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
 * resulting from differential dynamic logic.
 * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2016-03-09
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXAxiomParser

/**
 * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.AxiomIndex]]]]
 */
private[core] object AxiomBase {
  /**
   * KeYmaera X Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @author Andre Platzer
   */
  private[core] def loadAxiomaticRules : immutable.Map[String, (immutable.IndexedSeq[Sequent], Sequent)] = {
    val x = Variable("x_", None, Real)
    val pany = PredOf(Function("p_", None, Real, Bool), Anything)
    val qany = PredOf(Function("q_", None, Real, Bool), Anything)
    val fany = FuncOf(Function("f_", None, Real, Real), Anything)
    val gany = FuncOf(Function("g_", None, Real, Real), Anything)
    val ctxt = Function("ctx_", None, Real, Real) // function symbol
    val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
    // Sort of predicational is really (Real->Bool)->Bool except sort system doesn't know that type.
    val context = Function("ctx_", None, Bool, Bool) // predicational symbol
    val a = ProgramConst("a_")

    Map(
      /**
       * Rule "all generalization".
       * Premise p(x)
       * Conclusion \forall x p(x)
       * End.
       */
      /*("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(px)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), px))))),*/
      /**
       * Rule "all generalization".
       * Premise p(??)
       * Conclusion \forall x p(??)
       * End.
       * @Note generalization of p(x) to p(??) as in Theorem 14
       */
      ("all generalization",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Forall(immutable.Seq(x), pany))))),
      /**
       * Rule "CT term congruence".
       * Premise f_(??) = g_(??)
       * Conclusion ctxT_(f_(??)) = ctxT_(g_(??))
       * End.
       * @derived ("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
       */
      ("CT term congruence",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany)))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(FuncOf(ctxt, fany), FuncOf(ctxt, gany)))))),
      /**
       * Rule "CQ equation congruence".
       * Premise f_(??) = g_(??)
       * Conclusion ctxP_(f_(??)) <-> ctxP_(g_(??))
       * End.
       * {{{
       *      f(x)   =  g(x)
       *   --------------------- CQ
       *    c(f(x)) <-> c(g(x))
       * }}}
       */
      ("CQ equation congruence",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany)))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredOf(ctxf, fany), PredOf(ctxf, gany)))))),
      /**
       * Rule "CE congruence".
       * Premise p_(??) <-> q_(??)
       * Conclusion ctxF_(p_(??)) <-> ctxF_(q_(??))
       * End.
       * {{{
       *       p(x) <-> q(x)
       *   --------------------- CE
       *    C{p(x)} <-> C{q(x)}
       * }}}
       */
      ("CE congruence",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany)))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredicationalOf(context, pany), PredicationalOf(context, qany)))))),
      /**
       * Rule "[] monotone".
       * Premise p(??) ==> q(??)
       * Conclusion [a;]p(??) ==> [a;]q(??)
       * End.
       * @derived useAt("<> diamond") & by("<> monotone")
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       * @see "André Platzer. Differential Hybrid Games."
       */
      ("[] monotone",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Box(a, pany)), immutable.IndexedSeq(Box(a, qany))))),
      /**
       * Rule "<> monotone".
       * Premise p(??) ==> q(??)
       * Conclusion <a;>p(??) ==> <a;>q(??)
       * End.
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       */
      ("<> monotone",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Diamond(a, pany)), immutable.IndexedSeq(Diamond(a, qany))))),
      /**
       * Rule "ind induction".
       * Premise p(??) ==> [a;]p(??)
       * Conclusion p(??) ==> [a*]p(??)
       * {{{
       *     p(x) |- [a]p(x)
       *   --------------------- ind
       *     p(x) |- [{a}*]p(x)
       * }}}
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 17(1), 2015.  Lemma 4.1"
       */
      ("ind induction",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany)))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
      /* UNSOUND FOR HYBRID GAMES */
      /**
       * Rule "Goedel".
       * Premise p(??)
       * Conclusion [a;]p(??)
       * End.
       * {{{
       *       p(??)
       *   ----------- G
       *    [a;]p(??)
       * }}}
       * @NOTE Unsound for hybrid games
       * @TODO Add [a;]true -> to conclusion to make it sound for hybrid games (and then equivalent to [] monotone)
       */
      ("Goedel",
        (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Box(a, pany)))))
    )
  }

  /**
   * Look up an axiom of KeYmaera X,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   * parse the axiom file and add all loaded knowledge to the axioms map.
   * @note Result of axiom parse is asserted for a decent set of axioms to remove from soundness-critical core.
   */
  private[core] def loadAxioms: immutable.Map[String, Formula] = {
    try {
      //Code for old parser:
//      val parser = new KeYmaeraParser(enabledLogging = false)
//      val alp = parser.ProofFileParser
//      val res = alp.runParser(loadAxiomString())
      val res = KeYmaeraXAxiomParser(loadAxiomString())

      assert(res.length == res.map(k => k._1).distinct.length, "No duplicate axiom names during parse")

      res.map(k => (k._1 -> k._2)).toMap
    } catch { case e: Exception => e.printStackTrace(); println("Problem while reading axioms " + e); sys.exit(10) }
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  /** Redundant code checking expected form of axioms */
  private def assertCheckAxiomFile(axs : Map[String, Formula]) = {
    val x = Variable("x_", None, Real)
    val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
    val p = Function("p", None, Real, Bool)
    val pany = PredOf(p, Anything)
    val q0 = PredOf(Function("q", None, Unit, Bool), Nothing)
    val qany = PredOf(Function("q", None, Real, Bool), Anything)
    val c = FuncOf(Function("c", None, Unit, Real), Nothing)
    val f0 = FuncOf(Function("f", None, Unit, Real), Nothing)
    val fany = FuncOf(Function("f", None, Real, Real), Anything)
    val gany = FuncOf(Function("g", None, Real, Real), Anything)
    val t0 = FuncOf(Function("t", None, Unit, Real), Nothing)
    val a = ProgramConst("a")
    val b = ProgramConst("b")

    val H0 = PredOf(Function("H", None, Unit, Bool), Nothing)

    // Figure 2
    assert(axs("<> diamond") == Equiv(Not(Box(a, Not(pany))), Diamond(a, pany)), "<> diamond")
    assert(axs("[:=] assign") == Equiv(Box(Assign(x,f0), PredOf(p,x)), PredOf(p, f0)), "[:=] assign")
    assert(axs("[?] test") == Equiv(Box(Test(q0), p0), Imply(q0, p0))
      || axs("[?] test") == Equiv(Box(Test(H0), p0), Imply(H0, p0)), "[?] test")
    assert(axs("[++] choice") == Equiv(Box(Choice(a,b), pany), And(Box(a, pany), Box(b, pany))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Box(Compose(a,b), pany), Box(a, Box(b, pany))), "[;] compose")
    assert(axs("[*] iterate") == Equiv(Box(Loop(a), pany), And(pany, Box(a, Box(Loop(a), pany)))), "[*] iterate")
    //@note only sound for hybrid systems not for hybrid games
    assert(axs("K modal modus ponens") == Imply(Box(a, Imply(pany,qany)), Imply(Box(a, pany), Box(a, qany))), "K modal modus ponens")
    //@note could also have accepted axiom I for hybrid systems but not for hybrid games
    assert(axs("V vacuous") == Imply(p0, Box(a, p0)), "V vacuous")

    // Figure 3
   /* assert(axs("DC differential cut") == Imply(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(r,x)),
      Equiv(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(p,x)),
        Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), And(PredOf(q,x), PredOf(r,x))), PredOf(p,x)))), "DC differential cut") */

    assert(axs("c()' derive constant fn") == Equal(Differential(c), Number(0)), "c()' derive constant fn")
    assert(axs("+' derive sum") == Equal(Differential(Plus(fany, gany)), Plus(Differential(fany), Differential(gany))), "+' derive sum")
    assert(axs("-' derive minus") == Equal(Differential(Minus(fany, gany)), Minus(Differential(fany), Differential(gany))), "-' derive minus")
    assert(axs("*' derive product") == Equal(Differential(Times(fany, gany)), Plus(Times(Differential(fany), gany), Times(fany, Differential(gany)))), "*' derive product")
    assert(axs("!=' derive !=") == Equiv(DifferentialFormula(NotEqual(fany, gany)), Equal(Differential(fany), Differential(gany))), "!=' derive !=")
    assert(axs("&' derive and") == Equiv(DifferentialFormula(And(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))), "&' derive and")
    assert(axs("|' derive or") == Equiv(DifferentialFormula(Or(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))) || axs("|' derive or") == Imply(And(DifferentialFormula(pany), DifferentialFormula(qany)), DifferentialFormula(Or(pany, qany))), "|' derive or")
    assert(axs("x' derive var") == Equal(Differential(x), DifferentialSymbol(x)), "x' derive var")
    //assert(axs("x' derive variable") == Forall(immutable.Seq(x_), Equal(Differential(x_), DifferentialSymbol(x_))), "x' derive variable")

    assert(axs("all instantiate") == Imply(Forall(Seq(x), PredOf(p,x)), PredOf(p,f0)), "all instantiate")
    // soundness-critical that these are for p() not for p(x) or p(??)
    assert(axs("vacuous all quantifier") == Equiv(Forall(immutable.IndexedSeq(x), p0), p0), "vacuous all quantifier")

    true
  }

  /**
   * KeYmaera X axioms,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   *
   * @note Soundness-critical: Only adopt valid formulas as axioms.
   *
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @author Jan-David Quesel
   * @author Andre Platzer
   *
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
   * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012."
   * @see "Andre Platzer. Dynamic logics of dynamical systems. arXiv 1205.4788, May 2012."
   * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   */
  private[core] def loadAxiomString() : String =
"""
Variables.
End.

/**
 * HYBRID PROGRAM MODALITY AXIOMS
 */

Axiom "<> diamond".
  (![a;](!p(??))) <-> <a;>p(??)
End.

Axiom "[:=] assign".
  [x_:=f();]p(x_) <-> p(f())
End.

Axiom "[:=] assign equality".
  [x_:=f();]p(??) <-> \forall x_ (x_=f() -> p(??))
End.

Axiom "[:=] assign equality exists".
  [x_:=f();]p(??) <-> \exists x_ (x_=f() & p(??))
End.

Axiom "[:=] assign exists".
  [x_:=f();]p(??) -> \exists x_ p(??)
End.

Axiom "[:=] self assign".
  [x_:=x_;]p(??) <-> p(??)
End.

Axiom "[':=] differential assign".
  [x_':=f();]p(x_') <-> p(f())
End.

Axiom "[:*] assign nondet".
  [x_:=*;]p(??) <-> \forall x_ p(??)
End.

Axiom "[?] test".
  [?q();]p() <-> (q() -> p())
End.

Axiom "[++] choice".
  [a;++b;]p(??) <-> ([a;]p(??) & [b;]p(??))
End.

Axiom "[;] compose".
  [a;b;]p(??) <-> [a;][b;]p(??)
End.

Axiom "[*] iterate".
  [{a;}*]p(??) <-> (p(??) & [a;][{a;}*]p(??))
End.

/**
 * DIFFERENTIAL EQUATION AXIOMS
 */

Axiom "DW".
  [{c&H(??)}]H(??)
/* [x'=f(x)&q(x);]q(x) THEORY */
End.

Axiom "DC differential cut".
  ([{c&H(??)}]p(??) <-> [{c&(H(??)&r(??))}]p(??)) <- [{c&H(??)}]r(??)
/* ([x'=f(x)&q(x);]p(x) <-> [x'=f(x)&(q(x)&r(x));]p(x)) <- [x'=f(x)&q(x);]r(x) THEORY */
End.

Axiom "DE differential effect".
  /* [x'=f(x)&q(x);]p(x,x') <-> [x'=f(x)&q(x);][x':=f(x);]p(x,x')  THEORY */
  /* @NOTE Generalized argument compared to theory as in DE differential effect (system) */
  /* @NOTE In systems, f(x) cannot have ' by data structure invariant */
  [{x_'=f(x_)&q(x_)}]p(??) <-> [{x_'=f(x_)&q(x_)}][x_':=f(x_);]p(??)
End.

Axiom "DE differential effect (system)".
  /* @NOTE Soundness: AtomicODE requires explicit-form so f(??) cannot verbatim mention differentials/differential symbols */
  /* @NOTE Completeness: reassociate needed in DifferentialProduct data structures */
  [{x_'=f(??),c&H(??)}]p(??) <-> [{c,x_'=f(??)&H(??)}][x_':=f(??);]p(??)
End.

Axiom "DI differential invariant".
  [{c&H(??)}]p(??) <- (H(??)-> (p(??) & [{c&H(??)}]((p(??))')))
/* [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DG differential ghost".
  [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=(t()*y_)+s()&H(??)}]p(??)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y [{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}]p(x) THEORY */
End.

/* DG differential ghost, general Lipschitz case */
/*Axiom "DG differential Lipschitz ghost".
  ([x_'=f(x_)&q(x_);]p(x_) <-> \exists y_ [{x_'=f(x_),y_'=g(x_,y_)&q(x_)}]p(x_))
  <- (\exists L_ \forall x_ \forall y_ \forall z_ (abs(g(x_,y_)-g(x_,z_)) <= L_*abs(y_-z_)))
End.*/

/* DG differential ghost, general Lipschitz case, system case */
Axiom "DG differential Lipschitz ghost system".
  /* @see "DG differential Lipschitz ghost" THEORY */
  ([{c&H(??)}]p(??) <-> (\exists y_ [{y_'=g(??),c&H(??)}]p(??)))
  <- (\exists L_ [{c&H(??)}] (\forall a_ \forall b_ \forall u_ \forall v_ (a_>=b_ -> [y_:=a_;u_:=g(??);y_:=b_;v_:=g(??);] (-L_*(a_-b_) <= u_-v_ & u_-v_ <= L_*(a_-b_)))))
  /* <- (\exists L_ [{c&H(??)}] (\forall a_ \forall b_ \forall u_ \forall v_ ([y_:=a_;u_:=g(??);y_:=b_;v_:=g(??);] (abs(u_-v_) <= L_*abs(a_-b_))))) */
End.

Axiom "DG++ System".
  ([{x_'=f(x_),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(x_),c&H(??)}]p(??))
End.

Axiom "DG++".
  ([{x_'=f(x_)&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(x_)&H(??)}]p(??))
End.

/* Formatter axioms for diff eqs. */
Axiom ", commute".
  [{c,d&H(??)}]p(??) <-> [{d,c&H(??)}]p(??)
End.

Axiom "DS& differential equation solution".
  [{x_'=c()&q(x_)}]p(x_) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(x_)))
End.

/** @Derived from DW (not implementable for technical reasons - abstraction of c, ??) */
Axiom "DX differential skip".
  [{c&H(??)}]p(??) -> (H(??)->p(??))
End.

/* DIFFERENTIAL AXIOMS FOR TERMS */

Axiom "c()' derive constant fn".
  c()' = 0
End.

Axiom "x' derive var".
  (x_)' = x_'
End.

Axiom "-' derive neg".
  (-f(??))' = -(f(??)')
End.

Axiom "+' derive sum".
  (f(??) + g(??))' = (f(??)') + (g(??)')
End.

Axiom "-' derive minus".
  (f(??) - g(??))' = (f(??)') - (g(??)')
End.

Axiom "*' derive product".
  (f(??) * g(??))' = ((f(??)')*g(??)) + (f(??)*(g(??)'))
End.

Axiom "/' derive quotient".
  (f(??) / g(??))' = (((f(??)')*g(??)) - (f(??)*(g(??)'))) / (g(??)^2)
End.

Axiom "chain rule".
	[y_:=g(x_);][y_':=1;]( (f(g(x_)))' = (f(y_)') * (g(x_)') )
End.

Axiom "^' derive power".
	((f(??)^(c()))' = (c()*(f(??)^(c()-1)))*(f(??)')) <- (c() != 0)
End.

/**
 * DIFFERENTIAL FOR FORMULAS
 */

Axiom "=' derive =".
  (f(??) = g(??))' <-> ((f(??)') = (g(??)'))
End.

Axiom ">=' derive >=".
  (f(??) >= g(??))' <-> ((f(??)') >= (g(??)'))
End.

Axiom ">' derive >".
  (f(??) > g(??))' <-> ((f(??)') >= (g(??)'))
  /* sic! easier */
End.

Axiom "<=' derive <=".
  (f(??) <= g(??))' <-> ((f(??)') <= (g(??)'))
End.

Axiom "<' derive <".
  (f(??) < g(??))' <-> ((f(??)') <= (g(??)'))
  /* sic! easier */
End.

Axiom "!=' derive !=".
  (f(??) != g(??))' <-> ((f(??)') = (g(??)'))
  /* sic! */
End.

Axiom "&' derive and".
  (p(??) & q(??))' <-> ((p(??)') & (q(??)'))
End.

Axiom "|' derive or".
  (p(??) | q(??))' <-> ((p(??)') & (q(??)'))
  /* sic! yet <- */
End.

Axiom "forall' derive forall".
  (\forall x_ p(??))' <-> (\forall x_ (p(??)'))
End.

Axiom "exists' derive exists".
  (\exists x_ p(??))' <-> (\forall x_ (p(??)'))
  /* sic! yet <- */
End.

/** EXCLUSIVELY FOR HYBRID PROGRAMS. UNSOUND FOR HYBRID GAMES. */

/* @NOTE requires removing axioms unsound for hybrid games */
/*Axiom "<d> dual".
  <{a;}^d>p(??) <-> !<a;>!p(??)
  <{a;}^@>p(??) <-> !<a;>!p(??)
End.*/

/* @NOTE Unsound for hybrid games */
Axiom "V vacuous".
  p() -> [a;]p()
  /* @TODO (p() -> [a;]p()) <- [a;]true sound for hybrid games */
End.

/* @NOTE Unsound for hybrid games */
Axiom "K modal modus ponens".
  [a;](p(??)->q(??)) -> (([a;]p(??)) -> ([a;]q(??)))
End.

/* @NOTE Unsound for hybrid games, use ind induction rule instead */
Axiom "I induction".
  /*@TODO Drop or Use this form instead? which is possibly more helpful: ([{a;}*](p(??) -> [a;] p(??))) -> (p(??) -> [{a;}*]p(??)) THEORY */
  (p(??) & [{a;}*](p(??) -> [a;] p(??))) -> [{a;}*]p(??)
End.

/**
 * FIRST-ORDER QUANTIFIER AXIOMS
 */

Axiom "all dual".
  (!\exists x_ (!p(??))) <-> (\forall x_ p(??))
End.

Axiom /*\\foralli */ "all instantiate".
  (\forall x_ p(x_)) -> p(f())
End.

/* consequence of "all instantiate" @note generalized "all instantiate" */
Axiom "all eliminate".
  (\forall x_ p(??)) -> p(??)
End.

Axiom "exists eliminate".
  p(??) -> (\exists x_ p(??))
End.

Axiom "vacuous all quantifier".
  (\forall x_ p()) <-> p()
End.

/**
 * CONGRUENCE AXIOMS (for constant terms)
 */

Axiom "const congruence".
  (s() = t()) -> (ctxT_(s()) = ctxT_(t()))
End.

Axiom "const formula congruence".
  (s() = t()) -> (ctxF_(s()) <-> ctxF_(t()))
End.
"""
}
