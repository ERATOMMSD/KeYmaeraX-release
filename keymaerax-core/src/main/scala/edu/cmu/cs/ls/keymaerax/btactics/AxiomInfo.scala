/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool

import scala.collection.immutable.HashMap

/**
  * Since axioms are always referred to by their names (which are strings), we have the following problems:
  * 1) It's hard to keep everything up to date when a new axiom is added
  * 2) We don't get any static exhaustiveness checking when we case on an axiom
  *
  * AxiomInfo exists to help fix that. An AxiomInfo is just a collection of per-axiom information. The tests for
  * this object dynamically ensure it is exhaustive with respect to AxiomBase and DerivedAxioms. By adding a new
  * field to AxiomInfo you can ensure that all new axioms will have to have that field.
  * Created by bbohrer on 12/28/15.
  */

/** UI display information on how to show an axiom, rule, or tactic application */
sealed trait DisplayInfo {
  def name: String
  def asciiName: String
}
case class SimpleDisplayInfo(override val name: String, override val asciiName: String) extends DisplayInfo
case class RuleDisplayInfo(names: SimpleDisplayInfo, conclusion: SequentDisplay, premises:List[SequentDisplay]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean = false)
case class AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}

object DerivationInfo {
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name, name)}
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }
  implicit def sequentDisplay(succAccClosed:(List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }

  implicit def qeTool:QETool with DiffSolutionTool = DerivedAxioms.qeTool
  case class AxiomNotFoundException(axiomName: String) extends ProverException("Axiom with said name not found: " + axiomName)

  private val needsCodeName = "THISAXIOMSTILLNEEDSACODENAME"

  private def useAt(l:Lemma):BelleExpr = HilbertCalculus.useAt(l)

  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  private [btactics] val allInfo: List[DerivationInfo] = List(
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> diamond"
      , AxiomDisplayInfo(("〈·〉", "<.>"), "〈a〉P ↔ ¬[a]¬P")
      , "diamond", {case () => HilbertCalculus.diamond}),
    new DerivedAxiomInfo("[] box", "[.]", "box", {case () => HilbertCalculus.useAt(DerivedAxioms.boxAxiom)}),
    new PositionTacticInfo("assignb"
      , AxiomDisplayInfo("[:=]", "[x:=c]p(x)↔p(c)")
      , {case () => TactixLibrary.assignb}),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignbAxiom", {case () => HilbertCalculus.useAt("[:=] assign")}),
    new CoreAxiomInfo("[:=] self assign", "[:=]", "selfassignb", {case () => HilbertCalculus.useAt("[:=] self assign")}),
    new DerivedAxiomInfo("<:=> assign", "<:=>", "assignd", {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:=> assign equality", "<:=>", "assigndEquality", {case () => HilbertCalculus.useAt("<:=> assign equality")}),
    new CoreAxiomInfo("[:=] assign equality", "[:=]=", "assignbeq", {case () => HilbertCalculus.useAt("[:=] assign equality")}),
    new CoreAxiomInfo("[:=] assign exists", ("[:=]∃","[:=]exists"), "assignbexists", {case () => HilbertCalculus.useAt("[:=] assign exists") }),
    new CoreAxiomInfo("[:=] assign equality exists", ("[:=]","[:=] assign exists"), "assignbequalityexists", {case () => HilbertCalculus.useAt("[:=] assign equality exists") }),
    //new DerivedAxiomInfo("[:=] assign equality exists", "[:=]", "assignbequalityexists", {case () => HilbertCalculus.useAt("[:=] assign equality exists") }),
    //@todo new DerivedAxiomInfo("<:=> assign equality", "<:=>=", "assigndeq", {case () => ???}),
    new CoreAxiomInfo("[':=] differential assign"
      , AxiomDisplayInfo(("[′:=]","[':=]"), "[x′:=c]p(x′)↔p(c)")
      , "Dassignb", {case () => HilbertCalculus.Dassignb}),
    new CoreAxiomInfo("[:*] assign nondet"
      , AxiomDisplayInfo("[:*]", "[x:=*]p(x)↔∀x p(x)")
      , "randomb", {case () => HilbertCalculus.randomb}),
    new CoreAxiomInfo("[?] test"
      , AxiomDisplayInfo("[?]", "[?q]p↔(q→p)")
      , "testb", {case () => HilbertCalculus.testb}),
    new DerivedAxiomInfo("<?> test", "<?>", "testd", {case () => HilbertCalculus.testd}),
    new CoreAxiomInfo("[++] choice"
      , AxiomDisplayInfo(("[∪]", "[++]"), "[a∪b]P↔[a]P∧[b]P"), "choiceb", {case () => HilbertCalculus.choiceb}),
    new DerivedAxiomInfo("<++> choice", ("<∪>", "<++>"), "choiced", {case () => HilbertCalculus.choiced}),
    new CoreAxiomInfo("[;] compose"
      , AxiomDisplayInfo("[;]", "[a;b]P↔[a][b]P")
      , "composeb", {case () => HilbertCalculus.composeb}),
    new DerivedAxiomInfo("<;> compose", "<;>", "composed", {case () => HilbertCalculus.composed}),
    new CoreAxiomInfo("[*] iterate"
      , AxiomDisplayInfo("[*]", "[a*]P↔P∧[a][a*]P")
      , "iterateb", {case () => HilbertCalculus.iterateb}),
    new DerivedAxiomInfo("<*> iterate", "<*>", "iterated", {case () => HilbertCalculus.iterated}),
  //@todo if hybrid games enabled
    //new CoreAxiomInfo("<d> dual", "<d>", "duald", {case () => HilbertCalculus.duald}),
    //new DerivedAxiomInfo("[d] dual", "[d]", "dualb", {case () => HilbertCalculus.dualb}),
    new CoreAxiomInfo("K modal modus ponens", "K", "K", {case () => TactixLibrary.K}),
    //@note the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I axiom
  //@todo why isn't the code name just "I"? And the belleExpr could be useAt("I")?
    new CoreAxiomInfo("I induction", "I", "induction", {case () => ???}),
    new CoreAxiomInfo("V vacuous"
      , AxiomDisplayInfo("V", "p→[a]p")
      , "V", {case () => TactixLibrary.V}),

    // differential equation axioms
    new CoreAxiomInfo("DW", "DW", "DWaxiom", {case () => HilbertCalculus.DW}),
    new PositionTacticInfo("diffWeaken", "DW", {case () => DifferentialTactics.diffWeaken}),
    new CoreAxiomInfo("DC differential cut"
    , InputAxiomDisplayInfo("DC","([{x′=f(x)&q(x)}]p(x)↔[{x′=f(x)&q(x)∧r(x)}]p(x))←[{x′:=f(x)&q(x)}]r(x)", List(FormulaArg("r(x)")))
    , "DCaxiom", {case () => (fml: Formula) => HilbertCalculus.DC(fml) }),
    new InputPositionTacticInfo("diffCut"
    , RuleDisplayInfo("DC"
      , /* conclusion */ (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;"))
      , /* premises */ List((List("&Gamma;"), List("[{x′ = f(x) & q(x)}]r(x)", "&Delta;")),
        (List("&Gamma;"), List("[{x′ = f(x) & (q(x) ∧ r(x))}]p(x)","&Delta;"))))
    , List(FormulaArg("r(x)")) //@todo should be ListArg -> before merge, we already had lists in concrete Bellerophon syntax
    , {case () => (fml: Formula) => TactixLibrary.diffCut(fml)}),
    new CoreAxiomInfo("DE differential effect"
      , AxiomDisplayInfo("DE", "[{x′=f(x)&q(x)}]P↔[x′=f(x)&q(x)][x′:=f(x)]P")
      , "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system)"
      , AxiomDisplayInfo("DE", "[{x′=F,c&H}]P↔[{c,x′=F&H}][x′:=f(x)]P")
      , "DEs", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DI differential invariant"
      , AxiomDisplayInfo("DI", "[{x′=f(x)&q(x)}]p(x)←(q(x)→p(x)∧[{x′=f(x)&q(x)}](p(x))′)")
      , "DI", {case () => HilbertCalculus.DI}),
    new CoreAxiomInfo("DG differential ghost"
      , AxiomDisplayInfo("DG", "[{x′=f(x)&q(x)}]p(x)↔∃y [{x′=f(x),y′=a(x)y+b(x)&q(x)}]p(x)")
      , "DG", {case () => (x:Variable) => (t1:Term) => (t2:Term) => HilbertCalculus.DG(x,t1,t2)},
      List(VariableArg("x"), TermArg("t1"), TermArg("t2"))),
    new CoreAxiomInfo("DG differential Lipschitz ghost system", "DG", "DGs", {case () => ???}),
    new CoreAxiomInfo("DG++ System", "DG++", "DGpps", {case () => ???}),
    new CoreAxiomInfo("DG++", "DG++", "DGpp", {case () => ???}),
    new CoreAxiomInfo(", commute", ",", "commaCommute", {case () => ???}),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS", {case () => HilbertCalculus.DS}),

    // Differential Axioms
    new CoreAxiomInfo("c()' derive constant fn"
      , AxiomDisplayInfo(("c()'", "c()′"), "(c)′=0")
      , "Dconst", {case () => HilbertCalculus.Dconst}),
    new CoreAxiomInfo("x' derive var"
      ,  AxiomDisplayInfo("x'", "(x)′=x′")
      , "Dvar", {case () => HilbertCalculus.Dvar}),
    new DerivedAxiomInfo("x' derive variable"
      ,  AxiomDisplayInfo(("x′","x'"), "(x)′=x′")
      , "DvariableAxiom", {case () => HilbertCalculus.useAt(DerivedAxioms.Dvariable)}),
    new DerivedAxiomInfo("x' derive var commuted"
      ,  AxiomDisplayInfo(("x′+C","x'+C"), "x′=(x)′")
      , "DvariableCommutedAxiom", {case () => HilbertCalculus.useAt(DerivedAxioms.DvariableCommuted)}),
    new PositionTacticInfo("DvariableTactic"
      ,  AxiomDisplayInfo(("x′","x'"), "(x)′=x′")
      , {case () => DifferentialTactics.Dvariable}),
    new CoreAxiomInfo("+' derive sum"
      ,  AxiomDisplayInfo(("+′","+'"), "(f(x)+g(x))′=f(x)′+g(x)′")
      , "Dplus", {case () => HilbertCalculus.Dplus}),
    new CoreAxiomInfo("-' derive neg"
      ,  AxiomDisplayInfo(("-′","-'"),"(-f(x))′=-(f(x))′")
      , "Dneg", {case () => HilbertCalculus.Dneg}),
    new CoreAxiomInfo("-' derive minus"
      ,  AxiomDisplayInfo(("-′","-'"), "(f(x)-g(x))′=f(x)′-g(x)′")
      , "Dminus", {case () => HilbertCalculus.Dminus}),
    new CoreAxiomInfo("*' derive product"
      ,  AxiomDisplayInfo(("·′","*'"), "(f(x)·g(x))′=(f(x))′·g(x)+f(x)·(g(x))′")
      , "Dtimes", {case () => HilbertCalculus.Dtimes}),
    new CoreAxiomInfo("/' derive quotient"
      ,  AxiomDisplayInfo(("/′","/'"), "(f(g)/g(x))′=(g(x)·(f(x))w-f(x)·(g(x))′)/g(x)^2")
      , "Dquotient", {case () => HilbertCalculus.Dquotient}),
    new CoreAxiomInfo("^' derive power"
      ,  AxiomDisplayInfo(("^′","^'"), "(f(g)^n)′=n·f(g)^(n-1)·(f(g))′←n≠0")
      , "Dpower", {case () => HilbertCalculus.Dpower}),
    new CoreAxiomInfo("chain rule"
      ,  AxiomDisplayInfo(("∘′","o'"), "[y:=g(x)][y′:=1]((f(g(x)))′=(f(y))′·(g(x))′")
      , "Dcompose", {case () => TactixLibrary.Dcompose}),

    new CoreAxiomInfo("=' derive ="
      ,  AxiomDisplayInfo(("=′","='"),"(f(x)=g(x))′↔f(x)′=g(x)′")
      , "Dequal", {case () => HilbertCalculus.Dequal}),
    new CoreAxiomInfo(">=' derive >="
      ,  AxiomDisplayInfo(("≥′",">='"), "(f(x)≥g(x))′↔f(x)′≥g(x)′")
      , "Dgreaterequal", {case () => HilbertCalculus.Dgreaterequal}),
    new CoreAxiomInfo(">' derive >"
      ,  AxiomDisplayInfo((">′",">'"),"(f(x)>g(x))′  f(x)′≥g(x)′")
      , "Dgreater", {case () => HilbertCalculus.Dgreater}),
    new CoreAxiomInfo("<=' derive <="
      ,  AxiomDisplayInfo(("≤′","<='"), "(f(x)≤g(x))′↔f(x)′≤g(x)′")
      , "Dlessequal", {case () => HilbertCalculus.Dlessequal}),
    new CoreAxiomInfo("<' derive <"
      ,  AxiomDisplayInfo(("<′","<'"),"(f(x)<g(m))′↔f(x)′≤g(x)′")
      , "Dless", {case () => HilbertCalculus.Dless}),
    new CoreAxiomInfo("!=' derive !="
      ,  AxiomDisplayInfo(("≠′","!='"), "(f(x)¬=g(x))′↔f(x)′=g(x)′")
      , "Dnotequal", {case () => HilbertCalculus.Dnotequal}),
    new CoreAxiomInfo("&' derive and"
      ,  AxiomDisplayInfo(("∧′", "&'"),"(f(x)&g(x))′↔f(x)′∧g(x)′")
      , "Dand", {case () => HilbertCalculus.Dand}),
    new CoreAxiomInfo("|' derive or"
      ,  AxiomDisplayInfo(("∨′", "|'"), "(f(x)|g(x))′↔f(x)′∧g(x)′")
      , "Dor", {case () => HilbertCalculus.Dor}),
    new DerivedAxiomInfo("->' derive imply"
      ,  AxiomDisplayInfo(("→′","->'"), "(f(x)→g(x))′↔(¬f(x)∨g(x))′")
      , "Dimply", {case () => HilbertCalculus.Dimply}),
    new CoreAxiomInfo("forall' derive forall"
      ,  AxiomDisplayInfo(("∀′","forall'"), "(∀x p(x))′↔∀x (p(x))′")
      , "Dforall", {case () => HilbertCalculus.Dforall}),
    new CoreAxiomInfo("exists' derive exists"
      ,  AxiomDisplayInfo(("∃′","exists'"), "(∃x p(x))′↔∀x (p(x))′")
      , "Dexists", {case () => HilbertCalculus.Dexists}),

    new PositionTacticInfo("derive", "'", {case () => HilbertCalculus.derive}),

    // first-order logic quantifiers
    new CoreAxiomInfo("all instantiate", ("∀inst","allInst"), "allInst", {case () => ???}),
    new DerivedAxiomInfo("all distribute", ("∀→","all->"), "allDist", {case () => HilbertCalculus.allDist}),
    new CoreAxiomInfo("vacuous all quantifier", ("V∀","allV"), "allV", {case () => HilbertCalculus.allV}),
    new DerivedAxiomInfo("vacuous exists quantifier", ("V∃","existsV"), "existsV", {case () => HilbertCalculus.existsV}),

    // more
    new CoreAxiomInfo("const congruence", "CCE", "constCongruence", {case () => ???}),
    new CoreAxiomInfo("const formula congruence", "CCQ", "constFormulaCongruence", {case () => ???}),
    // Note: only used to implement Dskipd
    new CoreAxiomInfo("DX differential skip", "DX", "DX", {case () => ???}),

    new CoreAxiomInfo("all dual", ("∀d","alld"), "alld", {case () => }),
    new CoreAxiomInfo("all eliminate", ("∀e","alle"), "alle", {case () => }),
    new CoreAxiomInfo("exists eliminate", ("∃e","existse"), "existse", {case () => }),


    // Derived axioms
    new DerivedAxiomInfo("[:=] assign update", "[:=]", "assignbup", {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign update", "<:=>", "assigndup", {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:*> assign nondet", "<:*>", "randomd", {case () => HilbertCalculus.randomd}),
    new DerivedAxiomInfo("[:=] assign equational", "[:=]==", "assignbequational", {case () => HilbertCalculus.assignb}),
    //@note derived axiom <:=> assign equational not yet proven
//    new DerivedAxiomInfo("<:=> assign equational", "<:=>==", "assigndequational", {case () => HilbertCalculus.assignd}),
    /* @todo replace all the axioms with useAt(axiom) */
    new DerivedAxiomInfo("<':=> differential assign", ("<′:=>","<':=>"), "Dassignd", {case () => useAt(DerivedAxioms.assignDAxiom)}),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain", {case () => useAt(DerivedAxioms.DSnodomain)}),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain", {case () => useAt(DerivedAxioms.DSddomain)}),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain", {case () => useAt(DerivedAxioms.DSdnodomain)}),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost", {case () => useAt(DerivedAxioms.DGpreghost)}),
    new DerivedAxiomInfo("DW differential weakening"
      , AxiomDisplayInfo("DW","[x′=f(x)&q(x)]p(x)↔[x′=f(x)&q(x)](q(x)→p(x))")
      , "DWeaken", {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd", {case () => useAt(DerivedAxioms.Dskipd)}),
//    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate", {case () => useAt(DerivedAxioms.allEliminateAxiom)}),
    //@note derived axiom exists eliminate not yet proven -> use core axiom instead
//    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate", {case () => useAt(DerivedAxioms.existsEliminate)}),
    new DerivedAxiomInfo("exists dual", ("∃d","existsd"), "existsDual", {case () => useAt(DerivedAxioms.existsDualAxiom)}),
    new DerivedAxiomInfo("' linear", ("l′","l'"), "Dlinear", {case () => useAt(DerivedAxioms.Dlinear)}),
    new DerivedAxiomInfo("' linear right", ("l′","l'"), "DlinearRight", {case () => useAt(DerivedAxioms.DlinearRight)}),
    new DerivedAxiomInfo("!& deMorgan"
      , AxiomDisplayInfo(("¬∧", "!&"), "¬(p∧q)↔(¬p|¬q)")
      , "notAnd", {case () => useAt(DerivedAxioms.notAnd)}),
    new DerivedAxiomInfo("!| deMorgan"
      , AxiomDisplayInfo(("¬∨","!|"), "(¬(p|q))↔(¬p∧¬q)")
      , "notOr", {case () => useAt(DerivedAxioms.notOr)}),
    new DerivedAxiomInfo("!-> deMorgan"
      , AxiomDisplayInfo(("¬→","!->"), "¬(p->q)↔(p∧¬q)")
      , "notImply", {case () => useAt(DerivedAxioms.notImply)}),
    new DerivedAxiomInfo("!<-> deMorgan"
      , AxiomDisplayInfo(("¬↔", "!<->"), "¬(p↔q)↔(p∧¬q)| (¬p∧q)")
      , "notEquiv", {case () => useAt(DerivedAxioms.notEquiv)}),
    new DerivedAxiomInfo("!all"
      , AxiomDisplayInfo(("¬∀", "!all"), "¬∀x (p(x)))↔∃x (¬p(x))")
      , "notAll", {case () => useAt(DerivedAxioms.notAll)}),
    new DerivedAxiomInfo("!exists"
      , AxiomDisplayInfo(("¬∃","!exists"), "(¬∃x (p(x)))↔∀x (¬p(x))")
      , "notExists", {case () => useAt(DerivedAxioms.notExists)}),
    new DerivedAxiomInfo("![]", ("¬[]","![]"), "notBox", {case () => useAt(DerivedAxioms.notBox)}),
    new DerivedAxiomInfo("!<>", ("¬<>","!<>"), "notDiamond", {case () => useAt(DerivedAxioms.notDiamond)}),
    new DerivedAxiomInfo("[] split"
      , AxiomDisplayInfo(("[]∧", "[]^"), "[a](P ∧ Q)↔[a]P ∧ [a]Q")
      , "boxAnd", {case () => HilbertCalculus.useAt(DerivedAxioms.boxAnd)}),
    new DerivedAxiomInfo("<> split"
      , AxiomDisplayInfo(("<>∨","<>|"), "<a>(P ∨ Q)↔<a>P ∨ <a>Q")
        , "diamondOr", {case () => useAt(DerivedAxioms.diamondOr)}),
//    new DerivedAxiomInfo("<> split left", "<>|<-", "diamondSplitLeft", {case () => useAt(DerivedAxioms.diamondSplitLeft)}),
//    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft", {case () => useAt(DerivedAxioms.boxSplitLeft)}),
//    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight", {case () => useAt(DerivedAxioms.boxSplitRight)}),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd", {case () => useAt(DerivedAxioms.loopApproxd)}),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck", {case () => useAt(DerivedAxioms.loopStuck)}),
    new DerivedAxiomInfo("<'> stuck", ("<′> stuck","<'> stuck"), "odeStuck", {case () => useAt(DerivedAxioms.odeStuck)}),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postWeaken", {case () => useAt(DerivedAxioms.postconditionWeaken)}),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus", {case () => useAt(DerivedAxioms.intervalUpPlus)}),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus", {case () => useAt(DerivedAxioms.intervalUpMinus)}),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPlus", {case () => useAt(DerivedAxioms.intervalDownPlus)}),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus", {case () => useAt(DerivedAxioms.intervalDownMinus)}),
    new DerivedAxiomInfo("<-> reflexive", ("↔R","<->R"), "equivReflexive", {case () => useAt(DerivedAxioms.equivReflexiveAxiom)}),
    new DerivedAxiomInfo("-> distributes over &", ("→∧", "->&"), "implyDistAnd", {case () => useAt(DerivedAxioms.implyDistAndAxiom)}),
    new DerivedAxiomInfo("-> distributes over <->", ("→↔","-><->"), "implyDistEquiv", {case () => useAt(DerivedAxioms.implyDistEquivAxiom)}),
    new DerivedAxiomInfo("-> weaken", ("→W","->W"), "implyWeaken", {case () => useAt(DerivedAxioms.implWeaken)}),
    new DerivedAxiomInfo("!! double negation"
      , AxiomDisplayInfo(("¬¬","!!"), "(¬¬p↔p")
      , "doubleNegation", {case () => useAt(DerivedAxioms.doubleNegationAxiom)}),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual", {case () => useAt(DerivedAxioms.assignDualAxiom)}),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb", {case () => useAt(DerivedAxioms.vacuousAssignbAxiom)}),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd", {case () => useAt(DerivedAxioms.vacuousAssigndAxiom)}),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb", {case () => useAt(DerivedAxioms.loopApproxb)}),
  //@todo might have a better name
    new DerivedAxiomInfo("exists generalize", ("∃G","existsG"), "existsGeneralize", {case () => useAt(DerivedAxioms.existsGeneralize)}),
    new DerivedAxiomInfo("all substitute", ("∀S","allS"), "allSubstitute", {case () => useAt(DerivedAxioms.allSubstitute)}),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet", {case () => useAt(DerivedAxioms.vacuousBoxAssignNondetAxiom)}),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet", {case () => useAt(DerivedAxioms.vacuousDiamondAssignNondetAxiom)}),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", ("{∧}C","{&}C"), "domainCommute", {case () => useAt(DerivedAxioms.domainCommute)}), //@todo shortname
    new DerivedAxiomInfo("& commute", ("∧C","&C"), "andCommute", {case () => useAt(DerivedAxioms.andCommute)}),
    new DerivedAxiomInfo("& associative", ("∧A","&A"), "andAssoc", {case () => useAt(DerivedAxioms.andAssoc)}),
    new DerivedAxiomInfo("-> expand", ("→E","->E"), "implyExpand", {case () => useAt(DerivedAxioms.implyExpand)}),
    new DerivedAxiomInfo("-> tautology", ("→taut","->taut"), "implyTautology", {case () => useAt(DerivedAxioms.implyTautology)}),
    new DerivedAxiomInfo("\\forall->\\exists", ("∀→∃","all->exists"), "forallThenExists", {case () => useAt(DerivedAxioms.forallThenExistsAxiom)}),
    new DerivedAxiomInfo("->true"
      , AxiomDisplayInfo(("→⊤","->T"), "(p→⊤)↔⊤")
      , "implyTrue", {case () => useAt(DerivedAxioms.impliesTrue)}),
    new DerivedAxiomInfo("true->"
      , AxiomDisplayInfo(("⊤→", "T->"), "(⊤→p)↔p")
      , "trueImply", {case () => useAt(DerivedAxioms.trueImplies)}),
    new DerivedAxiomInfo("&true"
      , AxiomDisplayInfo(("∧⊤","&T"), "(p∧⊤)↔p")
      , "andTrue", {case () => useAt(DerivedAxioms.andTrue)}),
    new DerivedAxiomInfo("true&"
      , AxiomDisplayInfo(("⊤∧","T&"), "(v∧p)↔p")
      , "trueAnd", {case () => useAt(DerivedAxioms.trueAnd)}),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes", {case () => useAt(DerivedAxioms.zeroTimes)}),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus", {case () => useAt(DerivedAxioms.zeroPlus)}),
    new DerivedAxiomInfo("*0", "*0", "timesZero", {case () => useAt(DerivedAxioms.timesZero)}),
    new DerivedAxiomInfo("+0", "+0", "plusZero", {case () => useAt(DerivedAxioms.plusZero)}),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive", {case () => useAt(DerivedAxioms.equalReflex)}),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute", {case () => useAt(DerivedAxioms.equalCommute)}),
    new DerivedAxiomInfo("<=", "<=", "lessEqual", {case () => useAt(DerivedAxioms.lessEqual)}),
    new DerivedAxiomInfo("! <"
      , AxiomDisplayInfo(("¬<","!<"), "¬(f<g)↔(f≥g)")
      , "notLess", {case () => useAt(DerivedAxioms.notLess)}),
    new DerivedAxiomInfo("! >"
      , AxiomDisplayInfo(("¬>","!>"), "¬(f>g)↔(f≤g)")
      , "notGreater", {case () => useAt(DerivedAxioms.notGreater)}),
    new DerivedAxiomInfo("< negate", ("¬≤","!<="), "notGreaterEqual", {case () => useAt(DerivedAxioms.notGreaterEqual)}),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual", {case () => useAt(DerivedAxioms.flipGreaterEqual)}),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater", {case () => useAt(DerivedAxioms.flipGreater)}),
    new DerivedAxiomInfo("<", "<", "less", {case () => useAt(DerivedAxioms.less)}),
    new DerivedAxiomInfo(">", ">", "greater", {case () => useAt(DerivedAxioms.greater)}),
    new DerivedAxiomInfo("abs", "abs", "abs", {case () => useAt(DerivedAxioms.absDef)}),
    new DerivedAxiomInfo("min", "min", "min", {case () => useAt(DerivedAxioms.minDef)}),
    new DerivedAxiomInfo("max", "max", "max", {case () => useAt(DerivedAxioms.maxDef)}),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes", {case () => useAt(DerivedAxioms.intervalUpTimes)}),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide", {case () => useAt(DerivedAxioms.intervalUp1Divide)}),
    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide", {case () => useAt(DerivedAxioms.intervalUpDivide)}),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes", {case () => useAt(DerivedAxioms.intervalDownTimes)}),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide", {case () => useAt(DerivedAxioms.intervalDown1Divide)}),
    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide", {case () => useAt(DerivedAxioms.intervalDownDivide)}),
    new DerivedAxiomInfo("! !="
      , AxiomDisplayInfo(("¬≠","!!="), "(¬(f≠g)↔(f=g))")
      , "notNotEqual", {case () => useAt(DerivedAxioms.notNotEqual)}),
    new DerivedAxiomInfo("! ="
      , AxiomDisplayInfo(("¬ =","! ="), "(¬(f=g))↔(f≠g)")
      , "notEqual", {case () => useAt(DerivedAxioms.notEqual)}),
    new DerivedAxiomInfo("! <="
      , AxiomDisplayInfo(("¬≤","!<="), "(!(f≤g)↔(f>g)")
      , "notLessEqual", {case () => useAt(DerivedAxioms.notLessEqual)}),
    new DerivedAxiomInfo("* associative", "*A", "timesAssociative", {case () => useAt(DerivedAxioms.timesAssociative)}),
    new DerivedAxiomInfo("* commute", "*C", "timesCommute", {case () => useAt(DerivedAxioms.timesCommutative)}),
    new DerivedAxiomInfo("* inverse", "*i", "timesInverse", {case () => useAt(DerivedAxioms.timesInverse)}),
    new DerivedAxiomInfo("* closed", "*c", "timesClosed", {case () => useAt(DerivedAxioms.timesClosed)}),
    new DerivedAxiomInfo("* identity", "*I", "timesIdentity", {case () => useAt(DerivedAxioms.timesIdentity)}),
    new DerivedAxiomInfo("+ associative", "+A", "plusAssociative", {case () => useAt(DerivedAxioms.plusAssociative)}),
    new DerivedAxiomInfo("+ commute", "+C", "plusCommute", {case () => useAt(DerivedAxioms.plusCommutative)}),
    new DerivedAxiomInfo("+ inverse", "+i", "plusInverse", {case () => useAt(DerivedAxioms.plusInverse)}),
    new DerivedAxiomInfo("+ closed", "+c", "plusClosed", {case () => useAt(DerivedAxioms.plusClosed)}),
    new DerivedAxiomInfo("positivity", "Pos", "positivity", {case () => useAt(DerivedAxioms.positivity)}),
    new DerivedAxiomInfo("distributive", "*+", "distributive", {case () => useAt(DerivedAxioms.distributive)}),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", "boxDiamondPropagation", {case () => useAt(DerivedAxioms.boxDiamondPropagation)}),
    new DerivedAxiomInfo("-> self", ("→self","-> self"), "implySelf", {case () => useAt(DerivedAxioms.implySelf)}),
    //@todo internal only
//    new DerivedAxiomInfo("K1", "K1", "K1", {case () => useAt(DerivedAxioms.K1)}),
//    new DerivedAxiomInfo("K2", "K2", "K2", {case () => useAt(DerivedAxioms.K2)}),
    new DerivedAxiomInfo("PC1", "PC1", "PC1", {case () => useAt(DerivedAxioms.PC1)}),
    new DerivedAxiomInfo("PC2", "PC2", "PC2", {case () => useAt(DerivedAxioms.PC2)}),
    new DerivedAxiomInfo("PC3", "PC3", "PC3", {case () => useAt(DerivedAxioms.PC3)}),
    new DerivedAxiomInfo("PC9", "PC9", "PC9", {case () => useAt(DerivedAxioms.PC9)}),
    new DerivedAxiomInfo("PC10", "PC10", "PC10", {case () => useAt(DerivedAxioms.PC10)}),
    // @internal axioms for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", "dummyexistsDualAxiomT", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", "dummyallDualAxiom", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", "dummyallDualAxiom2", {case () => ???}),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", "dummyDplus0", {case () => ???}),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", "dummyDplustimesreduceAxiom", {case () => ???}),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", "dummyDplustimesexpandAxiom", {case () => ???}),
    new DerivedAxiomInfo("^' dummy", "DUMMY", "dummyDpowerconsequence", {case () => ???}),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL"
      , RuleDisplayInfo(("¬L", "!L"), (List("¬P", "&Gamma;"),List("&Delta;")), List((List("&Gamma;"),List("&Delta;","P"))))
      , {case () => ProofRuleTactics.notL}),
    new PositionTacticInfo("notR"
      , RuleDisplayInfo(("¬R", "!R"), (List("&Gamma;"),List("¬P","&Delta;")), List((List("&Gamma;","P"),List("&Delta;"))))
      , {case () => ProofRuleTactics.notR}),
    new PositionTacticInfo("andR"
      , RuleDisplayInfo(("∧R", "^R"), (List("&Gamma;"),List("P∧Q","&Delta;")),
        List((List("&Gamma;"),List("P", "&Delta;")),
          (List("&Gamma;"), List("Q", "&Delta;"))))
      , {case () => ProofRuleTactics.andR}),
    new PositionTacticInfo("andL"
      , RuleDisplayInfo(("∧L", "^L"), (List("P∧Q", "&Gamma;"),List("&Delta;")), List((List("&Gamma;","P","Q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.andL}),
    new PositionTacticInfo("orL"
      , RuleDisplayInfo(("∨L", "|L"), (List("P∨Q", "&Gamma;"),List("&Delta;")),
        List((List("&Gamma;", "P"),List("&Delta;")),
          (List("&Gamma;", "Q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.orL}),
    new PositionTacticInfo("orR"
      , RuleDisplayInfo(("∨R", "|R"), (List("&Gamma;"),List("P∨Q","&Delta;")), List((List("&Gamma;"),List("P","Q","&Delta;"))))
      , {case () => ProofRuleTactics.orR}),
    new PositionTacticInfo("implyR"
      , RuleDisplayInfo(("→R", "->R"), (List("&Gamma;"),List("P→Q", "&Delta;")), List((List("&Gamma;","P"),List("Q","&Delta;"))))
      , {case () => ProofRuleTactics.implyR}),
    new PositionTacticInfo("implyL"
      , RuleDisplayInfo(("→L", "->L"), (List("P→Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P"),List("&Delta;")),
          (List("&Gamma;"),List("Q","&Delta;"))))
      , {case () => ProofRuleTactics.implyL}),
    new PositionTacticInfo("equivL"
      , RuleDisplayInfo(("↔L", "<->L"), (List("P↔Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P∧Q"),List("&Delta;")),
          (List("&Gamma;","¬P∧¬Q"),List("&Delta;"))
         ))
      , {case () => ProofRuleTactics.equivL}),
    new PositionTacticInfo("equivR"
      , RuleDisplayInfo(("↔R", "<->R"), (List("&Gamma;"),List("P↔Q","&Delta;")),
        List((List("&Gamma;","P","Q"),List("&Delta;")),
          (List("&Gamma;","¬P","¬Q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.equivR}),
    new InputPositionTacticInfo("allL"
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(TermArg("θ"))
      , {case () => (t:Term) => SequentCalculus.allL(t)}),
    new PositionTacticInfo("allR"
      , RuleDisplayInfo(("∀R", "allR"), (List("&Gamma;"), List("∀x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(x)","&Delta;"))))
      , {case () => SequentCalculus.allR}),
    new PositionTacticInfo("existsL"
      , RuleDisplayInfo(("∃L", "existsL"), (List("&Gamma;","∃x P(x)"),List("&Delta;")),
        List((List("&Gamma;","P(x)"),List("&Delta;"))))
      , {case () => SequentCalculus.existsL}),
    new PositionTacticInfo("existsR"
      , RuleDisplayInfo(("∃R", "existsR"), (List("&Gamma;"),List("∃x P(x)","&Delta;")),
        List((List("&Gamma;"),List("P(&theta;)","&Delta;"))))
      , {case () => SequentCalculus.existsR}),
    new TacticInfo("G"
      , RuleDisplayInfo("G", (List(""),List("[a]P")), List((List(),List("P"))))
      , {case () => DLBySubst.G}),
    new TacticInfo("hideG"
      , RuleDisplayInfo("G", (List("&Gamma;"), List("[a]P", "&Delta;")), List((List(),List("P"))))
      , {case () => HilbertCalculus.hideG}),
    new PositionTacticInfo("abstractionb"
      , RuleDisplayInfo("V++", (List("&Gamma;", "[a]P"), List("&Delta;"))
      , List((List("&Gamma; \\ a", "P"), List("&Delta;"))))
      , {case () => TactixLibrary.abstractionb}),
    new PositionTacticInfo("dualFree"
      , RuleDisplayInfo(("[]⊤", "[]T"), (List("&Gamma;"),List("[a]⊤","&Delta;")),
        List())
      , {case () => HilbertCalculus.dualFree}),

    new PositionTacticInfo("commuteEquivL", ("↔CL", "<->CL"), {case () => ProofRuleTactics.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", ("↔CR", "<->CR"), {case () => ProofRuleTactics.commuteEquivR}),
    new PositionTacticInfo("equivifyR", ("→↔","-><->"), {case () => ProofRuleTactics.equivifyR}),
    new PositionTacticInfo("hideL"
      , RuleDisplayInfo("WL", (List("&Gamma;", "P"),List("&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => ProofRuleTactics.hideL}),
    new PositionTacticInfo("hideR"
      , RuleDisplayInfo("WR", (List("&Gamma;"),List("P", "&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => ProofRuleTactics.hideR}),
    new PositionTacticInfo("coHideL", "W", {case () => ProofRuleTactics.coHideL}),
    new PositionTacticInfo("coHideR", "W", {case () => ProofRuleTactics.coHideR}),
    new PositionTacticInfo("closeFalse"
      , RuleDisplayInfo(("⊥L", "falseL"), (List("⊥","&Gamma;"),List("&Delta;")), List())
      , {case () => ProofRuleTactics.closeFalse}),
    new PositionTacticInfo("closeTrue"
      , RuleDisplayInfo(("⊤R","trueR"), (List("&Gamma;"), List("⊤","&Delta;")),List())
        ,{case () => ProofRuleTactics.closeTrue}),
    new PositionTacticInfo("skolemizeL", "skolem", {case () => ProofRuleTactics.skolemizeL}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}),
    new PositionTacticInfo("skolemize", "skolem", {case () => ProofRuleTactics.skolemize}),
    new PositionTacticInfo("coHide", "W", {case () => ProofRuleTactics.coHide}),
    new PositionTacticInfo("hide", "W", {case () => ProofRuleTactics.hide}),
    new PositionTacticInfo("allL2R", "L=R all", {case () => TactixLibrary.exhaustiveEqL2R}),

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "W", {case () => ProofRuleTactics.coHide2}),
    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    new TwoPositionTacticInfo("closeId",
      RuleDisplayInfo("closeId", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => (ante: AntePosition, succ: SuccPosition) => TactixLibrary.close(ante, succ)}),
    new TwoPositionTacticInfo("L2R",
      RuleDisplayInfo("L2R",
        /*conclusion*/ (List("&Gamma;", "x=y", "P(x)"), List("Q(x)", "&Delta;")),
        /*premise*/    List((List("&Gamma;", "x=y", "P(y)"), List("Q(y)", "&Delta;")))),
      {case () => (pos: AntePosition) => TactixLibrary.eqL2R(pos)}),
//      {case () => ProofRuleTactics.trivialCloser}), //@todo This is a 4.1b3 merge conflict. I'm not sure what the correct behavior is.

    // Proof rule input tactics
    new InputTacticInfo("cut"
      , RuleDisplayInfo(("\u2702","cut")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;"),List("&Delta;","P")),
          (List("&Gamma;", "P"), List("&Delta;"))))
        ,List(FormulaArg("P")), {case () => (fml:Formula) => ProofRuleTactics.cut(fml)}),
    // Proof rule input position tactics
    //@todo Move these DependentPositionTactic wrappers to ProofRuleTactics?
    new InputPositionTacticInfo("cutL", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutL") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutL") {
          ProofRuleTactics.cutL(fml)(pos.checkAnte.top)
        }
      }}),
    new InputPositionTacticInfo("cutR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutR") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutR") {
          ProofRuleTactics.cutR(fml)(pos.checkSucc.top)
        }
      }}),
    new InputPositionTacticInfo("cutLR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutLR") {
          /** Create the actual tactic to be applied at position pos */
          override def factory(pos: Position): DependentTactic = new DependentTactic("cutLR") {
            ProofRuleTactics.cutLR(fml)(pos)
          }
        }}),
    new InputPositionTacticInfo("loop",
      RuleDisplayInfo("loop",(List("&Gamma;"), List("[a*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(x)", "&Delta;")),
          (List("j(x)"),List("[a]j(x)")),
          (List("j(x)"),List("P"))))
      , List(FormulaArg("j(x)")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),
    new InputPositionTacticInfo("generalizeb",
    RuleDisplayInfo("G[]",(List("&Gamma;"), List("[a]P", "&Delta;")),
      List(
        (List("&Gamma;"),List("[a]Q", "&Delta;")),
        (List("Q"),List("P"))))
    , List(FormulaArg("Q")), {case () => (fml:Formula) => TactixLibrary.generalize(fml)}),
    new InputPositionTacticInfo("transform", "trafo", List(FormulaArg("toFormula")),
      {case () => (fml:Formula) => TactixLibrary.transform(fml)}),

  //
    new TacticInfo("TrivialCloser", "TrivialCloser", {case () => ProofRuleTactics.trivialCloser}),
    new TacticInfo("nil", "nil", {case () => Idioms.nil}),

    // TactixLibrary tactics
    new PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    new PositionTacticInfo("stepAt", "stepAt", {case () => HilbertCalculus.stepAt}),
    new PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}),
    new PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}),
    new PositionTacticInfo("chase", "chase", {case () => TactixLibrary.chase}),
    // Technically in InputPositionTactic(Generator[Formula, {case () => ???}), but the generator is optional
    new PositionTacticInfo("master", "master", {case () => (gen:Generator[Formula]) => TactixLibrary.master(gen)}, needsGenerator = true),
    new TacticInfo("QE", "QE",  {case () => TactixLibrary.QE}, needsTool = true),
    new TacticInfo("MathematicaQE", "MathematicaQE", {case () => TactixLibrary.QE}, needsTool = true),
    new TacticInfo("pQE", "pQE",  {case () => ToolTactics.partialQE}, needsTool = true),

    // Differential tactics
    new PositionTacticInfo("DIRule",
      RuleDisplayInfo("DI",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        /* premises */ List((List("&Gamma;", "q(x)"), List("p(x)", "&Delta;")),
          (List("&Gamma;", "q(x)"), List("[{x′ = f(x) & q(x)}](p(x))′","&Delta;")))),
      {case () => DifferentialTactics.DIRule}),
    new PositionTacticInfo("autoDIRule",
    RuleDisplayInfo("DI",
      (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
      /* premises */ List((List("&Gamma;", "q(x)"), List("p(x)", "&Delta;"), true),
        (List("&Gamma;", "q(x)"), List("[{x′ = f(x) & q(x)}](p(x))′","&Delta;"), true))),
    {case () => DifferentialTactics.diffInd}, needsTool = true),
    new PositionTacticInfo("diffInd",
    RuleDisplayInfo("diffInd",
      (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
      /* premises */ List((List("&Gamma;", "q(x)"), List("p(x)", "&Delta;")),
        (List("q(x)"), List("[x′:=f(x)](p(x))′")))),
    {case () => DifferentialTactics.diffIndRule}),
    new PositionTacticInfo("autoDiffInd",
    RuleDisplayInfo("diffInd",
      (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
      /* premises */ List((List("&Gamma;", "q(x)"), List("p(x)", "&Delta;"), true),
        (List("q(x)"), List("[x′:=f(x)](p(x))′"), true))),
    {case () => DifferentialTactics.diffInd}),
    new InputPositionTacticInfo("diffInvariant"
    , RuleDisplayInfo("DC+DI"
      , (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;"))
      , /* premises */ List((List("&Gamma;"), List("[{x′ = f(x) & q(x)}]r(x)", "&Delta;"), true),
        (List("&Gamma;"), List("[{x′ = f(x) & (q(x) ∧ r(x))}]p(x)","&Delta;"))))
    , List(FormulaArg("r(x)")) //@todo should be ListArg, before merge we already had concrete Bellerophon syntax for lists
    , {case () => (fml:Formula) => TactixLibrary.diffInvariant(fml)}),
    new PositionTacticInfo("diffSolve",
      RuleDisplayInfo("[′]R",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( (∀0≤s≤t q(sol(s))) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.diffSolve(None)}, needsTool = true), //@todo change the tactic back when we get a chance to implement the new one.
    new PositionTacticInfo("autoDiffSolve",
    RuleDisplayInfo("[′]R",
      (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
      List((List("&Gamma;", "t≥0"), List("[x:=sol(t)](q(x) → p(x))")))),
    {case () => TactixLibrary.diffSolve(None)}, needsTool = true),
    new PositionTacticInfo("Dvariable", "Dvar", {case () => DifferentialTactics.Dvariable}),

    // DLBySubst
    new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => TactixLibrary.loop(fml)})
  ) ensuring(consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    //@note to avoid file storage issues on some OSes, lowercase versions of names are expected to be unique.
    val canonicals = list.map(i => i.canonicalName.toLowerCase())
    val codeNames = list.map(i => i.codeName.toLowerCase()).filter(n => n!=needsCodeName)
    list.forall(i => i match {
        case ax: CoreAxiomInfo => Axiom.axioms.contains(ax.canonicalName) ensuring(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
        case ax: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
        case _ => true
      }
    ) &
      (canonicals.length==canonicals.distinct.length ensuring(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &
      (codeNames.length==codeNames.distinct.length ensuring(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct)))
  }

  /** code name mapped to derivation information */
  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc.+((info.codeName.toLowerCase(), info))
    }

  /** canonical name mapped to derivation information */
  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc.+((info.canonicalName.toLowerCase, info))
    }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.getOrElse(axiomName.toLowerCase,
        throw new AxiomNotFoundException(axiomName))
  }

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id:String) = { assert(id.forall{case c => c.isLetterOrDigit})}

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): DerivationInfo = byCodeName.getOrElse(codeName.toLowerCase,
    throw new IllegalArgumentException("No such DerivationInfo of identifier " + codeName)
  )

  def hasCodeName(codeName: String): Boolean = byCodeName.keySet.contains(codeName.toLowerCase)
}

object AxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  /** Retrieve meta-information on an axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): AxiomInfo =
    DerivationInfo.ofCodeName(codeName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
    }
}

object TacticInfo {
  def apply(tacticName: String): TacticInfo =
    DerivationInfo(tacticName) match {
      case info:TacticInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a tactic")
    }
}

sealed trait ArgInfo {
  val sort: String
  val name: String
}
case class FormulaArg (override val name: String) extends ArgInfo {
  val sort = "formula"
}
case class VariableArg (override val name: String) extends ArgInfo {
  val sort = "variable"
}
case class TermArg (override val name: String) extends ArgInfo {
  val sort = "term"
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (override val name: String, elementSort: String) extends ArgInfo {
  val sort = "list"
}

/** Meta-information on a derivation step, which is an axiom, derived axiom, proof rule, or tactic. */
sealed trait DerivationInfo {
  /** Canonical name unique across all derivations (axioms or tactics). For axioms this is as declared in the
    * axioms file, for and tactics it is identical to codeName. Can and will contain spaces and special chars. */
  val canonicalName: String
  /** How to display this inference step in a UI */
  val display: DisplayInfo
  /** The unique alphanumeric identifier for this inference step. */
  val codeName: String
  /** Specification of inputs (other than positions) to the derivation, along with names to use when displaying in the UI. */
  val inputs: List[ArgInfo] = Nil
  /** Bellerophon tactic implementing the derivation. For non-input tactics this is simply a BelleExpr. For input tactics
    * it is (curried) function which accepts the inputs and produces a BelleExpr. */
  def belleExpr: Any
  //@todo add formattedName/unicodeName: String
  /** Number of positional arguments to the derivation. Can be 0, 1 or 2. */
  val numPositionArgs: Int = 0
  /** Whether the derivation expects the caller to provide it with a way to generate invariants */
  val needsGenerator: Boolean = false
}

/** Meta-Information for an axiom or derived axiom */
trait AxiomInfo extends DerivationInfo {
  /** The valid formula that this axiom represents */
  def formula: Formula
  /** A Provable concluding this axiom */
  def provable: Provable
}

/** Meta-Information for an axiom from the prover core */
case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any, override val inputs:List[ArgInfo] = Nil) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  override val formula:Formula = {
    Axiom.axioms.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override lazy val provable:Provable = Axiom.axiom(canonicalName)
  override val numPositionArgs = 1
}

/** Information for a derived axiom proved from the core */
case class DerivedAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  override lazy val formula: Formula =
    DerivedAxioms.derivedAxiom(canonicalName).conclusion.succ.head
//  {
//    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
//      case Some(fml) => fml._1
//      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
//    }
//  }
  override lazy val provable:Provable = DerivedAxioms.derivedAxiom(canonicalName)
  override val numPositionArgs = 1
}

object DerivedAxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def locate(axiomName: String): Option[DerivedAxiomInfo] =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivedAxiomInfo =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived axiom")
    }

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}

// tactics

/** Meta-information on a tactic performing a proof step (or more) */
class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false) extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator)

case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}