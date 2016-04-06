/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/*
 * This file contains data structures targeted by the KeYmaera proof parser.
 * This file probably belongs in the parser namespace instead of the core TODO
 * @author Nathan Fulton
 */

package edu.cmu.cs.ls.keymaerax.parser

import java.io.File
import edu.cmu.cs.ls.keymaerax.btactics.Axiom
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.ProofNode

object LoadedKnowledgeTools {
  /**
   * LoadedKnowledge List -> String -> LoadedKnowledge List
 *
   * @returns All evidence associated with the name.
   */
  def fromName(knowledge : List[LoadedKnowledge])(n:String) = {
    knowledge.filter(_ match {
      case LoadedAxiom(name, formula)           => n.equals(name)
      case LoadedLemma(name, formula, evidence) => n.equals(name)
    })
  }
}
sealed class LoadedKnowledge(val name : String, val formula : Formula)
@deprecated("Not needed. Use (String,Formula) instead")
case class LoadedAxiom(n : String, f : Formula) extends LoadedKnowledge(n,f)
case class LoadedLemma(n : String, f : Formula, evidence : List[Evidence]) extends LoadedKnowledge(n,f)

class LoadedBranch(val name : String, val rules : List[LoadedRule]) {
  def getProof : ProofNode = ??? //TODO
}

class LoadedRule(val name : String, info : List[LoadedRuleInfo]) 
{
  /**
   * Converts a LoadedRule into a proof (in the sense of the core data structure)
   */
  def getProof : ProofNode = {
    //Proceed according to the name of the rule.
    if(this.isAxiom) {
      getAxiom
    }
    else {
      ??? //TODO convert LoadedRuleInfo into a proof.
    }
  }
  
  val isAxiom = {
    val matchingAxioms = Axiom.axioms.filter(ax => ax._1.equals(name))
    !matchingAxioms.isEmpty
  }
  
  def getAxiom : ProofNode = {
    if(isAxiom) {
      //formula
      val ax = Axiom.axioms.filter(ax => ax._1.equals(name)).last._2
      ??? //TODO
    }
    else {
      throw new Exception("Requested axiom " + name + " but this is not an axiom")
    }
  }
}

sealed trait LoadedRuleInfo {
  def fromName(name:String, value:String) = name match {
    case "formula" => TargetedFormula(Integer.parseInt(value))
    case "tool" => ToolUsed(value)
    case "nodenum" => NodeNum(Integer.parseInt(value))
    case "TargetedTerms" => {
      val values = value.split(""",""").map(Integer.parseInt(_))
      TargetedTerms(List() ++ values)
    }
  }
}
case class TargetedFormula(n : Int) extends LoadedRuleInfo
case class ToolUsed(name : String) extends LoadedRuleInfo
case class NodeNum(n : Int) extends LoadedRuleInfo
case class TargetedTerms(ns : List[Int]) extends LoadedRuleInfo
case class EmptyRule() extends LoadedRuleInfo
