package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable.Map

/**
  * Tests of direct calls to quantifier elimination tools
  */
class QETest extends TacticTestBase {

  "Standalone Mathematica QE tool" should "prove abs(5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(5)=5".asFormula)
    }
  }

  it should "prove abs(-5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(-5)=5".asFormula)
    }
  }

  it should "prove abs(x)^2=x^2" in withMathematica  { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(x)^2=x^2".asFormula)
    }
  }

  it should "not get stuck on a quantified arithmetic goal" taggedAs IgnoreInBuildTest in withMathematica  { qeTool =>
    //Strange example that finishes immediately on Mathematica 12.0 but not earlier versions (11.2,11.3)
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("\\forall t \\forall v \\forall x \\forall y  (T()>0&A()>0&B()>0&rad()>0&ox()^2+oy()^2=rad()^2&(v>=0&t<=T())&x^2+y^2=rad()^2&t>=0->x-ox()-(v*(T()-t)+A()*(T()-t)^2/2+(v+A()*(T()-t))^2/(2*B()))>0->-y*v/rad()+v>=0)".asFormula)
    }
  }
}
