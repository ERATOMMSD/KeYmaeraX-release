/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package parserTests

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.UIKeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest.{FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable._

/**
 * Tests the parser on pairs of strings that are expected to parse the same.
 * @author Andre Platzer
 */
@SummaryTest
class PairParserTests extends FlatSpec with Matchers {
  val pp = if (false) KeYmaeraXPrettyPrinter
  else new edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter
  val parser = KeYmaeraXParser
  KeYmaera.init(Map.empty)
  val uipp = if (true) None else Some(new UIKeYmaeraXPrettyPrinter("-7"))

  def parseShouldBe(input: String, expr: Expression) = {
    val parse = parser(input)
    if (!(parse == expr)) {
      println("Reparsing" +
        "\nInput:      " + input +
        "\nParsed:     " + parse + " @ " + parse.getClass.getSimpleName +
        "\nExpression: " + pp.fullPrinter(parse))
      parse shouldBe expr
    }
  }

  "The parser" should "parse table of string pairs as expected" taggedAs(KeYmaeraXTestTags.SummaryTest) in {
    for ((s1, s2) <- expectedParse) {
      println("\ninput : " + s1 + "\nversus: " + s2)
      if (s2 == unparseable) {
        // ParseExceptions and CoreExceptions and AssertionErrors are simply all allowed.
        a[Throwable] should be thrownBy println("Parsed:  " + pp(parser(s1)))
      } else {
        val p1 = parser(s1)
        val p2 = parser(s2)
        println("parsed: " + pp(p1))
        p1 shouldBe p2
        parser(pp(p1)) shouldBe parser(pp(p2))
        pp(p1) shouldBe pp(p2)
        if (uipp.isDefined) println(uipp.get(p1))
      }
    }
  }

  /** A special swearing string indicating that the other string cannot be parsed. */
  private val unparseable: String = "@#%@*!!!"
  /** Left string is expected to parse like the right string parses, or not at all if right==unparseable */
  private val expectedParse /*: List[Pair[String,String]]*/ = List(
    // from doc/dL-grammar.md or crucially important
    ("x-y-z","(x-y)-z"),
    ("x/y/z","(x/y)/z"),
    ("x^2^4", "x^(2^4)"),
    ("-x^2", "-(x^2)"),
    ("-(x+5)^2+9>=7 & y>5 -> [x:=1;]x>=1", "((((-(x+5)^2)+9)>=7) & (y>5)) -> ([x:=1;](x>=1))"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("p()<-q()<-r()", "(p()<-q())<-r()"),
    ("p()<->q() &\nx>0 &&\ny<2", unparseable),

    ("p()<->q()<->r()", unparseable),
    ("p()->q()<-r()", unparseable),
    ("p()<-q()->r()", unparseable),
    ("x:=1;x:=2;x:=3;", "x:=1;{x:=2;x:=3;}"),
    ("[x:=1;x:=2;x:=3;]x=3", "[x:=1;{x:=2;x:=3;}]x=3"),
    ("x:=1;++x:=2;++x:=3;", "x:=1;++{x:=2;++x:=3;}"),
    ("[x:=1;++x:=2;++x:=3;]x=3", "[x:=1;++{x:=2;++x:=3;}]x=3"),

    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("p()<->q()<-r()", "p()<->(q()<-r())"),


    // full table
    // unary meets unary
    ("-x'", "-(x')"),
    ("-(x)'", "-((x)')"),
    // unary meets binary left
    ("-x+y", "(-x)+y"),
    ("-x-y", "(-x)-y"),
    ("-x*y", "-(x*y)"),
    ("-x/y", "-(x/y)"),
    ("-x^y", "-(x^y)"),
    // unary meets binary right
    ("x+-y", "x+(-y)"),
    ("x--y", "x-(-y)"),
    ("x*-y", "x*(-y)"),
    ("x/-y", "x/(-y)"),
    ("x^-y", "x^(-y)"),
    // unary meets binary left
    ("x'+y", "(x')+y"),
    ("x'-y", "(x')-y"),
    ("x'*y", "(x')*y"),
    ("x'/y", "(x')/y"),
    ("x'^y", "(x')^y"),
    // unary meets binary right
    ("x+y'", "x+(y')"),
    ("x-y'", "x-(y')"),
    ("x*y'", "x*(y')"),
    ("x/y'", "x/(y')"),
    ("x^y'", "x^(y')"),

    // binary meets binary from left
    ("x+y+z", "(x+y)+z"),
    ("x+y-z", "(x+y)-z"),
    ("x+y*z", "x+(y*z)"),
    ("x+y/z", "x+(y/z)"),
    ("x+y^z", "x+(y^z)"),
    // binary meets binary from right
    ("x+y+z", "(x+y)+z"),
    ("x-y+z", "(x-y)+z"),
    ("x*y+z", "(x*y)+z"),
    ("x/y+z", "(x/y)+z"),
    ("x^y+z", "(x^y)+z"),
    // binary meets binary from left
    ("x-y+z", "(x-y)+z"),
    ("x-y-z", "(x-y)-z"),
    ("x-y*z", "x-(y*z)"),
    ("x-y/z", "x-(y/z)"),
    ("x-y^z", "x-(y^z)"),
    // binary meets binary from right
    ("x+y-z", "(x+y)-z"),
    ("x-y-z", "(x-y)-z"),
    ("x*y-z", "(x*y)-z"),
    ("x/y-z", "(x/y)-z"),
    ("x^y-z", "(x^y)-z"),
    // binary meets binary from left
    ("x*y+z", "(x*y)+z"),
    ("x*y-z", "(x*y)-z"),
    ("x*y*z", "(x*y)*z"),
    ("x*y/z", "(x*y)/z"),
    ("x*y^z", "x*(y^z)"),
    // binary meets binary from right
    ("x+y*z", "x+(y*z)"),
    ("x-y*z", "x-(y*z)"),
    ("x*y*z", "(x*y)*z"),
    ("x/y*z", "(x/y)*z"),
    ("x^y*z", "(x^y)*z"),
    // binary meets binary from left
    ("x/y+z", "(x/y)+z"),
    ("x/y-z", "(x/y)-z"),
    ("x/y*z", "(x/y)*z"),
    ("x/y/z", "(x/y)/z"),
    ("x/y^z", "x/(y^z)"),
    // binary meets binary from right
    ("x+y/z", "x+(y/z)"),
    ("x-y/z", "x-(y/z)"),
    ("x*y/z", "(x*y)/z"),
    ("x/y/z", "(x/y)/z"),
    ("x^y/z", "(x^y)/z"),
    // binary meets binary from left
    ("x^y+z", "(x^y)+z"),
    ("x^y-z", "(x^y)-z"),
    ("x^y*z", "(x^y)*z"),
    ("x^y/z", "(x^y)/z"),
    ("x^y^z", "x^(y^z)"),
    // binary meets binary from right
    ("x+y^z", "x+(y^z)"),
    ("x-y^z", "x-(y^z)"),
    ("x*y^z", "x*(y^z)"),
    ("x/y^z", "x/(y^z)"),
    ("x^y^z", "x^(y^z)"),


    // reasonably systematic
    ("x+y+z","(x+y)+z"),
    ("x-y+z","(x-y)+z"),
    ("x+y-z","(x+y)-z"),
    ("x-y-z","(x-y)-z"),
    //("x++y", unparseable),  //@todo if statementSemicolon
    ("x*y+z","(x*y)+z"),
    ("x*y-z","(x*y)-z"),
    ("x+y*z","x+(y*z)"),
    ("x-y*z","x-(y*z)"),
    ("x**y", unparseable),
    ("x/y+z","(x/y)+z"),
    ("x/y-z","(x/y)-z"),
    ("x+y/z","x+(y/z)"),
    ("x-y/z","x-(y/z)"),
    ("x*y*z","(x*y)*z"),
    ("x*y/z","(x*y)/z"),
    ("x/y/z","(x/y)/z"),
    ("x/y*z","(x/y)*z"),
    ("x//y", unparseable),

    ("x+y^z","x+(y^z)"),
    ("x-y^z","x-(y^z)"),
    ("x^y+z","(x^y)+z"),
    ("x^y-z","(x^y)-z"),
    ("x^y*z","(x^y)*z"),
    ("x^y/z","(x^y)/z"),
    ("x*y^z","x*(y^z)"),
    ("x/y^z","x/(y^z)"),
    ("x^^y", unparseable),

    ("x+y+z","(x+y)+z"),
    ("x-y-z","(x-y)-z"),
    ("x*y*z","(x*y)*z"),
    ("x/y/z","(x/y)/z"),
    ("x^y^z","x^(y^z)"),

    // unary minus
    ("-x+y+z","((-x)+y)+z"),
    ("-x-y+z","((-x)-y)+z"),
    ("x+-y-z","(x+(-y))-z"),
    ("x- -y-z","(x-(-y))-z"),
    ("x+y- -z","(x+y)-(-z)"),
    ("x-y- -z","(x-y)-(-z)"),
    ("-x*y+z","(-(x*y))+z"),
    ("x*-y-z","(x*(-y))-z"),
    ("x+y*-z","x+(y*(-z))"),
    ("x-y*-z","x-(y*(-z))"),
    ("-x/y+z","(-(x/y))+z"),
    ("x/-y-z","(x/(-y))-z"),
    ("-x+y/z","(-x)+(y/z)"),
    ("x-y/-z","x-(y/(-z))"),
    ("-x*y*z","-((x*y)*z)"),
    ("x*-y/z","x*(-(y/z))"),     // subtle  (x*(-y))/z
    ("x/y/-z","(x/y)/(-z)"),
    ("x/y*-z","(x/y)*(-z)"),
    ("x*-/y", unparseable),

    ("-x+y^z","(-x)+(y^z)"),
    ("-x-y^z","(-x)-(y^z)"),
    ("x^-y+z","(x^(-y))+z"),
    ("x^-y-z","(x^(-y))-z"),
    ("x^y+-z","(x^y)+(-z)"),
    ("x^y- -z","(x^y)-(-z)"),

    // more unary minus
    ("x+-y+z","(x+(-y))+z"),
    ("x- -y-z","(x-(-y))-z"),
    ("x-y- -z","(x-y)-(-z)"),
    ("x- -y- -z","(x-(-y))-(-z)"),
    ("-x- -y- -z","((-x)-(-y))-(-z)"),
    ("x*-y*z","x*(-(y*z))"),   // subtle (x*(-y))*z
    ("-x*y*z","-((x*y)*z)"),        // subtle ((-x)*y)*z
    ("x*y*-z","(x*y)*(-z)"),

    // primes
    ("x'+y+z","(x'+y)+z"),
    ("x+y'+z","(x+(y'))+z"),
    ("x+y+z'","(x+y)+(z')"),
    ("x'-y-z","(x'-y)-z"),
    ("x-y'-z","(x-(y'))-z"),
    ("x-y-z'","(x-y)-(z')"),
    ("x'*y*z","(x'*y)*z"),
    ("x*y'*z","(x*(y'))*z"),
    ("x*y*z'","(x*y)*(z')"),
    ("x/-y/z","x/(-(y/z))"),   // subtle "(x/(-y))/z"
    ("x^-y^z","x^(-(y^z))"),

    ("-x'", "-(x')"),
    ("x+y'", "x+(y')"),
    ("x-y'", "x-(y')"),
    ("x*y'", "x*(y')"),
    ("x/y'", "x/(y')"),
    ("x^2'", "x^(2')"),
    ("x^2^4'", "x^(2^(4'))"),

    // prop meet table
    ("p()&q()&r()", "p()&(q()&r())"),
    ("p()&q()|r()", "(p()&q())|r()"),
    ("p()&q()->r()", "(p()&q())->r()"),
    ("p()&q()<->r()", "(p()&q())<->r()"),
    ("!p()&q()", "(!p())&q()"),
    ("p()&q()&r()", "p()&(q()&r())"),
    ("p()|q()&r()", "p()|(q()&r())"),
    ("p()->q()&r()", "p()->(q()&r())"),
    ("p()<->q()&r()", "p()<->(q()&r())"),
    ("p()&!q()", "p()&(!q())"),

    ("p()|q()&r()", "p()|(q()&r())"),
    ("p()|q()|r()", "p()|(q()|r())"),
    ("p()|q()->r()", "(p()|q())->r()"),
    ("p()|q()<->r()", "(p()|q())<->r()"),
    ("!p()|q()", "(!p())|q()"),
    ("p()&q()|r()", "(p()&q())|r()"),
    ("p()|q()|r()", "p()|(q()|r())"),
    ("p()->q()|r()", "p()->(q()|r())"),
    ("p()<->q()|r()", "p()<->(q()|r())"),
    ("p()|!q()", "p()|(!q())"),

    ("p()->q()&r()", "p()->(q()&r())"),
    ("p()->q()|r()", "p()->(q()|r())"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("!p()->q()", "(!p())->q()"),
    ("p()&q()->r()", "(p()&q())->r()"),
    ("p()|q()->r()", "(p()|q())->r()"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()->!q()", "p()->(!q())"),

    ("p()<->q()&r()", "p()<->(q()&r())"),
    ("p()<->q()|r()", "p()<->(q()|r())"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()<->q()<->r()", unparseable),
    ("!p()<->q()", "(!p())<->q()"),
    ("p()&q()<->r()", "(p()&q())<->r()"),
    ("p()|q()<->r()", "(p()|q())<->r()"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()<->q()<->r()", unparseable),
    ("p()<->!q()", "p()<->(!q())"),

    ("\\forall x p(x)&q(x)", "(\\forall x p(x))&q(x)"),
    ("\\forall x p(x)|q(x)", "(\\forall x p(x))|q(x)"),
    ("\\forall x p(x)->q(x)", "(\\forall x p(x))->q(x)"),
    ("\\forall x p(x)<->q(x)", "(\\forall x p(x))<->q(x)"),

    ("\\exists x p(x)&q(x)", "(\\exists x p(x))&q(x)"),
    ("\\exists x p(x)|q(x)", "(\\exists x p(x))|q(x)"),
    ("\\exists x p(x)->q(x)", "(\\exists x p(x))->q(x)"),
    ("\\exists x p(x)<->q(x)", "(\\exists x p(x))<->q(x)"),

    ("\\forall x x>=0&x<0", "(\\forall x (x>=0))&(x<0)"),
    ("\\forall x x>=0|x<0", "(\\forall x (x>=0))|(x<0)"),
    ("\\forall x x>=0->x<0", "(\\forall x (x>=0))->(x<0)"),
    ("\\forall x x>=0<->x<0", "(\\forall x (x>=0))<->(x<0)"),

    ("\\exists x x>=0&x<0", "(\\exists x (x>=0))&(x<0)"),
    ("\\exists x x>=0|x<0", "(\\exists x (x>=0))|(x<0)"),
    ("\\exists x x>=0->x<0", "(\\exists x (x>=0))->(x<0)"),
    ("\\exists x x>=0<->x<0", "(\\exists x (x>=0))<->(x<0)"),
    ("\\forall \\forall", unparseable),
    ("\\exists \\exists", unparseable),
    ("\\forall \\exists", unparseable),
    ("\\exists \\forall", unparseable),

    ("[x:=x+1;] p(x)&q(x)", "([x:=x+1;] p(x))&q(x)"),
    ("[x:=x+1;] p(x)|q(x)", "([x:=x+1;] p(x))|q(x)"),
    ("[x:=x+1;] p(x)->q(x)", "([x:=x+1;] p(x))->q(x)"),
    ("[x:=x+1;] p(x)<->q(x)", "([x:=x+1;] p(x))<->q(x)"),

    ("<x:=x+1;> p(x)&q(x)", "(<x:=x+1;> p(x))&q(x)"),
    ("<x:=x+1;> p(x)|q(x)", "(<x:=x+1;> p(x))|q(x)"),
    ("<x:=x+1;> p(x)->q(x)", "(<x:=x+1;> p(x))->q(x)"),
    ("<x:=x+1;> p(x)<->q(x)", "(<x:=x+1;> p(x))<->q(x)"),

    ("[x:=x+1;] x>=0&x<0", "([x:=x+1;] (x>=0))&(x<0)"),
    ("[x:=x+1;] x>=0|x<0", "([x:=x+1;] (x>=0))|(x<0)"),
    ("[x:=x+1;] x>=0->x<0", "([x:=x+1;] (x>=0))->(x<0)"),
    ("[x:=x+1;] x>=0<->x<0", "([x:=x+1;] (x>=0))<->(x<0)"),

    ("<x:=x+1;> x>=0&x<0", "(<x:=x+1;> (x>=0))&(x<0)"),
    ("<x:=x+1;> x>=0|x<0", "(<x:=x+1;> (x>=0))|(x<0)"),
    ("<x:=x+1;> x>=0->x<0", "(<x:=x+1;> (x>=0))->(x<0)"),
    ("<x:=x+1;> x>=0<->x<0", "(<x:=x+1;> (x>=0))<->(x<0)"),

    ("<x:=x+1;>[x:=x+1;]", unparseable),

    ("[{x'=1}] p(x)&q(x)", "([{x'=1}] p(x))&q(x)"),
    ("[{x'=1}] p(x)|q(x)", "([{x'=1}] p(x))|q(x)"),
    ("[{x'=1}] p(x)->q(x)", "([{x'=1}] p(x))->q(x)"),
    ("[{x'=1}] p(x)<->q(x)", "([{x'=1}] p(x))<->q(x)"),

    ("<{x'=1}> p(x)&q(x)", "(<{x'=1}> p(x))&q(x)"),
    ("<{x'=1}> p(x)|q(x)", "(<{x'=1}> p(x))|q(x)"),
    ("<{x'=1}> p(x)->q(x)", "(<{x'=1}> p(x))->q(x)"),
    ("<{x'=1}> p(x)<->q(x)", "(<{x'=1}> p(x))<->q(x)"),

    ("[{x'=1}] x>=0&x<0", "([{x'=1}] (x>=0))&(x<0)"),
    ("[{x'=1}] x>=0|x<0", "([{x'=1}] (x>=0))|(x<0)"),
    ("[{x'=1}] x>=0->x<0", "([{x'=1}] (x>=0))->(x<0)"),
    ("[{x'=1}] x>=0<->x<0", "([{x'=1}] (x>=0))<->(x<0)"),

    ("<{x'=1}> x>=0&x<0", "(<{x'=1}> (x>=0))&(x<0)"),
    ("<{x'=1}> x>=0|x<0", "(<{x'=1}> (x>=0))|(x<0)"),
    ("<{x'=1}> x>=0->x<0", "(<{x'=1}> (x>=0))->(x<0)"),
    ("<{x'=1}> x>=0<->x<0", "(<{x'=1}> (x>=0))<->(x<0)"),

    ("<{x'=1}>[{x'=1}]true", "<{x'=1}>([{x'=1}](true))"),
    ("<{x'=1}>[{x'=1}]", unparseable),

    ("\\forall p(x())","\\forall p (x())"),   //@todo not a great test on string level


    ("x:=1;x:=2;++x:=3;", "{x:=1;x:=2;}++{x:=3;}"),
    ("[x:=1;x:=2;++x:=3;]x>=5", "[{x:=1;x:=2;}++{x:=3;}]x>=5"),
    ("<x:=1;x:=2;++x:=3;>x>5", "<{x:=1;x:=2;}++{x:=3;}>x>5"),
    ("x:=1;++x:=2;x:=3;", "x:=1;++{x:=2;x:=3;}"),
    ("[x:=1;++x:=2;x:=3;]x^2>4", "[x:=1;++{x:=2;x:=3;}]x^2>4"),
    ("<x:=1;++x:=2;x:=3;>x^2>4", "<x:=1;++{x:=2;x:=3;}>x^2>4"),
    ("x:=1;?x>0&x^2>5;{x'=5}", "x:=1;{?((x>0)&((x^2)>5));{x'=5}}"),
    ("[x:=1;?x>0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x>0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x>0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x>0)&((x^2)>5));{x'=5}}>x+y>99"),
    ("x:=1;?x<0&x^2>5;{x'=5}", "x:=1;{?((x<0)&((x^2)>5));{x'=5}}"),
    ("[x:=1;?x<0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x<0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x<0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x<0)&((x^2)>5));{x'=5}}>x+y>99"),
    ("x:=1;++x:=2;++x:=3;", "x:=1;++{x:=2;++x:=3;}"),
    ("[x:=1;++x:=2;++x:=3;]x>5", "[x:=1;++{x:=2;++x:=3;}]x>5"),
    ("<x:=1;++x:=2;++x:=3;>x>5", "<x:=1;++{x:=2;++x:=3;}>x>5"),

    // nested modalities within programs
    ("<x:=1;?<x:=2;>x>1;>x>5", "<x:=1;?(<x:=2;>(x>1));>(x>5)"),
    ("[x:=1;?<x:=2;>x>1;]x>5", "[x:=1;?(<x:=2;>(x>1));](x>5)"),
    ("<x:=1;?<{x'=2}>x>1;>x>5", "<x:=1;?(<{x'=2}>(x>1));>(x>5)"),
    ("[x:=1;?<{x'=2}>x>1;]x>5", "[x:=1;?(<{x'=2}>(x>1));](x>5)"),
    ("[?[?[?q();]p();]r();]s()", "[?([?([?(q());]p());]r());]s()"),
    ("[?<?[?q();]p();>r();]s()", "[?(<?([?(q());]p());>r());]s()"),
    ("<?<?<?q();>p();>r();>s()", "<?(<?(<?(q());>p());>r());>s()"),
    ("[?<?[?q();]p();>r();]s()", "[?(<?([?(q());]p());>r());]s()"),
    ("<?[?<?q();>p();]r();>s()", "<?([?(<?(q());>p());]r());>s()"),

    // Converted from ParserParenTests:

    // unary operator binds stronger than binary operator
    ("! p > 0 & p < 5", "(!(p>0)) & (p<5)"),
      ("! p = 0 & p = 5", "(!(p=0)) & (p=5)") ,
      ("! p > 0 | p < 5", "(!(p>0)) | (p<5)") ,
      ("! p > 0 -> p > 5", "(!(p>0)) -> (p>5)") ,
      ("! p > 0 <-> p > 5", "(!(p>0)) <-> (p>5)") ,
      // quantifiers do not bind logical connectives but do bind inequalities.
      ("! \\forall x x > 0 | p < 5", "(!(\\forall x x>0)) | (p<5)") ,
      ("! \\exists x x > 0 | p < 5", "(!(\\exists x x>0)) | (p<5)") ,
      ("! \\forall x [p:=x;]p >= x | p < 5", "(!(\\forall x ([p:=x;](p>=x)))) | (p<5)") ,
      // quantifiers with multiple variables
      //("\\forall x, y . (y > x -> y > x)", "\\forall x, y . (y > x -> y > x)") ,
      //("\\exists y, x . (y > x -> y > x)", "\\exists y, x . (y > x -> y > x)") ,
      // modalities do not bind logical connectives.
      ("[p:=1;] p>0 & p < 1", "([p:=1;](p>0)) & (p<1)") ,
      ("[p:=1;] p>0 | p < 1", "([p:=1;](p>0)) | (p<1)") ,
      ("[p:=1;] p>0 -> p < 1", "([p:=1;](p>0)) -> (p<1)") ,
      ("<p:=1;> p>0 & p < 1", "(<p:=1;>(p>0)) & (p<1)") ,
      ("<p:=1;> p>0 | p < 1", "(<p:=1;>(p>0)) | (p<1)") ,
      ("<p:=1;> p>0 -> p < 1", "(<p:=1;>(p>0)) -> (p<1)") ,
      ("\\forall x x > 2 & a()", "(\\forall x (x > 2)) & a()") ,
      ("\\forall x x > 2 | a()", "(\\forall x (x > 2)) | a()") ,
      ("\\forall x x > 2 -> a()", "(\\forall x (x > 2)) -> a()") ,
      ("\\forall x x > 2 <-> a()", "(\\forall x (x > 2)) <-> a()") ,
      ("\\exists x x > 2 & a()", "(\\exists x (x > 2)) & a()") ,
      ("\\exists x x > 2 | a()", "(\\exists x (x > 2)) | a()") ,
      ("\\exists x x > 2 -> a()", "(\\exists x (x > 2)) -> a()") ,
      ("\\exists x x > 2 <-> a()", "(\\exists x (x > 2)) <-> a()") ,
      //nested modalities
      ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)") ,
      ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)") ,
      ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)") ,
      //[], <>, \forall, \exists magic.
      ("\\forall x [x:=1;]<x:=2;>x>0","\\forall x ([x:=1;]<x:=2;>(x>0))") ,
      ("\\exists x [x:=1;]<x:=2;>x>0","\\exists x ([x:=1;]<x:=2;>(x>0))") ,
      ("[p:=0;]\\forall x [x:=p;] \\exists y [q := x + y; ] q > 0", "[p:=0;](\\forall  x [x:=p;] (\\exists y [q := x + y; ] q > 0))") ,
      // <> vs >.
      ("< ?p>q; > p > 1", "<?(p > q);>(p>1)") ,
      ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)") ,
      ("< ?a(); ++ ?a(); > a()", "< {?a();} ++ {?a();} > a()") ,
      //arith.
      ("p + q * r = s", "p + (q * r) = s") ,
      ("p * q + r = s", "(p * q) + r = s") ,
      ("p - q * r = s", "p - (q * r) = s") ,
      ("p * q - r = s", "(p * q) - r = s") ,
      ("-p + q = s", "(-p) + q = s") ,
      ("p - q - s = 0", "(p-q) - s = 0") ,
      ("p^2 >= 0", "(p^2) >= 0") ,
      ("p^2 + q^2 = s^2", "(p^2) + (q^2) = (s^2)") ,
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0") ,
      ("1^2 + 3^2 = s^2", "(1^2) + (3^2) = (s^2)") ,
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0"),
      // implicit {} either assumed correctly or rejected
      ("[ p:=1; p:=2; ++ p:=3;] p>0", "[ {p:=1; p:=2;} ++ p:=3;] p>0") ,
      ("[ p:=1; ++ p:=2; p:=3;] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0") ,
      ("[ p:=1; p:=2; {p:=3;}*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0") ,
      ("[ p:=1; p:=2; ++ {p:=3;}*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0"),

  // more tests

    ("-x^2", "-(x^2)"),
    ("-x^1", "-(x^1)"),
    ("y+x^2", "y+(x^2)"),
    ("y-x^2", "y-(x^2)"),
    ("y*x^2", "y*(x^2)"),
    ("y/x^2", "y/(x^2)"),
    ("-x*y", "-(x*y)"),

    ("[{x'=1,y'=2,z'=3}]x>0", "[{x'=1,{y'=2,z'=3}}]x>0"),
    ("[{x'=1,y'=2,z'=3&x<5}]x>0", "[{x'=1,{y'=2,z'=3}&x<5}]x>0"),
    ("p(x)>0->[x:=0;{x'=2}x:=x+1;\n{y'=x&\nx<   2}]x<=5", "p(x)>0->[x:=0;{{x'=2}{x:=x+1;{y'=x&(x<2)}}}](x<=5)"),

    ("v>=0&A()>0->[{x'=v,v'=A()&true}]v>=0", "(v>=0&A()>0)->[{{x'=v,v'=A()}&true}](v>=0)"),
    ("abs(f()) = g() <->  f()>=0 & g()=f() | f()<=0 & g()=-f()", "(abs(f()) = g()) <->  ((f()>=0 & g()=f()) | (f()<=0 & g()=-f()))"),
    ("max(f(), g()) = h() <-> f()>=g() & h()=f() | f()<=g() & h()=g()", "(max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<=g() & h()=g()))"),


    //("x() -> [x:=x(x);]x()>x(x,x())", unparseable) //@todo if !LAX

    ("-x*y", "-(x*y)"),
    ("-3*y", "(-3)*y"), //@note subtle "-(3*y)"),
    ("-5*(y-z)", "(-5)*(y-z)"), // subtle "-(5*(y-z))"),
    ("-2-3", "(-2)-(3)"),  // subtle "(-(2))-(3)"),
    ("-2*-3", "(-2)*(-3)"),  // subtle "-(2*(-(3)))"),
    ("-8", "(-8)"),
    ("-2*a", "(-2)*a"),  // subtle -(2*a)"),
    ("-0*a", "(-0)*a"),  // subtle "-(0*a)"),
    ("a-3*b", "a-(3*b)"),
    ("-2-3*b", "(-2)-(3*b)"),
    ("-2+-3*b", "(-2)+((-3)*b)"),
    ("-(5*x)", "-(5*x)"),
    ("-(5+x)", "-(5+x)"),
    ("-(5-x)", "-(5-x)"),
    ("-(5*x)<=0", "-(5*x)<=0"),
    ("-0*min_0/a<=0*(tl-to)", "(((-0)*(min_0))/(a))<=0*(tl-to)"), // subtle "-(((0)*(min_0))/(a))<=0*(tl-to)"),
    ("-(0*min_0/a)<=0*(tl-to)", "-((0*(min_0))/(a))<=0*(tl-to)"),

    //@note hybrid games
//    ("<{x:=x+1;{x'=1}^@ ++ x:=x-1;}*>(0<=x&x<1)", "<{x:=x+1;{x'=1}^@ ++ x:=x-1;}*> (0<=x&x<1)"),
//    ("<{{x:=x+1;{x'=1}^@ ++ x:=x-1;}^@}*^@>(0<=x&x<1)", "<{{{{x:=x+1;{{x'=1}^@}} ++ {x:=x-1;}}^@}*}^@> (0<=x&x<1)"),

    ("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;} ]x>=1", unparseable),

    ("x + y*z + 3*(x+y)  >=  3+x+7", "((x+(y*z))+(3*(x+y)))>=((3+x)+7)"),
    ("x + y*z + 3*(x+y) >= 3+x+7  &  x+1 < 2   ->   x^2 >= (x-1)^2  |  5 > 1", "((((x+(y*z))+(3*(x+y)))>=((3+x)+7))&((x+1)<2))->((x^2)>=(((x-1)^2))|(5>1))"),
    ("2 + 3*x >= 2   ->   [{x:=x+1; x:=2*x;   ++  x:=0;}*] 3*x >= 0", "((2+(3*x))>=2)->([{{x:=(x+1);x:=(2*x);}++{x:=0;}}*]((3*x)>=0))"),

    ("true", "true"),
    ("false", "false"),

    ("a+2*b", "a+(2*b)"),
    ("a+2b+1", unparseable),
    ("a+f(b+1)", "a+(f((b+1)))"),
    ("a+2(b+1)", unparseable),
    ("a+2b+1", unparseable),

    ("00", "0")
  )
}
