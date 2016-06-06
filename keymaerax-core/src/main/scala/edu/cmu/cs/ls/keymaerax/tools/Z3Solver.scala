/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.io.{InputStream, FileOutputStream, FileWriter, File}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{ParseException, KeYmaeraXParser}
import scala.collection.immutable
import scala.sys.process._

/**
 * Created by ran on 3/27/15.
 * @author Ran Ji
 */
class Z3Solver extends SMTSolver {
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"

  /** Get the absolute path to Z3 jar */
  private val pathToZ3 : String = {
    val z3TempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    if(!new File(z3TempDir).exists) new File(z3TempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    if(osName.contains("windows") && new File(z3TempDir+"z3.exe").exists()) {
      z3TempDir+"z3.exe"
    } else if(new File(z3TempDir+"z3").exists()) {
      z3TempDir+"z3"
    } else {
      val osArch = System.getProperty("os.arch")
      var resource : InputStream = null
      if(osName.contains("mac")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/mac64/z3")
        }
      } else if(osName.contains("windows")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/windows64/z3.exe")
        } else {
          resource = this.getClass.getResourceAsStream("/z3/windows32/z3.exe")
        }
      } else if(osName.contains("linux")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/ubuntu64/z3")
        } else {
          resource = this.getClass.getResourceAsStream("/z3/ubuntu32/z3")
        }
      } else if(osName.contains("freebsd")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/freebsd64/z3")
        }
      } else {
        throw new Exception("Z3 solver is currently not supported in your operating system.")
      }
      if(resource == null)
        throw new Exception("Could not find Z3 in classpath: " + System.getProperty("user.dir"))
      val z3Source = Channels.newChannel(resource)
      val z3Temp = {
        if(osName.contains("windows")) {
          new File(z3TempDir, "z3.exe")
        } else {
          new File(z3TempDir, "z3")
        }
      }

      // Get a stream to the script in the resources dir
      val z3Dest = new FileOutputStream(z3Temp)
      // Copy file to temporary directory
      z3Dest.getChannel.transferFrom(z3Source, 0, Long.MaxValue)
      val z3AbsPath = z3Temp.getAbsolutePath
      val permissionCmd =
        if(osName.contains("windows")) "icacls " + z3AbsPath + " /e /p Everyone:F"
        else "chmod u+x " + z3AbsPath
      //@todo preexisting files shouldn't be modified permissions
      Runtime.getRuntime.exec(permissionCmd)
      z3Source.close()
      z3Dest.close()
      assert(new File(z3AbsPath).exists())
      z3AbsPath
    }
  }

  /**
   * Check satisfiability with Z3
   * @param cmd the command for running Z3 with a given SMT file
   * @return    Z3 output as String and the interpretation of Z3 output as KeYmaera X formula
    *           if result is unsat, then return True
    *           if result is sat or unknown, then return the original formula
    *           Z3 does not give other possible result for (check-sat)
   */
  private def run(cmd: String, f: Formula) : (String, Formula)= {
    val z3Output = cmd.!!
    if (DEBUG) println("[Z3 result] \n" + z3Output + "\n")
    //@todo So far does not handle get-model or unsat-core
    val kResult = {
      if (z3Output.equals("unsat\n")) True
      else if(z3Output.equals("sat\n")) f
      else if(z3Output.equals("unknown\n")) f
      else throw new SMTConversionException("Conversion of Z3 result \n" + z3Output + "\n is not defined")
    }
    (z3Output, kResult)
  }

  //todo code review: delete this method
  /** Return Z3 QE result */
  def qe(f: Formula) : Formula = {
    qeEvidence(f)._1
  }

  /** Return Z3 QE result and the proof evidence */
  def qeEvidence(f: Formula) : (Formula, Evidence) = {
    val smtCode = SMTConverter(f, "Z3") + "\n(check-sat)\n"
    if (DEBUG) println("[Solving with Z3...] \n" + smtCode)
    val smtFile = File.createTempFile("z3qe", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + smtFile.getAbsolutePath
    val (z3Output, kResult) = run(cmd, f)
    kResult match {
      case ff: Formula => (ff, new ToolEvidence(immutable.Map("input" -> smtCode, "output" -> z3Output)))
      case _ => throw new Exception("Expected a formula from QE call but got a non-formula expression.")
    }
  }

  /**
   * Simplify a KeYmaera X term into a possibly simple term
   * @param t  KeYmaera X term to be simplified
   * @return   the simplified term, or the original term if the simplify result is not a parsable KeYmaera X term
   */
  def simplify(t: Term) : Term = {
    val smtCode = SMTConverter.generateSimplify(t, "Z3")
    if (DEBUG) println("[Simplifying with Z3 ...] \n" + smtCode)
    val smtFile = File.createTempFile("z3simplify", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + smtFile.getAbsolutePath
    val z3Output = cmd.!!
    if (DEBUG) println("[Z3 simplify result] \n" + z3Output + "\n")
    if(z3Output.contains("!"))
      t
    else {
      try {
        KeYmaeraXParser.termParser(z3Output)
      } catch {
        case e: ParseException =>
          if (DEBUG) println("[Info] Cannot parse Z3 simplified result: " + z3Output)
          t
      }
    }
  }
}
