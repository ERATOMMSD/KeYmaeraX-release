/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core.Expression

/**
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the .kyx format and a (partial) proof tactic in .kyt format.
  *
  * Format example:
  * {{{
  *   ArchiveEntry "Entry 1".
  *     Functions. ... End.
  *     ProgramVariables. ... End.
  *     Problem. ... End.
  *     Tactic "Proof 1". ... End.
  *     Tactic "Proof 2". ... End.
  *   End.
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 12/29/16.
  */
object KeYmaeraXArchiveParser {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val END_BLOCK: String = "End."

  /** Two groups: entry name, model+optional tactic */
  private val NAME_REGEX = "^\"([^\"]*)\"\\.(?s)(.*)".r

  /** The entry name, kyx file content (model), parsed model, and parsed name+tactic. */
  case class ParsedArchiveEntry(name: String, kind: String, fileContent: String, model: Expression, tactics: List[(String, BelleExpr)])
  /** The entry name, kyx file content, and list of name+tactic text. */
  type ArchiveEntry = (String, String, String, List[(String, String)])

  /** Parses the archive content into archive entries with parsed model and tactics. */
  def parse(archiveContentBOM: String): List[ParsedArchiveEntry] = {
    val archiveContents: List[ArchiveEntry] = read(archiveContentBOM)
    archiveContents.map({case (name, modelText, kind, tactics) =>
      ParsedArchiveEntry(name, modelText, kind, KeYmaeraXProblemParser.parseAsProblemOrFormula(modelText),
        tactics.map({case (tacticName, tacticText) => (tacticName, BelleParser(tacticText))}))
    })
  }

  /** Reads a specific entry from the archive. */
  def getEntry(entryName: String, archiveContentBOM: String): Option[ParsedArchiveEntry] = {
    parse(archiveContentBOM).find(_.name == entryName)
  }

  /** Reads the archive content into string-only archive entries. */
  def read(archiveContentBOM: String): List[ArchiveEntry] = {
    val archiveContent: String = ParserHelper.removeBOM(archiveContentBOM)
    // match ArchiveEntry, Lemma, Theorem, unless inside quotation marks
    val regex = s"(?=($ARCHIVE_ENTRY_BEGIN|$LEMMA_BEGIN|$THEOREM_BEGIN)" + "(?=([^\"]*\"[^\"]*\")*[^\"]*$))"
    archiveContent.trim().split(regex).flatMap({s =>
      val (entry, kind) =
        if (s.startsWith(ARCHIVE_ENTRY_BEGIN)) (s.stripPrefix(ARCHIVE_ENTRY_BEGIN), "theorem")
        else if (s.startsWith(THEOREM_BEGIN)) (s.stripPrefix(THEOREM_BEGIN), "theorem")
        else if (s.startsWith(LEMMA_BEGIN)) (s.stripPrefix(LEMMA_BEGIN), "lemma")
        else throw new IllegalArgumentException("Expected either ArchiveEntry, Lemma, Theorem, but got unknown entry kind " + s)
      NAME_REGEX.findAllMatchIn(entry.trim().stripSuffix(END_BLOCK)).map(
        { m =>
          val modelName = m.group(1)
          val (model: String, tactics: List[(String, String)]) = m.group(2).split(TACTIC_BEGIN).toList match {
            case modelText :: ts => (modelText.trim(), ts.flatMap(tacticText => {
              NAME_REGEX.findAllMatchIn(tacticText.trim().stripSuffix(END_BLOCK)).map({
                tm => (tm.group(1), tm.group(2))
              })
            }))
          }
          (modelName, model, kind, tactics)
        })
    }).toList
  }
}
