/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordData00
import VOA.DeligneAudit.D4FusionRealizationTwoWordData01
import VOA.DeligneAudit.D4FusionRealizationTwoWordData02
import VOA.DeligneAudit.D4FusionRealizationTwoWordData03
import VOA.DeligneAudit.D4FusionRealizationTwoWordData04
import VOA.DeligneAudit.D4FusionRealizationTwoWordData05
import VOA.DeligneAudit.D4FusionRealizationTwoWordData06
import VOA.DeligneAudit.D4FusionRealizationTwoWordData07
import VOA.DeligneAudit.D4FusionRealizationTwoWordData08
import VOA.DeligneAudit.D4FusionRealizationTwoWordData09
import VOA.DeligneAudit.D4FusionRealizationTwoWordData10
import VOA.DeligneAudit.D4FusionRealizationTwoWordData11
import VOA.DeligneAudit.D4FusionRealizationTwoWordData12
import VOA.DeligneAudit.D4FusionRealizationTwoWordData13
import VOA.DeligneAudit.D4FusionRealizationTwoWordData14
import VOA.DeligneAudit.D4FusionRealizationTwoWordData15
import VOA.DeligneAudit.D4FusionRealizationTwoWordData16
import VOA.DeligneAudit.D4FusionRealizationTwoWordData17
import VOA.DeligneAudit.D4FusionRealizationTwoWordData18
import VOA.DeligneAudit.D4FusionRealizationTwoWordData19
import VOA.DeligneAudit.D4FusionRealizationTwoWordData20
import VOA.DeligneAudit.D4FusionRealizationTwoWordData21
import VOA.DeligneAudit.D4FusionRealizationTwoWordData22
import VOA.DeligneAudit.D4FusionRealizationTwoWordData23
import VOA.DeligneAudit.D4FusionRealizationTwoWordData24
import VOA.DeligneAudit.D4FusionRealizationTwoWordData25
import VOA.DeligneAudit.D4FusionRealizationTwoWordData26

namespace VOA.DeligneAudit.D4Two.Certificate

def wordBlocks : List (List WordNode) :=
  [wordData00, wordData01, wordData02, wordData03, wordData04, wordData05, wordData06, wordData07,
    wordData08, wordData09, wordData10, wordData11, wordData12, wordData13, wordData14,
    wordData15, wordData16, wordData17, wordData18, wordData19, wordData20, wordData21,
    wordData22, wordData23, wordData24, wordData25, wordData26]

def wordNode (i : ℕ) : WordNode :=
  ((wordBlocks.getD (i / 32) []).getD (i % 32) default)

end VOA.DeligneAudit.D4Two.Certificate
