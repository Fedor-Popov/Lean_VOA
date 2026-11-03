/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.LatticeRealizationE7RowsA
import VOA.DeligneAudit.LatticeRealizationE7RowsB
import VOA.DeligneAudit.LatticeRealizationE7RowsC
import VOA.DeligneAudit.LatticeRealizationE7RowsD
import VOA.DeligneAudit.LatticeRealizationE7RowsE
import VOA.DeligneAudit.LatticeRealizationE7RowsF
import VOA.DeligneAudit.LatticeRealizationE7RowsG
import VOA.DeligneAudit.LatticeRealizationE7RowsH
import VOA.DeligneAudit.LatticeRealizationE7RowsI
import VOA.DeligneAudit.LatticeRealizationE7RowsJ
import VOA.DeligneAudit.LatticeRealizationE7RowsK
import VOA.DeligneAudit.LatticeRealizationE7RowsL
import VOA.DeligneAudit.LatticeRealizationE7RowsM
import VOA.DeligneAudit.LatticeRealizationE7RowsN
import VOA.DeligneAudit.LatticeRealizationE7RowsO
import VOA.DeligneAudit.LatticeRealizationE7RowsP
import VOA.DeligneAudit.LatticeRealizationE7RowsQ

/-!
# `E7`: the sector table is the lattice-model cert table (all rows)
-/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem table_eq_sL (a b : Fin 133) :
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T a b = (VOA.DeligneAudit.E7Lie.sL a b).map (fun t => ((t.1 : ℕ), t.2)) := by
  revert b
  fin_cases a
  · exact bridgeRow0
  · exact bridgeRow1
  · exact bridgeRow2
  · exact bridgeRow3
  · exact bridgeRow4
  · exact bridgeRow5
  · exact bridgeRow6
  · exact bridgeRow7
  · exact bridgeRow8
  · exact bridgeRow9
  · exact bridgeRow10
  · exact bridgeRow11
  · exact bridgeRow12
  · exact bridgeRow13
  · exact bridgeRow14
  · exact bridgeRow15
  · exact bridgeRow16
  · exact bridgeRow17
  · exact bridgeRow18
  · exact bridgeRow19
  · exact bridgeRow20
  · exact bridgeRow21
  · exact bridgeRow22
  · exact bridgeRow23
  · exact bridgeRow24
  · exact bridgeRow25
  · exact bridgeRow26
  · exact bridgeRow27
  · exact bridgeRow28
  · exact bridgeRow29
  · exact bridgeRow30
  · exact bridgeRow31
  · exact bridgeRow32
  · exact bridgeRow33
  · exact bridgeRow34
  · exact bridgeRow35
  · exact bridgeRow36
  · exact bridgeRow37
  · exact bridgeRow38
  · exact bridgeRow39
  · exact bridgeRow40
  · exact bridgeRow41
  · exact bridgeRow42
  · exact bridgeRow43
  · exact bridgeRow44
  · exact bridgeRow45
  · exact bridgeRow46
  · exact bridgeRow47
  · exact bridgeRow48
  · exact bridgeRow49
  · exact bridgeRow50
  · exact bridgeRow51
  · exact bridgeRow52
  · exact bridgeRow53
  · exact bridgeRow54
  · exact bridgeRow55
  · exact bridgeRow56
  · exact bridgeRow57
  · exact bridgeRow58
  · exact bridgeRow59
  · exact bridgeRow60
  · exact bridgeRow61
  · exact bridgeRow62
  · exact bridgeRow63
  · exact bridgeRow64
  · exact bridgeRow65
  · exact bridgeRow66
  · exact bridgeRow67
  · exact bridgeRow68
  · exact bridgeRow69
  · exact bridgeRow70
  · exact bridgeRow71
  · exact bridgeRow72
  · exact bridgeRow73
  · exact bridgeRow74
  · exact bridgeRow75
  · exact bridgeRow76
  · exact bridgeRow77
  · exact bridgeRow78
  · exact bridgeRow79
  · exact bridgeRow80
  · exact bridgeRow81
  · exact bridgeRow82
  · exact bridgeRow83
  · exact bridgeRow84
  · exact bridgeRow85
  · exact bridgeRow86
  · exact bridgeRow87
  · exact bridgeRow88
  · exact bridgeRow89
  · exact bridgeRow90
  · exact bridgeRow91
  · exact bridgeRow92
  · exact bridgeRow93
  · exact bridgeRow94
  · exact bridgeRow95
  · exact bridgeRow96
  · exact bridgeRow97
  · exact bridgeRow98
  · exact bridgeRow99
  · exact bridgeRow100
  · exact bridgeRow101
  · exact bridgeRow102
  · exact bridgeRow103
  · exact bridgeRow104
  · exact bridgeRow105
  · exact bridgeRow106
  · exact bridgeRow107
  · exact bridgeRow108
  · exact bridgeRow109
  · exact bridgeRow110
  · exact bridgeRow111
  · exact bridgeRow112
  · exact bridgeRow113
  · exact bridgeRow114
  · exact bridgeRow115
  · exact bridgeRow116
  · exact bridgeRow117
  · exact bridgeRow118
  · exact bridgeRow119
  · exact bridgeRow120
  · exact bridgeRow121
  · exact bridgeRow122
  · exact bridgeRow123
  · exact bridgeRow124
  · exact bridgeRow125
  · exact bridgeRow126
  · exact bridgeRow127
  · exact bridgeRow128
  · exact bridgeRow129
  · exact bridgeRow130
  · exact bridgeRow131
  · exact bridgeRow132

end VOA.DeligneAudit.LatticeRealization.E7
