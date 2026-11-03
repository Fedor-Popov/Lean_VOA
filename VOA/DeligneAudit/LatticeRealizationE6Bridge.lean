/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.LatticeRealizationE6RowsA
import VOA.DeligneAudit.LatticeRealizationE6RowsB
import VOA.DeligneAudit.LatticeRealizationE6RowsC
import VOA.DeligneAudit.LatticeRealizationE6RowsD
import VOA.DeligneAudit.LatticeRealizationE6RowsE
import VOA.DeligneAudit.LatticeRealizationE6RowsF
import VOA.DeligneAudit.LatticeRealizationE6RowsG
import VOA.DeligneAudit.LatticeRealizationE6RowsH
import VOA.DeligneAudit.LatticeRealizationE6RowsI
import VOA.DeligneAudit.LatticeRealizationE6RowsJ

/-!
# `E6`: the sector table is the lattice-model cert table (all rows)
-/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem table_eq_sL (a b : Fin 78) :
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T a b = (VOA.DeligneAudit.E6Lat.sL a b).map (fun t => ((t.1 : ℕ), t.2)) := by
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

end VOA.DeligneAudit.LatticeRealization.E6
