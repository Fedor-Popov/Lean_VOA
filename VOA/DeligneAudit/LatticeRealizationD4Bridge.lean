/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.LatticeRealizationD4RowsA
import VOA.DeligneAudit.LatticeRealizationD4RowsB
import VOA.DeligneAudit.LatticeRealizationD4RowsC
import VOA.DeligneAudit.LatticeRealizationD4RowsD

/-!
# `D4`: the sector table is the lattice-model cert table (all rows)
-/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.LatticeRealization.D4

theorem table_eq_sL (a b : Fin 28) :
    VOA.DeligneAudit.DeligneSector.D4.br a b = (VOA.DeligneAudit.D4Lie.sL a b).map (fun t => ((t.1 : ℕ), t.2)) := by
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

end VOA.DeligneAudit.LatticeRealization.D4
