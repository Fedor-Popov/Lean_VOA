/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E7`: the sector table is the lattice-model cert table, rows `0..7` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem bridgeRow0 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 0 b = (VOA.DeligneAudit.E7Lie.sL 0 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow1 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 1 b = (VOA.DeligneAudit.E7Lie.sL 1 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow2 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 2 b = (VOA.DeligneAudit.E7Lie.sL 2 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow3 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 3 b = (VOA.DeligneAudit.E7Lie.sL 3 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow4 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 4 b = (VOA.DeligneAudit.E7Lie.sL 4 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow5 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 5 b = (VOA.DeligneAudit.E7Lie.sL 5 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow6 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 6 b = (VOA.DeligneAudit.E7Lie.sL 6 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow7 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 7 b = (VOA.DeligneAudit.E7Lie.sL 7 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
