/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E7`: the sector table is the lattice-model cert table, rows `32..39` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem bridgeRow32 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 32 b = (VOA.DeligneAudit.E7Lie.sL 32 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow33 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 33 b = (VOA.DeligneAudit.E7Lie.sL 33 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow34 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 34 b = (VOA.DeligneAudit.E7Lie.sL 34 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow35 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 35 b = (VOA.DeligneAudit.E7Lie.sL 35 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow36 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 36 b = (VOA.DeligneAudit.E7Lie.sL 36 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow37 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 37 b = (VOA.DeligneAudit.E7Lie.sL 37 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow38 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 38 b = (VOA.DeligneAudit.E7Lie.sL 38 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow39 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 39 b = (VOA.DeligneAudit.E7Lie.sL 39 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
