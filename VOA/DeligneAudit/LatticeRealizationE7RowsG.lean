/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E7`: the sector table is the lattice-model cert table, rows `48..55` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem bridgeRow48 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 48 b = (VOA.DeligneAudit.E7Lie.sL 48 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow49 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 49 b = (VOA.DeligneAudit.E7Lie.sL 49 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow50 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 50 b = (VOA.DeligneAudit.E7Lie.sL 50 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow51 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 51 b = (VOA.DeligneAudit.E7Lie.sL 51 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow52 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 52 b = (VOA.DeligneAudit.E7Lie.sL 52 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow53 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 53 b = (VOA.DeligneAudit.E7Lie.sL 53 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow54 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 54 b = (VOA.DeligneAudit.E7Lie.sL 54 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow55 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 55 b = (VOA.DeligneAudit.E7Lie.sL 55 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
