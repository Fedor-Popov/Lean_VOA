/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E8`: the sector table is the lattice-model cert table, rows `184..191` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

theorem bridgeRow184 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 184 b = (VOA.DeligneAudit.E8Lie.sL 184 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow185 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 185 b = (VOA.DeligneAudit.E8Lie.sL 185 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow186 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 186 b = (VOA.DeligneAudit.E8Lie.sL 186 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow187 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 187 b = (VOA.DeligneAudit.E8Lie.sL 187 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow188 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 188 b = (VOA.DeligneAudit.E8Lie.sL 188 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow189 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 189 b = (VOA.DeligneAudit.E8Lie.sL 189 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow190 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 190 b = (VOA.DeligneAudit.E8Lie.sL 190 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow191 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 191 b = (VOA.DeligneAudit.E8Lie.sL 191 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E8
