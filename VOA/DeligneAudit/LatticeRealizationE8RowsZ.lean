/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E8`: the sector table is the lattice-model cert table, rows `200..207` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

theorem bridgeRow200 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 200 b = (VOA.DeligneAudit.E8Lie.sL 200 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow201 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 201 b = (VOA.DeligneAudit.E8Lie.sL 201 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow202 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 202 b = (VOA.DeligneAudit.E8Lie.sL 202 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow203 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 203 b = (VOA.DeligneAudit.E8Lie.sL 203 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow204 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 204 b = (VOA.DeligneAudit.E8Lie.sL 204 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow205 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 205 b = (VOA.DeligneAudit.E8Lie.sL 205 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow206 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 206 b = (VOA.DeligneAudit.E8Lie.sL 206 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow207 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 207 b = (VOA.DeligneAudit.E8Lie.sL 207 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E8
