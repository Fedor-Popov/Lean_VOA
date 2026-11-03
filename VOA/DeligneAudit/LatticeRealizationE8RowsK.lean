/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E8`: the sector table is the lattice-model cert table, rows `80..87` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

theorem bridgeRow80 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 80 b = (VOA.DeligneAudit.E8Lie.sL 80 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow81 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 81 b = (VOA.DeligneAudit.E8Lie.sL 81 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow82 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 82 b = (VOA.DeligneAudit.E8Lie.sL 82 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow83 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 83 b = (VOA.DeligneAudit.E8Lie.sL 83 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow84 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 84 b = (VOA.DeligneAudit.E8Lie.sL 84 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow85 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 85 b = (VOA.DeligneAudit.E8Lie.sL 85 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow86 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 86 b = (VOA.DeligneAudit.E8Lie.sL 86 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow87 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 87 b = (VOA.DeligneAudit.E8Lie.sL 87 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E8
