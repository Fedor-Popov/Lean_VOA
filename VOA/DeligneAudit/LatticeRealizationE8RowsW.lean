/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E8`: the sector table is the lattice-model cert table, rows `176..183` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

theorem bridgeRow176 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 176 b = (VOA.DeligneAudit.E8Lie.sL 176 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow177 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 177 b = (VOA.DeligneAudit.E8Lie.sL 177 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow178 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 178 b = (VOA.DeligneAudit.E8Lie.sL 178 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow179 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 179 b = (VOA.DeligneAudit.E8Lie.sL 179 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow180 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 180 b = (VOA.DeligneAudit.E8Lie.sL 180 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow181 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 181 b = (VOA.DeligneAudit.E8Lie.sL 181 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow182 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 182 b = (VOA.DeligneAudit.E8Lie.sL 182 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow183 : ∀ b : Fin 248,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T 183 b = (VOA.DeligneAudit.E8Lie.sL 183 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E8
