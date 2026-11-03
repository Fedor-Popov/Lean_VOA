/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTable
import VOA.DeligneAudit.DeligneSectorD4Table

/-!
# `D4`: the sector table is the lattice-model cert table, rows `0..6` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.D4

theorem bridgeRow0 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 0 b = (VOA.DeligneAudit.D4Lie.sL 0 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow1 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 1 b = (VOA.DeligneAudit.D4Lie.sL 1 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow2 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 2 b = (VOA.DeligneAudit.D4Lie.sL 2 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow3 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 3 b = (VOA.DeligneAudit.D4Lie.sL 3 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow4 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 4 b = (VOA.DeligneAudit.D4Lie.sL 4 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow5 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 5 b = (VOA.DeligneAudit.D4Lie.sL 5 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow6 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 6 b = (VOA.DeligneAudit.D4Lie.sL 6 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.D4
