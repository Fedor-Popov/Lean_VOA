/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTable
import VOA.DeligneAudit.DeligneSectorD4Table

/-!
# `D4`: the sector table is the lattice-model cert table, rows `7..13` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.D4

theorem bridgeRow7 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 7 b = (VOA.DeligneAudit.D4Lie.sL 7 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow8 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 8 b = (VOA.DeligneAudit.D4Lie.sL 8 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow9 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 9 b = (VOA.DeligneAudit.D4Lie.sL 9 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow10 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 10 b = (VOA.DeligneAudit.D4Lie.sL 10 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow11 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 11 b = (VOA.DeligneAudit.D4Lie.sL 11 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow12 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 12 b = (VOA.DeligneAudit.D4Lie.sL 12 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow13 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 13 b = (VOA.DeligneAudit.D4Lie.sL 13 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.D4
