/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTable
import VOA.DeligneAudit.DeligneSectorD4Table

/-!
# `D4`: the sector table is the lattice-model cert table, rows `21..27` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.D4

theorem bridgeRow21 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 21 b = (VOA.DeligneAudit.D4Lie.sL 21 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow22 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 22 b = (VOA.DeligneAudit.D4Lie.sL 22 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow23 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 23 b = (VOA.DeligneAudit.D4Lie.sL 23 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow24 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 24 b = (VOA.DeligneAudit.D4Lie.sL 24 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow25 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 25 b = (VOA.DeligneAudit.D4Lie.sL 25 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow26 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 26 b = (VOA.DeligneAudit.D4Lie.sL 26 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow27 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 27 b = (VOA.DeligneAudit.D4Lie.sL 27 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.D4
