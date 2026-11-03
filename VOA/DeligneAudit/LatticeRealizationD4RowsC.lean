/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTable
import VOA.DeligneAudit.DeligneSectorD4Table

/-!
# `D4`: the sector table is the lattice-model cert table, rows `14..20` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.D4

theorem bridgeRow14 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 14 b = (VOA.DeligneAudit.D4Lie.sL 14 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow15 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 15 b = (VOA.DeligneAudit.D4Lie.sL 15 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow16 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 16 b = (VOA.DeligneAudit.D4Lie.sL 16 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow17 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 17 b = (VOA.DeligneAudit.D4Lie.sL 17 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow18 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 18 b = (VOA.DeligneAudit.D4Lie.sL 18 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow19 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 19 b = (VOA.DeligneAudit.D4Lie.sL 19 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow20 : ∀ b : Fin 28,
    VOA.DeligneAudit.DeligneSector.D4.br 20 b = (VOA.DeligneAudit.D4Lie.sL 20 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.D4
