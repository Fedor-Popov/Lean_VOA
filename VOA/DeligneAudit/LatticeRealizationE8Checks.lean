/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable
import VOA.DeligneAudit.E8SectorChecks

/-!
# `E8` lattice realization: the index checks (light file)

The sign conditions of `LatData` for `e8LatData` (`LatticeRealizationE8`), on the integer form `formZ`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

open VOA.DeligneAudit.E8Lie (wt hvec formZ)
open VOA.DeligneAudit.DeligneCarrier.E8 (thetaH lowExpE8)

theorem chk_raising : ∀ e : Fin 248, 8 ≤ e.val ∧ e.val < 128 → 0 ≤ formZ (wt e) (wt 127) := by decide +kernel

theorem chk_cartan : ∀ h : Fin 248, h.val < 8 → formZ (hvec h) (wt 127) = (thetaH h : ℤ) := by decide +kernel

theorem chk_lowering : ∀ i : Fin 248, i.val ∈ [135, 134, 133, 132, 131, 130, 129, 128] →
    formZ (wt i) (wt i) = 2 ∧ -(lowExpE8 i : ℤ) ≤ formZ (wt i) (wt 127) := by decide +kernel

theorem chk_fusion : ∀ x : Fin 248, 128 ≤ x.val →
    (if x = (247 : Fin 248) then (-2 : ℤ) else -1) ≤ formZ (wt x) (wt 127) := by decide +kernel

theorem chk_theta : formZ (wt 127) (wt 127) = 2 := by decide +kernel

end VOA.DeligneAudit.LatticeRealization.E8
