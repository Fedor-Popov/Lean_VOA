/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorChecks

/-!
# `E7` lattice realization: the index checks (light file)

The sign conditions of `LatData` for `e7LatData` (`LatticeRealizationE7`), on the integer form `formZ`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

open VOA.DeligneAudit.E7Lie (wt hvec formZ)
open VOA.DeligneAudit.DeligneCarrier.E7 (thetaH lowExpE7)

theorem chk_raising : ∀ e : Fin 133, 7 ≤ e.val ∧ e.val < 70 → 0 ≤ formZ (wt e) (wt 69) := by decide +kernel

theorem chk_cartan : ∀ h : Fin 133, h.val < 7 → formZ (hvec h) (wt 69) = (thetaH h : ℤ) := by decide +kernel

theorem chk_lowering : ∀ i : Fin 133, i.val ∈ [76, 75, 74, 73, 72, 71, 70] →
    formZ (wt i) (wt i) = 2 ∧ -(lowExpE7 i : ℤ) ≤ formZ (wt i) (wt 69) := by decide +kernel

theorem chk_fusion : ∀ x : Fin 133, 70 ≤ x.val →
    (if x = (132 : Fin 133) then (-2 : ℤ) else -1) ≤ formZ (wt x) (wt 69) := by decide +kernel

theorem chk_theta : formZ (wt 69) (wt 69) = 2 := by decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
