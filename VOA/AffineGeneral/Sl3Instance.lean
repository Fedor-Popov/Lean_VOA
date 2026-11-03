/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Virasoro
import VOA.Examples.AffineSl3Structure
import VOA.Examples.AffineSl3InvariantPairing

/-!
# The sl₃ instance of the general affine VOA

`sl3Data : LieData AffineSl3.form (Fin 8)` packages the existing sl₃ facts (trace form invariance,
the Chevalley basis, its trace-dual family, adjoint Casimir `6 = 2·3`), so the general construction
`affineVOA` produces a VOA on the carrier `vacuumSpace form form_invariant k` (the carrier of the bespoke
`AffineSl3.affineSl3VOA`), with dual Coxeter number `3` and central charge `8k/(k+3)`.

Only the sl₃ Lie-algebra files are used, not the Wakimoto realization.
-/

namespace VOA.AffineGeneral

open VOA.AffineSl3

noncomputable section

/-- Lie data of `sl₃` with the trace form: Chevalley basis, trace-dual family, `h = 3`. -/
def sl3Data : LieData AffineSl3.form (Fin 8) where
  invariant := form_invariant
  basis := chevalleyBasis
  dual := dualGenerator
  pair i j := by rw [chevalleyBasis_apply]; exact generator_dual i j
  h := 3
  casimir x := by
    simp only [chevalleyBasis_apply]
    rw [adjoint_casimir]
    norm_num

/-- The general universal affine VOA at `𝔤 = sl₃`. -/
abbrev sl3VOA (k : ℂ) (hk : k + 3 ≠ 0) : VertexOperatorAlgebra (Vacuum sl3Data k) :=
  affineVOA sl3Data k hk

/-- Its central charge is the sl₃ Sugawara value `8k/(k+3)`. -/
theorem sl3VOA_centralCharge (k : ℂ) (hk : k + 3 ≠ 0) :
    (sl3VOA k hk).centralCharge = 8 * k / (k + 3) := by
  show (Fintype.card (Fin 8) : ℂ) * k / (k + sl3Data.h) = _
  simp [sl3Data]

end

end VOA.AffineGeneral
