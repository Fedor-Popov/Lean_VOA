/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCubicNilpotency
import VOA.Examples.Sl2SemiInfiniteCubicMixed

/-!
# Cancellation of the semi-infinite BRST anomaly at level minus four

The self-product of the actual BRST state is computed for every
`AffineSl2Action`: its coefficient is `k + 4`. The ghost contribution `4`
is proved by explicit cubic products, not assumed.

To identify the operator square with one half the residue of this self-product,
the theorem `semiInfiniteQ_sq` explicitly takes matter translation covariance
and the hypotheses needed to bundle the tensor SVA. These give the all-fields
commutator formula. No nilpotency datum is added to the matter structure.

OPEN: remove translation and tensor-grading hypotheses from the operator-square
theorem by completing the locally finite pure mode-algebra rearrangement. The
bare `AffineSl2Action` self-product calculation below already needs none of them.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The exact BRST self-product anomaly, with no extra matter hypotheses. -/
theorem semiInfiniteQ_brstState_anomaly (A : AffineSl2Action V k) :
    semiInfiniteQ A (brstState A) =
      (k + 4) • (V.vacuum ⊗ₜ[ℂ] ghostAnomalyState) := by
  rw [semiInfiniteQ_brstState_ghost_reduction, ghostBRSTState_zero_self,
    ← add_smul, TensorProduct.tmul_smul]

/-- At level minus four the actual BRST state is closed, for every affine
matter action, without a translation or nilpotency assumption. -/
theorem semiInfiniteQ_brstState_zero (A : AffineSl2Action V (-4)) :
    semiInfiniteQ A (brstState A) = 0 := by
  rw [semiInfiniteQ_brstState_anomaly]
  norm_num

/-- The exact operator-square anomaly for translated matter. All ghost OPE
calculations and the tensor commutator transfer are theorems. -/
theorem semiInfiniteQ_square_anomaly (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hV : TensorVA.ParityCompatible V)
    (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    semiInfiniteQ A * semiInfiniteQ A =
      ((1 / 2 : ℂ) * (k + 4)) •
        mode (TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostAnomalyState)) 0 := by
  rw [semiInfiniteQ_square_eq_residue A hV hg
      (matterGhost_zeroModeCommutator H hV hg),
    semiInfiniteQ_brstState_anomaly, map_smul, mode_smul, smul_smul]

/-- The actual semi-infinite charge is square-zero at level minus four.
Matter translation and the tensor grading hypotheses are explicit; no
BRST-specific commutator or square-zero assumption is used. -/
theorem semiInfiniteQ_sq (A : AffineSl2Action V (-4))
    (H : TranslationCovariant V) (hV : TensorVA.ParityCompatible V)
    (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    semiInfiniteQ A * semiInfiniteQ A = 0 := by
  rw [semiInfiniteQ_square_anomaly A H hV hg]
  norm_num

end VOA.Sl2SemiInfinite
