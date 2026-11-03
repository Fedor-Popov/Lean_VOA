/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteChargeProducts
import VOA.Examples.Sl2SemiInfiniteGhostCAR

/-! # The cubic ghost correction on the dual generators

These are actual state products, derived from the canonical anticommutators
and the zero-mode derivation formula. No ghost OPE is supplied as a hypothesis.
-/

namespace VOA.Sl2SemiInfinite

open AffineVOA
open scoped BigOperators TensorProduct

theorem cGhost_bGhost_product (a b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (cGhost a)) n (bGhost b) =
      if a = b ∧ n = 0 then sl2GhostSVA.vacuum else 0 := by
  simpa using ghostGenerator_nonneg_product a b 1 0 n hn

/-- A `c` zero mode contracts exactly the antighost in a bilinear. -/
theorem cGhost_zero_ghostBilinear (a c b : Fin 3) :
    mode (sl2GhostSVA.Y (cGhost a)) 0 (ghostBilinear c b) =
      if a = c then cGhost b else 0 := by
  have h := odd_zeroMode_deriv
    (zeroModeCommutator_of_translation translationCovariant_sl2GhostSVA)
    (cGhost_odd a) (bGhost c) (cGhost b) (-1)
  rw [cGhost_bGhost_product a c 0 (by omega), cGhost_product_nonneg a b 0 (by omega),
    map_zero, add_zero] at h
  change mode (sl2GhostSVA.Y (cGhost a)) 0 (ghostBilinear c b) = _ at h
  rw [h]
  by_cases hac : a = c
  · simp only [hac, true_and, and_self, ite_true, sl2GhostSVA.vacuum_Y,
      mode_apply, neg_neg, sub_self, FormalDist.one_apply, ite_true,
      Module.End.one_apply]
  · simp only [hac, false_and, if_false, map_zero, mode_zero, LinearMap.zero_apply]

/-- The dual-ghost contraction with the adjoint ghost current. -/
theorem cGhost_zero_ghostCurrent (b a : Fin 3) :
    mode (sl2GhostSVA.Y (cGhost b)) 0 (ghostCurrent a) =
      ∑ i : Fin 3, fabc a i b • cGhost i := by
  simp only [ghostCurrent, map_sum, map_smul, cGhost_zero_ghostBilinear]
  simp [ghostCurrentCoefficient, eq_comm]

/-- The cubic correction induces the Chevalley-Eilenberg differential on
the dual generators. This fixes the factor one half and its sign. -/
theorem cGhost_zero_ghostBRSTState (b : Fin 3) :
    mode (sl2GhostSVA.Y (cGhost b)) 0 ghostBRSTState =
      -(1 / 2 : ℂ) • ghostCEQuadratic b := by
  have hder (a : Fin 3) := odd_zeroMode_deriv
    (zeroModeCommutator_of_translation translationCovariant_sl2GhostSVA)
    (cGhost_odd b) (cGhost a) (ghostCurrent a) (-1)
  have hterm (a : Fin 3) :
      mode (sl2GhostSVA.Y (cGhost b)) 0
        (mode (sl2GhostSVA.Y (cGhost a)) (-1) (ghostCurrent a)) =
      -(∑ i : Fin 3, fabc a i b •
        mode (sl2GhostSVA.Y (cGhost a)) (-1) (cGhost i)) := by
    rw [hder a, cGhost_product_nonneg b a 0 (by omega), map_zero, mode_zero,
      LinearMap.zero_apply, zero_add, BRST.sgn_odd (cGhost_odd a), map_neg,
      mode_neg, LinearMap.neg_apply, cGhost_zero_ghostCurrent, map_sum]
    simp only [map_smul]
  simp only [ghostBRSTState, map_smul, map_sum, hterm, Finset.sum_neg_distrib,
    smul_neg, neg_smul, ghostCEQuadratic]

/-- The same mixed product in the opposite order, using the proved zero-product
skew identity. -/
theorem ghostBRSTState_zero_cGhost_eq (b : Fin 3) :
    mode (sl2GhostSVA.Y ghostBRSTState) 0 (cGhost b) =
      -(1 / 2 : ℂ) • ghostCEQuadratic b := by
  rw [ghostBRSTState_zero_cGhost, cGhost_zero_ghostBRSTState]

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- All terms involving matter-current states cancel in the BRST self-product.
Only the central matter contribution and the cubic ghost self-product remain. -/
theorem semiInfiniteQ_brstState_ghost_reduction (A : AffineSl2Action V k) :
    semiInfiniteQ A (brstState A) = V.vacuum ⊗ₜ[ℂ]
      (k • ghostAnomalyState + mode (sl2GhostSVA.Y ghostBRSTState) 0 ghostBRSTState) := by
  rw [semiInfiniteQ_brstState_expansion]
  simp only [ghostBRSTState_zero_cGhost_eq, smul_smul]
  norm_num

end VOA.Sl2SemiInfinite
