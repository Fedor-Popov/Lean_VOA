/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteModes
import VOA.Examples.Sl2SemiInfiniteDifferential

/-!
# Finite state-product expansion of the semi-infinite charge

The full mode formula becomes finite when applied to the BRST state itself.
Only current modes zero and one survive on the current-times-ghost states;
only current mode minus one survives on the cubic ghost state. These
truncations follow from actual creation, the affine commutator, and the
nonnegative ghost weight grading.

The remaining cubic ghost products are proved in `Sl2SemiInfiniteCubicMixed`
and `Sl2SemiInfiniteCubicNilpotency`. Their substitution into the expansion
below gives the exact `k + 4` anomaly in `Sl2SemiInfiniteNilpotency`.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open AffineVOA
open scoped BigOperators TensorProduct

/-- Two weight-zero ghosts have no singular state products. -/
theorem cGhost_product_nonneg (a b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (cGhost a)) n (cGhost b) = 0 := by
  have h := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a)
    (cGhost b) (cGhost_weight b) n
  have hbot : sl2GhostSVA.grading (0 + 0 - (n : ℂ) - 1) = ⊥ := by
    apply natSupported_sl2GhostSVA
    rintro ⟨m, hm⟩
    have hm' : ((m : ℤ) : ℂ) = ((-n - 1 : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have : (m : ℤ) = -n - 1 := by exact_mod_cast hm'
    omega
  rw [hbot] at h
  exact h

/-- Only the zero mode of a `c` ghost can have a singular product with the
weight-one cubic correction. -/
theorem cGhost_product_ghostBRSTState_high (a : Fin 3) (n : ℤ) (hn : 1 ≤ n) :
    mode (sl2GhostSVA.Y (cGhost a)) n ghostBRSTState = 0 := by
  have h := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a)
    ghostBRSTState ghostBRSTState_weight n
  have hbot : sl2GhostSVA.grading (0 + 1 - (n : ℂ) - 1) = ⊥ := by
    apply natSupported_sl2GhostSVA
    rintro ⟨m, hm⟩
    have hm' : ((m : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have : (m : ℤ) = -n := by exact_mod_cast hm'
    omega
  rw [hbot] at h
  exact h

/-- The quadratic Chevalley-Eilenberg expression in the dual ghosts. -/
noncomputable def ghostCEQuadratic (c : Fin 3) : Sl2GhostSpace :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    fabc a b c • mode (sl2GhostSVA.Y (cGhost a)) (-1) (cGhost b)

/-- The derivative-ghost state multiplying the level in the BRST anomaly. -/
noncomputable def ghostAnomalyState : Sl2GhostSpace :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    kappa a b • mode (sl2GhostSVA.Y (cGhost a)) (-2) (cGhost b)

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The current-times-ghost part on another current-times-ghost state is
exactly its simple-pole and central contributions. -/
theorem rawCurrentCharge_current_cGhost (A : AffineSl2Action V k) (a b : Fin 3) :
    TensorVA.rawCoeff V sl2GhostSVA (A.current a) (cGhost a) (-1)
      (A.current b ⊗ₜ[ℂ] cGhost b) =
      (∑ c : Fin 3, fabc a b c • A.current c) ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y (cGhost a)) (-1) (cGhost b) +
      (k * kappa a b) • V.vacuum ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y (cGhost a)) (-2) (cGhost b) := by
  rw [rawCurrentCharge_tmul]
  rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ))]
  · simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      zero_ne_one, not_false_eq_true, neg_zero, zero_sub]
    rw [A.current_product_zero, A.current_product_one]
    simp only [show (-1 - 1 : ℤ) = -2 by omega, TensorProduct.smul_tmul']
  · intro n hn
    by_contra hmem
    have hn0 : n ≠ 0 := by simpa using fun h => hmem (by simp [h])
    have hn1 : n ≠ 1 := by simpa using fun h => hmem (by simp [h])
    change _ ≠ 0 at hn
    apply hn
    dsimp only
    by_cases hneg : n < 0
    · rw [cGhost_product_nonneg a b (-n - 1) (by omega), TensorProduct.tmul_zero]
    · rw [A.current_product_high a b n (by omega), TensorProduct.zero_tmul]

/-- On the vacuum times the cubic correction, only current mode minus one
survives. This is a finite-state calculation, independent of translation. -/
theorem rawCurrentCharge_vacuum_cubic (A : AffineSl2Action V k) (a : Fin 3) :
    TensorVA.rawCoeff V sl2GhostSVA (A.current a) (cGhost a) (-1)
      (V.vacuum ⊗ₜ[ℂ] ghostBRSTState) =
      A.current a ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) 0 ghostBRSTState := by
  rw [rawCurrentCharge_tmul, finsum_eq_single _ (-1)]
  · rw [(V.creation _).1]
    rfl
  · intro n hn
    by_cases hnonneg : 0 ≤ n
    · rw [(V.creation _).2 n hnonneg, TensorProduct.zero_tmul]
    · rw [cGhost_product_ghostBRSTState_high a (-n - 1) (by omega),
        TensorProduct.tmul_zero]

/-- The complete charge on each current-times-ghost summand of its own state. -/
theorem semiInfiniteQ_current_cGhost (A : AffineSl2Action V k) (b : Fin 3) :
    semiInfiniteQ A (A.current b ⊗ₜ[ℂ] cGhost b) =
      (∑ a : Fin 3,
        ((∑ c : Fin 3, fabc a b c • A.current c) ⊗ₜ[ℂ]
            mode (sl2GhostSVA.Y (cGhost a)) (-1) (cGhost b) +
          (k * kappa a b) • V.vacuum ⊗ₜ[ℂ]
            mode (sl2GhostSVA.Y (cGhost a)) (-2) (cGhost b))) +
      A.current b ⊗ₜ[ℂ] mode (sl2GhostSVA.Y ghostBRSTState) 0 (cGhost b) := by
  rw [semiInfiniteQ_eq_modeCharges, Module.End.mul_apply, TensorVA.kappaTen_tmul,
    (TensorVA.parGr V).koszulOp_homog 1 (A.current_even b), koszul_zero_right,
    one_smul, LinearMap.add_apply]
  simp only [matterModeCharge, LinearMap.sum_apply, rawCurrentCharge_current_cGhost,
    cubicModeCharge, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The complete charge on the cubic summand of its own state. -/
theorem semiInfiniteQ_vacuum_cubic (A : AffineSl2Action V k) :
    semiInfiniteQ A (V.vacuum ⊗ₜ[ℂ] ghostBRSTState) =
      (∑ a : Fin 3, A.current a ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y (cGhost a)) 0 ghostBRSTState) +
      V.vacuum ⊗ₜ[ℂ] mode (sl2GhostSVA.Y ghostBRSTState) 0 ghostBRSTState := by
  rw [semiInfiniteQ_eq_modeCharges, Module.End.mul_apply, TensorVA.kappaTen_tmul,
    (TensorVA.parGr V).koszulOp_homog 1 V.vacuum_parity, koszul_zero_right,
    one_smul, LinearMap.add_apply]
  simp only [matterModeCharge, LinearMap.sum_apply, rawCurrentCharge_vacuum_cubic,
    cubicModeCharge, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The two mixed cubic/`c` zero products agree. The higher `c` products
vanish by weight, so the full mode commutator gives this skew-symmetry without
any separately assumed skew formula. -/
theorem ghostBRSTState_zero_cGhost (a : Fin 3) :
    mode (sl2GhostSVA.Y ghostBRSTState) 0 (cGhost a) =
      mode (sl2GhostSVA.Y (cGhost a)) 0 ghostBRSTState := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_two
    (cGhost_odd a) ghostBRSTState_odd
    (fun j hj => cGhost_product_ghostBRSTState_high a j (by omega)) (-1) 0
  have hv := congrArg (fun f : End ℂ Sl2GhostSpace => f sl2GhostSVA.vacuum) h
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.neg_apply, Module.End.mul_apply,
    LinearMap.add_apply, koszul_one_one, neg_one_smul,
    (sl2GhostSVA.creation ghostBRSTState).2 0 (by omega), map_zero,
    (sl2GhostSVA.creation (cGhost a)).1, zero_sub, neg_neg,
    add_zero, cGhost_product_ghostBRSTState_high a 1 (by omega)] at hv
  simpa only [map_zero, mode_zero, LinearMap.zero_apply, smul_zero, add_zero,
    (sl2GhostSVA.creation _).1] using hv

/-- The BRST state's zero product with itself, reduced to finite ghost
calculations. The matter commutator has been used in full: its simple pole
produces `ghostCEQuadratic`, and its central term produces `k` times the
explicit derivative-ghost anomaly. No cubic-ghost identity is assumed. -/
theorem semiInfiniteQ_brstState_expansion (A : AffineSl2Action V k) :
    semiInfiniteQ A (brstState A) =
      (∑ a : Fin 3, A.current a ⊗ₜ[ℂ]
        (ghostCEQuadratic a + (2 : ℂ) •
          mode (sl2GhostSVA.Y ghostBRSTState) 0 (cGhost a))) +
      V.vacuum ⊗ₜ[ℂ] (k • ghostAnomalyState +
        mode (sl2GhostSVA.Y ghostBRSTState) 0 ghostBRSTState) := by
  rw [brstState, map_add, map_sum]
  simp only [semiInfiniteQ_current_cGhost, semiInfiniteQ_vacuum_cubic,
    ← ghostBRSTState_zero_cGhost]
  simp only [ghostCEQuadratic, ghostAnomalyState, Fin.sum_univ_three,
    TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_add, smul_smul]
  module

end VOA.Sl2SemiInfinite
