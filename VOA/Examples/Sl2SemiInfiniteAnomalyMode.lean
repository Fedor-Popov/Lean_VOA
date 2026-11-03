/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGhostAnomaly

/-! # The derivative-ghost anomaly has a nonzero zero mode -/

namespace VOA.Sl2SemiInfinite

open Ghost SympFerm AffineVOA
open Module (End)
open scoped TensorProduct

/-- The derivative-pair state occurring in the Cartan part of the anomaly. -/
noncomputable def ghostDerivativePair : FockSF :=
  stWordSF [((1, 1) : ℕ × Fin 2), (0, 1)]

/-- Its exterior representative is the first derivative creator applied to `c`. -/
theorem ghostDerivativePair_eq :
    ghostDerivativePair = ghField 1 1 (ghostZeroWord [1]) := rfl

/-- The derivative pair has even parity. -/
theorem ghostDerivativePair_even : ghostDerivativePair ∈ bcGhostSVA.parity 0 := by
  have h := stWordSF_mem_evenOdd [((1, 1) : ℕ × Fin 2), (0, 1)]
  norm_num at h
  exact h

/-- The reconstructed derivative-pair field is the signed normal product. -/
theorem ghostDerivativePair_field :
    YGh ghostDerivativePair =
      nprodε (-1) ((ghField_isField 1).deriv) (ghField_isField 1) := by
  rw [ghostDerivativePair, YGh_word, YwordGh_cons]
  simp only [List.length_cons, List.length_nil, zero_add, Nat.cast_one, koszul_one_one]
  congr 1
  · simp [ghGenField]
  · exact ghostWord_single_field 1

/-- The derivative pair has simple pole twice the derivative ghost against `b`. -/
theorem ghostDerivativePair_zero_b :
    bcGhostSVA.Y ghostDerivativePair (-1) (ghostZeroWord [0]) =
      (2 : ℂ) • ghField 1 1 (ghostZeroWord []) := by
  change YGh ghostDerivativePair (-1) (ghostZeroWord [0]) = _
  rw [ghostDerivativePair_field, nprodε_apply]
  rw [finsum_eq_sum_of_support_subset _ (s := {-2, 0})]
  · norm_num [normalOrderedε_apply, deriv_apply, LinearMap.smul_apply,
      ghField_negOne_single, show (1 : Fin 2) + 1 = 0 from by decide]
    module
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    apply hj
    rw [normalOrderedε_apply]
    split_ifs with hj0
    · change VOA.deriv (ghField 1) j (ghField 1 (-1 - j) (ghostZeroWord [0])) = 0
      rw [ghField_lower_word 1 [0] (-1 - j) (by omega), map_zero]
    · change (-1 : ℂ) • ghField 1 (-1 - j)
        (VOA.deriv (ghField 1) j (ghostZeroWord [0])) = 0
      rw [deriv_apply, LinearMap.smul_apply]
      by_cases hj1 : j = -1
      · subst j
        norm_num
      · rw [ghField_lower_word 1 [0] (j + 1) (by omega), smul_zero, map_zero, smul_zero]

/-- The anomaly zero mode sends the Cartan antighost to four times the derivative ghost. -/
theorem ghostAnomaly_zero_bGhost_h :
    mode (sl2GhostSVA.Y ghostAnomalyState) 0 (bGhost colH) =
      (4 : ℂ) • ghostEmbed colH (ghField 1 1 (ghostZeroWord [])) := by
  have hleft (x : GhostPairSpace) :
      mode (sl2GhostSVA.Y (x ⊗ₜ[ℂ] ghostZeroWord [])) 0 (bGhost colH) = 0 := by
    change TensorVA.tenY ghostPairSVA bcGhostSVA (x ⊗ₜ[ℂ] ghostZeroWord []) (-1)
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [0]) = 0
    rw [tenY_left_ghostVac]
    have hz : ghostPairSVA.Y x (-1) (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) = 0 :=
      TensorVA.Ycoeff_vacuum_neg ghostPairSVA x (by omega)
    rw [hz, TensorProduct.zero_tmul]
  have hcart : mode (sl2GhostSVA.Y
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ]
        ghField 1 1 (ghostZeroWord [1]))) 0 (bGhost colH) =
      (2 : ℂ) • ghostEmbed colH (ghField 1 1 (ghostZeroWord [])) := by
    rw [← ghostDerivativePair_eq]
    change TensorVA.tenY ghostPairSVA bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] ghostDerivativePair) (-1)
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] ghostZeroWord [0]) = _
    rw [tenY_right_unit, ghostDerivativePair_zero_b, TensorProduct.tmul_smul]
    rfl
  rw [ghostAnomalyState_tensor, map_add, map_sub, map_smul,
    mode_add, mode_sub, mode_smul]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    hleft, hcart]
  module

/-- The derivative ghost in the Cartan factor is nonzero. -/
theorem ghostEmbed_derivative_c_ne_zero :
    ghostEmbed colH (ghField 1 1 (ghostZeroWord [])) ≠ 0 := by
  have hc : annBase (1, 1) (ghField 1 1 (ghostZeroWord [])) = ghostZeroWord [] := by
    change annBase (1, 1) (stWordSF [((1, 1) : ℕ × Fin 2)]) = stWordSF []
    simp [annBase_stWordSF_cons, annBase_stWordSF_nil, ← stWordSF_nil]
  have hmap : TensorProduct.map (LinearMap.id : End ℂ GhostPairSpace) (annBase (1, 1))
      (ghostEmbed colH (ghField 1 1 (ghostZeroWord []))) = sl2GhostSVA.vacuum := by
    change TensorProduct.map (LinearMap.id : End ℂ GhostPairSpace) (annBase (1, 1))
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ]
        ghField 1 1 (ghostZeroWord [])) = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hc]
    rfl
  intro hz
  rw [hz, map_zero] at hmap
  exact sl2GhostSVA_vacuum_ne_zero hmap.symm

/-- The anomaly is nontrivial as an operator, not just as a state. -/
theorem ghostAnomaly_zero_mode_ne_zero : mode (sl2GhostSVA.Y ghostAnomalyState) 0 ≠ 0 := by
  intro hz
  have h := LinearMap.congr_fun hz (bGhost colH)
  rw [ghostAnomaly_zero_bGhost_h, LinearMap.zero_apply] at h
  exact ghostEmbed_derivative_c_ne_zero
    ((smul_eq_zero.mp h).resolve_left (by norm_num))

end VOA.Sl2SemiInfinite
