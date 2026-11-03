/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteDifferential
import VOA.Examples.Sl2SemiInfiniteGhostCAR

/-! # The ghost Cartan homotopy identity from canonical anticommutators

The antighost zero modes contract the cubic state to the adjoint ghost currents.
The opposite zero-product order is proved from the complete mode commutator and
the vanishing higher antighost products, without assuming skew-symmetry.
-/

namespace VOA.Sl2SemiInfinite
open Module (End)
open AffineVOA
open scoped BigOperators

theorem bGhost_cGhost_product (a b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (bGhost a)) n (cGhost b) =
      if a = b ∧ n = 0 then sl2GhostSVA.vacuum else 0 := by
  simpa using ghostGenerator_nonneg_product a b 0 1 n hn

/-- Negative first products of `b` and `c` anticommute. -/
theorem cGhost_negOne_bGhost (a b : Fin 3) :
    mode (sl2GhostSVA.Y (cGhost a)) (-1) (bGhost b) = -ghostBilinear b a := by
  have h := congrArg (fun f : End ℂ Sl2GhostSpace => f sl2GhostSVA.vacuum)
    (bGhost_cGhost_modes_anticomm b a (-1) (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply,
    (sl2GhostSVA.creation (cGhost a)).1, (sl2GhostSVA.creation (bGhost b)).1,
    show ¬ ((-1 : ℤ) + -1 + 1 = 0) by omega, and_false, if_false,
    LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h

/-- An antighost can contract only the `c` entry of a quadratic ghost current. -/
theorem bGhost_ghostBilinear_nonneg (a c b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (bGhost a)) n (ghostBilinear c b) =
      if a = b ∧ n = 0 then -bGhost c else 0 := by
  have h := congrArg (fun f : End ℂ Sl2GhostSpace => f (cGhost b))
    (bGhost_modes_anticomm a c n (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  change mode (sl2GhostSVA.Y (bGhost a)) n (ghostBilinear c b) +
    mode (sl2GhostSVA.Y (bGhost c)) (-1)
      (mode (sl2GhostSVA.Y (bGhost a)) n (cGhost b)) = 0 at h
  rw [bGhost_cGhost_product a b n hn] at h
  by_cases habn : a = b ∧ n = 0
  · rw [if_pos habn, (sl2GhostSVA.creation (bGhost c)).1] at h
    rw [if_pos habn]
    exact eq_neg_of_add_eq_zero_left h
  · rw [if_neg habn, map_zero, add_zero] at h
    rw [if_neg habn]
    exact h

/-- The zero-mode antighost action on the adjoint ghost current. -/
theorem bGhost_zero_ghostCurrent (b a : Fin 3) :
    mode (sl2GhostSVA.Y (bGhost b)) 0 (ghostCurrent a) =
      -(∑ i : Fin 3, fabc a b i • bGhost i) := by
  simp only [ghostCurrent, map_sum, map_smul, bGhost_ghostBilinear_nonneg _ _ _ 0 (by omega)]
  simp [ghostCurrentCoefficient]

/-- Higher antighost products with a ghost current vanish. -/
theorem bGhost_high_ghostCurrent (b a : Fin 3) (n : ℤ) (hn : 1 ≤ n) :
    mode (sl2GhostSVA.Y (bGhost b)) n (ghostCurrent a) = 0 := by
  simp only [ghostCurrent, map_sum, map_smul,
    bGhost_ghostBilinear_nonneg _ _ _ n (by omega),
    show n ≠ 0 by omega, and_false, if_false, smul_zero, Finset.sum_const_zero]

/-- Contracting the cubic ghost state by an antighost gives the ghost current. -/
theorem bGhost_zero_ghostBRSTState (b : Fin 3) :
    mode (sl2GhostSVA.Y (bGhost b)) 0 ghostBRSTState = ghostCurrent b := by
  have hterm (a : Fin 3) :
      mode (sl2GhostSVA.Y (bGhost b)) 0
        (mode (sl2GhostSVA.Y (cGhost a)) (-1) (ghostCurrent a)) =
      (if b = a then ghostCurrent a else 0) -
        ∑ i : Fin 3, fabc a b i • ghostBilinear i a := by
    have h := odd_zeroMode_deriv
      (zeroModeCommutator_of_translation translationCovariant_sl2GhostSVA)
      (bGhost_odd b) (cGhost a) (ghostCurrent a) (-1)
    rw [bGhost_cGhost_product b a 0 (by omega), bGhost_zero_ghostCurrent,
      BRST.sgn_odd (cGhost_odd a)] at h
    rw [h]
    simp only [and_true, map_neg, mode_neg, LinearMap.neg_apply, neg_neg, map_sum,
      map_smul, cGhost_negOne_bGhost, smul_neg, Finset.sum_neg_distrib]
    congr 1
    by_cases hba : b = a
    · rw [if_pos hba, if_pos hba, sl2GhostSVA.vacuum_Y, mode_apply,
        show -(-1 : ℤ) - 1 = 0 by omega, FormalDist.one_apply, if_pos rfl,
        Module.End.one_apply]
    · rw [if_neg hba, if_neg hba, map_zero, mode_zero, LinearMap.zero_apply]
  rw [ghostBRSTState, map_smul, map_sum]
  simp only [hterm, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq]
  have hsum : (∑ a : Fin 3, ∑ i : Fin 3, fabc a b i • ghostBilinear i a) =
      -ghostCurrent b := by
    simp only [ghostCurrent, ghostCurrentCoefficient, fabc_antisymm _ b,
      neg_smul, Finset.sum_neg_distrib]
  rw [hsum, sub_neg_eq_add, if_pos (Finset.mem_univ b), ← two_smul ℂ, smul_smul]
  norm_num

/-- Higher antighost modes cannot contract the cubic ghost state. -/
theorem bGhost_high_ghostBRSTState (b : Fin 3) (n : ℤ) (hn : 1 ≤ n) :
    mode (sl2GhostSVA.Y (bGhost b)) n ghostBRSTState = 0 := by
  have hterm (a : Fin 3) :
      mode (sl2GhostSVA.Y (bGhost b)) n
        (mode (sl2GhostSVA.Y (cGhost a)) (-1) (ghostCurrent a)) = 0 := by
    have h := congrArg (fun f : End ℂ Sl2GhostSpace => f (ghostCurrent a))
      (bGhost_cGhost_modes_anticomm b a n (-1))
    simp only [LinearMap.add_apply, Module.End.mul_apply,
      bGhost_high_ghostCurrent b a n hn, map_zero, add_zero] at h
    rw [if_neg (by omega), LinearMap.zero_apply] at h
    exact h
  simp only [ghostBRSTState, map_smul, map_sum, hterm, Finset.sum_const_zero, smul_zero]

/-- The actual ghost Cartan identity in the order needed by the BRST differential. -/
theorem ghostBRSTState_zero_bGhost (a : Fin 3) :
    mode (sl2GhostSVA.Y ghostBRSTState) 0 (bGhost a) = ghostCurrent a := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_two
    (bGhost_odd a) ghostBRSTState_odd
    (fun j hj => bGhost_high_ghostBRSTState a j (by omega)) (-1) 0
  have hv := congrArg (fun f : End ℂ Sl2GhostSpace => f sl2GhostSVA.vacuum) h
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Module.End.mul_apply, LinearMap.add_apply, koszul_one_one, neg_one_smul,
    (sl2GhostSVA.creation ghostBRSTState).2 0 (by omega), map_zero,
    (sl2GhostSVA.creation (bGhost a)).1, zero_sub, neg_neg, neg_add_cancel,
    add_zero, bGhost_high_ghostBRSTState a 1 (by omega)] at hv
  simpa only [map_zero, mode_zero, LinearMap.zero_apply, smul_zero, add_zero,
    (sl2GhostSVA.creation _).1, bGhost_zero_ghostBRSTState] using hv

end VOA.Sl2SemiInfinite
