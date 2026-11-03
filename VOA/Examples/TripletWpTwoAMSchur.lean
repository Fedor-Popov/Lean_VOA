/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoMixed

/-!
# The screened Schur polynomial in the `p = 2` triplet identity

This file evaluates the neutral Fock polynomial which occurs after applying the two
screenings in the weight-ten Adamovic--Milas identity.  The calculation is independent
of the Virasoro-coordinate comparison and keeps the finite Schur expansion executable.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpTwoAMSchur

open scoped BigOperators
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.WpC2

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private abbrev alphaTwo : Ltwo.carrier := alphaP 2

private theorem chargeOsc_vSchur_same_two (m N : ℕ) (hm : 1 ≤ m) :
    chargeOsc Ltwo alphaTwo (m : ℤ) (vSchur Ltwo alphaTwo N) =
      if m ≤ N then (4 : ℂ) • vSchur Ltwo alphaTwo (N - m) else 0 := by
  have h := chargeOsc_vSchur Ltwo (latP_posDef 2 (by omega))
    alphaTwo alphaTwo m N hm
  have hself : Ltwo.form alphaTwo alphaTwo = 4 := by
    simpa using latP_form_alpha 2
  rw [hself] at h
  norm_num at h ⊢
  exact h

private theorem aExpVec_one_vSchur_seven :
    aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7) =
      (-4 : ℂ) • vSchur Ltwo alphaTwo 6 := by
  rw [aExpVec_succ, Finset.sum_range_one,
    aExpVec_zero, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.neg_apply]
  norm_num only [Nat.cast_zero, zero_add, inv_one, one_smul]
  have h1 := chargeOsc_vSchur_same_two 1 7 (by omega)
  norm_num at h1
  rw [h1]
  norm_num

private theorem aExpVec_two_vSchur_seven :
    aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7) =
      (6 : ℂ) • vSchur Ltwo alphaTwo 5 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 2 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) = _
  have h1 := chargeOsc_vSchur_same_two 1 6 (by omega)
  have h2 := chargeOsc_vSchur_same_two 2 7 (by omega)
  norm_num at h1 h2
  rw [aExpVec_one_vSchur_seven, map_smul, h1, h2]
  norm_num
  module

private theorem aExpVec_three_vSchur_seven :
    aExpVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7) =
      (-4 : ℂ) • vSchur Ltwo alphaTwo 4 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 3 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7))) = _
  have h1 := chargeOsc_vSchur_same_two 1 5 (by omega)
  have h2 := chargeOsc_vSchur_same_two 2 6 (by omega)
  have h3 := chargeOsc_vSchur_same_two 3 7 (by omega)
  norm_num at h1 h2 h3
  rw [aExpVec_two_vSchur_seven, aExpVec_one_vSchur_seven, map_smul, map_smul,
    h1, h2, h3]
  norm_num
  module

private theorem aExpVec_four_vSchur_seven :
    aExpVec Ltwo alphaTwo 4 (vSchur Ltwo alphaTwo 7) =
      vSchur Ltwo alphaTwo 3 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 4 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2
          (aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 3
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 4 (vSchur Ltwo alphaTwo 7))) = _
  have h1 := chargeOsc_vSchur_same_two 1 4 (by omega)
  have h2 := chargeOsc_vSchur_same_two 2 5 (by omega)
  have h3 := chargeOsc_vSchur_same_two 3 6 (by omega)
  have h4 := chargeOsc_vSchur_same_two 4 7 (by omega)
  norm_num at h1 h2 h3 h4
  rw [aExpVec_three_vSchur_seven, aExpVec_two_vSchur_seven,
    aExpVec_one_vSchur_seven, map_smul, map_smul, map_smul, h1, h2, h3, h4]
  norm_num
  module

private theorem aExpVec_five_vSchur_seven :
    aExpVec Ltwo alphaTwo 5 (vSchur Ltwo alphaTwo 7) = 0 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 5 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 4 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2
          (aExpVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 3
          (aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 4
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 5 (vSchur Ltwo alphaTwo 7))) = _
  have h1 := chargeOsc_vSchur_same_two 1 3 (by omega)
  have h2 := chargeOsc_vSchur_same_two 2 4 (by omega)
  have h3 := chargeOsc_vSchur_same_two 3 5 (by omega)
  have h4 := chargeOsc_vSchur_same_two 4 6 (by omega)
  have h5 := chargeOsc_vSchur_same_two 5 7 (by omega)
  norm_num at h1 h2 h3 h4 h5
  rw [aExpVec_four_vSchur_seven, aExpVec_three_vSchur_seven,
    aExpVec_two_vSchur_seven, aExpVec_one_vSchur_seven,
    map_smul, map_smul, map_smul, h1, h2, h3, h4, h5]
  norm_num
  module

private theorem aExpVec_six_vSchur_seven :
    aExpVec Ltwo alphaTwo 6 (vSchur Ltwo alphaTwo 7) = 0 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 6 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 5 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2
          (aExpVec Ltwo alphaTwo 4 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 3
          (aExpVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 4
          (aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 5
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 6 (vSchur Ltwo alphaTwo 7))) = _
  have h2 := chargeOsc_vSchur_same_two 2 3 (by omega)
  have h3 := chargeOsc_vSchur_same_two 3 4 (by omega)
  have h4 := chargeOsc_vSchur_same_two 4 5 (by omega)
  have h5 := chargeOsc_vSchur_same_two 5 6 (by omega)
  have h6 := chargeOsc_vSchur_same_two 6 7 (by omega)
  norm_num at h2 h3 h4 h5 h6
  rw [aExpVec_five_vSchur_seven, aExpVec_four_vSchur_seven,
    aExpVec_three_vSchur_seven, aExpVec_two_vSchur_seven,
    aExpVec_one_vSchur_seven, map_zero, neg_zero, zero_add,
    map_smul, map_smul, map_smul, h2, h3, h4, h5, h6]
  norm_num
  module

private theorem aExpVec_seven_vSchur_seven :
    aExpVec Ltwo alphaTwo 7 (vSchur Ltwo alphaTwo 7) = 0 := by
  rw [aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 7 : ℂ) •
      (-(chargeOsc Ltwo alphaTwo 1
          (aExpVec Ltwo alphaTwo 6 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 2
          (aExpVec Ltwo alphaTwo 5 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 3
          (aExpVec Ltwo alphaTwo 4 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 4
          (aExpVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 5
          (aExpVec Ltwo alphaTwo 2 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 6
          (aExpVec Ltwo alphaTwo 1 (vSchur Ltwo alphaTwo 7))) +
        -(chargeOsc Ltwo alphaTwo 7 (vSchur Ltwo alphaTwo 7))) = _
  have h3 := chargeOsc_vSchur_same_two 3 3 (by omega)
  have h4 := chargeOsc_vSchur_same_two 4 4 (by omega)
  have h5 := chargeOsc_vSchur_same_two 5 5 (by omega)
  have h6 := chargeOsc_vSchur_same_two 6 6 (by omega)
  have h7 := chargeOsc_vSchur_same_two 7 7 (by omega)
  norm_num at h3 h4 h5 h6 h7
  rw [aExpVec_six_vSchur_seven, aExpVec_five_vSchur_seven,
    aExpVec_four_vSchur_seven, aExpVec_three_vSchur_seven,
    aExpVec_two_vSchur_seven, aExpVec_one_vSchur_seven,
    map_zero, map_zero, neg_zero, zero_add,
    h3, map_smul, map_smul, map_smul, h4, h5, h6, h7]
  norm_num [vSchur_zero]
  module

private theorem sum_Icc_three_ten {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (3 : ℤ) 10, f m =
      f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  have h : Finset.Icc (3 : ℤ) 10 = {3, 4, 5, 6, 7, 8, 9, 10} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

/-- The exact neutral polynomial produced by the second screening at `p = 2`.
The coefficients `2,-8,6` include all annihilation contractions. -/
theorem EEVec_three_vSchur_seven_eq :
    EEVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7) =
      (2 : ℂ) • (vSchur Ltwo alphaTwo 3 * vSchur Ltwo alphaTwo 7) +
        (-8 : ℂ) • (vSchur Ltwo alphaTwo 4 * vSchur Ltwo alphaTwo 6) +
          (6 : ℂ) • (vSchur Ltwo alphaTwo 5 * vSchur Ltwo alphaTwo 5) := by
  rw [EEVec_eq_weight_bounded_sum' Ltwo alphaTwo 3
    (Screen.vSchur_mem_gradingWN Ltwo alphaTwo 7)]
  rw [show max (0 : ℤ) 3 = 3 by norm_num,
    show ((7 : ℕ) : ℤ) + 3 = 10 by norm_num, sum_Icc_three_ten]
  have hto3 : (3 : ℤ).toNat = 3 := rfl
  have hto4 : (4 : ℤ).toNat = 4 := rfl
  have hto5 : (5 : ℤ).toNat = 5 := rfl
  have hto6 : (6 : ℤ).toNat = 6 := rfl
  have hto7 : (7 : ℤ).toNat = 7 := rfl
  have hto8 : (8 : ℤ).toNat = 8 := rfl
  have hto9 : (9 : ℤ).toNat = 9 := rfl
  have hto10 : (10 : ℤ).toNat = 10 := rfl
  have h03 : ((3 : ℤ) - 3).toNat = 0 := rfl
  have h13 : ((4 : ℤ) - 3).toNat = 1 := rfl
  have h23 : ((5 : ℤ) - 3).toNat = 2 := rfl
  have h33 : ((6 : ℤ) - 3).toNat = 3 := rfl
  have h43 : ((7 : ℤ) - 3).toNat = 4 := rfl
  have h53 : ((8 : ℤ) - 3).toNat = 5 := rfl
  have h63 : ((9 : ℤ) - 3).toNat = 6 := rfl
  have h73 : ((10 : ℤ) - 3).toNat = 7 := rfl
  rw [hto3, hto4, hto5, hto6, hto7, hto8, hto9, hto10,
    h03, h13, h23, h33, h43, h53, h63, h73]
  norm_num only [aExpVec_zero, LinearMap.id_apply,
    aExpVec_one_vSchur_seven, aExpVec_two_vSchur_seven,
    aExpVec_three_vSchur_seven, aExpVec_four_vSchur_seven,
    aExpVec_five_vSchur_seven, aExpVec_six_vSchur_seven,
    aExpVec_seven_vSchur_seven, mul_zero, add_zero]
  simp only [mul_smul_comm]
  rw [mul_comm (vSchur Ltwo alphaTwo 6) (vSchur Ltwo alphaTwo 4),
    mul_comm (vSchur Ltwo alphaTwo 7) (vSchur Ltwo alphaTwo 3)]
  module

end VOA.LatGen.WpTwoAMSchur

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMSchur.EEVec_three_vSchur_seven_eq
end AxiomAudit
