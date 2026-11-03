/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroLengthTwoTowers
import VOA.Examples.VirasoroGram4

open scoped BigOperators
namespace VOA.VirGradedUnitarity
open VOA.VirModule

theorem lengthTwoQ_eq_explicit (c : ℂ) (m : ℕ) :
    lengthTwoQ c m =
      (2 : ℂ) • ∑ j ∈ Finset.range (m - 2),
        (((lengthTwoACoeff m j : ℚ) : ℂ)) • negWordVir c [2 * m - 4 - j, j]
      + (((lengthTwoACoeff m (m - 2) : ℚ) : ℂ)) •
          negWordVir c [m - 2, m - 2]
      + (((lengthTwoBCoeff m : ℚ) : ℂ)) • negWordVir c [2 * m - 2] := by
  rfl

end VOA.VirGradedUnitarity

namespace VOA.VirGradedUnitarity

open VOA.VirModule

theorem Lop_nat_negWordVir_single_self (c : ℂ) (j : ℕ) :
    Lop c (j : ℤ) (negWordVir c [j]) =
      (2 * (j : ℂ) + 2) • negWordVir c [0] := by
  have h := Lop_apply_bracket c (j : ℤ) (-(j : ℤ) - 2) (vacVec c)
  have hv : Lop c (j : ℤ) (vacVec c) = 0 := Lop_vacuum c (by omega)
  rw [hv, map_zero,
    if_neg (by omega : ¬((j : ℤ) + (-(j : ℤ) - 2) = 0)), zero_smul, add_zero,
    show (j : ℤ) + (-(j : ℤ) - 2) = -2 by ring,
    show ((j : ℤ) : ℂ) - ((-(j : ℤ) - 2 : ℤ) : ℂ) = 2 * (j : ℂ) + 2 by
      push_cast; ring, zero_add] at h
  simpa only [negWordVir_cons, negWordVir_nil] using h

theorem Lop_nat_negWordVir_single_eq_zero_of_gt (c : ℂ) (r i : ℕ)
    (hri : i + 2 < r) : Lop c (r : ℤ) (negWordVir c [i]) = 0 := by
  have h := Lop_apply_bracket c (r : ℤ) (-(i : ℤ) - 2) (vacVec c)
  have hv : Lop c (r : ℤ) (vacVec c) = 0 := Lop_vacuum c (by omega)
  have hsum : -1 ≤ (r : ℤ) + (-(i : ℤ) - 2) := by omega
  rw [hv, map_zero,
    if_neg (by omega : ¬((r : ℤ) + (-(i : ℤ) - 2) = 0)), zero_smul, add_zero,
    Lop_vacuum c hsum, smul_zero,
    add_zero] at h
  simpa only [negWordVir_cons, negWordVir_nil] using h

theorem Lop_lengthTwo_top_pair_zero (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    Lop c ((2 * m - 2 : ℕ) : ℤ) (negWordVir c [2 * m - 4, 0]) =
      (4 * (2 * (m : ℂ) - 2) +
          (((2 * (m : ℂ) - 2) ^ 3 - (2 * (m : ℂ) - 2)) / 12) * c) •
        negWordVir c [0] := by
  have h := Lop_apply_bracket c ((2 * m - 2 : ℕ) : ℤ)
    (-((2 * m - 4 : ℕ) : ℤ) - 2) (negWordVir c [0])
  have hmode : ((2 * m - 2 : ℕ) : ℤ) + (-((2 * m - 4 : ℕ) : ℤ) - 2) = 0 := by
    omega
  rw [Lop_nat_negWordVir_single_eq_zero_of_gt c (2 * m - 2) 0 (by omega), map_zero,
    if_pos hmode, hmode,
    VirModule.L0_negWord] at h
  simp only [energyVir_cons, energyVir_nil] at h
  change Lop c ((2 * m - 2 : ℕ) : ℤ)
      (Lop c (-((2 * m - 4 : ℕ) : ℤ) - 2) (negWordVir c [0])) = _
  rw [h]
  push_cast
  rw [Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_sub (by omega : 4 ≤ 2 * m)]
  push_cast
  module

theorem Lop_lengthTwo_top_pair_succ (c : ℂ) (m j : ℕ) (hm : 3 ≤ m)
    (hj0 : 1 ≤ j) (hjm : j + 3 ≤ m) :
    Lop c ((2 * m - 2 : ℕ) : ℤ) (negWordVir c [2 * m - 4 - j, j]) =
      ((4 * (m : ℂ) - 4 - j) * (2 * (j : ℂ) + 2)) • negWordVir c [0] := by
  have h := Lop_apply_bracket c ((2 * m - 2 : ℕ) : ℤ)
    (-((2 * m - 4 - j : ℕ) : ℤ) - 2) (negWordVir c [j])
  rw [Lop_nat_negWordVir_single_eq_zero_of_gt c (2 * m - 2) j (by omega), map_zero,
    if_neg (by omega : ¬(((2 * m - 2 : ℕ) : ℤ) +
      (-((2 * m - 4 - j : ℕ) : ℤ) - 2) = 0)), zero_smul, add_zero] at h
  have hmode : ((2 * m - 2 : ℕ) : ℤ) +
      (-((2 * m - 4 - j : ℕ) : ℤ) - 2) = (j : ℤ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * m),
      Nat.cast_sub (by omega : j ≤ 2 * m - 4), Nat.cast_sub (by omega : 4 ≤ 2 * m)]
    push_cast
    ring
  have hcoef : (((2 * m - 2 : ℕ) : ℤ) : ℂ) -
      ((-((2 * m - 4 - j : ℕ) : ℤ) - 2 : ℤ) : ℂ) = 4 * (m : ℂ) - 4 - j := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * m),
      Nat.cast_sub (by omega : j ≤ 2 * m - 4), Nat.cast_sub (by omega : 4 ≤ 2 * m)]
    push_cast
    ring
  rw [hmode, hcoef, Lop_nat_negWordVir_single_self] at h
  simpa only [negWordVir_cons, zero_add, smul_smul] using h

theorem Lop_lengthTwo_top_pair_diag (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    Lop c ((2 * m - 2 : ℕ) : ℤ) (negWordVir c [m - 2, m - 2]) =
      ((3 * (m : ℂ) - 2) * (2 * (m : ℂ) - 2)) • negWordVir c [0] := by
  have h := Lop_apply_bracket c ((2 * m - 2 : ℕ) : ℤ) (-((m - 2 : ℕ) : ℤ) - 2)
    (negWordVir c [m - 2])
  have hne : ¬(((2 * m - 2 : ℕ) : ℤ) + (-((m - 2 : ℕ) : ℤ) - 2) = 0) := by
    omega
  rw [Lop_nat_negWordVir_single_eq_zero_of_gt c (2 * m - 2) (m - 2) (by omega),
    map_zero, if_neg hne,
    zero_smul, add_zero,
    show ((2 * m - 2 : ℕ) : ℤ) + (-((m - 2 : ℕ) : ℤ) - 2) = (m - 2 : ℕ) by
      omega,
    show ((((2 * m - 2 : ℕ) : ℤ) : ℂ) - ((-((m - 2 : ℕ) : ℤ) - 2 : ℤ) : ℂ)) =
      3 * (m : ℂ) - 2 by
        rw [Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_sub (by omega : 2 ≤ m)]
        push_cast
        ring,
    Lop_nat_negWordVir_single_self] at h
  have hsmall : ((m - 2 : ℕ) : ℂ) = (m : ℂ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
  rw [hsmall] at h
  change Lop c ((2 * m - 2 : ℕ) : ℤ)
      (Lop c (-((m - 2 : ℕ) : ℤ) - 2) (negWordVir c [m - 2])) = _
  rw [h]
  module

end VOA.VirGradedUnitarity

namespace VOA.VirGradedUnitarity

open scoped BigOperators

def lengthTwoNormCertificate (m j : ℕ) : ℚ :=
  2 * ((j : ℚ) + 3) *
      (2 * (j : ℚ) ^ 2 * (m : ℚ) ^ 2 + 3 * (j : ℚ) ^ 2 * m + (j : ℚ) ^ 2
        - 8 * (j : ℚ) * (m : ℚ) ^ 3 - 2 * (j : ℚ) * (m : ℚ) ^ 2
        + 9 * (j : ℚ) * m + 3 * j - 8 * (m : ℚ) ^ 2 + 4 * m + 2) /
    ((m : ℚ) * (m + 1) * (2 * m + 1))

theorem lengthTwoNormCertificate_step (m j : ℕ) (hm : 3 ≤ m) (hjm : j + 3 ≤ m) :
    lengthTwoACoeff m (j + 1) * lengthTwoNormCertificate m (j + 1)
        - lengthTwoACoeff m j * lengthTwoNormCertificate m j =
      2 * lengthTwoACoeff m j * (4 * (m : ℚ) - 4 - j) * (2 * (j : ℚ) + 2) := by
  have hrec := lengthTwoACoeff_recurrence m j hjm
  have hj4 : (j : ℚ) + 4 ≠ 0 := by positivity
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  have ha : lengthTwoACoeff m (j + 1) =
      -(lengthTwoACoeff m j * (2 * (m : ℚ) - 1 - j)) / ((j : ℚ) + 4) := by
    apply (eq_div_iff hj4).2
    linarith
  rw [ha]
  unfold lengthTwoNormCertificate
  push_cast
  field_simp [hm0, hm1, h2m1, hj4]
  ring

theorem lengthTwoNormCertificate_partial (m k : ℕ) (hm : 3 ≤ m) (hk : k ≤ m - 3) :
    (∑ j ∈ Finset.range k,
      2 * lengthTwoACoeff m (j + 1) * (4 * (m : ℚ) - 4 - (j + 1)) *
        (2 * ((j + 1 : ℕ) : ℚ) + 2)) =
      lengthTwoACoeff m (k + 1) * lengthTwoNormCertificate m (k + 1)
        - lengthTwoACoeff m 1 * lengthTwoNormCertificate m 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ m - 3 := by omega
      rw [Finset.sum_range_succ, ih hk']
      have hstep := lengthTwoNormCertificate_step m (k + 1) hm (by omega : k + 1 + 3 ≤ m)
      push_cast at hstep ⊢
      linarith

theorem lengthTwoNormCertificate_one (m : ℕ) :
    lengthTwoNormCertificate m 1 =
      -16 * (4 * (m : ℚ) ^ 3 + 4 * (m : ℚ) ^ 2 - 8 * m - 3) /
        ((m : ℚ) * (m + 1) * (2 * m + 1)) := by
  unfold lengthTwoNormCertificate
  norm_num
  ring

theorem lengthTwoNormCertificate_diag (m : ℕ) (hm : 3 ≤ m) :
    lengthTwoNormCertificate m (m - 2) =
      -2 * (2 * (m : ℚ) - 3) * (3 * (m : ℚ) ^ 2 - 1) / (2 * m + 1) := by
  unfold lengthTwoNormCertificate
  rw [Nat.cast_sub (by omega : 2 ≤ m)]
  push_cast
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hm0, hm1, h2m1]
  ring

theorem lengthTwoChooseThree (m : ℕ) (hm : 3 ≤ m) :
    (Nat.choose (2 * m - 1) 3 : ℚ) =
      (2 * (m : ℚ) - 1) * ((m : ℚ) - 1) * (2 * (m : ℚ) - 3) / 3 := by
  have hnat := Nat.choose_succ_right_eq (2 * m - 1) 2
  have hn2 : 2 ≤ 2 * m - 1 := by omega
  have hncast : ((2 * m - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    push_cast
    ring
  have h : (Nat.choose (2 * m - 1) 3 : ℚ) * 3 =
      ((2 * (m : ℚ) - 1) * (2 * (m : ℚ) - 2) / 2) * (2 * (m : ℚ) - 3) := by
    calc
      (Nat.choose (2 * m - 1) 3 : ℚ) * 3 =
          (Nat.choose (2 * m - 1) 2 : ℚ) * (2 * m - 1 - 2 : ℕ) := by exact_mod_cast hnat
      _ = ((2 * (m : ℚ) - 1) * (2 * (m : ℚ) - 2) / 2) *
          (2 * (m : ℚ) - 3) := by
        rw [Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ 2 * m),
          Nat.cast_sub (by omega : 2 ≤ 2 * m - 1)]
        push_cast
        rw [hncast]
        ring
  linarith

theorem lengthTwoMixedArithmetic (m : ℕ) (hm : 3 ≤ m) :
    (∑ j ∈ Finset.range (m - 2),
      2 * lengthTwoACoeff m j * (4 * (m : ℚ) - 4 - j) * (2 * (j : ℚ) + 2))
      + lengthTwoACoeff m (m - 2) * (3 * (m : ℚ) - 2) * (2 * (m : ℚ) - 2)
      + lengthTwoBCoeff m * (4 * (m : ℚ) - 2) =
        (Nat.choose (2 * m - 1) 3 : ℚ) * lengthTwoRho m := by
  have hsum := lengthTwoNormCertificate_partial m (m - 3) hm (by omega)
  have hrec := lengthTwoBCoeff_residual m (by omega : 2 ≤ m)
  have hb : lengthTwoBCoeff m =
      -(((m : ℚ) + 1) * lengthTwoACoeff m (m - 2)) / (2 * (m : ℚ) + 1) := by
    apply (eq_div_iff (by positivity : (2 * (m : ℚ) + 1) ≠ 0)).2
    linarith
  have ha0 : lengthTwoACoeff m 0 = 1 := by
    simp [lengthTwoACoeff]
  have ha1 : lengthTwoACoeff m 1 = -(2 * (m : ℚ) - 1) / 4 := by
    unfold lengthTwoACoeff
    norm_num
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    push_cast
    ring
  push_cast at hsum
  rw [show m - 2 = (m - 3) + 1 by omega, Finset.sum_range_succ']
  rw [ha0]
  norm_num only
  push_cast
  rw [hsum, show m - 3 + 1 = m - 2 by omega,
    lengthTwoNormCertificate_one m, lengthTwoNormCertificate_diag m hm, hb, ha1,
    lengthTwoChooseThree m hm]
  unfold lengthTwoRho
  have hmQ : (3 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hm1 : (m : ℚ) - 1 ≠ 0 := by linarith
  have hp1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2m3 : 2 * (m : ℚ) - 3 ≠ 0 := by linarith
  have h2m1 : 2 * (m : ℚ) - 1 ≠ 0 := by linarith
  have h2p1 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hm0, hm1, hp1, h2m3, h2m1, h2p1]
  ring

end VOA.VirGradedUnitarity
namespace VOA.VirGradedUnitarity

open scoped BigOperators
open VOA.VirModule

theorem Lop_lengthTwoQ_top (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    Lop c ((2 * m - 2 : ℕ) : ℤ) (lengthTwoQ c m) =
      (((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) *
        (c + (lengthTwoRho m : ℂ))) • negWordVir c [0] := by
  have hsum :
      Lop c ((2 * m - 2 : ℕ) : ℤ)
          ((2 : ℂ) • ∑ j ∈ Finset.range (m - 2),
            ((lengthTwoACoeff m j : ℚ) : ℂ) • negWordVir c [2 * m - 4 - j, j]) =
        ((2 : ℂ) *
          (((4 * (m : ℂ) - 4) * 2 +
              (((2 * (m : ℂ) - 2) ^ 3 - (2 * (m : ℂ) - 2)) / 12) * c)
            + ∑ j ∈ Finset.range (m - 3),
                ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
                  ((4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2)))) •
          negWordVir c [0] := by
    rw [map_smul, map_sum]
    rw [show m - 2 = (m - 3) + 1 by omega, Finset.sum_range_succ']
    simp_rw [map_smul]
    simp only [Nat.sub_zero]
    rw [Lop_lengthTwo_top_pair_zero c m hm]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [Lop_lengthTwo_top_pair_succ c m (j + 1) hm (by omega)
        (by rw [Finset.mem_range] at hj; omega), smul_smul])]
    have ha0 : ((lengthTwoACoeff m 0 : ℚ) : ℂ) = 1 := by
      norm_num [lengthTwoACoeff]
    rw [ha0]
    rw [← Finset.sum_smul]
    push_cast
    module
  rw [lengthTwoQ_eq_explicit, map_add, map_add, hsum, map_smul,
    Lop_lengthTwo_top_pair_diag c m hm, map_smul,
    Lop_nat_negWordVir_single_self c (2 * m - 2)]
  have harithQ := lengthTwoMixedArithmetic m hm
  have harithC :
      (∑ j ∈ Finset.range (m - 2),
        2 * ((lengthTwoACoeff m j : ℚ) : ℂ) * (4 * (m : ℂ) - 4 - j) *
          (2 * (j : ℂ) + 2))
        + ((lengthTwoACoeff m (m - 2) : ℚ) : ℂ) * (3 * (m : ℂ) - 2) *
          (2 * (m : ℂ) - 2)
        + ((lengthTwoBCoeff m : ℚ) : ℂ) * (4 * (m : ℂ) - 2) =
          ((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) * (lengthTwoRho m : ℂ) := by
    exact_mod_cast harithQ
  have hcentral :
      2 * (((2 * (m : ℂ) - 2) ^ 3 - (2 * (m : ℂ) - 2)) / 12) =
        ((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) := by
    rw [lengthTwoChooseThree m hm]
    push_cast
    ring
  have ha0 : ((lengthTwoACoeff m 0 : ℚ) : ℂ) = 1 := by
    norm_num [lengthTwoACoeff]
  have harithP :
      2 * (4 * (m : ℂ) - 4) * 2 +
        (∑ j ∈ Finset.range (m - 3),
          2 * ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
            (4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2))
        + ((lengthTwoACoeff m (m - 2) : ℚ) : ℂ) * (3 * (m : ℂ) - 2) *
            (2 * (m : ℂ) - 2)
        + ((lengthTwoBCoeff m : ℚ) : ℂ) * (4 * (m : ℂ) - 2) =
          ((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) * (lengthTwoRho m : ℂ) := by
    rw [show m - 2 = (m - 3) + 1 by omega, Finset.sum_range_succ'] at harithC
    rw [ha0] at harithC
    rw [show m - 3 + 1 = m - 2 by omega] at harithC
    push_cast at harithC ⊢
    convert harithC using 1
    all_goals ring
  have hlast : (2 * ((2 * m - 2 : ℕ) : ℂ) + 2) = 4 * (m : ℂ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * m)]
    push_cast
    ring
  rw [hlast]
  have hsumTwo :
      2 * (∑ j ∈ Finset.range (m - 3),
          ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
            ((4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2))) =
        ∑ j ∈ Finset.range (m - 3),
          2 * ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
            (4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hscalar :
      2 * (((4 * (m : ℂ) - 4) * 2 +
          (((2 * (m : ℂ) - 2) ^ 3 - (2 * (m : ℂ) - 2)) / 12) * c) +
          ∑ j ∈ Finset.range (m - 3),
            ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
              ((4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2)))
        + ((lengthTwoACoeff m (m - 2) : ℚ) : ℂ) *
            ((3 * (m : ℂ) - 2) * (2 * (m : ℂ) - 2))
        + ((lengthTwoBCoeff m : ℚ) : ℂ) * (4 * (m : ℂ) - 2) =
          ((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) *
            (c + (lengthTwoRho m : ℂ)) := by
    calc
      _ = (2 * (((2 * (m : ℂ) - 2) ^ 3 - (2 * (m : ℂ) - 2)) / 12)) * c +
          (2 * (4 * (m : ℂ) - 4) * 2 +
            (∑ j ∈ Finset.range (m - 3),
              2 * ((lengthTwoACoeff m (j + 1) : ℚ) : ℂ) *
                (4 * (m : ℂ) - 4 - (j + 1)) * (2 * ((j + 1 : ℕ) : ℂ) + 2)) +
            ((lengthTwoACoeff m (m - 2) : ℚ) : ℂ) * (3 * (m : ℂ) - 2) *
              (2 * (m : ℂ) - 2) +
            ((lengthTwoBCoeff m : ℚ) : ℂ) * (4 * (m : ℂ) - 2)) := by
              rw [← hsumTwo]
              ring
      _ = _ := by rw [hcentral, harithP]; ring
  rw [← hscalar]
  module

end VOA.VirGradedUnitarity

namespace VOA.VirGradedUnitarity

open VOA.VirModule VOA.VirGram4

/-- The mixed matrix coefficient with the extreme length-two word.  Contravariance moves its
largest creation mode to the left; `Lop_lengthTwoQ_top` then evaluates the result. -/
theorem canB_lengthTwoQ_mixed (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4, 0]) =
      (1 / 2 : ℂ) * ((Nat.choose (2 * m - 1) 3 : ℚ) : ℂ) * c *
        (c + (lengthTwoRho m : ℂ)) := by
  have hadj := canB_adj c ((2 * m - 2 : ℕ) : ℤ) (lengthTwoQ c m) (negWordVir c [0])
  have hT : (canB c).form (negWordVir c [0]) (negWordVir c [0]) = c / 2 := by
    simpa only [negWordVir_cons, negWordVir_nil] using canB_L2_L2 c
  rw [Lop_lengthTwoQ_top c m hm, map_smul, LinearMap.smul_apply, smul_eq_mul, hT] at hadj
  have hneg :
      Lop c (-((2 * m - 2 : ℕ) : ℤ)) (negWordVir c [0]) =
        negWordVir c [2 * m - 4, 0] := by
    rw [negWordVir_cons]
    congr 2
    omega
  rw [hneg] at hadj
  rw [← hadj]
  ring

/-! ## Pairing recurrence across the length-two words -/

/-- Translation differentiates a length-two creation word in its two slots. -/
theorem Lop_neg_one_negWordVir_pair (c : ℂ) (a j : ℕ) :
    Lop c (-1) (negWordVir c [a, j]) =
      ((j : ℂ) + 1) • negWordVir c [a, j + 1] +
        ((a : ℂ) + 1) • negWordVir c [a + 1, j] := by
  rw [VirGoodFil.Lop_neg_one_negWordVir_cons, VirGoodFil.Lop_neg_one_negWordVir_cons,
    VirGoodFil.Lop_neg_one_negWordVir_nil, map_zero, zero_add, map_smul]
  rfl

/-- Pairing a quasi-primary against a translated length-two word gives the neighboring-word
recurrence used to recover its full self-pairing from one extreme mixed coefficient. -/
theorem canB_lengthTwoQ_pairing_step (c : ℂ) (m j : ℕ) (hm : 3 ≤ m)
    (hj : j < 2 * m - 4) :
    ((j : ℂ) + 1) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 5 - j, j + 1]) +
      ((2 * m - 4 - j : ℕ) : ℂ) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4 - j, j]) = 0 := by
  have hadj := canB_adj c 1 (lengthTwoQ c m) (negWordVir c [2 * m - 5 - j, j])
  have horth :
      (canB c).form (lengthTwoQ c m)
        (Lop c (-1) (negWordVir c [2 * m - 5 - j, j])) = 0 := by
    calc
      _ = (canB c).form (Lop c 1 (lengthTwoQ c m))
          (negWordVir c [2 * m - 5 - j, j]) := hadj.symm
      _ = 0 := by rw [lengthTwoQ_quasiPrimary c m (by omega)]; simp
  rw [Lop_neg_one_negWordVir_pair, map_add, map_smul, map_smul, smul_eq_mul] at horth
  have ha : 2 * m - 5 - j + 1 = 2 * m - 4 - j := by omega
  rw [ha] at horth
  have hcast : (((2 * m - 5 - j : ℕ) : ℂ) + 1) = ((2 * m - 4 - j : ℕ) : ℂ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ha]
  rw [hcast] at horth
  exact horth

/-- Closed solution of the neighboring-word pairing recurrence. -/
theorem canB_lengthTwoQ_pairing_closed (c : ℂ) (m j : ℕ) (hm : 3 ≤ m)
    (hj : j ≤ 2 * m - 4) :
    (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4 - j, j]) =
      ((-1 : ℂ) ^ j * (Nat.choose (2 * m - 4) j : ℂ)) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4, 0]) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hj' : j ≤ 2 * m - 4 := by omega
      have hstep := canB_lengthTwoQ_pairing_step c m j hm (by omega)
      have hj1 : ((j : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero j
      have hsolve :
          (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 5 - j, j + 1]) =
            -(((2 * m - 4 - j : ℕ) : ℂ) *
                (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4 - j, j])) /
              ((j : ℂ) + 1) := by
        apply (eq_div_iff hj1).2
        linear_combination hstep
      rw [show 2 * m - 4 - (j + 1) = 2 * m - 5 - j by omega, hsolve, ih hj']
      have hchooseNat := Nat.choose_succ_right_eq (2 * m - 4) j
      have hchoose :
          (Nat.choose (2 * m - 4) (j + 1) : ℂ) * ((j : ℂ) + 1) =
            (Nat.choose (2 * m - 4) j : ℂ) * ((2 * m - 4 - j : ℕ) : ℂ) := by
        exact_mod_cast hchooseNat
      rw [pow_succ]
      field_simp [hj1]
      linear_combination
        ((canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4, 0])) * hchoose

/-! ## The length-one term -/

/-- Translation on a one-letter creation word. -/
theorem Lop_neg_one_negWordVir_singleton_norm (c : ℂ) (i : ℕ) :
    Lop c (-1) (negWordVir c [i]) = ((i : ℂ) + 1) • negWordVir c [i + 1] := by
  rw [VirGoodFil.Lop_neg_one_negWordVir_cons,
    VirGoodFil.Lop_neg_one_negWordVir_nil, map_zero, zero_add]

/-- The `r`-fold translate of the stress tensor is `r!` times its one-letter word. -/
theorem Lop_neg_one_pow_negWordVir_zero (c : ℂ) (r : ℕ) :
    (Lop c (-1) ^ r) (negWordVir c [0]) =
      (r.factorial : ℂ) • negWordVir c [r] := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul,
        Lop_neg_one_negWordVir_singleton_norm]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      module

/-- A positive-weight length-one word is a nonzero global descendant, hence is orthogonal to
the quasi-primary `Q_{2m}`. -/
theorem canB_lengthTwoQ_single_zero (c : ℂ) (m : ℕ) (hm : 2 ≤ m) :
    (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 2]) = 0 := by
  have hqp :
      (virasoroVOA c).L 1 (lengthTwoQ c m) = 0 := by
    simpa only [virasoroVOA_L_eq_Lop] using lengthTwoQ_quasiPrimary c m hm
  have horth := (canB c).form_quasiPrimary_Lneg1_pow_succ hqp
    (negWordVir c [0]) (2 * m - 3)
  simp only [virasoroVOA_L_eq_Lop] at horth
  rw [show 2 * m - 3 + 1 = 2 * m - 2 by omega,
    Lop_neg_one_pow_negWordVir_zero] at horth
  simp only [map_smul, smul_eq_mul] at horth
  have hfac : (((2 * m - 2).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 2)
  exact (mul_eq_zero.mp horth).resolve_left hfac

/-! ## The normalization sum -/

/-- The scalar contributed by the `j`-th ordered length-two word after applying the closed
pairing recurrence. -/
def lengthTwoNormSummand (m j : ℕ) : ℚ :=
  lengthTwoACoeff m j * (-1 : ℚ) ^ j * (Nat.choose (2 * m - 4) j : ℚ)

theorem lengthTwoNormSummand_cast (m j : ℕ) :
    ((lengthTwoNormSummand m j : ℚ) : ℂ) =
      ((lengthTwoACoeff m j : ℚ) : ℂ) * (-1 : ℂ) ^ j *
        (Nat.choose (2 * m - 4) j : ℂ) := by
  unfold lengthTwoNormSummand
  push_cast
  rfl

/-- Each normalization summand is a Vandermonde convolution term divided by
`binom(2m-1,3)`. -/
theorem lengthTwoNormSummand_mul_choose (m j : ℕ) (hm : 3 ≤ m) (hj : j ≤ 2 * m - 4) :
    (Nat.choose (2 * m - 1) 3 : ℚ) * lengthTwoNormSummand m j =
      (Nat.choose (2 * m - 1) j : ℚ) *
        (Nat.choose (2 * m - 1) (2 * m - 4 - j) : ℚ) := by
  have hden : (Nat.choose (j + 3) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ j + 3)))
  have hmulNat := Nat.choose_mul (n := 2 * m - 1) (k := j + 3) (s := 3) (by omega)
  have hmul :
      (Nat.choose (2 * m - 1) (j + 3) : ℚ) * (Nat.choose (j + 3) 3 : ℚ) =
        (Nat.choose (2 * m - 1) 3 : ℚ) * (Nat.choose (2 * m - 4) j : ℚ) := by
    exact_mod_cast (by simpa [show 2 * m - 1 - 3 = 2 * m - 4 by omega] using hmulNat)
  have hsym :
      Nat.choose (2 * m - 1) (j + 3) = Nat.choose (2 * m - 1) (2 * m - 4 - j) := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hsign : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← pow_add, (Even.add_self j).neg_one_pow]
  have hsquare : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
    nlinarith [hsign]
  unfold lengthTwoNormSummand lengthTwoACoeff
  field_simp [hden]
  rw [hsquare]
  rw [hsym] at hmul
  nlinarith [hmul]

/-- The normalization summands are symmetric about the diagonal. -/
theorem lengthTwoNormSummand_reflect (m j : ℕ) (hm : 3 ≤ m) (hj : j ≤ 2 * m - 4) :
    lengthTwoNormSummand m (2 * m - 4 - j) = lengthTwoNormSummand m j := by
  have hchoose : (Nat.choose (2 * m - 1) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ 2 * m - 1)))
  apply (mul_left_cancel₀ hchoose)
  rw [lengthTwoNormSummand_mul_choose m (2 * m - 4 - j) hm (Nat.sub_le _ _),
    lengthTwoNormSummand_mul_choose m j hm hj, Nat.sub_sub_self hj]
  ring

/-- Vandermonde evaluates the full ordered normalization sum. -/
theorem lengthTwoNormSummand_sum_full (m : ℕ) (hm : 3 ≤ m) :
    ∑ j ∈ Finset.range (2 * m - 4 + 1), lengthTwoNormSummand m j =
      (Nat.choose (4 * m - 2) (2 * m - 4) : ℚ) /
        (Nat.choose (2 * m - 1) 3 : ℚ) := by
  have hchoose : (Nat.choose (2 * m - 1) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ 2 * m - 1)))
  apply (eq_div_iff hchoose).2
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [mul_comm, lengthTwoNormSummand_mul_choose m j hm
      (by rw [Finset.mem_range] at hj; omega)])]
  have hv := Nat.add_choose_eq (2 * m - 1) (2 * m - 1) (2 * m - 4)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have htop : (2 * m - 1) + (2 * m - 1) = 4 * m - 2 := by omega
  rw [← htop]
  exact_mod_cast hv.symm

/-- The ordered sum is twice the strict lower half plus its central term.  This is the
normalization scalar that occurs in `lengthTwoQ`. -/
theorem lengthTwoNormSummand_sum_half (m : ℕ) (hm : 3 ≤ m) :
    2 * (∑ j ∈ Finset.range (m - 2), lengthTwoNormSummand m j) +
        lengthTwoNormSummand m (m - 2) =
      (Nat.choose (4 * m - 2) (2 * m - 4) : ℚ) /
        (Nat.choose (2 * m - 1) 3 : ℚ) := by
  have href := Finset.sum_Ico_reflect (lengthTwoNormSummand m) 0
    (m := m - 2) (n := 2 * m - 4) (by omega)
  have hleft :
      (∑ j ∈ Finset.Ico 0 (m - 2), lengthTwoNormSummand m (2 * m - 4 - j)) =
        ∑ j ∈ Finset.Ico 0 (m - 2), lengthTwoNormSummand m j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [lengthTwoNormSummand_reflect m j hm]
    rw [Finset.mem_Ico] at hj
    omega
  rw [hleft] at href
  have hupper :
      (∑ j ∈ Finset.Ico (m - 1) (2 * m - 4 + 1), lengthTwoNormSummand m j) =
        ∑ j ∈ Finset.range (m - 2), lengthTwoNormSummand m j := by
    rw [← Nat.Ico_zero_eq_range]
    simpa only [Nat.zero_add, Nat.sub_zero,
      show 2 * m - 4 + 1 - (m - 2) = m - 1 by omega] using href.symm
  calc
    2 * (∑ j ∈ Finset.range (m - 2), lengthTwoNormSummand m j) +
          lengthTwoNormSummand m (m - 2) =
        (∑ j ∈ Finset.range (m - 2 + 1), lengthTwoNormSummand m j) +
          ∑ j ∈ Finset.Ico (m - 1) (2 * m - 4 + 1), lengthTwoNormSummand m j := by
            rw [Finset.sum_range_succ, hupper]
            ring
    _ = ∑ j ∈ Finset.range (2 * m - 4 + 1), lengthTwoNormSummand m j := by
      rw [show m - 2 + 1 = m - 1 by omega]
      exact Finset.sum_range_add_sum_Ico _ (by omega)
    _ = _ := lengthTwoNormSummand_sum_full m hm

/-! ## Assembly of the self-pairing -/

theorem canB_lengthTwoACoeff_mul_pairing_closed (c : ℂ) (m j : ℕ) (hm : 3 ≤ m)
    (hj : j ≤ 2 * m - 4) :
    ((lengthTwoACoeff m j : ℚ) : ℂ) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4 - j, j]) =
      (lengthTwoNormSummand m j : ℂ) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4, 0]) := by
  rw [canB_lengthTwoQ_pairing_closed c m j hm hj, lengthTwoNormSummand_cast]
  ring

/-- Expanding the second copy of `Q_{2m}` and using the quasi-primary recurrence reduces its
self-pairing to the normalization half-sum times one extreme mixed coefficient. -/
theorem canB_lengthTwoQ_self_eq_normalization_mul_mixed (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    (canB c).form (lengthTwoQ c m) (lengthTwoQ c m) =
      (((2 : ℚ) * (∑ j ∈ Finset.range (m - 2), lengthTwoNormSummand m j) +
          lengthTwoNormSummand m (m - 2) : ℚ) : ℂ) *
        (canB c).form (lengthTwoQ c m) (negWordVir c [2 * m - 4, 0]) := by
  nth_rewrite 2 [lengthTwoQ_eq_explicit]
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  rw [canB_lengthTwoQ_single_zero c m (by omega), mul_zero, add_zero]
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [canB_lengthTwoACoeff_mul_pairing_closed c m j hm
      (by rw [Finset.mem_range] at hj; omega)])]
  have hdiag := canB_lengthTwoACoeff_mul_pairing_closed c m (m - 2) hm (by omega)
  rw [show 2 * m - 4 - (m - 2) = m - 2 by omega] at hdiag
  rw [hdiag]
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- Closed norm of `Q_{2m}` in all weights at least six. -/
theorem canB_lengthTwoQ_self_of_three_le (c : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    (canB c).form (lengthTwoQ c m) (lengthTwoQ c m) =
      (1 / 2 : ℂ) * ((Nat.choose (4 * m - 2) (2 * m - 4) : ℚ) : ℂ) * c *
        (c + (lengthTwoRho m : ℂ)) := by
  rw [canB_lengthTwoQ_self_eq_normalization_mul_mixed c m hm,
    canB_lengthTwoQ_mixed c m hm]
  have hhalf := lengthTwoNormSummand_sum_half m hm
  have hchoose : (Nat.choose (2 * m - 1) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ 2 * m - 1)))
  have hhalfC := congrArg (fun q : ℚ => (q : ℂ)) hhalf
  dsimp only at hhalfC
  have hchooseC : (Nat.choose (2 * m - 1) 3 : ℂ) ≠ 0 := by
    exact_mod_cast hchoose
  rw [hhalfC]
  push_cast
  field_simp [hchooseC]

/-- The weight-four endpoint, computed from the explicit Gram matrix. -/
theorem canB_lengthTwoQ_self_two_norm (c : ℂ) :
    (canB c).form (lengthTwoQ c 2) (lengthTwoQ c 2) =
      c * (5 * c + 22) / 10 := by
  rw [lengthTwoQ_two, LeeYang.negWordVir_zero_zero,
    LeeYang.negWordVir_two]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    canB_L2L2_L2L2, canB_L2L2_L4, canB_L4_L2L2, canB_L4_L4]
  ring

/-- **Closed all-weight norm formula for the length-two quasi-primaries.** -/
theorem canB_lengthTwoQ_self (c : ℂ) (m : ℕ) (hm : 2 ≤ m) :
    (canB c).form (lengthTwoQ c m) (lengthTwoQ c m) =
      (1 / 2 : ℂ) * ((Nat.choose (4 * m - 2) (2 * m - 4) : ℚ) : ℂ) * c *
        (c + (lengthTwoRho m : ℂ)) := by
  rcases eq_or_lt_of_le hm with rfl | hm'
  · rw [canB_lengthTwoQ_self_two_norm]
    norm_num [lengthTwoRho, Nat.choose]
    ring
  · exact canB_lengthTwoQ_self_of_three_le c m (by omega)

end VOA.VirGradedUnitarity
