/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.LocalSystemAction
import VOA.Core.FieldProductIterate
import VOA.Foundations.IotaZExpansion

/-!
# Borcherds identity for two local fields acting on their common carrier

This file proves the two-sorted field/module form of Borcherds' identity.  If `a` and `b`
are mutually local fields on `M`, their modes and their integer field products satisfy the
full three-index identity after evaluation on every `x : M`.

The proof is deliberately independent of the completed vertex-algebra Borcherds theorem.
It has two ingredients:

* locality gives the mode commutator, with the coefficients identified as the nonnegative
  products `Fld.prod k a b`;
* `Fld.mode_prod_iterate` gives the other boundary for every integer product.

The two boundaries are propagated by the elementary Pascal recurrences for the two sides.
This is the module-action theorem on the original carrier `M`.  It does **not** yet identify
the products of the induced regular fields on a `LocalFieldSystem` carrier, assert locality
of those induced fields, or package a `BarePreVA`.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open FieldCombinatorics

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace Fld

/-! ## Truncation and the locality commutator -/

/-- Field lower truncation, expressed in mode indices. -/
theorem mode_eventually_zero (a : Fld M) (x : M) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode a.1 n x = 0 := by
  obtain ⟨B, hB⟩ := a.2 x
  refine ⟨-B, fun n hn => ?_⟩
  rw [mode_apply]
  exact hB (-n - 1) (by omega)

/-- A single locality decomposition simultaneously bounds the nonnegative products and
expresses the commutator of modes in terms of those products. -/
theorem commutator_prod_bound_of_local {a b : Fld M} (h : Local a.1 b.1) (m n : ℤ) :
    ∃ N : ℕ, (∀ k : ℕ, N ≤ k → prod (k : ℤ) a b = 0) ∧
      ⁅mode a.1 m, mode b.1 n⁆ = ∑ j : Fin N,
        gBinom m (j : ℕ) • mode (prod ((j : ℕ) : ℤ) a b).1
          (m + n - ((j : ℕ) : ℤ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum_of_local h
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    apply Subtype.ext
    rw [prod_of_nonneg (Int.natCast_nonneg k), hdecomp, cCoeff_sum,
      Finset.sum_eq_zero (fun j _ => by
        rw [cCoeff_deltaDeriv, if_neg (by have hj := j.2; omega)])]
    rfl
  · rw [mode_bracket_ope_fields hdecomp m n]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (j : ℕ)
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) •
        (prod ((j : ℕ) : ℤ) a b).1 := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp] at hrec
      rw [prod_of_nonneg (Int.natCast_nonneg (j : ℕ)),
        show (((j : ℕ) : ℤ).toNat) = (j : ℕ) by omega, hrec,
        ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast,
        smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ
        (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl

/-! ## The two sides and their finite support -/

/-- The product side of the two-sorted Borcherds identity. -/
noncomputable def fieldBR (a b : Fld M) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, cbz m i • mode (prod (ell + i) a b).1 (m + n - i) x

/-- The first ordered-composition sum. -/
noncomputable def fieldPuv (a b : Fld M) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
    mode a.1 (ell + m - i) (mode b.1 (n + i) x)

/-- The exchanged ordered-composition sum. -/
noncomputable def fieldPvu (a b : Fld M) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
    mode b.1 (ell + n - i) (mode a.1 (m + i) x)

/-- The commutator side of the two-sorted Borcherds identity. -/
noncomputable def fieldBL (a b : Fld M) (x : M) (ell m n : ℤ) : M :=
  fieldPuv a b x ell m n - negOnePow ell • fieldPvu a b x ell m n

theorem fieldBR_fin {a b : Fld M} (h : Local a.1 b.1) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • mode (prod (ell + i) a b).1 (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := prod_eventually_zero_of_local h
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ell))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg m hneg, zero_smul]
  · rw [hN (ell + i) (by omega)]
    change cbz m i • (0 : End ℂ M) x = 0
    rw [LinearMap.zero_apply, smul_zero]

theorem fieldPuv_fin (a b : Fld M) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      mode a.1 (ell + m - i) (mode b.1 (n + i) x)).Finite := by
  obtain ⟨Nb, hNb⟩ := mode_eventually_zero b x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nb - n))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell hneg, mul_zero, zero_smul]
  · rw [hNb (n + i) (by omega), map_zero, smul_zero]

theorem fieldPvu_fin (a b : Fld M) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      mode b.1 (ell + n - i) (mode a.1 (m + i) x)).Finite := by
  obtain ⟨Na, hNa⟩ := mode_eventually_zero a x
  apply Set.Finite.subset (Set.finite_Icc 0 (Na - m))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell hneg, mul_zero, zero_smul]
  · rw [hNa (m + i) (by omega), map_zero, smul_zero]

theorem fieldPuv_fin' (a b : Fld M) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell (i - 1)) •
      mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x)).Finite := by
  obtain ⟨Nb, hNb⟩ := mode_eventually_zero b x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nb - n))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell (by omega), mul_zero, zero_smul]
  · rw [hNb (n + i) (by omega), map_zero, smul_zero]

theorem fieldPvu_fin' (a b : Fld M) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell (i - 1)) •
      mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x)).Finite := by
  obtain ⟨Na, hNa⟩ := mode_eventually_zero a x
  apply Set.Finite.subset (Set.finite_Icc 1 (Na - m))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell (by omega), mul_zero, zero_smul]
  · rw [hNa (m + i) (by omega), map_zero, smul_zero]

/-! ## Pascal recurrences -/

theorem fieldBR_rec {a b : Fld M} (h : Local a.1 b.1) (x : M) (ell m n : ℤ) :
    fieldBR a b x ell (m + 1) n =
      fieldBR a b x ell m (n + 1) + fieldBR a b x (ell + 1) m n := by
  have fin2 : (Function.support fun i : ℤ =>
      cbz m (i - 1) • mode (prod (ell + i) a b).1 (m + 1 + n - i) x).Finite := by
    obtain ⟨N, hN⟩ := prod_eventually_zero_of_local h
    apply Set.Finite.subset (Set.finite_Icc 1 (N - ell))
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · rw [hN (ell + i) (by omega)]
      change cbz m (i - 1) • (0 : End ℂ M) x = 0
      rw [LinearMap.zero_apply, smul_zero]
  rw [fieldBR, fieldBR, fieldBR,
    show (∑ᶠ i : ℤ, cbz (m + 1) i •
          mode (prod (ell + i) a b).1 (m + 1 + n - i) x) =
        ∑ᶠ i : ℤ, (cbz m i • mode (prod (ell + i) a b).1 (m + 1 + n - i) x +
          cbz m (i - 1) • mode (prod (ell + i) a b).1 (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have hf := fieldBR_fin h x ell m (n + 1)
      refine hf.subset fun i hi => ?_
      simp only [Function.mem_support] at hi ⊢
      rw [show m + 1 + n - i = m + (n + 1) - i by ring] at hi
      exact hi) fin2]
  congr 1
  · exact finsum_congr fun i => by
      rw [show m + 1 + n - i = m + (n + 1) - i by ring]
  · rw [← finsum_int_succ_shift (fun i : ℤ =>
      cbz m (i - 1) • mode (prod (ell + i) a b).1 (m + 1 + n - i) x)]
    exact finsum_congr fun i => by
      rw [show i + 1 - 1 = i by ring, show ell + (i + 1) = (ell + 1) + i by ring,
        show m + 1 + n - (i + 1) = m + n - i by ring]

omit [Module ℂ M] in private theorem field_finsum_neg_distrib {ι : Type*} (f : ι → M) :
    (∑ᶠ i, -f i) = -∑ᶠ i, f i := by
  by_cases h : (Function.support f).Finite
  · rw [← neg_one_zsmul (∑ᶠ i, f i), smul_finsum' (-1 : ℤ) h]
    exact finsum_congr fun i => (neg_one_zsmul (f i)).symm
  · have h' : ¬ (Function.support fun i => -f i).Finite := by
      rwa [show (Function.support fun i => -f i) = Function.support f from by
        ext i
        simp [Function.mem_support]]
    rw [finsum_of_infinite_support h', finsum_of_infinite_support h, neg_zero]

theorem fieldPuv_rec (a b : Fld M) (x : M) (ell m n : ℤ) :
    fieldPuv a b x ell (m + 1) n =
      fieldPuv a b x ell m (n + 1) + fieldPuv a b x (ell + 1) m n := by
  have e1 : fieldPuv a b x (ell + 1) m n =
      (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        mode a.1 (ell + (m + 1) - i) (mode b.1 (n + i) x)) +
      ∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x) := by
    rw [fieldPuv,
      show (∑ᶠ i : ℤ, (negOnePow i * cbz (ell + 1) i) •
          mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x)) =
        ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
            mode a.1 (ell + (m + 1) - i) (mode b.1 (n + i) x) +
          (negOnePow i * cbz ell (i - 1)) •
            mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul,
            show ell + 1 + m - i = ell + (m + 1) - i by ring],
      finsum_add_distrib (fieldPuv_fin a b x ell (m + 1) n)
        (fieldPuv_fin' a b x ell m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      mode a.1 (ell + (m + 1) - i) (mode b.1 (n + i) x)) =
      fieldPuv a b x ell (m + 1) n := by rw [fieldPuv]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
      mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x)) =
      -fieldPuv a b x ell m (n + 1) := by
    have step : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x)) =
        ∑ᶠ i : ℤ, -((negOnePow i * cbz ell i) •
          mode a.1 (ell + m - i) (mode b.1 (n + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ =>
        (negOnePow i * cbz ell (i - 1)) •
          mode a.1 (ell + 1 + m - i) (mode b.1 (n + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i by ring, negOnePow_succ,
          show ell + 1 + m - (i + 1) = ell + m - i by ring,
          show n + (i + 1) = n + 1 + i by ring, neg_mul, neg_smul]
    rw [step, field_finsum_neg_distrib, fieldPuv]
  rw [e1, e2, e3]
  abel

theorem fieldPvu_rec (a b : Fld M) (x : M) (ell m n : ℤ) :
    fieldPvu a b x ell (m + 1) n =
      fieldPvu a b x ell m (n + 1) - fieldPvu a b x (ell + 1) m n := by
  have e1 : fieldPvu a b x (ell + 1) m n =
      (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        mode b.1 (ell + (n + 1) - i) (mode a.1 (m + i) x)) +
      ∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x) := by
    rw [fieldPvu,
      show (∑ᶠ i : ℤ, (negOnePow i * cbz (ell + 1) i) •
          mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x)) =
        ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
            mode b.1 (ell + (n + 1) - i) (mode a.1 (m + i) x) +
          (negOnePow i * cbz ell (i - 1)) •
            mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul,
            show ell + 1 + n - i = ell + (n + 1) - i by ring],
      finsum_add_distrib (fieldPvu_fin a b x ell m (n + 1))
        (fieldPvu_fin' a b x ell m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      mode b.1 (ell + (n + 1) - i) (mode a.1 (m + i) x)) =
      fieldPvu a b x ell m (n + 1) := by rw [fieldPvu]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
      mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x)) =
      -fieldPvu a b x ell (m + 1) n := by
    have step : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x)) =
        ∑ᶠ i : ℤ, -((negOnePow i * cbz ell i) •
          mode b.1 (ell + n - i) (mode a.1 (m + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ =>
        (negOnePow i * cbz ell (i - 1)) •
          mode b.1 (ell + 1 + n - i) (mode a.1 (m + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i by ring, negOnePow_succ,
          show ell + 1 + n - (i + 1) = ell + n - i by ring,
          show m + (i + 1) = m + 1 + i by ring, neg_mul, neg_smul]
    rw [step, field_finsum_neg_distrib, fieldPvu]
  rw [e1, e2, e3]
  abel

theorem fieldBL_rec (a b : Fld M) (x : M) (ell m n : ℤ) :
    fieldBL a b x ell (m + 1) n =
      fieldBL a b x ell m (n + 1) + fieldBL a b x (ell + 1) m n := by
  simp only [fieldBL, fieldPuv_rec a b x ell m n, fieldPvu_rec a b x ell m n,
    negOnePow_succ]
  module

/-! ## The iterate base and commutator boundary -/

private theorem field_negOnePow_eq_zpow (ell : ℤ) :
    negOnePow ell = (-1 : ℂ) ^ ell := by
  rcases lt_or_ge ell 0 with hell | hell
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ell = -(k : ℤ) :=
      ⟨(-ell).toNat, by omega⟩
    rw [show negOnePow (-(k : ℤ)) = negOnePow (k : ℤ) by simp [negOnePow],
      negOnePow_natCast, zpow_neg, zpow_natCast]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow, inv_one]
    · rw [hk.neg_one_pow]
      norm_num
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ell = (k : ℤ) :=
      ⟨ell.toNat, (Int.toNat_of_nonneg hell).symm⟩
    rw [negOnePow_natCast, zpow_natCast]

theorem fieldBR_zero (a b : Fld M) (x : M) (ell n : ℤ) :
    fieldBR a b x ell 0 n = mode (prod ell a b).1 n x := by
  rw [fieldBR, finsum_eq_single _ (0 : ℤ) (fun i hi => by
    rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, add_zero, zero_add, sub_zero]

theorem fieldBL_as_finsum (a b : Fld M) (x : M) (ell m n : ℤ) :
    fieldBL a b x ell m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode a.1 (ell + m - i) (mode b.1 (n + i) x) -
        negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x)) := by
  have hf : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ell i) •
        (negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x)))).Finite := by
    refine (fieldPvu_fin a b x ell m n).subset fun i hi => ?_
    simp only [Function.mem_support] at hi ⊢
    intro hz
    exact hi (by rw [smul_comm, hz, smul_zero, neg_zero])
  symm
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (mode a.1 (ell + m - i) (mode b.1 (n + i) x) -
          negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x))) =
      ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
          mode a.1 (ell + m - i) (mode b.1 (n + i) x) +
        -((negOnePow i * cbz ell i) •
          (negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x)))) from
      finsum_congr fun i => by rw [smul_sub, sub_eq_add_neg],
    finsum_add_distrib (fieldPuv_fin a b x ell m n) hf,
    field_finsum_neg_distrib,
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x))) =
        negOnePow ell • fieldPvu a b x ell m n from by
      rw [fieldPvu, smul_finsum' (negOnePow ell) (fieldPvu_fin a b x ell m n)]
      exact finsum_congr fun i => by rw [smul_comm],
    fieldBL, fieldPuv, ← sub_eq_add_neg]

theorem field_borcherds_base (a b : Fld M) (x : M) (ell n : ℤ) :
    fieldBL a b x ell 0 n = fieldBR a b x ell 0 n := by
  rw [fieldBR_zero, fieldBL_as_finsum, mode_prod_iterate a b ell n x,
    finsum_nat_to_int _
      (fun p : ℤ => (negOnePow p * cbz ell p) •
        (mode a.1 (ell - p) (mode b.1 (n + p) x) -
          negOnePow ell • mode b.1 (ell + n - p) (mode a.1 p x)))
      (fun p hp => by simp only [cbz_apply_neg ell hp, mul_zero, zero_smul])
      (fun j => by
        simp only [field_negOnePow_eq_zpow, cbz_apply_nonneg ell (Int.natCast_nonneg j),
          Int.toNat_natCast, zpow_natCast])]
  exact finsum_congr fun i => by
    rw [show ell + (0 : ℤ) - i = ell - i by ring,
      show (0 : ℤ) + i = i by ring]

theorem field_borcherds_boundary {a b : Fld M} (h : Local a.1 b.1)
    (x : M) (m n : ℤ) : fieldBL a b x 0 m n = fieldBR a b x 0 m n := by
  obtain ⟨N, hzero, hcomm⟩ := commutator_prod_bound_of_local h m n
  have e0 : negOnePow (0 : ℤ) = 1 := by
    rw [field_negOnePow_eq_zpow]
    norm_num
  have hBL : fieldBL a b x 0 m n = ⁅mode a.1 m, mode b.1 n⁆ x := by
    rw [fieldBL, fieldPuv, fieldPvu,
      finsum_eq_single _ (0 : ℤ) (fun i hi => by
        rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by
        rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [e0, cbz_zero_left, if_pos, mul_one, one_smul, add_zero,
      zero_add, sub_zero]
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hcommx : ⁅mode a.1 m, mode b.1 n⁆ x = ∑ j : Fin N,
      gBinom m (j : ℕ) • mode (prod ((j : ℕ) : ℤ) a b).1
        (m + n - ((j : ℕ) : ℤ)) x := by
    rw [hcomm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.smul_apply]
  have hBR : fieldBR a b x 0 m n = ∑ j : Fin N,
      gBinom m (j : ℕ) • mode (prod ((j : ℕ) : ℤ) a b).1
        (m + n - ((j : ℕ) : ℤ)) x := by
    rw [fieldBR,
      show (∑ᶠ i : ℤ, cbz m i • mode (prod (0 + i) a b).1 (m + n - i) x) =
          ∑ᶠ i : ℤ, cbz m i • mode (prod i a b).1 (m + n - i) x from
        finsum_congr fun i => by rw [zero_add],
      show (∑ᶠ i : ℤ, cbz m i • mode (prod i a b).1 (m + n - i) x) =
          ∑ᶠ j : ℕ, cbz m (j : ℤ) •
            mode (prod (j : ℤ) a b).1 (m + n - (j : ℤ)) x from
        (finsum_nat_to_int _ _
          (fun p hp => by simp only [cbz_apply_neg m hp, zero_smul])
          (fun j => rfl)).symm,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) (by
        intro i hi
        rw [Function.mem_support] at hi
        by_contra hc
        rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
        exact hi (by
          rw [hzero i hc]
          change cbz m (i : ℤ) • (0 : End ℂ M) x = 0
          rw [LinearMap.zero_apply, smul_zero])),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by
      rw [cbz_apply_nonneg m (Int.natCast_nonneg _), Int.toNat_natCast]
  rw [hBL, hcommx, hBR]

/-! ## Full two-sorted identity -/

omit [Module ℂ M] in private theorem field_antidiag_pin (D : ℤ → ℤ → M)
    (hrec : ∀ ell n : ℤ, D ell (n + 1) = -D (ell + 1) n)
    (hbd : ∀ n : ℤ, D 0 n = 0) : ∀ ell n : ℤ, D ell n = 0 := by
  have hpos : ∀ (j : ℕ) (n : ℤ), D (j : ℤ) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
        have hz : -D ((k : ℤ) + 1) n = 0 := by
          rw [← hrec (k : ℤ) n]
          exact ih (n + 1)
        exact neg_eq_zero.mp hz
  have hneg : ∀ (j : ℕ) (n : ℤ), D (-(j : ℤ)) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 by push_cast; ring]
        have hr := hrec (-(k : ℤ) - 1) (n - 1)
        rw [show (n - 1) + 1 = n by ring,
          show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at hr
        rw [hr, ih (n - 1), neg_zero]
  intro ell n
  rcases lt_or_ge ell 0 with hell | hell
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ell = -(j : ℤ) :=
      ⟨(-ell).toNat, by omega⟩
    exact hneg j n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ell = (j : ℤ) :=
      ⟨ell.toNat, (Int.toNat_of_nonneg hell).symm⟩
    exact hpos j n

/-- The full Borcherds identity for two mutually local fields acting on their original
carrier.  No vertex-algebra or induced-local-system structure is assumed. -/
theorem field_borcherds_of_local {a b : Fld M} (h : Local a.1 b.1)
    (x : M) (ell m n : ℤ) : fieldBL a b x ell m n = fieldBR a b x ell m n := by
  induction m using Int.induction_on generalizing ell n with
  | zero => exact field_borcherds_base a b x ell n
  | succ k ih =>
      rw [fieldBL_rec, fieldBR_rec h, ih ell (n + 1), ih (ell + 1) n]
  | pred k ih =>
      have key := field_antidiag_pin
        (fun ell' n' => fieldBL a b x ell' (-(k : ℤ) - 1) n' -
          fieldBR a b x ell' (-(k : ℤ) - 1) n')
        (fun ell' n' => by
          dsimp only
          have hbl := fieldBL_rec a b x ell' (-(k : ℤ) - 1) n'
          have hbr := fieldBR_rec h x ell' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) by ring] at hbl hbr
          have hih := ih ell' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by
          dsimp only
          rw [field_borcherds_boundary h x (-(k : ℤ) - 1) n', sub_self])
        ell n
      exact sub_eq_zero.mp key

/-- The same theorem with both sides unfolded. -/
theorem field_jacobi_of_local {a b : Fld M} (h : Local a.1 b.1)
    (x : M) (ell m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode a.1 (ell + m - i) (mode b.1 (n + i) x) -
        negOnePow ell • mode b.1 (ell + n - i) (mode a.1 (m + i) x))) =
      ∑ᶠ i : ℤ, cbz m i • mode (prod (ell + i) a b).1 (m + n - i) x := by
  have hB := field_borcherds_of_local h x ell m n
  rwa [fieldBL_as_finsum, fieldBR] at hB

end Fld

end VOA
