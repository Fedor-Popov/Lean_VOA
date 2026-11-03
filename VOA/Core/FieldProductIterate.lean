/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.LocalSystemBare
import VOA.Core.FieldCombinatorics

/-!
# Mode iterates for products of arbitrary fields

The integer products in `Core.LocalSystemBare` are defined directly on fields: nonnegative
products are commutator residues, while negative products are divided normal products.  This
file reads those definitions coefficientwise and proves the standard iterate formula for every
integer product index.

No locality, Jacobi identity, or vertex-algebra structure is assumed.  Lower truncation enters
only in the negative branch, where it makes each normal-product diagonal finite after evaluation
on a vector.  Consequently the negative and all-integer endpoints are intentionally pointwise.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open FieldCombinatorics

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Nonnegative commutator residues -/

/-- The coefficient formula for a nonnegative commutator product, with ordinary binomial
coefficients.  This is purely formal and needs no field or locality hypothesis. -/
theorem mode_cCoeff_bracket_choose (a b : FormalDist (End ℂ M)) (k : ℕ) (n : ℤ) :
    mode (cCoeff k (bracketDist a b)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ)) •
        (mode a (r : ℤ) * mode b (n + ((k - r : ℕ) : ℤ))
          - mode b (n + ((k - r : ℕ) : ℤ)) * mode a (r : ℤ)) := by
  rw [mode_apply, cCoeff_apply, mulBySubPow_apply_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [bracketDist_apply]
  simp only [mode_apply]
  congr 1
  all_goals ring_nf

/-- The same nonnegative formula in generalized-binomial notation. -/
theorem mode_cCoeff_bracket_nonneg (a b : FormalDist (End ℂ M)) (k : ℕ) (n : ℤ) :
    mode (cCoeff k (bracketDist a b)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode a (r : ℤ) * mode b (n + ((k - r : ℕ) : ℤ))
          - mode b (n + ((k - r : ℕ) : ℤ)) * mode a (r : ℤ)) := by
  rw [mode_cCoeff_bracket_choose]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [gBinom_natCast_eq_choose hrle]
  rw [← Int.cast_smul_eq_zsmul ℂ (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ))]
  congr 1
  push_cast
  rfl

/-- The nonnegative product formula in the standard Borcherds-iterate indexing. -/
theorem mode_cCoeff_bracket_iterate (a b : FormalDist (End ℂ M)) (k : ℕ) (n : ℤ) :
    mode (cCoeff k (bracketDist a b)) n =
      ∑ i ∈ Finset.range (k + 1), ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) •
        (mode a ((k : ℤ) - i) * mode b (n + i)
          - ((-1 : ℂ) ^ k) • (mode b ((k : ℤ) + n - i) * mode a i)) := by
  rw [mode_cCoeff_bracket_nonneg]
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_range_reflect
      (fun r => (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode a (r : ℤ) * mode b (n + ((k - r : ℕ) : ℤ)))) (k + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show k + 1 - 1 - i = k - i by omega, Nat.sub_sub_self hik,
      gBinom_symm_nat hik, Nat.cast_sub hik]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_sub hik, smul_smul,
      show n + ((k : ℤ) - i) = (k : ℤ) + n - i by ring]
    congr 1
    rw [mul_right_comm ((-1 : ℂ) ^ i) (gBinom (k : ℤ) i) ((-1 : ℂ) ^ k)]
    congr 1
    rw [← pow_add, show i + k = (k - i) + 2 * i by omega, pow_add, pow_mul]
    simp

namespace Fld

/-- The nonnegative branch specialized to the total field product. -/
theorem mode_prod_nonneg (a b : Fld M) (k : ℕ) (n : ℤ) :
    mode (prod (k : ℤ) a b).1 n =
      ∑ i ∈ Finset.range (k + 1), ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) •
        (mode a.1 ((k : ℤ) - i) * mode b.1 (n + i)
          - ((-1 : ℂ) ^ k) • (mode b.1 ((k : ℤ) + n - i) * mode a.1 i)) := by
  rw [prod_of_nonneg (Int.natCast_nonneg k)]
  exact mode_cCoeff_bracket_iterate a.1 b.1 k n

end Fld

/-! ## Negative normal products -/

namespace FieldProductIterate

theorem negone_sq_pow (i : ℕ) : (-1 : ℂ) ^ i * (-1 : ℂ) ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem posfac_eq (k i : ℕ) :
    (k.factorial : ℂ)⁻¹ * (∏ j ∈ Finset.range k, ((i : ℂ) + 1 + (j : ℂ))) =
      (-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i := by
  rw [gBinom_negsucc, asc_prod_cast i k,
    show (i + k).factorial = (k + i).factorial by rw [Nat.add_comm]]
  have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [mul_div_assoc, ← mul_assoc, negone_sq_pow, one_mul]
  field_simp

theorem negfac_eq (k i : ℕ) :
    (k.factorial : ℂ)⁻¹ *
        (∏ j ∈ Finset.range k, ((-(k : ℂ) - 1 - (i : ℂ)) + 1 + (j : ℂ))) =
      (-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) := by
  have hsimp :
      (∏ j ∈ Finset.range k, ((-(k : ℂ) - 1 - (i : ℂ)) + 1 + (j : ℂ))) =
        ∏ j ∈ Finset.range k, ((-(k : ℂ) - (i : ℂ)) + (j : ℂ)) := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hsimp, sing_prod_cast i k, gBinom_negsucc,
    show (i + k).factorial = (k + i).factorial by rw [Nat.add_comm]]
  have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [show (-1 : ℂ) ^ i *
        ((-1 : ℂ) ^ i * ↑(k + i).factorial / (↑k.factorial * ↑i.factorial)) =
        ↑(k + i).factorial / (↑k.factorial * ↑i.factorial) by
      rw [← mul_div_assoc, ← mul_assoc, negone_sq_pow, one_mul]]
  field_simp

omit [Module ℂ M] in theorem finsum_le_neg_shift (F : ℤ → M) (k : ℕ)
    (h : ∀ m : ℤ, -(k : ℤ) - 1 < m → F m = 0) :
    (∑ᶠ m : ℤ, F m) = ∑ᶠ i : ℕ, F (-(k : ℤ) - 1 - i) := by
  have hφinj : Function.Injective (fun i : ℕ => (-(k : ℤ) - 1 - (i : ℤ))) := by
    intro a b hab
    simp only at hab
    omega
  have hsupp : Function.support F ⊆ Set.range (fun i : ℕ => (-(k : ℤ) - 1 - (i : ℤ))) := by
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hcon
    refine hm (h m ?_)
    by_contra hle
    push Not at hle
    exact hcon ⟨(-(k : ℤ) - 1 - m).toNat, by simp only; omega⟩
  rw [← finsum_mem_of_support_subset' F _ hsupp, finsum_mem_range hφinj]

omit [Module ℂ M] in theorem finsum_split_nat_neg (f : ℤ → M) (k : ℕ)
    (hfin : (Function.support f).Finite)
    (hmid : ∀ m : ℤ, -(k : ℤ) - 1 < m → m < 0 → f m = 0) :
    (∑ᶠ m : ℤ, f m) = ∑ᶠ i : ℕ, (f (i : ℤ) + f (-(k : ℤ) - 1 - i)) := by
  classical
  have hfP : (Function.support fun m : ℤ => if 0 ≤ m then f m else 0).Finite :=
    hfin.subset fun m hm => by
      rw [Function.mem_support] at hm ⊢
      by_cases h : 0 ≤ m
      · rw [if_pos h] at hm
        exact hm
      · rw [if_neg h] at hm
        exact absurd rfl hm
  have hfN : (Function.support fun m : ℤ => if 0 ≤ m then 0 else f m).Finite :=
    hfin.subset fun m hm => by
      rw [Function.mem_support] at hm ⊢
      by_cases h : 0 ≤ m
      · rw [if_pos h] at hm
        exact absurd rfl hm
      · rw [if_neg h] at hm
        exact hm
  have hiA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hiB : Function.Injective (fun i : ℕ => -(k : ℤ) - 1 - (i : ℤ)) :=
    fun a b hab => by simp only at hab; omega
  have hA : (Function.support fun i : ℕ => f (i : ℤ)).Finite :=
    (hfin.preimage hiA.injOn).subset fun i hi => by
      rw [Function.mem_support] at hi
      exact hi
  have hB : (Function.support fun i : ℕ => f (-(k : ℤ) - 1 - i)).Finite :=
    (hfin.preimage hiB.injOn).subset fun i hi => by
      rw [Function.mem_support] at hi
      exact hi
  rw [show (∑ᶠ m : ℤ, f m) =
        ∑ᶠ m : ℤ, ((if 0 ≤ m then f m else 0) + (if 0 ≤ m then 0 else f m)) from
      finsum_congr fun m => by by_cases h : 0 ≤ m <;> simp [h],
    finsum_add_distrib hfP hfN,
    show (∑ᶠ m : ℤ, if 0 ≤ m then f m else 0) = ∑ᶠ i : ℕ, f (i : ℤ) from
      (finsum_nat_to_int (fun i => f (i : ℤ)) _
        (fun p hp => by rw [if_neg (not_le.mpr hp)])
        (fun j => by rw [if_pos (by exact_mod_cast Nat.zero_le j)])).symm,
    show (∑ᶠ m : ℤ, if 0 ≤ m then 0 else f m) =
        ∑ᶠ i : ℕ, f (-(k : ℤ) - 1 - i) from by
      rw [finsum_le_neg_shift _ k fun m hm => by
        by_cases h0 : 0 ≤ m
        · rw [if_pos h0]
        · rw [if_neg h0]
          exact hmid m hm (not_le.mp h0)]
      exact finsum_congr fun i => by
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ -(k : ℤ) - 1 - i)],
    ← finsum_add_distrib hA hB]

theorem neg_one_zpow_negsucc (k : ℕ) :
    (-1 : ℂ) ^ (-(k : ℤ) - 1) = -((-1 : ℂ) ^ k) := by
  rw [show (-(k : ℤ) - 1) = -(((k + 1 : ℕ)) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one, pow_succ, mul_neg_one]

theorem deriv_pow_middle_zero (a : FormalDist (End ℂ M)) (k : ℕ) {m : ℤ}
    (h1 : -(k : ℤ) - 1 < m) (h2 : m < 0) : ((deriv^[k]) a) m = 0 := by
  rw [deriv_pow_apply,
    show (∏ j ∈ Finset.range k, (m + 1 + (j : ℤ))) = 0 from
      Finset.prod_eq_zero (i := (-m - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [Int.toNat_of_nonneg (by omega)]; ring), zero_smul]

theorem iterate_neg_term_A (a b : FormalDist (End ℂ M)) (k : ℕ) (N : ℤ) (x : M) (i : ℕ) :
    (k.factorial : ℂ)⁻¹ •
        (normalOrdered ((deriv^[k]) a) b (i : ℤ) (-N - 1 - i) x) =
      ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
        mode a (-(k : ℤ) - 1 - i) (mode b (N + i) x) := by
  have ha : a ((i : ℤ) + k) = mode a (-(k : ℤ) - 1 - i) := by
    rw [mode_apply]
    congr 1
    ring
  have hb : b (-N - 1 - (i : ℤ)) = mode b (N + i) := by
    rw [mode_apply]
    congr 1
    ring
  rw [normalOrdered_apply, if_pos (by exact_mod_cast Nat.zero_le i), Module.End.mul_apply,
    deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply, ha, hb, smul_smul,
    show (k.factorial : ℂ)⁻¹ *
        ((∏ j ∈ Finset.range k, ((i : ℤ) + 1 + (j : ℤ)) : ℤ) : ℂ) =
        (-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i from by
      rw [Int.cast_prod]
      push_cast
      exact posfac_eq k i]

theorem iterate_neg_term_B (a b : FormalDist (End ℂ M)) (k : ℕ) (N : ℤ) (x : M) (i : ℕ) :
    (k.factorial : ℂ)⁻¹ •
        (normalOrdered ((deriv^[k]) a) b (-(k : ℤ) - 1 - i)
          (-N - 1 - (-(k : ℤ) - 1 - i)) x) =
      ((-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i)) •
        mode b (-(k : ℤ) - 1 + N - i) (mode a i x) := by
  have hb : b (-N - 1 - (-(k : ℤ) - 1 - i)) =
      mode b (-(k : ℤ) - 1 + N - i) := by
    rw [mode_apply]
    congr 1
    ring
  have ha : a ((-(k : ℤ) - 1 - i) + (k : ℤ)) = mode a i := by
    rw [mode_apply]
    congr 1
    ring
  rw [normalOrdered_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ -(k : ℤ) - 1 - i),
    Module.End.mul_apply, deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ,
    LinearMap.smul_apply, map_smul, hb, ha, smul_smul,
    show (k.factorial : ℂ)⁻¹ *
        ((∏ j ∈ Finset.range k,
          ((-(k : ℤ) - 1 - i) + 1 + (j : ℤ)) : ℤ) : ℂ) =
        (-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) from by
      rw [Int.cast_prod]
      push_cast
      exact negfac_eq k i]

theorem gBinom_natCast_eq_zero {k i : ℕ} (h : k < i) : gBinom (k : ℤ) i = 0 := by
  rw [gBinom, Finset.prod_eq_zero (Finset.mem_range.mpr h) (by push_cast; ring), zero_div]

end FieldProductIterate

/-- The raw diagonal expansion of a negative field product. -/
theorem mode_negProd_expand {a b : FormalDist (End ℂ M)} (ha : IsField a) (hb : IsField b)
    (k : ℕ) (N : ℤ) (x : M) :
    mode (negProd ha hb k) N x = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
      normalOrdered ((deriv^[k]) a) b m (-N - 1 - m) x := by
  rw [mode_apply, negProd_apply, nprod_apply]

/-- The negative normal product in standard Borcherds-iterate form. -/
theorem mode_negProd_iterate {a b : FormalDist (End ℂ M)} (ha : IsField a) (hb : IsField b)
    (k : ℕ) (N : ℤ) (x : M) :
    mode (negProd ha hb k) N x =
      ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
        (mode a (-(k : ℤ) - 1 - i) (mode b (N + i) x)
          - ((-1 : ℂ) ^ (-(k : ℤ) - 1)) •
            mode b (-(k : ℤ) - 1 + N - i) (mode a i x)) := by
  rw [mode_negProd_expand]
  let f : ℤ → M := fun m => normalOrdered ((deriv^[k]) a) b m (-N - 1 - m) x
  have hfin : (Function.support f).Finite :=
    normalOrdered_diag_support_finite (ha.deriv_iterate k) hb (-N - 1) x
  have hmid : ∀ m : ℤ, -(k : ℤ) - 1 < m → m < 0 → f m = 0 := by
    intro m hm1 hm2
    rw [show f m = normalOrdered ((deriv^[k]) a) b m (-N - 1 - m) x by rfl,
      normalOrdered_apply, if_neg (not_le.mpr hm2), Module.End.mul_apply,
      FieldProductIterate.deriv_pow_middle_zero a k hm1 hm2, LinearMap.zero_apply, map_zero]
  have hinjA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hinjB : Function.Injective (fun i : ℕ => -(k : ℤ) - 1 - (i : ℤ)) :=
    fun p q hpq => by simp only at hpq; omega
  have hA : (Function.support fun i : ℕ => f (i : ℤ)).Finite :=
    (hfin.preimage hinjA.injOn).subset fun i hi => hi
  have hB : (Function.support fun i : ℕ => f (-(k : ℤ) - 1 - (i : ℤ))).Finite :=
    (hfin.preimage hinjB.injOn).subset fun i hi => hi
  have hsum_fin :
      (Function.support fun i : ℕ => f (i : ℤ) + f (-(k : ℤ) - 1 - (i : ℤ))).Finite := by
    refine (hA.union hB).subset fun i hi => ?_
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Set.mem_union, Function.mem_support, Function.mem_support, not_or, not_not,
      not_not] at hc
    exact hi (by rw [hc.1, hc.2, add_zero])
  rw [FieldProductIterate.finsum_split_nat_neg f k hfin hmid,
    smul_finsum' (k.factorial : ℂ)⁻¹ hsum_fin]
  refine finsum_congr fun i => ?_
  rw [smul_add, FieldProductIterate.iterate_neg_term_A a b k N x i,
    FieldProductIterate.iterate_neg_term_B a b k N x i,
    FieldProductIterate.neg_one_zpow_negsucc]
  module

namespace Fld

/-- The negative branch specialized to the total field product. -/
theorem mode_prod_neg (a b : Fld M) (k : ℕ) (N : ℤ) (x : M) :
    mode (prod (-(k : ℤ) - 1) a b).1 N x =
      ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
        (mode a.1 (-(k : ℤ) - 1 - i) (mode b.1 (N + i) x)
          - ((-1 : ℂ) ^ (-(k : ℤ) - 1)) •
            mode b.1 (-(k : ℤ) - 1 + N - i) (mode a.1 i x)) := by
  rw [prod_of_neg (by omega)]
  rw [show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
  exact mode_negProd_iterate a.2 b.2 k N x

/-- The standard pointwise iterate formula for the total field product, at every integer
product index.  This is a theorem of formal field calculus, not a Jacobi assumption. -/
theorem mode_prod_iterate (a b : Fld M) (ell N : ℤ) (x : M) :
    mode (prod ell a b).1 N x =
      ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ell i) •
        (mode a.1 (ell - i) (mode b.1 (N + i) x)
          - ((-1 : ℂ) ^ ell) • mode b.1 (ell + N - i) (mode a.1 i x)) := by
  rcases lt_or_ge ell 0 with hell | hell
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ell = -(k : ℤ) - 1 :=
      ⟨(-ell - 1).toNat, by omega⟩
    exact mode_prod_neg a b k N x
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ell = (k : ℤ) := ⟨ell.toNat, by omega⟩
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
      exact hi (by
        rw [FieldProductIterate.gBinom_natCast_eq_zero (by omega : k < i), mul_zero,
          zero_smul]))]
    have happ := DFunLike.congr_fun (mode_prod_nonneg a b k N) x
    rw [happ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.mul_apply, ← zpow_natCast (-1 : ℂ) k]

end Fld

end VOA
