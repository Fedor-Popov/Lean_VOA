/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Foundations.FormalDist3
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# Low-level combinatorics for products of formal fields

This file contains only formal-distribution coefficient identities, factorial identities, and
finite-support reindexing lemmas.  It is intentionally independent of vertex algebras and of
the reconstruction, weak-associativity, and Jacobi/Borcherds layers.
-/

namespace VOA.FieldCombinatorics

open scoped BigOperators

/-! ## Coefficients of powers of `z₁-z₂` -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

omit [Module ℂ W] in theorem formalDist₂_sum_apply {ι : Type*} (s : Finset ι)
    (F : ι → FormalDist₂ W)
    (m n : ℤ) : (∑ i ∈ s, F i) m n = ∑ i ∈ s, F i m n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rfl
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change F a m n + (∑ i ∈ t, F i) m n = F a m n + ∑ i ∈ t, F i m n
    rw [ih]

theorem shiftZ₁_pow_apply (k : ℕ) (f : FormalDist₂ W) (m n : ℤ) :
    (((shiftZ₁ : Module.End ℂ (FormalDist₂ W)) ^ k) f) m n = f (m - (k : ℤ)) n := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, shiftZ₁_apply, ih]
      congr 1
      omega

theorem neg_shiftZ₂_pow_apply (k : ℕ) (f : FormalDist₂ W) (m n : ℤ) :
    (((-shiftZ₂ : Module.End ℂ (FormalDist₂ W)) ^ k) f) m n =
      ((-1 : ℤ) ^ k) • f m (n - (k : ℤ)) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change - ((((-shiftZ₂ : Module.End ℂ (FormalDist₂ W)) ^ k) f) m (n - 1)) = _
      rw [ih, ← neg_zsmul]
      congr 2
      · rw [pow_succ]
        ring
      · omega

theorem shiftZ₁_comm_shiftZ₂ :
    Commute (shiftZ₁ : Module.End ℂ (FormalDist₂ W)) shiftZ₂ := by
  change shiftZ₁ * shiftZ₂ = shiftZ₂ * shiftZ₁
  ext f m n
  simp only [Module.End.mul_apply, shiftZ₁_apply, shiftZ₂_apply]

theorem mulBySubPow_eq_npow (N : ℕ) :
    (mulBySubPow N : Module.End ℂ (FormalDist₂ W)) =
      (mulBySub : Module.End ℂ (FormalDist₂ W)) ^ N := by
  induction N with
  | zero => rfl
  | succ k ih =>
      rw [mulBySubPow_succ, ih, pow_succ']
      rfl

theorem mulBySub_eq_shiftZ₁_sub_shiftZ₂ :
    (mulBySub : Module.End ℂ (FormalDist₂ W)) = shiftZ₁ - shiftZ₂ := rfl

/-- The finite binomial expansion of a coefficient of `(z₁-z₂)^N f`. -/
theorem mulBySubPow_apply_sum (N : ℕ) (f : FormalDist₂ W) (m n : ℤ) :
    mulBySubPow N f m n =
      ∑ r ∈ Finset.range (N + 1), (((-1 : ℤ) ^ (N - r)) * (N.choose r : ℤ)) •
        f (m - (r : ℤ)) (n - ((N - r : ℕ) : ℤ)) := by
  rw [mulBySubPow_eq_npow, mulBySub_eq_shiftZ₁_sub_shiftZ₂, sub_eq_add_neg]
  let S₁ : Module.End ℂ (FormalDist₂ W) := shiftZ₁
  let S₂ : Module.End ℂ (FormalDist₂ W) := shiftZ₂
  change (((S₁ + -S₂) ^ N) f) m n = _
  have hcomm : Commute S₁ (-S₂) := by
    dsimp [S₁, S₂]
    exact shiftZ₁_comm_shiftZ₂.neg_right
  rw [hcomm.add_pow N]
  rw [LinearMap.sum_apply (Finset.range (N + 1))
    (fun r => S₁ ^ r * (-S₂) ^ (N - r) *
      (↑(N.choose r) : Module.End ℂ (FormalDist₂ W))) f]
  rw [formalDist₂_sum_apply (Finset.range (N + 1))
    (fun d => (S₁ ^ d * (-S₂) ^ (N - d) *
      (↑(N.choose d) : Module.End ℂ (FormalDist₂ W))) f) m n]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  dsimp [S₁, S₂]
  rw [shiftZ₁_pow_apply, neg_shiftZ₂_pow_apply]
  change ((-1 : ℤ) ^ (N - r)) •
      ((N.choose r : ℕ) • f (m - (r : ℤ)) (n - ((N - r : ℕ) : ℤ))) = _
  rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]

/-! ## Generalized binomial and derivative coefficients -/

theorem gBinom_natCast_eq_choose {n k : ℕ} (hk : k ≤ n) :
    gBinom (n : ℤ) k = (n.choose k : ℂ) := by
  rw [gBinom]
  have hprod : (∏ i ∈ Finset.range k, (((n : ℤ) : ℂ) - (i : ℂ))) =
      (n.descFactorial k : ℂ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hin : i ≤ n := le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hk
    rw [Nat.cast_sub hin]
    rfl
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [Nat.factorial_ne_zero]

theorem gBinom_symm_nat {k i : ℕ} (hik : i ≤ k) :
    gBinom (k : ℤ) (k - i) = gBinom (k : ℤ) i := by
  rw [gBinom_natCast_eq_choose (Nat.sub_le k i), gBinom_natCast_eq_choose hik,
    Nat.choose_symm hik]

theorem deriv_pow_apply (f : FormalDist W) (j : ℕ) (s : ℤ) :
    (deriv^[j] f) s =
      (∏ i ∈ Finset.range j, (s + 1 + (i : ℤ))) • f (s + (j : ℤ)) := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, deriv_apply, ih, smul_smul,
        Finset.prod_range_succ']
      have hidx : (s + 1) + (k : ℤ) = s + ((k + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hidx]
      congr 1
      rw [Nat.cast_zero, add_zero, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by push_cast; ring

theorem asc_prod_cast (a n : ℕ) :
    (∏ i ∈ Finset.range n, ((a : ℂ) + 1 + (i : ℂ))) =
      ((a + n).factorial : ℂ) / (a.factorial : ℂ) := by
  have hN : a.factorial * (a + 1).ascFactorial n = (a + n).factorial :=
    Nat.factorial_mul_ascFactorial a n
  have hprod : ((a + 1).ascFactorial n : ℂ) =
      ∏ i ∈ Finset.range n, ((a : ℂ) + 1 + (i : ℂ)) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have hfac : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  rw [← hprod]
  field_simp
  rw [mul_comm, ← Nat.cast_mul, hN]

theorem gBinom_negsucc (s n : ℕ) :
    gBinom (-(s : ℤ) - 1) n =
      (-1) ^ n * ((s + n).factorial : ℂ) /
        ((s.factorial : ℂ) * (n.factorial : ℂ)) := by
  rw [gBinom]
  have key :
      (∏ i ∈ Finset.range n, (((-(s : ℤ) - 1 : ℤ) : ℂ) - (i : ℂ))) =
        (∏ i ∈ Finset.range n, (-1 : ℂ)) *
          ∏ i ∈ Finset.range n, ((s : ℂ) + 1 + (i : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  rw [key, Finset.prod_const, Finset.card_range, asc_prod_cast s n]
  have hfs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

theorem sing_prod_cast (s n : ℕ) :
    (∏ i ∈ Finset.range n, ((-(n : ℂ) - (s : ℂ)) + (i : ℂ))) =
      (-1) ^ n * ((s + n).factorial : ℂ) / (s.factorial : ℂ) := by
  have key :
      (∏ i ∈ Finset.range n, ((-(n : ℂ) - (s : ℂ)) + (i : ℂ))) =
        (∏ i ∈ Finset.range n, (-1 : ℂ)) *
          ∏ i ∈ Finset.range n, ((n : ℂ) + (s : ℂ) - (i : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [key, Finset.prod_const, Finset.card_range]
  have hrefl :
      (∏ i ∈ Finset.range n, ((n : ℂ) + (s : ℂ) - (i : ℂ))) =
        ∏ i ∈ Finset.range n, ((s : ℂ) + 1 + (i : ℂ)) := by
    rw [← Finset.prod_range_reflect (fun i => (s : ℂ) + 1 + (i : ℂ)) n]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hc : ((n - 1 - i : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc]
    ring
  rw [hrefl, asc_prod_cast s n, mul_div_assoc]

/-! ## Finsum reindexing -/

omit [Module ℂ W] in theorem finsum_mem_of_support_subset' (F : ℤ → W) (s : Set ℤ)
    (h : Function.support F ⊆ s) : (∑ᶠ i ∈ s, F i) = ∑ᶠ i, F i := by
  rw [← finsum_mem_inter_support F s, ← finsum_mem_univ (f := F),
    ← finsum_mem_inter_support F Set.univ, Set.univ_inter, Set.inter_eq_right.mpr h]

omit [Module ℂ W] in theorem finsum_nat_to_int (g : ℕ → W) (F : ℤ → W)
    (hF0 : ∀ p : ℤ, p < 0 → F p = 0) (hFg : ∀ j : ℕ, F (j : ℤ) = g j) :
    (∑ᶠ j : ℕ, g j) = ∑ᶠ p : ℤ, F p := by
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := fun a b h => by simpa using h
  have hsub : Function.support F ⊆ Set.range (fun j : ℕ => (j : ℤ)) := by
    intro p hp
    rw [Function.mem_support] at hp
    rcases lt_or_ge p 0 with hlt | hge
    · exact absurd (hF0 p hlt) hp
    · exact ⟨p.toNat, by simp [Int.toNat_of_nonneg hge]⟩
  rw [← finsum_mem_of_support_subset' F _ hsub, finsum_mem_range hinj]
  exact finsum_congr fun j => (hFg j).symm

end VOA.FieldCombinatorics
