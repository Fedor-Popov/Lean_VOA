/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningVandermonde

/-!
# Pair sums in the screening Ward multiplier

An unordered pair contains each variable r-1 times. The cross terms in
the square of a sum occur twice. These finite identities simplify the two
Vandermonde Ward multipliers without a rational-function calculation.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators

/-- Summing both endpoints of every unordered pair counts each entry r-1 times. -/
theorem screening_pair_sum {R : Type*} [AddCommMonoid R] (r : ℕ) (f : Fin r → R) :
    (∑ ij ∈ variablePairs r, (f ij.1 + f ij.2)) = (r-1) • ∑ i, f i := by
  classical
  rw [variablePairs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hs : ∀ i j : Fin r, (if i < j then f i + f j else 0) =
      (if i < j then f i else 0) + (if i < j then f j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin r => if i < j then f j else 0)]
  rw [← Finset.sum_add_distrib]
  have h : ∀ i j : Fin r, (if i < j then f i else 0) + (if j < i then f i else 0) =
      if j = i then 0 else f i := by
    intro i j
    by_cases hij : i < j
    · simp [hij, not_lt_of_ge hij.le, ne_of_gt hij]
    by_cases hji : j < i
    · simp [hij, hji, ne_of_lt hji]
    have heq : i = j := by omega
    subst j
    simp
  simp_rw [← Finset.sum_add_distrib, h]
  have he : ∀ i : Fin r, Finset.univ.filter (fun j => ¬j = i) = Finset.univ.erase i := by
    intro i
    ext j
    simp [eq_comm]
  simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, he, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  exact (Finset.smul_sum ..).symm

/-- The square of a sum is its diagonal sum plus twice the unordered cross sum. -/
theorem screening_pair_square {R : Type*} [CommRing R] (r : ℕ) (f : Fin r → R) :
    (∑ i, f i)^2 = (∑ i, f i^2) + 2*(∑ ij ∈ variablePairs r, f ij.1*f ij.2) := by
  classical
  have hs : ∀ i j : Fin r, f i*f j =
      (if i = j then f i^2 else 0) +
      (if i < j then f i*f j else 0) + (if j < i then f i*f j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i (_ : i ∈ Finset.univ) => Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun j (_ : j ∈ Finset.univ) => hs i j))
  rw [hsum]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun i j : Fin r => if j < i then f i*f j else 0)]
  have hc : (∑ i : Fin r, ∑ j : Fin r, if i < j then f j*f i else 0) =
      ∑ i : Fin r, ∑ j : Fin r, if i < j then f i*f j else 0 := by
    simp_rw [mul_comm]
  rw [hc]
  simp only [variablePairs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  ring_nf
  simp only [Finset.sum_mul, ite_mul, zero_mul]

end VOA.VirasoroScreening
