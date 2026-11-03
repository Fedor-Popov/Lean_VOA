/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerLimit

/-!
# `pp` is Mathlib's partition count

`RRLowerQBinomial.pp M` was defined by recursion (partitions of `M` into parts `≤ M`).  This file
identifies it with the cardinality of Mathlib's `Nat.Partition M`, through the multiplicity
equivalence `Nat.Partition M ≃ {a : Fin M → Fin (M+1) // Σ_j (j+1) a_j = M}`
(`partitionMultEquiv`), so that the Rocha-Caridi side `rc` is literally
`Σ_k (-1)^k p(N - k(5k+3)/2)` with Mathlib's `p`.

* `pp_eq_card : pp M = Fintype.card (Nat.Partition M)`.

All proved, no hypotheses.
-/

namespace VOA.RRLower

open Finset

theorem parts_card_le {M : ℕ} (p : Nat.Partition M) : Multiset.card p.parts ≤ M := by
  have h : (p.parts.map (fun _ => 1)).sum ≤ (p.parts.map id).sum :=
    Multiset.sum_map_le_sum_map _ _ fun i hi => p.parts_pos hi
  simpa [p.parts_sum] using h

/-- The multiplicity of the part `j + 1`. -/
def multOf {M : ℕ} (p : Nat.Partition M) : Fin M → Fin (M + 1) := fun j =>
  ⟨p.parts.count ((j : ℕ) + 1),
    Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans (parts_card_le p))⟩

theorem sum_mult_eq {M : ℕ} (p : Nat.Partition M) :
    ∑ j : Fin M, ((j : ℕ) + 1) * p.parts.count ((j : ℕ) + 1) = M := by
  classical
  have hsub : p.parts.toFinset ⊆ range (M + 1) := by
    intro i hi
    rw [Multiset.mem_toFinset] at hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hi)
  have h := Finset.sum_multiset_count_of_subset p.parts (range (M + 1)) hsub
  rw [p.parts_sum, Finset.sum_range_succ'] at h
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  rw [← Fin.sum_univ_eq_sum_range (fun j => p.parts.count (j + 1) * (j + 1)) M] at h
  conv_rhs => rw [h]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The partition with prescribed multiplicities. -/
def partOfMult {M : ℕ} (a : Fin M → Fin (M + 1))
    (ha : ∑ j : Fin M, (((j : ℕ) + 1 : ℕ) : ℤ) * ((a j : ℕ) : ℤ) = M) : Nat.Partition M where
  parts := ∑ j : Fin M, (a j : ℕ) • ({(j : ℕ) + 1} : Multiset ℕ)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_sum] at hi
    obtain ⟨j, _, hj⟩ := hi
    rw [Multiset.mem_nsmul] at hj
    rw [Multiset.mem_singleton.mp hj.2]
    exact Nat.succ_pos _
  parts_sum := by
    rw [Multiset.sum_sum]
    simp only [Multiset.sum_nsmul, Multiset.sum_singleton, smul_eq_mul]
    have : ((∑ j : Fin M, (a j : ℕ) * ((j : ℕ) + 1) : ℕ) : ℤ) = M := by
      push_cast
      rw [← ha]
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact_mod_cast this

theorem count_partOfMult {M : ℕ} (a : Fin M → Fin (M + 1))
    (ha : ∑ j : Fin M, (((j : ℕ) + 1 : ℕ) : ℤ) * ((a j : ℕ) : ℤ) = M) (i : ℕ) :
    (partOfMult a ha).parts.count i =
      ∑ j : Fin M, if i = (j : ℕ) + 1 then (a j : ℕ) else 0 := by
  classical
  simp only [partOfMult]
  rw [Multiset.count_sum']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  split_ifs <;> simp

/-- The multiplicity equivalence. -/
def partitionMultEquiv (M : ℕ) :
    Nat.Partition M ≃
      {a : Fin M → Fin (M + 1) // ∑ j : Fin M, ((j : ℕ) + 1 : ℤ) * ((a j : ℕ) : ℤ) = M} where
  toFun p := ⟨multOf p, by
    have := sum_mult_eq p
    simp only [multOf]
    exact_mod_cast this⟩
  invFun a := partOfMult a.1 (by have := a.2; push_cast; exact this)
  left_inv p := by
    classical
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro i
    rw [count_partOfMult]
    simp only [multOf]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [Finset.sum_eq_zero (fun j _ => if_neg (Nat.succ_ne_zero _).symm)]
      exact (Multiset.count_eq_zero.mpr fun h => (lt_irrefl 0) (p.parts_pos h)).symm
    · by_cases hiM : i ≤ M
      · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩]
        · simp only
          rw [if_pos (by omega), show i - 1 + 1 = i by omega]
        · intro j _ hj
          rw [if_neg]
          intro h
          apply hj
          ext
          simp only
          omega
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero (fun j _ => if_neg (by omega))]
        exact (Multiset.count_eq_zero.mpr fun h =>
          hiM (Nat.Partition.le_of_mem_parts h)).symm
  right_inv a := by
    classical
    apply Subtype.ext
    funext j
    apply Fin.ext
    simp only [multOf]
    rw [count_partOfMult, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [if_neg]
      intro h
      apply hk
      ext
      omega
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **`pp` is Mathlib's partition number.** -/
theorem pp_eq_card (M : ℕ) : pp M = Fintype.card (Nat.Partition M) := by
  have h := card_wt M M M le_rfl
  rw [pp, show ((M : ℤ)).toNat = M from Int.toNat_natCast M, ← h]
  exact_mod_cast (Fintype.card_congr (partitionMultEquiv M)).symm

end VOA.RRLower
