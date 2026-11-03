/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonDivisor

/-! # Quadratic form for the Gordon cluster degree -/

namespace VOA.GordonDegree

open scoped BigOperators
open Finset VOA.GordonFiltration VOA.GordonDivisor VOA.GordonCommonFactors

variable {τ : Type*} [Fintype τ] [LinearOrder τ]

/-- The diagonal plus twice the unordered-pair sum is the full symmetric quadratic sum. -/
theorem two_pairSum_add_diagonal (w : τ → ℕ) :
    2 * (∑ ij : IncreasingPair τ, min (w ij.val.1) (w ij.val.2)) + ∑ i, w i =
      ∑ i, ∑ j, min (w i) (w j) := by
  have hpair : (∑ ij : IncreasingPair τ, min (w ij.val.1) (w ij.val.2)) =
      ∑ i, ∑ j, if i < j then min (w i) (w j) else 0 := by
    have hs := Finset.sum_subtype (p := fun p : τ × τ ↦ p.1 < p.2) (F := inferInstance) (Finset.univ.filter (fun p : τ × τ ↦ p.1 < p.2))
      (by simp) (fun p ↦ min (w p.1) (w p.2))
    rw [Finset.sum_filter, Fintype.sum_prod_type] at hs
    exact hs.symm
  have hswap : (∑ i, ∑ j, if j < i then min (w i) (w j) else 0) =
      ∑ i, ∑ j, if i < j then min (w i) (w j) else 0 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [min_comm]
  have hterm : ∀ i j : τ, min (w i) (w j) =
      (if i < j then min (w i) (w j) else 0) +
      (if j < i then min (w i) (w j) else 0) + (if i = j then w i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le, h.ne]
    · subst j; simp
    · simp [h, not_lt_of_ge h.le, h.ne.symm]
  have htotal : (∑ i, ∑ j, min (w i) (w j)) =
      (∑ i, ∑ j, if i < j then min (w i) (w j) else 0) +
      (∑ i, ∑ j, if j < i then min (w i) (w j) else 0) + ∑ i, w i := by
    calc
      _ = ∑ i, ∑ j, ((if i < j then min (w i) (w j) else 0) +
        (if j < i then min (w i) (w j) else 0) + (if i = j then w i else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_congr rfl (fun j _ ↦ hterm i j)
      _ = _ := by simp only [Finset.sum_add_distrib]; simp
  rw [hswap, ← hpair] at htotal
  omega

/-- The cluster degree is the minimum-kernel quadratic energy minus the number
of original variables, written without truncated subtraction. -/
theorem clusterDegree_add_card {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → τ) :
    clusterDegree f + Fintype.card σ = ∑ i, ∑ j, min (blockSize f i) (blockSize f j) := by
  have h := two_pairSum_add_diagonal (blockSize f)
  have hsum : (∑ i, blockSize f i) = Fintype.card σ := sum_rawParts f
  simpa only [clusterDegree, ← Finset.mul_sum, hsum] using h

theorem clusterDegree_eq_quadratic_sub_card {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → τ) :
    clusterDegree f = (∑ i, ∑ j, min (blockSize f i) (blockSize f j)) - Fintype.card σ := by
  have := clusterDegree_add_card f
  omega

end VOA.GordonDegree
