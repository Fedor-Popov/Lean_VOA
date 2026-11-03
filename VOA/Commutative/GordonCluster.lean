/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFiltration
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # A chosen cluster pair with arbitrary remaining blocks -/

namespace VOA.GordonCluster

open Finset Polynomial VOA.GordonPartitionOrder VOA.GordonTwoBlock
open VOA.GordonCollisionCoordinates VOA.GordonFiltration

variable {ρ β K : Type*} [Fintype ρ] [Fintype β] [DecidableEq ρ] [DecidableEq β]

/-- Repartition the chosen pair while leaving every other block assignment fixed. -/
def combinedMap (n v : ℕ) (rest : ρ → β) : Fin n ⊕ ρ → Bool ⊕ β :=
  Sum.map (twoBlockMap n v) rest

@[simp]
theorem blockSize_combinedMap_inl (n v : ℕ) (rest : ρ → β) (j : Bool) :
    blockSize (combinedMap n v rest) (Sum.inl j) = blockSize (twoBlockMap n v) j := by
  simp only [blockSize, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type]
  simp [combinedMap]

@[simp]
theorem blockSize_combinedMap_inr (n v : ℕ) (rest : ρ → β) (j : β) :
    blockSize (combinedMap n v rest) (Sum.inr j) = blockSize rest j := by
  simp only [blockSize, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type]
  simp [combinedMap]

theorem rawParts_combinedMap (n v : ℕ) (rest : ρ → β) :
    rawParts (combinedMap n v rest) = rawParts (twoBlockMap n v) + rawParts rest := by
  simp only [rawParts, ← Finset.univ_disjSum_univ, Finset.val_disjSum,
    Multiset.disjSum, Multiset.map_add, Multiset.map_map, Function.comp_def,
    blockSize_combinedMap_inl, blockSize_combinedMap_inr]

theorem shape_combinedMap_parts {n v : ℕ} (hv : v ≤ n) (rest : ρ → β) :
    (shape (combinedMap n v rest)).parts =
      (rawParts rest + {n - v, v}).filter (· ≠ 0) := by
  rw [shape_parts, rawParts_combinedMap, rawParts_twoBlockMap hv, add_comm]

/-- Repartitioning the chosen pair outside its occupancy interval increases the
full partition, including all other blocks. -/
theorem shape_combinedMap_lexGreater {a b v : ℕ} (hb : 0 < b) (hab : b ≤ a)
    (hv : v ≤ a + b) (hout : v < b ∨ a < v) (rest : ρ → β) :
    LexGreater (shape (combinedMap (a + b) v rest))
      (shape (combinedMap (a + b) a rest)) := by
  apply lexGreater_outside_occupancy _ _ ((rawParts rest).filter (· ≠ 0)) hab hv hout
  · rw [shape_combinedMap_parts (by omega)]
    have ha : a ≠ 0 := by omega
    have hb' : b ≠ 0 := by omega
    simp only [Nat.add_sub_cancel_left, Multiset.filter_add]
    congr 1
    simpa [ha, hb', Multiset.filter_singleton] using (Multiset.pair_comm b a)
  · rw [shape_combinedMap_parts hv]
    simp only [Multiset.filter_add, Multiset.filter_filter, and_self]

noncomputable section
variable [CommRing K]

/-- Evaluate the other blocks as coefficient parameters, retaining the chosen
pair's original variables independently. -/
def partialEval (n : ℕ) (rest : ρ → β) :
    MvPolynomial (Fin n ⊕ ρ) K →+* MvPolynomial (Fin n) (MvPolynomial β K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (Sum.elim MvPolynomial.X (fun i ↦ MvPolynomial.C (MvPolynomial.X (rest i))))

theorem partialEval_rename_left (n : ℕ) (rest : ρ → β)
    (F : MvPolynomial (Fin n ⊕ ρ) K) (e : Equiv.Perm (Fin n)) :
    MvPolynomial.rename e (partialEval n rest F) =
      partialEval n rest (MvPolynomial.rename (Equiv.sumCongr e (Equiv.refl ρ)) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [partialEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i <;> simp [partialEval]

theorem partialEval_isSymmetric (n : ℕ) (rest : ρ → β)
    (F : MvPolynomial (Fin n ⊕ ρ) K) (hF : F.IsSymmetric) :
    (partialEval n rest F).IsSymmetric := by
  intro e
  rw [partialEval_rename_left, hF]

theorem twoValueEval_partialEval (n v : ℕ) (rest : ρ → β)
    (F : MvPolynomial (Fin n ⊕ ρ) K) :
    twoValueEval (initialVariables n v) (partialEval n rest F) =
      MvPolynomial.sumToIter K Bool β (blockEval (combinedMap n v rest) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [partialEval, twoValueEval, blockEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i with
    | inl i =>
      by_cases hi : i.val < v
      · simp [partialEval, twoValueEval, initialVariables, blockEval, combinedMap, twoBlockMap, hi]
      · simp [partialEval, twoValueEval, initialVariables, blockEval, combinedMap, twoBlockMap, hi]
    | inr i => simp [partialEval, twoValueEval, blockEval, combinedMap]

/-- The cluster difference factor for a chosen pair in an arbitrary block
configuration, derived from the concrete Gordon kernel filtration. -/
theorem difference_pow_dvd_of_mem_filtration [Algebra ℚ K] [IsDomain K] [CharZero K]
    {a b : ℕ} (hab : b ≤ a) (rest : ρ → β)
    (U : Submodule K (MvPolynomial (Fin (a + b) ⊕ ρ) K))
    (F : MvPolynomial (Fin (a + b) ⊕ ρ) K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := Bool ⊕ β) U (shape (combinedMap (a + b) a rest))) :
    (MvPolynomial.X (Sum.inl true) - MvPolynomial.X (Sum.inl false)) ^ (2 * b) ∣
      blockEval (combinedMap (a + b) a rest) F := by
  by_cases hb : b = 0
  · simp [hb]
  have hd := difference_pow_two_mul_dvd hab (partialEval (a + b) rest F)
    (partialEval_isSymmetric _ _ _ hF)
  have hlow : ∀ i : Fin b,
      twoValueEval (initialVariables (a + b) i.val) (partialEval (a + b) rest F) = 0 := by
    intro i
    rw [twoValueEval_partialEval,
      eval_eq_zero_of_mem_filtration U _ F hmem _
        (shape_combinedMap_lexGreater (by omega) hab (by omega) (Or.inl i.isLt) rest), map_zero]
  have hhigh : ∀ i : Fin b,
      twoValueEval (initialVariables (a + b) (a + 1 + i.val))
        (partialEval (a + b) rest F) = 0 := by
    intro i
    rw [twoValueEval_partialEval,
      eval_eq_zero_of_mem_filtration U _ F hmem _
        (shape_combinedMap_lexGreater (by omega) hab (by omega) (Or.inr (by omega)) rest), map_zero]
  have hm := map_dvd (MvPolynomial.iterToSum K Bool β) (hd hlow hhigh)
  rw [twoValueEval_partialEval] at hm
  simpa only [map_pow, map_sub, MvPolynomial.iterToSum_X,
    MvPolynomial.iterToSum_sumToIter] using hm

end
end VOA.GordonCluster
