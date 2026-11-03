/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonPartitionOrder
import VOA.Commutative.GordonCollisionCoordinates
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual evaluation kernels in the Gordon filtration

Block maps assign each original variable to a block label. Their fiber cardinalities,
with empty fibers deleted, give actual `Nat.Partition` indices. The filtration is
an intersection of kernels of the corresponding polynomial evaluation maps, indexed
by descending lexicographic order of these partitions.
-/

namespace VOA.GordonFiltration

open Finset Polynomial VOA.GordonPartitionOrder VOA.GordonTwoBlock
open VOA.GordonCollisionCoordinates

variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

/-- Number of original variables assigned to a block. -/
def blockSize (f : σ → τ) (j : τ) : ℕ := (Finset.univ.filter (f · = j)).card

/-- The block-size multiset, temporarily retaining empty labels. -/
def rawParts (f : σ → τ) : Multiset ℕ := Finset.univ.val.map (blockSize f)

omit [DecidableEq σ] in
theorem sum_rawParts (f : σ → τ) : (rawParts f).sum = Fintype.card σ := by
  change (∑ j : τ, (Finset.univ.filter (f · = j)).card) = Fintype.card σ
  simpa using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset σ)) (t := (Finset.univ : Finset τ))
    (f := f) (fun _ _ ↦ Finset.mem_univ _)).symm

/-- A labeled block map determines a genuine partition; empty blocks are omitted. -/
def shape (f : σ → τ) : Nat.Partition (Fintype.card σ) :=
  Nat.Partition.ofSums _ (rawParts f) (sum_rawParts f)

@[simp]
theorem shape_parts (f : σ → τ) : (shape f).parts = (rawParts f).filter (· ≠ 0) := rfl

/-- The two-block assignment with the first `v` variables in the `true` block. -/
def twoBlockMap (n v : ℕ) : Fin n → Bool := fun i ↦ decide (i.val < v)

@[simp]
theorem blockSize_twoBlockMap_true {n v : ℕ} (hv : v ≤ n) :
    blockSize (twoBlockMap n v) true = v := by
  simpa [blockSize, twoBlockMap, Nat.min_eq_right hv] using
    (Fin.card_filter_val_lt (n := n) (m := v))

@[simp]
theorem blockSize_twoBlockMap_false {n v : ℕ} (hv : v ≤ n) :
    blockSize (twoBlockMap n v) false = n - v := by
  have hc : (Finset.univ.filter (fun i : Fin n ↦ i.val < v)).card = v :=
    card_initialVariables hv
  simp only [blockSize, twoBlockMap, decide_eq_false_iff_not]
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i ↦ i.val < v)
  rw [hc, Finset.card_univ, Fintype.card_fin] at hh
  omega

theorem rawParts_twoBlockMap {n v : ℕ} (hv : v ≤ n) :
    rawParts (twoBlockMap n v) = {n - v, v} := by
  simpa [rawParts, hv] using (Multiset.pair_comm v (n - v))

@[simp]
theorem shape_twoBlockMap_parts {n v : ℕ} (hv : v ≤ n) :
    (shape (twoBlockMap n v)).parts = ({n - v, v} : Multiset ℕ).filter (· ≠ 0) := by
  rw [shape_parts, rawParts_twoBlockMap hv]

/-- The two-block outside specializations have genuinely larger partition indices. -/
theorem shape_twoBlockMap_lexGreater {a b v : ℕ} (hb : 0 < b) (hab : b ≤ a)
    (hv : v ≤ a + b) (hout : v < b ∨ a < v) :
    LexGreater (shape (twoBlockMap (a + b) v)) (shape (twoBlockMap (a + b) a)) := by
  apply lexGreater_outside_occupancy _ _ 0 hab hv hout
  · rw [shape_twoBlockMap_parts (by omega)]
    have ha : a ≠ 0 := by omega
    have hb' : b ≠ 0 := by omega
    simpa [ha, hb', Multiset.filter_singleton] using (Multiset.pair_comm b a)
  · simpa using shape_twoBlockMap_parts hv

noncomputable section
variable [CommRing K]

/-- Evaluate every variable at the variable of its assigned block. -/
def blockEval (f : σ → τ) : MvPolynomial σ K →ₐ[K] MvPolynomial τ K :=
  MvPolynomial.rename f

/-- The Gordon kernel filtration for a fixed finite ambient set of block labels.
Every possible assignment with lexicographically larger shape contributes its actual kernel. -/
def filtration (U : Submodule K (MvPolynomial σ K))
    (lam : Nat.Partition (Fintype.card σ)) : Submodule K (MvPolynomial σ K) :=
  U ⊓ ⨅ f : σ → τ, ⨅ (_ : LexGreater (shape f) lam), (blockEval f).toLinearMap.ker

@[simp]
theorem mem_filtration (U : Submodule K (MvPolynomial σ K))
    (lam : Nat.Partition (Fintype.card σ)) (F : MvPolynomial σ K) :
    F ∈ filtration (τ := τ) U lam ↔
      F ∈ U ∧ ∀ f : σ → τ, LexGreater (shape f) lam → blockEval f F = 0 := by
  simp [filtration, LinearMap.mem_ker]

/-- An evaluation at a larger shape vanishes by the filtration's actual kernel definition. -/
theorem eval_eq_zero_of_mem_filtration (U : Submodule K (MvPolynomial σ K))
    (lam : Nat.Partition (Fintype.card σ)) (F : MvPolynomial σ K)
    (hF : F ∈ filtration (τ := τ) U lam) (f : σ → τ)
    (hlt : LexGreater (shape f) lam) : blockEval f F = 0 :=
  ((mem_filtration U lam F).mp hF).2 f hlt

/-- The evaluation restricted to the corresponding filtration step. -/
def restrictedEval (U : Submodule K (MvPolynomial σ K)) (f : σ → τ) :
    filtration (τ := τ) U (shape f) →ₗ[K] MvPolynomial τ K :=
  (blockEval f).toLinearMap.domRestrict (filtration (τ := τ) U (shape f))

/-- The Gordon successive quotient injects into the polynomial ring via block evaluation. -/
def quotientEquivImage (U : Submodule K (MvPolynomial σ K)) (f : σ → τ) :
    ((filtration (τ := τ) U (shape f)) ⧸ (restrictedEval U f).ker) ≃ₗ[K]
      (restrictedEval U f).range := (restrictedEval U f).quotKerEquivRange

theorem blockEval_twoBlockMap (n v : ℕ) (F : MvPolynomial (Fin n) K) :
    blockEval (twoBlockMap n v) F = twoValueEval (initialVariables n v) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [blockEval, twoValueEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    by_cases hi : i.val < v
    · simp [blockEval, twoBlockMap, twoValueEval, initialVariables, hi]
    · simp [blockEval, twoBlockMap, twoValueEval, initialVariables, hi]

/-- The two-block Gordon difference divisor is derived from membership in actual
lexicographically larger evaluation kernels. No outside vanishing is assumed separately. -/
theorem difference_pow_two_mul_dvd_of_mem_filtration
    [Algebra ℚ K] [IsDomain K] [CharZero K] {a b : ℕ} (hab : b ≤ a)
    (U : Submodule K (MvPolynomial (Fin (a + b)) K))
    (F : MvPolynomial (Fin (a + b)) K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := Bool) U (shape (twoBlockMap (a + b) a))) :
    (MvPolynomial.X true - MvPolynomial.X false) ^ (2 * b) ∣
      blockEval (twoBlockMap (a + b) a) F := by
  by_cases hb : b = 0
  · simp [hb]
  rw [blockEval_twoBlockMap]
  apply difference_pow_two_mul_dvd hab F hF
  · intro i
    rw [← blockEval_twoBlockMap]
    exact eval_eq_zero_of_mem_filtration U _ F hmem _
      (shape_twoBlockMap_lexGreater (by omega) hab (by omega) (Or.inl i.isLt))
  · intro i
    rw [← blockEval_twoBlockMap]
    exact eval_eq_zero_of_mem_filtration U _ F hmem _
      (shape_twoBlockMap_lexGreater (by omega) hab (by omega) (Or.inr (by omega)))

end
end VOA.GordonFiltration
