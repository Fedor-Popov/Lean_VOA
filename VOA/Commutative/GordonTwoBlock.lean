/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.SymmetricOccupancy
import Mathlib.Data.Fintype.Fin

/-!
# The two-block occupancy root geometry

For block sizes `a ≥ b`, the occupancy cardinalities `0, ..., b-1` and
`a+1, ..., a+b` form `2b` distinct valid roots. If a symmetric polynomial
vanishes under these explicit specializations, the occupancy degree bound
forces every specialization, including the split into blocks of sizes `a`
and `b`, to vanish to displacement order at least `2b`.

This proves the root-count geometry used in the Gordon divisibility argument.
The hypotheses concern actual shifted specializations; deriving their vanishing
from a partition filtration is a separate step.
-/

namespace VOA.GordonTwoBlock

open scoped BigOperators
open Polynomial
open VOA.SymmetricOccupancy

/-- The first `v` of `n` variables, with truncation when `v > n`. -/
def initialVariables (n v : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i ↦ i.val < v)

@[simp]
theorem card_initialVariables {n v : ℕ} (hv : v ≤ n) : (initialVariables n v).card = v := by
  simpa [initialVariables, Nat.min_eq_right hv] using (Fin.card_filter_val_lt (n := n) (m := v))

/-- The two outside ranges of occupancies in the two-block argument. -/
def rootCardinality (a b : ℕ) : Fin b ⊕ Fin b → ℕ :=
  Sum.elim (fun i ↦ i.val) (fun i ↦ a + 1 + i.val)

theorem rootCardinality_le (a b : ℕ) (i : Fin b ⊕ Fin b) :
    rootCardinality a b i ≤ a + b := by
  cases i with
  | inl i => simp only [rootCardinality, Sum.elim_inl]; omega
  | inr i => simp only [rootCardinality, Sum.elim_inr]; omega

theorem rootCardinality_injective {a b : ℕ} (hab : b ≤ a) :
    Function.Injective (rootCardinality a b) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [rootCardinality, Sum.elim_inl] at hij
      exact congrArg Sum.inl (Fin.ext hij)
    | inr j => simp only [rootCardinality, Sum.elim_inl, Sum.elim_inr] at hij; omega
  | inr i =>
    cases j with
    | inl j => simp only [rootCardinality, Sum.elim_inl, Sum.elim_inr] at hij; omega
    | inr j =>
      simp only [rootCardinality, Sum.elim_inr] at hij
      exact congrArg Sum.inr (Fin.ext (by omega))

/-- Canonical subsets realizing each of the `2b` root cardinalities. -/
def rootSubset (a b : ℕ) (i : Fin b ⊕ Fin b) : Finset (Fin (a + b)) :=
  initialVariables (a + b) (rootCardinality a b i)

@[simp]
theorem card_rootSubset (a b : ℕ) (i : Fin b ⊕ Fin b) :
    (rootSubset a b i).card = rootCardinality a b i :=
  card_initialVariables (rootCardinality_le a b i)

theorem rootSubset_card_injective {a b : ℕ} (hab : b ≤ a) :
    Function.Injective (fun i ↦ (rootSubset a b i).card) := by
  simpa only [card_rootSubset] using rootCardinality_injective hab

noncomputable section

variable {K : Type*} [CommRing K] [Algebra ℚ K] [IsDomain K] [CharZero K]

/-- The two outside occupancy ranges force order `2b` along every two-value
specialization of the symmetric polynomial. -/
theorem X_pow_two_mul_dvd_of_outer_vanishing {a b : ℕ} (hab : b ≤ a)
    (F : MvPolynomial (Fin (a + b)) K) (hF : F.IsSymmetric) (z : K)
    (hlow : ∀ i : Fin b, shiftedSpecialize z (initialVariables (a + b) i.val) F = 0)
    (hhigh : ∀ i : Fin b, shiftedSpecialize z (initialVariables (a + b) (a + 1 + i.val)) F = 0)
    (T : Finset (Fin (a + b))) :
    Polynomial.X ^ (2 * b) ∣ shiftedSpecialize z T F := by
  apply X_pow_dvd_shifted_of_cardinal_roots F hF z (2 * b) (rootSubset a b)
    (rootSubset_card_injective hab)
  · intro i
    have hzero : shiftedSpecialize z (rootSubset a b i) F = 0 := by
      cases i with
      | inl i => exact hlow i
      | inr i => exact hhigh i
    rw [hzero]
    exact dvd_zero _
  · simp [two_mul]

/-- In particular, the prescribed `a | b` block split has displacement multiplicity
at least `2b`. -/
theorem X_pow_two_mul_dvd_twoBlock {a b : ℕ} (hab : b ≤ a)
    (F : MvPolynomial (Fin (a + b)) K) (hF : F.IsSymmetric) (z : K)
    (hlow : ∀ i : Fin b, shiftedSpecialize z (initialVariables (a + b) i.val) F = 0)
    (hhigh : ∀ i : Fin b, shiftedSpecialize z (initialVariables (a + b) (a + 1 + i.val)) F = 0) :
    Polynomial.X ^ (2 * b) ∣ shiftedSpecialize z (initialVariables (a + b) a) F :=
  X_pow_two_mul_dvd_of_outer_vanishing hab F hF z hlow hhigh _

end
end VOA.GordonTwoBlock
