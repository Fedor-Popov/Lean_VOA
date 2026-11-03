/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroContractionDiagonal

/-!
# Exact degree of the vacuum partition Gram determinant

In the top matrix, a shorter row than column gives zero. A permutation cannot
increase all partition lengths strictly, since it preserves their sum. Every
nonzero determinant term must therefore preserve lengths, and the diagonal
support theorem then forces the permutation to be the identity. The remaining
product consists of the explicitly nonzero diagonal contraction values.

This proves sharp degree at all levels, not singular roots or their multiplicities.
-/
namespace VOA.VirDeformModes.NormalOrdering
open VirModule Polynomial

/-- Every nonidentity permutation contributes zero to the top determinant.
A nonzero contribution would preserve all lengths, then all partition indices. -/
theorem partitionTopMatrix_perm_prod_zero (n : ℕ)
    (σ : Equiv.Perm (SortedOfEnergy n)) (hσ : σ ≠ 1) :
    ∏ j : SortedOfEnergy n, partitionTopMatrix n (σ j) j = 0 := by
  classical
  by_contra hp
  have hne : ∀ j, partitionTopMatrix n (σ j) j ≠ 0 := by
    intro j hj
    apply hp
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  have hle : ∀ j : SortedOfEnergy n, j.val.length ≤ (σ j).val.length := by
    intro j
    by_contra hj
    exact hne j (partitionTopMatrix_eq_zero_of_length_lt n (σ j) j (by omega))
  have hsum : (∑ j : SortedOfEnergy n, j.val.length) =
      ∑ j : SortedOfEnergy n, (σ j).val.length := (Equiv.sum_comp σ (fun j => j.val.length)).symm
  have heq : ∀ j : SortedOfEnergy n, j.val.length = (σ j).val.length :=
    fun j => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum j (Finset.mem_univ j)
  apply hσ
  apply Equiv.ext
  intro j
  change σ j = j
  by_contra hj
  exact hne j (partitionTopMatrix_eq_zero_of_ne_equal_length n (σ j) j hj (heq j).symm)

/-- The determinant of the top matrix is exactly the product of its diagonal
contraction values. No ordering of the finite partition index type is needed. -/
theorem partitionTopMatrix_det (n : ℕ) :
    (partitionTopMatrix n).det = ∏ j : SortedOfEnergy n, diagonalContraction j.val := by
  classical
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (SortedOfEnergy n))]
  · simp [partitionTopMatrix_diagonal]
  · intro σ hσ hne
    rw [partitionTopMatrix_perm_prod_zero n σ hne, smul_zero]
  · simp

/-- The candidate leading coefficient of the vacuum Gram determinant is
nonzero at every level, including the empty partition-index cases. -/
theorem partitionTopMatrix_det_ne_zero (n : ℕ) : (partitionTopMatrix n).det ≠ 0 := by
  rw [partitionTopMatrix_det]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => diagonalContraction_ne_zero j.val)

/-- The actual polynomial Gram determinant is not the zero polynomial.
Its coefficient at the sum of partition lengths is explicitly nonzero. -/
theorem partitionDeterminant_ne_zero (n : ℕ) : (partitionGramPolynomial n).det ≠ 0 := by
  intro hz
  have h := partitionTopMatrix_det_ne_zero n
  rw [← partitionDeterminant_top_coeff, hz, Polynomial.coeff_zero] at h
  exact h rfl

/-- The degree bound is sharp: each partition contributes its number of parts
to the degree of the vacuum Gram determinant. Root factorization is a separate
representation-theoretic theorem and is not assumed in this calculation. -/
theorem partitionDeterminant_natDegree (n : ℕ) :
    (partitionGramPolynomial n).det.natDegree = ∑ j : SortedOfEnergy n, j.val.length := by
  apply le_antisymm (partitionDeterminant_natDegree_le n)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [partitionDeterminant_top_coeff]
  exact partitionTopMatrix_det_ne_zero n

/-- The leading coefficient is the product of the exact diagonal contraction
values. This identifies the nonzero constant needed for a future factorization. -/
theorem partitionDeterminant_leadingCoeff (n : ℕ) :
    (partitionGramPolynomial n).det.leadingCoeff =
      ∏ j : SortedOfEnergy n, diagonalContraction j.val := by
  rw [Polynomial.leadingCoeff, partitionDeterminant_natDegree,
    partitionDeterminant_top_coeff, partitionTopMatrix_det]

end VOA.VirDeformModes.NormalOrdering
