/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointContractionDiagonal

/-!
# Sharp degree and leading coefficient of affine joint determinants

A nonzero permutation term in the top matrix cannot lower any row length.
Since a permutation preserves the sum of lengths, all lengths agree. The
multiset support theorem then forces every index to be fixed. Thus only the
identity contributes, giving a nonzero explicit product at every joint weight.
This proves exact degree, not the locations or multiplicities of admissible roots.
-/
namespace VOA.AffineSl2GeneralRigidity
open scoped Classical
open AffineVOA AffineSl2PBWWakimotoReduction Sl2NonLisse NormalOrdering Polynomial

/-- Every nonidentity permutation gives zero in the top determinant. The
argument uses lengths and multisets, without an ordering on the finite index set. -/
theorem jointTopMatrix_perm_prod_zero (n h : ℤ) (σ : Equiv.Perm (JointIndex n h))
    (hσ : σ ≠ 1) : (∏ j, jointTopMatrix n h (σ j) j) = 0 := by
  classical
  by_contra hp
  have hne : ∀ j, jointTopMatrix n h (σ j) j ≠ 0 := by
    intro j hj
    exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hle : ∀ j, jointColumnLength n h j ≤ jointColumnLength n h (σ j) := by
    intro j
    by_contra hj
    apply hne j
    apply jointTopMatrix_zero_of_shorter_row
    rw [← jointColumnLength_eq]
    omega
  have hsum : (∑ j, jointColumnLength n h j) = ∑ j, jointColumnLength n h (σ j) :=
    (Equiv.sum_comp σ (jointColumnLength n h)).symm
  have heq : ∀ j, jointColumnLength n h j = jointColumnLength n h (σ j) :=
    fun j => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum j (Finset.mem_univ j)
  apply hσ
  apply Equiv.ext
  intro j
  change σ j=j
  by_contra hj
  exact hne j (jointTopMatrix_zero_of_ne_equal_length n h (σ j) j hj
    (by rw [← jointColumnLength_eq]; exact (heq j).symm))

/-- The exact top determinant is the product of the diagonal contraction
values, each including the sign from the actual opposite-mode adjoint. -/
theorem jointTopMatrix_det (n h : ℤ) :
    (jointTopMatrix n h).det =
      ∏ j : JointIndex n h, (-1 : ℂ)^(orderedPBWColorWord j.val).length *
        diagonalContraction (orderedPBWColorWord j.val) := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (JointIndex n h))]
  · simp [jointTopMatrix_diagonal]
  · intro σ _ hσ
    rw [jointTopMatrix_perm_prod_zero n h σ hσ, smul_zero]
  · simp

/-- The leading candidate never vanishes, including empty joint index sets. -/
theorem jointTopMatrix_det_ne_zero (n h : ℤ) : (jointTopMatrix n h).det ≠ 0 := by
  rw [jointTopMatrix_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (diagonalContraction_ne_zero _)

/-- The actual joint Gram determinant is a nonzero polynomial at every
energy and Cartan charge. This does not assert nondegeneracy at any fixed level. -/
theorem jointDeterminant_ne_zero (n h : ℤ) : jointDeterminant n h ≠ 0 := by
  intro hz
  have hn := jointTopMatrix_det_ne_zero n h
  rw [← jointDeterminant_top_coeff, hz, Polynomial.coeff_zero] at hn
  exact hn rfl

/-- The total PBW column length is the exact degree of the actual joint
Gram determinant, not just an upper bound. -/
theorem jointDeterminant_natDegree (n h : ℤ) :
    (jointDeterminant n h).natDegree = ∑ j, jointColumnLength n h j := by
  apply le_antisymm (jointDeterminant_natDegree_le n h)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [jointDeterminant_top_coeff]
  exact jointTopMatrix_det_ne_zero n h

/-- The leading coefficient is the explicit nonzero signed product of
central matching weights and repeated-letter multiplicities. -/
theorem jointDeterminant_leadingCoeff (n h : ℤ) :
    (jointDeterminant n h).leadingCoeff =
      ∏ j : JointIndex n h, (-1 : ℂ)^(orderedPBWColorWord j.val).length *
        diagonalContraction (orderedPBWColorWord j.val) := by
  rw [Polynomial.leadingCoeff, jointDeterminant_natDegree,
    jointDeterminant_top_coeff, jointTopMatrix_det]

end VOA.AffineSl2GeneralRigidity
