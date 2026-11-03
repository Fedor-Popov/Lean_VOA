/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2FockPolynomialMatrices

/-!
# Exact highest-weight degree of actual affine Verma determinants

The creation factor has leading coefficient one; the adjoint factor has
nonzero oscillator-product leading coefficient at every noncritical level.
Their actual polynomial factorization proves the sharp root-letter degree.
This is an ordinary determinant theorem, not an assumed Kac product.
-/
namespace VOA.Wak.Charged
open Polynomial Matrix
noncomputable section
local instance weightLeadingFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance weightLeadingDecidable (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Total number of lowering letters across the actual creation basis. -/
def creationDegree (n : ℕ) (c : ℤ) : ℕ :=
  ∑ i : JointIndex n c,loweringCount (occupationWord i.val)

/-- Total number of lowering letters across the actual adjoint basis. -/
def rowDegree (n : ℕ) (c : ℤ) : ℕ :=
  ∑ i : JointIndex n c,loweringCount (adjointWord (occupationWord i.val))

/-- Column-wise bounds give the creation determinant degree upper bound. -/
theorem creationPolynomialMatrix_det_degree (k : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).det.natDegree≤creationDegree n c := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans
    (Finset.sum_le_sum (fun i _ => creationPolynomialMatrix_degree k n c (σ i) i))

/-- The coefficient at the creation degree bound is exactly one. -/
theorem creationPolynomialMatrix_det_top (k : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).det.coeff (creationDegree n c)=1 := by
  rw [creationDegree,VirDeformModes.NormalOrdering.coeff_det_sum_column_bounds _ _
    (creationPolynomialMatrix_degree k n c)]
  simpa only [creationPolynomialMatrix_top] using creationTopMatrix_det k n c

/-- The creation determinant is nonzero at every fixed level, including critical level. -/
theorem creationPolynomialMatrix_det_ne_zero (k : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).det≠0 := by
  intro hz
  have ht := creationPolynomialMatrix_det_top k n c
  rw [hz,coeff_zero] at ht
  exact zero_ne_one ht

/-- The creation determinant attains its precise lowering-letter degree. -/
theorem creationPolynomialMatrix_det_natDegree (k : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).det.natDegree=creationDegree n c := by
  apply le_antisymm (creationPolynomialMatrix_det_degree k n c)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [creationPolynomialMatrix_det_top]
  exact one_ne_zero

/-- The actual creation determinant is monic in highest weight. -/
theorem creationPolynomialMatrix_det_leadingCoeff (k : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).det.leadingCoeff=1 := by
  rw [leadingCoeff,creationPolynomialMatrix_det_natDegree,creationPolynomialMatrix_det_top]

/-- Row-wise bounds give the adjoint determinant degree upper bound. -/
theorem rowPolynomialMatrix_det_degree (k : ℂ) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).det.natDegree≤rowDegree n c := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ i : JointIndex n c,loweringCount (adjointWord (occupationWord (σ i).val)) :=
      Finset.sum_le_sum (fun i _ => rowPolynomialMatrix_degree k n c (σ i) i)
    _ = _ := Equiv.sum_comp σ (fun i : JointIndex n c => loweringCount (adjointWord (occupationWord i.val)))

/-- The row determinant's top coefficient is the exact pure-oscillator product. -/
theorem rowPolynomialMatrix_det_top (k : ℂ) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).det.coeff (rowDegree n c)=
      ∏ i : JointIndex n c,derivativeMultiplier k i.val.toMultiset.toList.reverse 0 := by
  rw [← Matrix.det_transpose (rowPolynomialMatrix k n c)]
  rw [rowDegree,VirDeformModes.NormalOrdering.coeff_det_sum_column_bounds
    (rowPolynomialMatrix k n c).transpose _ (fun i j => rowPolynomialMatrix_degree k n c j i)]
  simp only [Matrix.transpose_apply,rowPolynomialMatrix_top]
  change (rowTopMatrix k n c).transpose.det=_
  rw [Matrix.det_transpose,rowTopMatrix_det]

/-- The actual adjoint determinant is a nonzero polynomial at noncritical level. -/
theorem rowPolynomialMatrix_det_ne_zero (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).det≠0 := by
  intro hz
  have ht := rowPolynomialMatrix_det_top k n c
  rw [hz,coeff_zero] at ht
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero k hk _ _)) ht.symm

/-- The row determinant attains its precise adjoint lowering-letter degree. -/
theorem rowPolynomialMatrix_det_natDegree (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).det.natDegree=rowDegree n c := by
  apply le_antisymm (rowPolynomialMatrix_det_degree k n c)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [rowPolynomialMatrix_det_top]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero k hk _ _)

/-- Explicit nonzero leading coefficient of the actual adjoint determinant. -/
theorem rowPolynomialMatrix_det_leadingCoeff (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).det.leadingCoeff=
      ∏ i : JointIndex n c,derivativeMultiplier k i.val.toMultiset.toList.reverse 0 := by
  rw [leadingCoeff,rowPolynomialMatrix_det_natDegree k hk,rowPolynomialMatrix_det_top]

end
end VOA.Wak.Charged
namespace VOA.AffineVOA.HighestModule
open Wak.Charged Polynomial
noncomputable section
local instance vermaLeadingFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance vermaLeadingDecidable (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- The actual highest-weight Verma determinant is nonzero at every
noncritical level and every joint label, including empty blocks. -/
theorem weightDeterminant_ne_zero (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    weightDeterminant k n c≠0 := by
  rw [weightDeterminant,weightGramPolynomial_fock_factor k hk,Matrix.det_mul]
  exact mul_ne_zero (rowPolynomialMatrix_det_ne_zero k hk n c) (creationPolynomialMatrix_det_ne_zero k n c)

/-- Exact highest-weight degree: total charged creation letters, with neutral
letters contributing instead to the level-dependent leading coefficient. -/
theorem weightDeterminant_natDegree (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (weightDeterminant k n c).natDegree=rowDegree n c+creationDegree n c := by
  rw [weightDeterminant,weightGramPolynomial_fock_factor k hk,Matrix.det_mul,
    Polynomial.natDegree_mul (rowPolynomialMatrix_det_ne_zero k hk n c)
      (creationPolynomialMatrix_det_ne_zero k n c),
    rowPolynomialMatrix_det_natDegree k hk,creationPolynomialMatrix_det_natDegree]

/-- Actual Verma leading coefficient is the explicit oscillator product,
including all horizontal, mode, level and repeated-letter factors. -/
theorem weightDeterminant_leadingCoeff (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (weightDeterminant k n c).leadingCoeff=
      ∏ i : JointIndex n c,derivativeMultiplier k i.val.toMultiset.toList.reverse 0 := by
  rw [weightDeterminant,weightGramPolynomial_fock_factor k hk,Matrix.det_mul,
    Polynomial.leadingCoeff_mul,rowPolynomialMatrix_det_leadingCoeff k hk,
    creationPolynomialMatrix_det_leadingCoeff,mul_one]

end
end VOA.AffineVOA.HighestModule
