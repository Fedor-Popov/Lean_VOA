/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ParabolicAdaptedBasis
import VOA.Examples.AffineSl2VacuumDeterminantCoefficient

/-! # The constant adapted parabolic polynomial Gram matrix -/
namespace VOA.AffineVOA.HighestModule
open Polynomial Matrix
noncomputable section
local instance parabolicDetJointFintype (N : ℕ) (c : ℤ) :
    Fintype (Wak.Charged.JointIndex N c) := Wak.Charged.jointIndexFintype N c

local instance parabolicDetJointDecidable (N : ℕ) (c : ℤ) :
    DecidableEq (Wak.Charged.JointIndex N c) := Classical.decEq _
local instance parabolicDetAdaptedDecidable (d N : ℕ) (c : ℤ) :
    DecidableEq (ParabolicAdaptedIndex d N c) := Classical.decEq _

/-- Actual polynomial entries in the fixed adapted family, including chosen complement lifts. -/
def parabolicAdaptedGram (k : ℂ) (d N : ℕ) (c : ℤ) :
    Matrix (ParabolicAdaptedIndex d N c) (ParabolicAdaptedIndex d N c) ℂ[X] :=
  ((parabolicBasisChange d N c).map Polynomial.C).transpose *
    Matrix.reindex (parabolicAdaptedIndexEquiv d N c) (parabolicAdaptedIndexEquiv d N c)
      (weightGramPolynomial k N c) * (parabolicBasisChange d N c).map Polynomial.C

/-- The reindexed original matrix is the actual restricted contravariant form. -/
theorem parabolic_jointContravariant_original_matrix (k h : ℂ) (d N : ℕ) (c : ℤ) :
    LinearMap.BilinForm.toMatrix (parabolicReindexedBasis k h d N c) (jointContravariant k h N c) =
      Matrix.reindex (parabolicAdaptedIndexEquiv d N c) (parabolicAdaptedIndexEquiv d N c)
        (gramMatrix k h N c) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply,parabolicReindexedBasis,
    jointContravariant,LinearMap.compl₁₂_apply,jointBasis_apply,gramMatrix]

/-- Evaluation gives exactly the actual form in the fixed adapted basis. -/
theorem parabolicAdaptedGram_eval_eq (k h : ℂ) (d N : ℕ) (c : ℤ) :
    (parabolicAdaptedGram k d N c).map (Polynomial.eval h) =
      LinearMap.BilinForm.toMatrix (parabolicAdaptedFamilyBasis k h d N c)
        (jointContravariant k h N c) := by
  have he := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (parabolicReindexedBasis k h d N c) (parabolicAdaptedFamilyBasis k h d N c)
    (jointContravariant k h N c)
  rw [parabolicBasisChange_eq,parabolic_jointContravariant_original_matrix] at he
  rw [← he]
  change (Polynomial.evalRingHom h).mapMatrix (parabolicAdaptedGram k d N c) = _
  simp only [parabolicAdaptedGram,RingHom.mapMatrix_apply,Matrix.map_mul]
  have hp : ((parabolicBasisChange d N c).map Polynomial.C).map (Polynomial.evalRingHom h) =
      parabolicBasisChange d N c := by ext i j; simp
  have hpt : ((parabolicBasisChange d N c).map Polynomial.C).transpose.map
      (Polynomial.evalRingHom h) = (parabolicBasisChange d N c).transpose := by ext i j; simp
  have hg : (Matrix.reindex (parabolicAdaptedIndexEquiv d N c) (parabolicAdaptedIndexEquiv d N c)
      (weightGramPolynomial k N c)).map (Polynomial.evalRingHom h) =
      Matrix.reindex (parabolicAdaptedIndexEquiv d N c) (parabolicAdaptedIndexEquiv d N c)
        (gramMatrix k h N c) := by
    have ht := weightGramPolynomial_eval k h N c
    exact congrArg (Matrix.reindex (parabolicAdaptedIndexEquiv d N c)
      (parabolicAdaptedIndexEquiv d N c)) ht
  rw [hp,hpt,hg]

/-- Entrywise evaluation identifies arbitrary complement vectors as well as literal right words. -/
theorem parabolicAdaptedGram_eval (k h : ℂ) (d N : ℕ) (c : ℤ)
    (i j : ParabolicAdaptedIndex d N c) :
    (parabolicAdaptedGram k d N c i j).eval h =
      contravariant k h (parabolicAdaptedFamilyBasis k h d N c i)
        (parabolicAdaptedFamilyBasis k h d N c j) := by
  have he := congrFun (congrFun (parabolicAdaptedGram_eval_eq k h d N c) i) j
  simpa [LinearMap.BilinForm.toMatrix_apply,jointContravariant,LinearMap.compl₁₂_apply] using he

/-- The nonzero scaling is fixed before either variable parameter is specialized. -/
def parabolicDeterminantScale (d N : ℕ) (c : ℤ) : ℂ :=
  (parabolicBasisChange d N c).det ^ 2

theorem parabolicDeterminantScale_ne_zero (d N : ℕ) (c : ℤ) :
    parabolicDeterminantScale d N c ≠ 0 := by
  unfold parabolicDeterminantScale
  exact pow_ne_zero 2 (parabolicBasisChange_det_ne_zero d N c)

/-- The adapted determinant differs from the true Verma determinant by one constant nonzero square. -/
theorem parabolicAdaptedGram_det (k : ℂ) (d N : ℕ) (c : ℤ) :
    (parabolicAdaptedGram k d N c).det =
      Polynomial.C (parabolicDeterminantScale d N c) * weightDeterminant k N c := by
  rw [parabolicAdaptedGram,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    Matrix.det_reindex_self]
  have hp := Polynomial.C.map_det (parabolicBasisChange d N c)
  change Polynomial.C (parabolicBasisChange d N c).det =
    ((parabolicBasisChange d N c).map Polynomial.C).det at hp
  rw [← hp]
  simp only [parabolicDeterminantScale,map_pow,weightDeterminant]
  ring

end
end VOA.AffineVOA.HighestModule
