/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumFirstBlock
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The actual affine Verma-to-vacuum determinant coefficient

The adapted creation family is a basis at every parameter with constant
coordinates. Its Gram determinant differs from the original determinant
by one fixed nonzero square. The first horizontal coefficient therefore
gives the ordinary vacuum determinant times the weight-minus-two determinant.
-/
namespace VOA.AffineVOA.HighestModule
open Polynomial Matrix
noncomputable section
local instance coefficientFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c
local instance coefficientVermaDecidable (n : ℕ) (c : ℤ) : DecidableEq (Wak.Charged.JointIndex n c) := Classical.decEq _
local instance coefficientVacDecidable (n : ℕ) (c : ℤ) : DecidableEq (AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) := Classical.decEq _

/-- A fixed finite index equivalence, justified by the actual adapted basis. -/
def vacuumAdaptedIndexEquiv (n : ℕ) (c : ℤ) : Wak.Charged.JointIndex n c≃VacuumAdaptedIndex n c :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum] using joint_vacuum_dimension n c)

/-- The original PBW basis reindexed by the two adapted blocks. -/
def vacuumReindexedBasis (k h : ℂ) (n : ℕ) (c : ℤ) :
    Module.Basis (VacuumAdaptedIndex n c) ℂ (jointSpace k h n c) :=
  (jointBasis k h n c).reindex (vacuumAdaptedIndexEquiv n c)

/-- The reindexed original basis is transported by the same constant
coordinate equivalence as the adapted basis. -/
theorem vacuumReindexedBasis_transport (k h : ℂ) (n : ℕ) (c : ℤ) :
    vacuumReindexedBasis k h n c=
      (vacuumReindexedBasis 1 0 n c).map (jointCoordinateTransport 1 0 k h n c) := by
  ext i
  simp only [vacuumReindexedBasis,Module.Basis.map_apply,Module.Basis.reindex_apply]
  change (jointBasis k h n c ((vacuumAdaptedIndexEquiv n c).symm i) : Verma k h)=
    (((jointBasis 1 0 n c).equiv (jointBasis k h n c) (Equiv.refl _))
      (jointBasis 1 0 n c ((vacuumAdaptedIndexEquiv n c).symm i)) : Verma k h)
  rw [Module.Basis.equiv_apply]
  rfl

/-- The constant change-of-basis matrix, computed once at level one and
highest weight zero. It is independent of both polynomial parameters. -/
def vacuumBasisChange (n : ℕ) (c : ℤ) : Matrix (VacuumAdaptedIndex n c) (VacuumAdaptedIndex n c) ℂ :=
  (vacuumReindexedBasis 1 0 n c).toMatrix (vacuumAdaptedFamilyBasis 1 0 n c)

/-- Actual basis-change entries have this same value at every parameter. -/
theorem vacuumBasisChange_eq (k h : ℂ) (n : ℕ) (c : ℤ) :
    (vacuumReindexedBasis k h n c).toMatrix (vacuumAdaptedFamilyBasis k h n c)=
      vacuumBasisChange n c := by
  rw [vacuumReindexedBasis_transport,Module.Basis.toMatrix_map]
  have he : (jointCoordinateTransport 1 0 k h n c).symm ∘ vacuumAdaptedFamilyBasis k h n c=
      vacuumAdaptedFamilyBasis 1 0 n c := by
    funext i
    change (jointCoordinateTransport 1 0 k h n c).symm
      (jointCoordinateTransport 1 0 k h n c (vacuumAdaptedBasis 1 (by norm_num) n c i))=_
    rw [LinearEquiv.symm_apply_apply]
    simp [vacuumAdaptedFamilyBasis,jointCoordinateTransport]
  rw [he]
  rfl

/-- The constant basis-change determinant is nonzero, since the actual
basis changes in both directions multiply to the identity. -/
theorem vacuumBasisChange_det_ne_zero (n : ℕ) (c : ℤ) : (vacuumBasisChange n c).det≠0 := by
  have he := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip
    (vacuumReindexedBasis 1 0 n c) (vacuumAdaptedFamilyBasis 1 0 n c))
  rw [Matrix.det_mul,Matrix.det_one] at he
  intro hz
  change (vacuumBasisChange n c).det * _=1 at he
  rw [hz,zero_mul] at he
  exact zero_ne_one he

/-- The fixed nonzero square by which the adapted Gram determinant differs
from the original normalized Verma determinant. -/
def vacuumDeterminantScale (n : ℕ) (c : ℤ) : ℂ := (vacuumBasisChange n c).det^2

/-- This scale never vanishes, including empty joint spaces. -/
theorem vacuumDeterminantScale_ne_zero (n : ℕ) (c : ℤ) : vacuumDeterminantScale n c≠0 :=
  pow_ne_zero _ (vacuumBasisChange_det_ne_zero n c)

/-- The actual canonical form restricted to one joint Verma space. -/
def jointContravariant (k h : ℂ) (n : ℕ) (c : ℤ) :
    LinearMap.BilinForm ℂ (jointSpace k h n c) :=
  (contravariant k h).compl₁₂ (jointSpace k h n c).subtype (jointSpace k h n c).subtype

/-- In the reindexed original basis, the form matrix is just a simultaneous
row/column reindexing of the proved actual Gram matrix. -/
theorem jointContravariant_original_matrix (k h : ℂ) (n : ℕ) (c : ℤ) :
    LinearMap.BilinForm.toMatrix (vacuumReindexedBasis k h n c) (jointContravariant k h n c)=
      Matrix.reindex (vacuumAdaptedIndexEquiv n c) (vacuumAdaptedIndexEquiv n c)
        (gramMatrix k h n c) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply,vacuumReindexedBasis,
    jointContravariant,LinearMap.compl₁₂_apply,jointBasis_apply,gramMatrix]

/-- In the adapted basis the same actual form is exactly the evaluated
fixed-word polynomial Gram matrix. -/
theorem jointContravariant_adapted_matrix (k h : ℂ) (n : ℕ) (c : ℤ) :
    LinearMap.BilinForm.toMatrix (vacuumAdaptedFamilyBasis k h n c) (jointContravariant k h n c)=
      (vacuumAdaptedGram k n c).map (Polynomial.eval h) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply,jointContravariant,
    LinearMap.compl₁₂_apply,Submodule.subtype_apply,vacuumAdaptedFamilyBasis_word,
    Matrix.map_apply,vacuumAdaptedGram,indexedPairPolynomial_eval]

/-- The full adapted polynomial determinant is the original actual Verma
determinant times a fixed nonzero square, with both parameters accounted for. -/
theorem vacuumAdaptedGram_det (k : ℂ) (n : ℕ) (c : ℤ) :
    (vacuumAdaptedGram k n c).det=Polynomial.C (vacuumDeterminantScale n c)*weightDeterminant k n c := by
  apply Polynomial.funext
  intro h
  have he := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (vacuumReindexedBasis k h n c) (vacuumAdaptedFamilyBasis k h n c) (jointContravariant k h n c)
  rw [vacuumBasisChange_eq,jointContravariant_original_matrix,jointContravariant_adapted_matrix] at he
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_reindex_self] at hd
  have hleft : (vacuumAdaptedGram k n c).det.eval h=
      ((vacuumAdaptedGram k n c).map (Polynomial.eval h)).det :=
    (Polynomial.evalRingHom h).map_det _
  have hright : (weightDeterminant k n c).eval h=(gramMatrix k h n c).det := by
    change Polynomial.evalRingHom h (weightGramPolynomial k n c).det=_
    rw [RingHom.map_det]
    change ((weightGramPolynomial k n c).map (Polynomial.eval h)).det=_
    rw [weightGramPolynomial_eval]
  rw [eval_mul,eval_C,hleft,hright,← hd,vacuumDeterminantScale]
  ring

/-- The precise ordinary Verma-to-vacuum coefficient identity. The nonzero
scale is constant in the level, so it cannot change root multiplicities. -/
theorem weightDeterminant_vacuum_coefficient (k : ℂ) (n : ℕ) (c : ℤ) :
    vacuumDeterminantScale n c *
      (weightDeterminant k n c).coeff (Fintype.card (Wak.Charged.JointIndex n (c+1)))=
      ((vacuumChevalleyPolynomial n c).map (Polynomial.eval k)).det*
        (weightDeterminant k n (c+1)).eval (-2) := by
  have he := vacuumAdaptedGram_first_determinant k n c
  rw [vacuumAdaptedGram_det,coeff_C_mul] at he
  exact he

end
end VOA.AffineVOA.HighestModule
