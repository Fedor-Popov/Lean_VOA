import VOA.Huang.NgSchauenburgMixedDetection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # The actual double of a supplied modular representation

The homomorphism is constructed on pair-label functions, with no center data.
Its generator matrices are independent of both scalar normalizations of the
supplied lift. Existence of a base modular lift is not asserted by this file.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open scoped MatrixGroups

section Matrices
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Standard-coordinate equivalence between invertible matrices and linear automorphisms. -/
def matrixLinearEquiv : (Matrix I I ℂ)ˣ ≃* ((I → ℂ) ≃ₗ[ℂ] (I → ℂ)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ _)

theorem matrixLinearEquiv_apply (A : (Matrix I I ℂ)ˣ) (z : I → ℂ) :
    matrixLinearEquiv A z = (A : Matrix I I ℂ).mulVec z := rfl

theorem matrixLinearEquiv_symm_apply (E : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (i j : I) :
    (matrixLinearEquiv.symm E : Matrix I I ℂ) i j = E (Pi.single j 1) i := rfl

variable {G : Type*} [Group G]

/-- The double representation, constructed directly on functions of pairs. -/
def mixedRepresentation (ρ : G →* ((I → ℂ) ≃ₗ[ℂ] (I → ℂ))) :
    G →* ((I × I → ℂ) ≃ₗ[ℂ] (I × I → ℂ)) :=
  matrixLinearEquiv.toMonoidHom.comp (matrixDouble.toHomUnits.comp
    (matrixLinearEquiv.symm.toMonoidHom.comp ρ))

theorem mixedRepresentation_apply (ρ : G →* ((I → ℂ) ≃ₗ[ℂ] (I → ℂ)))
    (γ : G) (z : I × I → ℂ) :
    mixedRepresentation ρ γ z = (matrixDouble (matrixLinearEquiv.symm (ρ γ))).mulVec z := rfl
end Matrices

open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The S generator of the actual double is the categorical mixed S. -/
theorem mixedRepresentation_S_matrix (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    matrixDouble (matrixLinearEquiv.symm (ρ ModularGroup.S)) = mixedS F M := by
  obtain ⟨a, b, ha, hb⟩ := hr
  apply matrixDouble_eq_of_smul _ (categoricalSUnit F M) a.ne_zero
  ext i j
  rw [matrixLinearEquiv_symm_apply, ha]
  change (a : ℂ) * (∑ k, categoricalS F i k * (Pi.single j (1 : ℂ) : F.Label → ℂ) k) =
    (a : ℂ) * categoricalS F i j
  simp [Pi.single_apply]

open Classical in
/-- The T generator of the double is exactly the raw twist ratio. -/
theorem mixedRepresentation_T_matrix (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    matrixDouble (matrixLinearEquiv.symm (ρ ModularGroup.T)) = mixedT F M.toRibbon := by
  obtain ⟨a, b, ha, hb⟩ := hr
  apply matrixDouble_eq_of_smul _ (categoricalTUnit F M.toRibbon) b.ne_zero
  ext i j
  rw [matrixLinearEquiv_symm_apply, hb]
  change (b : ℂ) * M.twistScalar i * (Pi.single j (1 : ℂ) : F.Label → ℂ) i =
    (b : ℂ) * (Matrix.diagonal M.twistScalar) i j
  by_cases h : i = j
  · subst j; simp
  · simp [h]

open Classical in
theorem mixedRepresentation_S (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (z : F.Label × F.Label → ℂ) :
    mixedRepresentation ρ ModularGroup.S z = (mixedS F M).mulVec z := by
  rw [mixedRepresentation_apply, mixedRepresentation_S_matrix F M ρ hr]

open Classical in
theorem mixedRepresentation_T (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (z : F.Label × F.Label → ℂ) (p : F.Label × F.Label) :
    mixedRepresentation ρ ModularGroup.T z p =
      (M.twistScalar p.1 / M.twistScalar p.2) * z p := by
  rw [mixedRepresentation_apply, mixedRepresentation_T_matrix F M ρ hr, mixedT_eq_diagonal]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

open Classical in
/-- The directly constructed double is independent of the supplied modular lift. -/
theorem mixedRepresentation_independent (F : SphericalFusion C) (M : Modular F)
    (ρ τ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hρ : IsModularRepresentation F M ρ) (hτ : IsModularRepresentation F M τ) :
    mixedRepresentation ρ = mixedRepresentation τ := by
  have hs : mixedRepresentation ρ ModularGroup.S = mixedRepresentation τ ModularGroup.S := by
    ext z p
    rw [mixedRepresentation_S F M ρ hρ, mixedRepresentation_S F M τ hτ]
  have ht : mixedRepresentation ρ ModularGroup.T = mixedRepresentation τ ModularGroup.T := by
    ext z p
    rw [mixedRepresentation_T F M ρ hρ, mixedRepresentation_T F M τ hτ]
  ext γ : 1
  have hg : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases (show g = ModularGroup.S ∨ g = ModularGroup.T by simpa using hg) with rfl | rfl
    · exact hs
    · exact ht
  | one => simp
  | mul a b _ _ ha hb => simp only [map_mul, ha, hb]
  | inv a _ ha => simp only [map_inv, ha]

end VOA.Huang.NgSchauenburg
