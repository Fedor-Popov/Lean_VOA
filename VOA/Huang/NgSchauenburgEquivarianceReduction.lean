import VOA.Huang.NgSchauenburgTEquivariance
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! # Reduction of full generalized-indicator equivariance to the S identity

T-equivariance is proved in the imported file. The S identity is an explicit
hypothesis here; this file does not claim Ng–Schauenburg Theorem 5.4 unconditionally.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- The integer row action is a right group action. -/
theorem rowAction_mul (m l : ℤ) (γ δ : SL(2, ℤ)) :
    rowAction m l (γ * δ) =
      rowAction (rowAction m l γ).1 (rowAction m l γ).2 δ := by
  ext <;> simp [rowAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem rowAction_one (m l : ℤ) : rowAction m l 1 = (m, l) := by
  simp [rowAction]

theorem rowAction_S (m l : ℤ) : rowAction m l ModularGroup.S = (l, -m) := by
  simp [rowAction, ModularGroup.S]

theorem rowAction_T (m l : ℤ) : rowAction m l ModularGroup.T = (m, l + m) := by
  simp [rowAction, ModularGroup.T, add_comm]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- The proved T identity and an S identity imply equivariance under every word
in the modular group, including inverse generators. -/
theorem equivariantIndicator_of_S (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C)
    (hS : ∀ (m l : ℤ) (z : Z.Label → ℂ),
      equivariantIndicator F Z.simple V l (-m) z =
        equivariantIndicator F Z.simple V m l (ρ ModularGroup.S⁻¹ z))
    (m l : ℤ) (γ : SL(2, ℤ)) (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V (rowAction m l γ).1 (rowAction m l γ).2 z =
      equivariantIndicator F Z.simple V m l (ρ (modularInvolution γ) z) := by
  have hm : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  have h (g : SL(2, ℤ)) (hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T}) :
      ∀ (m l : ℤ) (z : Z.Label → ℂ),
        equivariantIndicator F Z.simple V (rowAction m l g).1 (rowAction m l g).2 z =
          equivariantIndicator F Z.simple V m l (ρ (modularInvolution g) z) := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases (show g = ModularGroup.S ∨ g = ModularGroup.T by simpa using hg) with rfl | rfl
      · simpa only [rowAction_S, modularInvolution_S] using hS
      · intro m l z
        simpa only [rowAction_T, modularInvolution_T] using
          equivariantIndicator_T F Z M ρ hr V m l z
    | one =>
      intro m l z
      have ho : modularInvolution 1 = 1 := modularOuterAutomorphism.map_one
      simp [ho]
    | mul a b _ _ ha hb =>
      intro m l z
      rw [rowAction_mul, hb, ha, modularInvolution_mul, map_mul]
      rfl
    | inv a _ ha =>
      intro m l z
      have ho : modularInvolution a⁻¹ = (modularInvolution a)⁻¹ :=
        modularOuterAutomorphism.map_inv a
      have he := ha (rowAction m l a⁻¹).1 (rowAction m l a⁻¹).2
        (ρ (modularInvolution a⁻¹) z)
      have hc : ρ (modularInvolution a) (ρ (modularInvolution a⁻¹) z) = z := by
        rw [ho, map_inv]
        exact (ρ (modularInvolution a)).apply_symm_apply z
      rw [hc] at he
      have hx : rowAction (rowAction m l a⁻¹).1 (rowAction m l a⁻¹).2 a = (m, l) := by
        rw [← rowAction_mul, inv_mul_cancel, rowAction_one]
      rw [hx] at he
      exact he.symm
  exact h γ hm m l z

/-- The full-equivariance target has just its categorical S-generator
identity as an obligation. No separate T-generator premise remains. -/
theorem generalizedIndicatorEquivariance_iff_S (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z) :
    GeneralizedIndicatorEquivariance F Z M ↔
      ∀ (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ))),
        CanonicalCenterRepresentation F Z M ρ → ∀ (V : C) (m l : ℤ) (z : Z.Label → ℂ),
          equivariantIndicator F Z.simple V l (-m) z =
            equivariantIndicator F Z.simple V m l (ρ ModularGroup.S⁻¹ z) := by
  constructor
  · intro he ρ hr V m l z
    simpa only [rowAction_S, modularInvolution_S] using he ρ hr V m l ModularGroup.S z
  · intro hs ρ hr V m l γ z
    exact equivariantIndicator_of_S F Z M ρ hr V (hs ρ hr V) m l γ z

end VOA.Huang.NgSchauenburg
