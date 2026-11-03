import VOA.Huang.NgSchauenburgExponent
import VOA.Huang.NgSchauenburgCongruenceLevel

/-! # Generalized-indicator and projective-kernel descent

The row invariance and center representation identifications required by NS
remain explicit. Equivariance alone is not asserted to imply congruence.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- The outer involution preserves each principal congruence subgroup. -/
theorem modularInvolution_inPrincipalCongruence {N : ℕ} {γ : SL(2, ℤ)}
    (h : InPrincipalCongruence N γ) : InPrincipalCongruence N (modularInvolution γ) := by
  classical
  intro i j
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  fin_cases i <;> fin_cases j <;>
    simp_all [modularInvolution]

/-- NS's last center-kernel step: product covariance and a fixed unit force identity action.
The product is supplied explicitly so this also applies before a Grothendieck
algebra instance is installed. -/
theorem kernelContainsGamma_of_product_and_unit
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (N : ℕ) (mul : W → W → W) (e : W)
    (hunit : ∀ z, mul z e = z)
    (hfix : ∀ γ, InPrincipalCongruence N γ → ρ γ e = e)
    (hprod : ∀ γ, InPrincipalCongruence N γ → ∀ z w,
      mul (ρ γ z) (ρ (modularInvolution γ) w) = mul z w) :
    KernelContainsGamma ρ N := by
  classical
  intro γ hγ
  ext z
  have h := hprod γ hγ z e
  rw [hfix _ (modularInvolution_inPrincipalCongruence hγ), hunit, hunit] at h
  exact h

/-- Descend identity on the tensor representation to scalar action on each factor.
The supplied action identity is what the categorical center factorization must prove. -/
theorem projectiveGamma_of_tensor_action
    {I J K : Type*} [Nonempty I] [Nonempty J]
    (ρ : SL(2, ℤ) →* ((I → ℂ) ≃ₗ[ℂ] (I → ℂ)))
    (τ : SL(2, ℤ) →* ((J → ℂ) ≃ₗ[ℂ] (J → ℂ)))
    (σ : SL(2, ℤ) →* ((K → ℂ) ≃ₗ[ℂ] (K → ℂ)))
    (e : (K → ℂ) ≃ₗ[ℂ] (I × J → ℂ)) (N : ℕ)
    (hσ : KernelContainsGamma σ N)
    (htensor : ∀ γ z w i j,
      e (σ γ (e.symm (fun p => z p.1 * w p.2))) (i, j) = ρ γ z i * τ γ w j) :
    ProjectiveKernelContainsGamma ρ N := by
  classical
  intro γ hγ
  let i₀ : I := Classical.choice inferInstance
  let j₀ : J := Classical.choice inferInstance
  have hp (z : I → ℂ) (w : J → ℂ) (i : I) (j : J) :
      ρ γ z i * τ γ w j = z i * w j := by
    rw [← htensor, hσ γ hγ]
    simp
  have h₀ := hp (fun _ => 1) (fun _ => 1) i₀ j₀
  have hne : τ γ (fun _ => 1) j₀ ≠ 0 := by
    intro hh; simp [hh] at h₀
  refine ⟨Units.mk0 (τ γ (fun _ => 1) j₀)⁻¹ (inv_ne_zero hne), fun z => ?_⟩
  funext i
  have hh := hp z (fun _ => 1) i j₀
  apply mul_right_cancel₀ hne
  simpa [mul_assoc, mul_comm, hne] using hh

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

section Center
variable [RightRigidCategory (Center C)] [HasKernels (Center C)] [HasFiniteBiproducts (Center C)]

/-- Turn the required row invariance into invariance of actual generalized indicators
under the canonical center representation, accounting for the outer involution. -/
theorem indicator_invariant_of_equivariance_and_rows
    (F : SphericalFusion C) (Z : SphericalFusion (Center C)) (M : Modular Z)
    (he : GeneralizedIndicatorEquivariance F Z M)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (N : ℕ)
    (hrow : ∀ γ, InPrincipalCongruence N γ → ∀ (V : C) (m l : ℤ) z,
      equivariantIndicator F Z.simple V (rowAction m l γ).1 (rowAction m l γ).2 z =
        equivariantIndicator F Z.simple V m l z)
    (γ : SL(2, ℤ)) (hγ : InPrincipalCongruence N γ) (V : C) (m l : ℤ) z :
    equivariantIndicator F Z.simple V m l (ρ γ z) =
      equivariantIndicator F Z.simple V m l z := by
  classical
  have hh := hrow (modularInvolution γ) (modularInvolution_inPrincipalCongruence hγ) V m l z
  rw [he ρ hr, modularInvolution_involutive] at hh
  exact hh

/-- The degree `(1,0)` functional is the actual forgetful Hom multiplicity vector. -/
theorem equivariantIndicator_one_zero (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (V : C) (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V 1 0 z =
      ∑ i, z i * (Module.finrank ℂ ((Z.simple i).1 ⟶ V) : ℂ) := by
  classical
  unfold equivariantIndicator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  funext i
  rw [show (1 : ℤ) = (0 : ℕ) + 1 by rfl, generalizedIndicatorAll_positive,
    generalizedIndicatorInt_zero]
  rfl

/-- A concrete consequence needed in NS's multiplication argument; it does not
assume that these forgetful multiplicity rows separate central simple labels. -/
theorem forgetful_multiplicity_invariant
    (F : SphericalFusion C) (Z : SphericalFusion (Center C)) (M : Modular Z)
    (he : GeneralizedIndicatorEquivariance F Z M)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (N : ℕ)
    (hrow : ∀ γ, InPrincipalCongruence N γ → ∀ (V : C) (m l : ℤ) z,
      equivariantIndicator F Z.simple V (rowAction m l γ).1 (rowAction m l γ).2 z =
        equivariantIndicator F Z.simple V m l z)
    (γ : SL(2, ℤ)) (hγ : InPrincipalCongruence N γ) (V : C) z :
    (∑ i, ρ γ z i * (Module.finrank ℂ ((Z.simple i).1 ⟶ V) : ℂ)) =
      ∑ i, z i * (Module.finrank ℂ ((Z.simple i).1 ⟶ V) : ℂ) := by
  classical
  simpa only [equivariantIndicator_one_zero] using
    indicator_invariant_of_equivariance_and_rows F Z M he ρ hr N hrow γ hγ V 1 0 z

/-- Assemble NS's projective endpoint from a canonical center congruence theorem
and the actual factorization of its action. These categorical premises remain open. -/
theorem projectiveCongruenceTheorem_of_center_factorization [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (MZ : Modular Z)
    (he : ModularExponentTheorem F M) (hc : CenterCongruenceTheorem F Z MZ)
    (hfactor : ∀ ρ, IsModularRepresentation F M ρ →
      ∃ (τ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
        (σ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
        (e : (Z.Label → ℂ) ≃ₗ[ℂ] (F.Label × F.Label → ℂ)),
        CanonicalCenterRepresentation F Z MZ σ ∧ ∀ γ z w i j,
          e (σ γ (e.symm (fun p => z p.1 * w p.2))) (i, j) = ρ γ z i * τ γ w j) :
    ProjectiveCongruenceTheorem F M := by
  classical
  apply projectiveCongruenceTheorem_of_containment F M he
  intro ρ hr
  obtain ⟨τ, σ, e, hσ, htensor⟩ := hfactor ρ hr
  letI : Nonempty F.Label := ⟨F.unitLabel⟩
  exact projectiveGamma_of_tensor_action ρ τ σ e (fsExponent F) (hc.2 σ hσ).1 htensor

end Center
end VOA.Huang.NgSchauenburg
