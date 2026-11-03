import VOA.Huang.NgSchauenburgInductionDimension

/-! # The exact entrywise S-equivariance obligation

The inverse S action is computed with the existing center normalization.
Full indicator equivariance is equivalent to the displayed finite identity
for the genuine rotation traces, for every pair of integer indices.
The finite identity itself remains an obligation, not a proved trace formula.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- The inverse canonical S action has the same base-dimension denominator,
with charge conjugation on its first index. -/
theorem canonicalCenter_S_inv (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (z : Z.Label → ℂ) (i : Z.Label) :
    ρ ModularGroup.S⁻¹ z i = F.globalDimension⁻¹ *
      ∑ j, categoricalS Z (Z.dualLabel i) j * z j := by
  have h := canonicalCenter_S_square_dual F Z M ρ hr
    (ρ ModularGroup.S⁻¹ z) (Z.dualLabel i)
  have hc : ρ ModularGroup.S (ρ ModularGroup.S⁻¹ z) = z := by
    rw [map_inv]
    exact (ρ ModularGroup.S).apply_symm_apply z
  rw [hc, Z.dualLabel_involutive i, hr.2.2.1] at h
  exact h.symm

open Classical in
/-- The inverse S action on a coordinate vector, without any convention left implicit. -/
theorem canonicalCenter_S_inv_single (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (i j : Z.Label) :
    ρ ModularGroup.S⁻¹ (Pi.single i 1) j =
      F.globalDimension⁻¹ * categoricalS Z (Z.dualLabel i) j := by
  classical
  rw [canonicalCenter_S_inv F Z M ρ hr]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [categoricalS_dual_left Z M.toRibbon, categoricalS_symm Z M.toRibbon]

/-- Linear extension of the entrywise S transform of the actual indicators. -/
theorem equivariantIndicator_S_inv (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (m l : ℤ)
    (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V m l (ρ ModularGroup.S⁻¹ z) =
      ∑ i, z i * (F.globalDimension⁻¹ * ∑ j,
        categoricalS Z (Z.dualLabel i) j *
          generalizedIndicatorAll F (Z.simple j) V m l) := by
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    canonicalCenter_S_inv F Z M ρ hr, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [categoricalS_dual_left Z M.toRibbon j i,
    categoricalS_symm Z M.toRibbon j (Z.dualLabel i)]
  ring

/-- Exact equivalence with the existing full-equivariance target. No numerical
indicator family is substituted: both sides use the original rotation traces. -/
theorem generalizedIndicatorEquivariance_iff_S_entries (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z) :
    GeneralizedIndicatorEquivariance F Z M ↔
      ∀ (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ))),
        CanonicalCenterRepresentation F Z M ρ →
        ∀ (V : C) (m l : ℤ) (i : Z.Label),
          generalizedIndicatorAll F (Z.simple i) V l (-m) =
            F.globalDimension⁻¹ * ∑ j,
              categoricalS Z (Z.dualLabel i) j *
                generalizedIndicatorAll F (Z.simple j) V m l := by
  classical
  rw [generalizedIndicatorEquivariance_iff_S]
  constructor
  · intro h ρ hr V m l i
    have hi := h ρ hr V m l (Pi.single i 1)
    rw [equivariantIndicator_basis, equivariantIndicator_S_inv F Z M ρ hr] at hi
    simpa [Pi.single_apply] using hi
  · intro h ρ hr V m l z
    rw [equivariantIndicator_S_inv F Z M ρ hr]
    change (∑ i, z i * generalizedIndicatorAll F (Z.simple i) V l (-m)) = _
    simp only [h ρ hr V m l]

end VOA.Huang.NgSchauenburg
