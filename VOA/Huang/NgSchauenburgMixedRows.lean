import VOA.Huang.NgSchauenburgMixedCongruence

/-! # Explicit transforms of the actual mixed multiplicity rows

The S identity is derived from categorical Verlinde and orthogonality. It
computes the transformed (1,0) row, without assuming full indicator equivariance.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits BraidedCategory
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- Verlinde evaluates the S-transform of the genuine mixed (1,0) row. -/
theorem mixed_indicator_one_zero_S (F : SphericalFusion C) (M : Modular F)
    (a k l : F.Label) :
    (∑ p : F.Label × F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 * mixedS F M p (k, l)) =
      if l = F.dualLabel k then
        categoricalS F a k / F.dimension (F.simple k) else 0 := by
  have hi (i : F.Label) :
      (∑ j, (F.fusionMultiplicity i j (F.simple a) : ℂ) *
        categoricalS F (F.dualLabel j) l) =
      categoricalS F i l *
        (categoricalS F a (F.dualLabel l) / F.dimension (F.simple l)) := by
    simp_rw [F.fusion_reciprocity i _ a, F.fusion_comm (F.dualLabel i) a,
      categoricalS_dual_left F M.toRibbon]
    rw [categoricalS_fusion, categoricalS_dual_both F M.toRibbon,
      F.dimension_dualLabel]
    ring
  rw [Fintype.sum_prod_type]
  simp only [mixed_indicator_one_zero, mixedS_apply]
  calc
    _ = F.globalDimension⁻¹ * ∑ i, categoricalS F i k *
        (∑ j, (F.fusionMultiplicity i j (F.simple a) : ℂ) *
          categoricalS F (F.dualLabel j) l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = F.globalDimension⁻¹ *
        (∑ i, categoricalS F k i * categoricalS F l i) *
          (categoricalS F a (F.dualLabel l) / F.dimension (F.simple l)) := by
      simp only [hi, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [categoricalS_symm F M.toRibbon i k, categoricalS_symm F M.toRibbon i l]
      ring
    _ = _ := by
      rw [categoricalS_orthogonality F M]
      split_ifs with h
      · subst l
        simp [F.dualLabel_involutive k, F.dimension_dualLabel, F.globalDimension_ne_zero]
      · simp

open Classical in
/-- Linear-functional version for any supplied modular lift; normalization cancels. -/
theorem equivariantIndicator_mixed_one_zero_S (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label)
    (z : F.Label × F.Label → ℂ) :
    equivariantIndicator F (fun p => mixedCenter (F.simple p.1) (F.simple p.2))
      (F.simple a) 1 0 (mixedRepresentation ρ ModularGroup.S z) =
        ∑ k, z (k, F.dualLabel k) *
          (categoricalS F a k / F.dimension (F.simple k)) := by
  rw [mixedRepresentation_S F M ρ hr]
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h (p : F.Label × F.Label) :
      (∑ q : F.Label × F.Label, mixedS F M q p * z p *
        generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2))
          (F.simple a) 1 0) =
      z p * (if p.2 = F.dualLabel p.1 then
        categoricalS F a p.1 / F.dimension (F.simple p.1) else 0) := by
    rw [← mixed_indicator_one_zero_S F M a p.1 p.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp only [h, Fintype.sum_prod_type, mul_ite, mul_zero]
  simp

/-- The untransformed (1,0) entries lie in every rational subalgebra. -/
theorem mixed_indicator_one_zero_mem (F : SphericalFusion C) (K : Subalgebra ℚ ℂ)
    (a i j : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
      (F.simple a) 1 0 ∈ K := by
  rw [mixed_indicator_one_zero]
  exact K.natCast_mem _

end VOA.Huang.NgSchauenburg
