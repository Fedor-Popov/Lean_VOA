import VOA.Huang.NSSMove2Diagrams

/-! # A proved fusion moment of the mixed exchange coefficients

This identity is strictly scalar. It checks the coefficient normalization and
dual-label orientation against actual categorical fusion multiplicities; it
does not assert the open morphism exchange.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- A scalar consequence of Verlinde for exactly the `NSSMove2` coefficient. -/
theorem mixedExchangeCoefficient_fusion_sum (F : SphericalFusion C) (M : Modular F)
    (a b i : F.Label) :
    (∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
      (F.fusionMultiplicity q.1 q.2 (F.simple i) : ℂ)) =
      if b = F.dualLabel a then
        categoricalS F a i / F.dimension (F.simple a) else 0 := by
  have inner (r : F.Label) :
      (∑ s, categoricalS F (F.dualLabel s) b *
        (F.fusionMultiplicity r s (F.simple i) : ℂ)) =
      categoricalS F r b * categoricalS F i (F.dualLabel b) /
        F.dimension (F.simple b) := by
    calc
      _ = ∑ s, (F.fusionMultiplicity (F.dualLabel r) i (F.simple s) : ℂ) *
          categoricalS F s (F.dualLabel b) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [categoricalS_dual_left F M.toRibbon, F.fusion_reciprocity r s i]
        ring
      _ = _ := by
        rw [categoricalS_fusion, categoricalS_dual_both F M.toRibbon,
          F.dimension_dualLabel]
  rw [Fintype.sum_prod_type]
  simp only [mixedExchangeCoefficient]
  simp_rw [mul_assoc, ← Finset.mul_sum, inner]
  have rearrange :
      (∑ r, F.globalDimension⁻¹ * (categoricalS F r a *
        (categoricalS F r b * categoricalS F i (F.dualLabel b) /
          F.dimension (F.simple b)))) =
      F.globalDimension⁻¹ *
        (∑ r, categoricalS F a r * categoricalS F b r) *
          (categoricalS F i (F.dualLabel b) / F.dimension (F.simple b)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [categoricalS_symm F M.toRibbon r a, categoricalS_symm F M.toRibbon r b]
    ring
  rw [Finset.mul_sum, rearrange, categoricalS_orthogonality F M]
  split_ifs with h
  · subst b
    rw [F.dualLabel_involutive a, F.dimension_dualLabel]
    rw [inv_mul_cancel₀ F.globalDimension_ne_zero, one_mul,
      categoricalS_symm F M.toRibbon i a]
  · simp

open Classical in
/-- A named, proved scalar target, retaining the exact fusion data. It is not
offered as a replacement for `MixedMugerExchange`. -/
def MixedFusionMoment (F : SphericalFusion C) : Prop :=
  ∀ a b i : F.Label,
    (∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
      (F.fusionMultiplicity q.1 q.2 (F.simple i) : ℂ)) =
      if b = F.dualLabel a then
        categoricalS F a i / F.dimension (F.simple a) else 0

theorem mixedFusionMoment_holds (F : SphericalFusion C) (M : Modular F) :
    MixedFusionMoment F := mixedExchangeCoefficient_fusion_sum F M

end VOA.Huang.NSCongruence
