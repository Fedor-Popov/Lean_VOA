import VOA.Huang.NSSMove6Inverse

/-! # Fourier inversion after both open sewing calculations -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Remove the double dual-label convention from an actual loop. -/
theorem monodromyLoop_dualLabel_dual (F : SphericalFusion C) (b : F.Label) (X : C) :
    monodromyLoop F.toPivotal (F.simple (F.dualLabel b))ᘁ X =
      monodromyLoop F.toPivotal (F.simple b) X := by
  simpa only [F.dualLabel_involutive b] using
    monodromyLoop_iso F (F.dualLabelIso (F.dualLabel b)) X

/-- The first-label Fourier sum is the normalized projector once its loop
has been transferred to the right bent strand. -/
theorem sum_S_monodromyLoop (F : SphericalFusion C) (M : Modular F)
    (a : F.Label) (X : C) :
    F.globalDimension⁻¹ • (∑ r, categoricalS F r a •
      monodromyLoop F.toPivotal (F.simple r) X) =
      (F.dimension (F.simple a))⁻¹ • F.simpleProjector a X := by
  rw [simpleProjector_eq_sum_loops F M]
  simp only [categoricalS_inv_apply F M, Finset.smul_sum, smul_smul]
  have hc (r : F.Label) : (F.dimension (F.simple a))⁻¹ *
      (F.dimension (F.simple a) * (F.globalDimension⁻¹ *
        categoricalS F (F.dualLabel a) r)) =
      F.globalDimension⁻¹ * categoricalS F (F.dualLabel a) r := by
    field_simp [F.dimension_simple_ne_zero]
  simp only [hc]
  rw [← (F.dualLabelEquiv).sum_comp
    (fun r => (F.globalDimension⁻¹ * categoricalS F (F.dualLabel a) r) •
      monodromyLoop F.toPivotal (F.simple r)ᘁ X)]
  change (∑ r, _ • _) = ∑ r, (F.globalDimension⁻¹ *
    categoricalS F (F.dualLabel a) (F.dualLabel r)) •
      monodromyLoop F.toPivotal (F.simple (F.dualLabel r))ᘁ X
  simp_rw [categoricalS_dual_both F M.toRibbon, monodromyLoop_dualLabel_dual,
    categoricalS_symm F M.toRibbon a]

/-- A proved open first-label Fourier evaluation on the inverse sewing map. -/
theorem inverseChannelCrossing_eq_loopSum (F : SphericalFusion C) (M : Modular F)
    (a b i j : F.Label) :
    inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j =
      F.globalDimension⁻¹ • ∑ r, categoricalS F r a •
        inverseSewingMap F (F.simple b) i j
          (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ)) := by
  rw [inverseChannelCrossing_eq_sewnProjector, ← map_smul,
    ← sum_S_monodromyLoop F M a]
  simp only [map_smul, map_sum]

/-- The remaining local loop transposition, with both sewing maps explicit.
This is an unproved sufficient condition, not a field of `F` or `Modular F`. -/
def MixedLoopTranspose (F : SphericalFusion C) : Prop :=
  ∀ r b i j : F.Label,
    forwardSewingMap F (F.simple r) i j
      (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) =
    inverseSewingMap F (F.simple b) i j
      (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ))

/-- Both label sums and their dimension factors are discharged; the only
premise here is the explicit two-loop transposition. -/
theorem mixedMugerExchange_of_loopTranspose (F : SphericalFusion C) (M : Modular F)
    (h : MixedLoopTranspose F) : MixedMugerExchange F := by
  intro a b i j
  dsimp only [MixedLoopTranspose] at h
  rw [mixedForwardExchange_eq_singleLoopSum F M.toRibbon,
    inverseChannelCrossing_eq_loopSum F M]
  simp_rw [monodromyLoop_dualLabel_dual, h]

/-- Categorical S Fourier inversion is faithful for values in any complex
module, including the full open Hom space. -/
theorem categoricalS_smul_sum_injective (F : SphericalFusion C) (M : Modular F)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (f g : F.Label → E)
    (h : ∀ a, (∑ r, categoricalS F r a • f r) = ∑ r, categoricalS F r a • g r) :
    f = g := by
  classical
  have inv (k : F.Label) (q : F.Label → E) :
      (∑ a, (categoricalS F)⁻¹ k a • ∑ r, categoricalS F r a • q r) = q k := by
    simp_rw [Finset.smul_sum, smul_smul, categoricalS_symm F M.toRibbon]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm (r : F.Label) :
        (∑ a, (categoricalS F)⁻¹ k a * categoricalS F a r) = if k = r then 1 else 0 := by
      have hm := congrArg (fun A : Matrix F.Label F.Label ℂ => A k r)
        (Matrix.nonsing_inv_mul (categoricalS F) (isUnit_iff_ne_zero.mpr M.nondegenerate))
      simpa only [Matrix.mul_apply, Matrix.one_apply] using hm
    simp_rw [hm]
    simp
  funext k
  rw [← inv k f, ← inv k g]
  simp_rw [h]

/-- Under modularity the loop transposition is exactly equivalent to the
original exchange; the reduction has not introduced a stronger residual. -/
theorem mixedMugerExchange_iff_loopTranspose (F : SphericalFusion C) (M : Modular F) :
    MixedMugerExchange F ↔ MixedLoopTranspose F := by
  constructor
  · intro h r b i j
    have hs (a : F.Label) :
        (∑ t, categoricalS F t a • forwardSewingMap F (F.simple t) i j
          (monodromyLoop F.toPivotal (F.simple b) ((F.simple t)ᘁ ⊗ F.simple i))) =
        ∑ t, categoricalS F t a • inverseSewingMap F (F.simple b) i j
          (monodromyLoop F.toPivotal (F.simple t) (F.simple j ⊗ (F.simple b)ᘁ)) := by
      have ha := h a b i j
      rw [mixedForwardExchange_eq_singleLoopSum F M.toRibbon,
        inverseChannelCrossing_eq_loopSum F M] at ha
      simp_rw [monodromyLoop_dualLabel_dual] at ha
      have hc := congrArg (fun f => F.globalDimension • f) ha.symm
      simpa only [smul_smul, mul_inv_cancel₀ F.globalDimension_ne_zero, one_smul] using hc
    exact congrFun (categoricalS_smul_sum_injective F M _ _ hs) r
  · exact mixedMugerExchange_of_loopTranspose F M

end VOA.Huang.NSCongruence
