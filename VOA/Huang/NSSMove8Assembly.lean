import VOA.Huang.NSSMove8Channels

/-! # Exact channel residual and the equal-twist supported case

Semisimplicity and balancing resolve the interaction, but the weighted
cancellation of the channel sewing defects is still a premise. The proved
special case permits nonsimple products whose supported channels have one twist.
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

/-- The actually occurring simple channels of the dual product have one twist.
This is an explicit sufficient condition, not asserted for arbitrary products. -/
def UniformDualChannelTwist (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (r b : F.Label) : Prop :=
  ∃ t : ℂ, ∀ k : F.Label,
    F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ) ≠ 0 → R.twistScalar k = t

/-- Equal supported twists suffice for scalar monodromy even if the product
is not simple and its decomposition has multiplicities. -/
theorem scalarDualMonodromy_of_uniformDualChannelTwist (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b : F.Label) (h : UniformDualChannelTwist F R r b) :
    ScalarDualMonodromy F r b := by
  classical
  obtain ⟨t, ht⟩ := h
  refine ⟨t / (R.twistScalar b * R.twistScalar r), ?_⟩
  rw [dualInteraction_eq_sum_projectors F R]
  calc
    _ = ∑ k, (t / (R.twistScalar b * R.twistScalar r)) •
        F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ) = 0
      · simp [hk]
      · rw [dualInteractionEigenvalue, ht k hk]
    _ = _ := by rw [← Finset.smul_sum, F.sum_simpleProjector]

/-- Named portion of the target allowing all dual products with one supported
twist, without requiring the products to be simple. -/
def MixedUniformTwistLoopTranspose (F : SphericalFusion C) (R : Ribbon F.toPivotal) : Prop :=
  ∀ r b i j : F.Label, UniformDualChannelTwist F R r b →
    forwardSewingMap F (F.simple r) i j
      (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) =
    inverseSewingMap F (F.simple b) i j
      (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ))

theorem mixedUniformTwistLoopTranspose_holds (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) : MixedUniformTwistLoopTranspose F R := by
  intro r b i j h
  exact mixedScalarLoopTranspose_holds F r b i j
    (scalarDualMonodromy_of_uniformDualChannelTwist F R r b h)

/-- Explicit implication from the supported-twist condition to the complete target. -/
theorem mixedLoopTranspose_of_uniformDualChannelTwists (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (h : ∀ r b, UniformDualChannelTwist F R r b) :
    MixedLoopTranspose F := by
  intro r b i j
  exact mixedUniformTwistLoopTranspose_holds F R r b i j (h r b)

/-- After removing the identity part, only channels of nontrivial twist
contribute to the gap. The prefactor is explicitly nonzero. -/
theorem loopTranspose_gap_eq_twist_channels (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (r b i j : F.Label) :
    forwardSewingMap F (F.simple r) i j
        (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) -
      inverseSewingMap F (F.simple b) i j
        (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ)) =
      (R.twistScalar b * R.twistScalar r)⁻¹ •
        ∑ k, (R.twistScalar k - 1) •
          interactionTransposeDefect F (F.simple r) (F.simple b) i j
            (F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ)) := by
  rw [loopTranspose_gap_eq_sum_shifted_channels F R r b i j
    (R.twistScalar b * R.twistScalar r)⁻¹, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul]
  congr 1
  dsimp only [dualInteractionEigenvalue]
  rw [div_eq_mul_inv]
  ring

/-- Exact remaining weighted cancellation, not proved here. The summands
are the actual open diagrams with intrinsic simple projectors inserted. -/
def MixedTwistChannelCancellation (F : SphericalFusion C) (R : Ribbon F.toPivotal) : Prop :=
  ∀ r b i j : F.Label,
    (∑ k, (R.twistScalar k - 1) •
      interactionTransposeDefect F (F.simple r) (F.simple b) i j
        (F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ))) = 0

/-- No information is lost in the finite channel reduction. -/
theorem mixedLoopTranspose_iff_twistChannelCancellation (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) : MixedLoopTranspose F ↔ MixedTwistChannelCancellation F R := by
  constructor
  · intro h r b i j
    have hg := loopTranspose_gap_eq_twist_channels F R r b i j
    rw [h r b i j, sub_self] at hg
    exact (smul_eq_zero.mp hg.symm).resolve_left
      (inv_ne_zero (mul_ne_zero (R.twistScalar_ne_zero b) (R.twistScalar_ne_zero r)))
  · intro h r b i j
    apply sub_eq_zero.mp
    rw [loopTranspose_gap_eq_twist_channels F R, h r b i j, smul_zero]

/-- Channel-by-channel transposition is sufficient; only the channels of
nontrivial twist need be supplied. This hypothesis remains explicit. -/
theorem mixedLoopTranspose_of_nontrivialTwistProjectors (F : SphericalFusion C)
    (R : Ribbon F.toPivotal)
    (h : ∀ r b i j k : F.Label, R.twistScalar k ≠ 1 →
      interactionTransposeDefect F (F.simple r) (F.simple b) i j
        (F.simpleProjector k (F.simple b ⊗ (F.simple r)ᘁ)) = 0) :
    MixedLoopTranspose F := by
  classical
  apply (mixedLoopTranspose_iff_twistChannelCancellation F R).mpr
  intro r b i j
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : R.twistScalar k = 1
  · simp [hk]
  · rw [h r b i j k hk, smul_zero]

/-- Conditional consequence for the exact original nonzero S move. -/
theorem mixedNonzeroSMove_of_twistChannelCancellation (F : SphericalFusion C)
    (M : Modular F) (h : MixedTwistChannelCancellation F M.toRibbon) :
    MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_loopTranspose F M
    ((mixedLoopTranspose_iff_twistChannelCancellation F M.toRibbon).mpr h)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- Universal version of the still-unproved finite channel cancellation. -/
def NSMixedTwistChannelCancellationAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F), MixedTwistChannelCancellation F M.toRibbon

/-- Conditional assembly; this is not the requested unconditional theorem. -/
theorem nsProjectiveKernelAll_of_twistChannelCancellation
    (h : NSMixedTwistChannelCancellationAll.{v, w}) : NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_nonzeroSMove
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_of_twistChannelCancellation F M (h C F M)

end VOA.Huang.DLNBridge
