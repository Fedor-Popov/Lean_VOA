import VOA.Huang.NSSMove7Scalar
import VOA.Huang.NSSMove7Pointed

/-! # Assembly with only the nonscalar loop interactions left open

`MixedScalarLoopTranspose` and `MixedUnitLoopTranspose` are proved. The
nonscalar residual below is not proved here. In particular this module does
not declare an unconditional projective-kernel theorem.
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

/-- Explicit remaining portion of the original target: interacting colors
whose actual dual monodromy is not a scalar endomorphism. -/
def MixedNonscalarLoopTranspose (F : SphericalFusion C) : Prop :=
  ∀ r b i j : F.Label, ¬ ScalarDualMonodromy F r b →
    forwardSewingMap F (F.simple r) i j
      (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) =
    inverseSewingMap F (F.simple b) i j
      (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ))

/-- The proved scalar cases leave exactly the stated nonscalar residual. -/
theorem mixedLoopTranspose_iff_nonscalar (F : SphericalFusion C) :
    MixedLoopTranspose F ↔ MixedNonscalarLoopTranspose F := by
  classical
  constructor
  · intro h r b i j _
    exact h r b i j
  · intro h r b i j
    by_cases hs : ScalarDualMonodromy F r b
    · exact mixedScalarLoopTranspose_holds F r b i j hs
    · exact h r b i j hs

/-- Conditional consequence for the original S-move, with the remaining
nonscalar diagram premise kept explicit. -/
theorem mixedNonzeroSMove_of_nonscalarLoopTranspose (F : SphericalFusion C)
    (M : Modular F) (h : MixedNonscalarLoopTranspose F) : MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_loopTranspose F M ((mixedLoopTranspose_iff_nonscalar F).mpr h)

/-- The S-move for the explicit simple-dual-product special case. -/
theorem mixedNonzeroSMove_of_simple_dual_products (F : SphericalFusion C)
    (M : Modular F) (h : ∀ r b : F.Label, Simple (F.simple b ⊗ (F.simple r)ᘁ)) :
    MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_loopTranspose F M (mixedLoopTranspose_of_simple_dual_products F h)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- Universal form of the still-unproved nonscalar residual. -/
def NSMixedNonscalarLoopTransposeAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (_M : Modular F), MixedNonscalarLoopTranspose F

/-- An explicit conditional assembly, not `nsProjectiveKernelAll_holds`. -/
theorem nsProjectiveKernelAll_of_nonscalarLoopTranspose
    (h : NSMixedNonscalarLoopTransposeAll.{v, w}) : NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_loopTranspose
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact (mixedLoopTranspose_iff_nonscalar F).mpr (h C F M)

end VOA.Huang.DLNBridge
