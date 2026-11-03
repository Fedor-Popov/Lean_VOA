import VOA.Huang.NSSMove6Fourier

/-! # Conditional assembly after the open sewing calculations

The local loop transposition is still an explicit premise. This module does
not declare an unconditional kernel theorem.
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

/-- The loop transposition suffices for the original nonzero S move. -/
theorem mixedNonzeroSMove_of_loopTranspose (F : SphericalFusion C) (M : Modular F)
    (h : MixedLoopTranspose F) : MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_mugerExchange F M (mixedMugerExchange_of_loopTranspose F M h)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- Explicit residual, universally quantified over modular categories. -/
def NSMixedLoopTransposeAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (_M : Modular F), MixedLoopTranspose F

/-- The universal residual is exactly equivalent to the previous local input. -/
theorem nsMixedMugerExchangeAll_iff_loopTransposeAll :
    NSMixedMugerExchangeAll.{v, w} ↔ NSMixedLoopTransposeAll.{v, w} := by
  constructor
  · intro h C _ _ _ _ _ _ _ _ _ _ F M
    exact (mixedMugerExchange_iff_loopTranspose F M).mp (h C F M)
  · intro h C _ _ _ _ _ _ _ _ _ _ F M
    exact mixedMugerExchange_of_loopTranspose F M (h C F M)

/-- Conditional kernel corollary; the loop transposition remains unproved. -/
theorem nsProjectiveKernelAll_of_loopTranspose (h : NSMixedLoopTransposeAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} :=
  nsProjectiveKernelAll_of_mugerExchange
    (nsMixedMugerExchangeAll_iff_loopTransposeAll.mpr h)

end VOA.Huang.DLNBridge
