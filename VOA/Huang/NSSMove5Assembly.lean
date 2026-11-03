import VOA.Huang.NSSMove5Trace
import VOA.Huang.NSSMove5Matrix

/-! # S move and kernel assembly with only the local exchange remaining -/
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

/-- The local exchange suffices; both trace clauses are proved. -/
theorem mixedNonzeroSMove_of_mugerExchange (F : SphericalFusion C) (M : Modular F)
    (he : MixedMugerExchange F) : MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_forward_exchange F M (mixedForwardTraceFormula_holds F) he

/-- The full multiplicity matrix identities also suffice, with no trace premise. -/
theorem mixedNonzeroSMove_of_mugerMatrixElements (F : SphericalFusion C) (M : Modular F)
    (he : MixedMugerMatrixElements F) : MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_mugerExchange F M ((mixedMugerExchange_iff_matrixElements F).mpr he)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- The sole remaining local input to this assembly, quantified over modular categories.
This definition is an explicit unproved premise, not an additional axiom. -/
def NSMixedMugerExchangeAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (_M : Modular F), MixedMugerExchange F

/-- The `NSSMove4` combined input is equivalent to the exchange alone. -/
theorem nsMixedForwardExchangeAll_iff_mugerExchangeAll :
    NSMixedForwardExchangeAll.{v, w} ↔ NSMixedMugerExchangeAll.{v, w} := by
  constructor
  · intro h C _ _ _ _ _ _ _ _ _ _ F M
    exact (h C F M).2
  · intro h C _ _ _ _ _ _ _ _ _ _ F M
    exact ⟨mixedForwardTraceFormula_holds F, h C F M⟩

/-- Conditional kernel theorem with the forward trace assumption discharged. -/
theorem nsProjectiveKernelAll_of_mugerExchange (h : NSMixedMugerExchangeAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_nonzeroSMove
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_of_mugerExchange F M (h C F M)

end VOA.Huang.DLNBridge
