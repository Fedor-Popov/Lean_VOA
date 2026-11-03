import VOA.Huang.NSSMove4Powers
import VOA.Huang.NSSMove4Matrix
import VOA.Huang.NSSMove2Assembly

/-! # The inverse trace clause is discharged; exact remaining assumptions -/
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

/-- The original first conjunct, at every pair of positive block sizes. -/
def MixedInverseTraceFormula (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (n k : ℕ) (a b : F.Label),
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V n
        (k + 1) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)

/-- The remaining second conjunct; no change to the original closure or crossing. -/
def MixedForwardTraceFormula (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (n k : ℕ) (a b : F.Label),
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V k
        (-(n + 1)) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j
        (forwardChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)

/-- The full inverse trace clause holds without a modularity assumption. -/
theorem mixedInverseTraceFormula_holds (F : SphericalFusion C) :
    MixedInverseTraceFormula F := fun V n k a b =>
  inverseTwoBlockTrace F (mixedCenter (F.simple a) (F.simple b)) V n k

/-- The full trace target is equivalent to its forward clause. -/
theorem mixedTwoBlockTraceFormula_iff_forward (F : SphericalFusion C) :
    MixedTwoBlockTraceFormula F ↔ MixedForwardTraceFormula F := by
  constructor
  · exact fun h V n k a b => (h V n k a b).2
  · exact fun h V n k a b => ⟨mixedInverseTraceFormula_holds F V n k a b, h V n k a b⟩

/-- Conditional S move with the already proved inverse clause removed. -/
theorem mixedNonzeroSMove_of_forward_exchange (F : SphericalFusion C) (M : Modular F)
    (hf : MixedForwardTraceFormula F) (he : MixedMugerExchange F) :
    MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_diagrams F M ((mixedTwoBlockTraceFormula_iff_forward F).mpr hf) he

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- The still unproved forward trace and exchange, uniformly over modular categories. -/
def NSMixedForwardExchangeAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (_M : Modular F),
      MixedForwardTraceFormula F ∧ MixedMugerExchange F

/-- Conditional kernel assembly. The two unresolved categorical inputs are explicit. -/
theorem nsProjectiveKernelAll_of_forward_exchange (h : NSMixedForwardExchangeAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_nonzeroSMove
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_of_forward_exchange F M (h C F M).1 (h C F M).2

end VOA.Huang.DLNBridge
