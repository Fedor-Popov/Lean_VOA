import VOA.Huang.NSSMoveUnitRows

/-! # The remaining positive-product, off-diagonal S identity

The residual below is an explicit restriction of the original target. The
implications proved here do not establish it, or the unconditional kernel theorem.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The S step for primitive, unequal coordinates of positive product.
For example `(1,2)` is included; the proved unit diagonal is excluded. -/
def MixedSameSignOffDiagonalSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ), 0 < m * l → m ≠ l → IsCoprime m l →
      ∀ z : F.Label × F.Label → ℂ,
        mixedRow F a l (-m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- Fill the only primitive same-sign diagonal rows with the unconditional result. -/
theorem mixedSameSignSMove_of_offDiagonal (F : SphericalFusion C) (M : Modular F)
    (h : MixedSameSignOffDiagonalSMove F M) : MixedSameSignSMove F M := by
  intro ρ hr a m l hpos hcop z
  by_cases he : m = l
  · subst l
    have hu : IsUnit m := isCoprime_self.mp hcop
    exact mixedUnitSMove_holds F M ρ hr a m m hu hu z
  · exact h ρ hr a m l hpos he hcop z

/-- The exact remaining restriction implies the original nonzero-row target. -/
theorem mixedNonzeroSMove_of_sameSignOffDiagonal (F : SphericalFusion C) (M : Modular F)
    (h : MixedSameSignOffDiagonalSMove F M) : MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_sameSign F M (mixedSameSignSMove_of_offDiagonal F M h)

/-- This is an equivalent residual, not a silently weakened replacement. -/
theorem mixedNonzeroSMove_iff_sameSignOffDiagonal (F : SphericalFusion C) (M : Modular F) :
    MixedNonzeroSMove F M ↔ MixedSameSignOffDiagonalSMove F M := by
  constructor
  · intro h ρ hr a m l hp _ hcop z
    exact (mixedNonzeroSMove_iff_sameSign F M).mp h ρ hr a m l hp hcop z
  · exact mixedNonzeroSMove_of_sameSignOffDiagonal F M

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- The positive-product off-diagonal residual, uniformly over modular categories. -/
def NSMixedSameSignOffDiagonalSMoveAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F), MixedSameSignOffDiagonalSMove F M

/-- Conditional assembly. The categorical positive-product S identity remains
an explicit argument; this is not `nsProjectiveKernelAll_holds`. -/
theorem nsProjectiveKernelAll_of_sameSignOffDiagonal
    (h : NSMixedSameSignOffDiagonalSMoveAll.{v, w}) : NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_nonzeroSMove
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_of_sameSignOffDiagonal F M (h C F M)

end VOA.Huang.DLNBridge
