import VOA.Huang.NSSMove2Diagrams

/-! # Conditional assembly from the explicit mixed diagrams

Both categorical inputs are explicit. Neither is established by this module.
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

/-- The signed convention, on a strictly negative first index. -/
theorem indicator_negative_degree (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) (l : ℤ) :
    generalizedIndicatorAll F A V (-((n : ℤ) + 1)) l =
      generalizedIndicatorInt F.toPivotal A Vᘁ n (-l) := by
  have hn : ¬ (0 : ℤ) < -((n : ℤ) + 1) := by omega
  have hn0 : -((n : ℤ) + 1) ≠ 0 := by omega
  rw [generalizedIndicatorAll, if_neg hn, if_neg hn0]
  congr 1

/-- Both signs follow from positive powers, using the actual negative-index
definition. No extra charge-symmetry assertion is assumed. -/
theorem mixedSameSignFourier_of_diagrams (F : SphericalFusion C)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F)
    (V : C) (m l : ℤ) (hp : 0 < m * l) (a b : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple a) (F.simple b)) V m l =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
        generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2)) V l (-m) := by
  rcases mul_pos_iff.mp hp with ⟨hm, hl⟩ | ⟨hm, hl⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨m.toNat - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, l = (k : ℤ) + 1 := ⟨l.toNat - 1, by omega⟩
    simpa only [generalizedIndicatorAll_positive] using
      mixedPositiveFourier_of_diagrams F htrace hex V n k a b
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m).toNat - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, l = -((k : ℤ) + 1) := ⟨(-l).toNat - 1, by omega⟩
    simpa only [indicator_negative_degree, neg_neg] using
      mixedPositiveFourier_of_diagrams F htrace hex Vᘁ n k a b

/-- The precise finite-sum residual, from the explicit diagrams. -/
theorem mixedSameSignOffDiagonalFourier_of_diagrams (F : SphericalFusion C)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F) :
    MixedSameSignOffDiagonalFourier F := by
  intro V m l hp _ _ a b
  exact mixedSameSignFourier_of_diagrams F htrace hex (F.simple V) m l hp a b

/-- Conditional nonzero S move. The two diagram hypotheses remain visible. -/
theorem mixedNonzeroSMove_of_diagrams (F : SphericalFusion C) (M : Modular F)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F) :
    MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_factorized F M
    (mixedSameSignOffDiagonalFourier_of_diagrams F htrace hex)

open Classical in
/-- The smallest open test row follows from these same two diagram obligations. -/
theorem mixedSMove_one_two_of_diagrams (F : SphericalFusion C) (M : Modular F)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label) (z : F.Label × F.Label → ℂ) :
    mixedRow F a 2 (-1) z = mixedRow F a 1 2 (mixedRepresentation ρ ModularGroup.S⁻¹ z) := by
  apply (mixedSMove_iff_factorized F M ρ hr a 1 2).mpr
    (fun i j => mixedSameSignFourier_of_diagrams F htrace hex (F.simple a) 1 2
      (by norm_num) i j)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- The two diagram obligations, uniformly over modular categories. -/
def NSMixedDiagramInputsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (_M : Modular F),
      MixedTwoBlockTraceFormula F ∧ MixedMugerExchange F

/-- Conditional kernel theorem. This is deliberately not the unconditional
`nsProjectiveKernelAll_holds`. -/
theorem nsProjectiveKernelAll_of_mixedDiagrams (h : NSMixedDiagramInputsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_nonzeroSMove
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_of_diagrams F M (h C F M).1 (h C F M).2

end VOA.Huang.DLNBridge
