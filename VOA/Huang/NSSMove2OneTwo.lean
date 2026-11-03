import VOA.Huang.NSSMove2Assembly

/-! # The first open row as a degree-two trace calculation

The degree-one side is evaluated unconditionally. The remaining equation is
an explicit trace of the inverse degree-two rotation, not an assumed value.
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

/-- The `(1,2)` indicator itself has a direct, unconditional value. This does
not evaluate the S-transformed row `(2,-1)`. -/
theorem mixed_indicator_one_two_value (F : SphericalFusion C) (M : Modular F)
    (a i j : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) 1 2 =
      (M.twistScalar i / M.twistScalar j) ^ (-2 : ℤ) *
        (F.fusionMultiplicity i j (F.simple a) : ℂ) := by
  change generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j))
    (F.simple a) 0 2 = _
  rw [generalizedIndicatorInt_one_scalar F _ _
    (div_ne_zero (M.toRibbon.twistScalar_ne_zero i) (M.toRibbon.twistScalar_ne_zero j))
    (mixedTwistIdentity_holds F M i j)]
  rw [F.finrank_hom_symm]
  rfl

/-- The remaining degree-two trace test. It is equivalent to the S move at
`(1,2)` for any supplied modular lift. It is not proved here. -/
def MixedOneTwoTraceIdentity (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ a i j : F.Label,
    (M.twistScalar i / M.twistScalar j) ^ (-2 : ℤ) *
        (F.fusionMultiplicity i j (F.simple a) : ℂ) =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F i j q *
        LinearMap.trace ℂ
          ((mixedCenter (F.simple q.1) (F.simple q.2)).1 ⟶
            tensorPower (F.simple a) 2)
          (((generalizedRotation F.toPivotal
            (mixedCenter (F.simple q.1) (F.simple q.2)) (F.simple a) 1) ^ (-1 : ℤ)).toLinearMap)

open Classical in
/-- An exact, nonvacuous test of the first missing row, with its known side
fully evaluated. No assertion is made that this trace equation holds. -/
theorem mixedSMove_one_two_iff_trace (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    (∀ (a : F.Label) (z : F.Label × F.Label → ℂ),
      mixedRow F a 2 (-1) z = mixedRow F a 1 2 (mixedRepresentation ρ ModularGroup.S⁻¹ z)) ↔
      MixedOneTwoTraceIdentity F M := by
  constructor
  · intro h a i j
    have he := (mixedSMove_iff_factorized F M ρ hr a 1 2).mp (h a) i j
    rw [mixed_indicator_one_two_value F M] at he
    exact he
  · intro h a
    apply (mixedSMove_iff_factorized F M ρ hr a 1 2).mpr
    intro i j
    rw [mixed_indicator_one_two_value F M]
    exact h a i j

/-- The diagram obligations specialize to the explicit degree-two test. -/
theorem mixedOneTwoTraceIdentity_of_diagrams (F : SphericalFusion C) (M : Modular F)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F) :
    MixedOneTwoTraceIdentity F M := by
  intro a i j
  have he := mixedSameSignFourier_of_diagrams F htrace hex (F.simple a) 1 2
    (by norm_num) i j
  rw [mixed_indicator_one_two_value F M] at he
  exact he

end VOA.Huang.NSCongruence
