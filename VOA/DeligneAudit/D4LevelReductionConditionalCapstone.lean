import VOA.DeligneAudit.D4LevelReductionGradeSymmetry
import VOA.DeligneAudit.D4CharRound109Audit
import VOA.DeligneAudit.DeligneSeries

/-! The D4 capstone conditional on interior core bounds and transfer of negative grades. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- Interior core estimates and negative-grade transfer give the full fusion dimension bound. -/
theorem fusionTotalDim_of_coreBounds_and_negativeGradeTransfer
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c)
    (htransfer : NegativeGradeRankTransfer) :
    FiniteG.FusionTotalDimG DeligneSector.D4.D4sector :=
  fusionTotalDim_of_levelBounds
    (levelTruncationBound_of_coreBounds_and_negativeGradeTransfer h htransfer)

/-- The existing character realization closes the capstone once both rank inputs are supplied. -/
theorem d4_classicallyFree_of_coreBounds_and_negativeGradeTransfer
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c)
    (htransfer : NegativeGradeRankTransfer) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4
      D4Lie.W4 D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1
          ⟨D4Lie.explicitPresentation4.gen i,
            D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  DeligneSeries.D4_classicallyFree_final
    (fusionTotalDim_of_coreBounds_and_negativeGradeTransfer h htransfer)
    D4Char.d4_demazureRealization

end VOA.DeligneAudit.D4LevelReduction

#print axioms
  VOA.DeligneAudit.D4LevelReduction.fusionTotalDim_of_coreBounds_and_negativeGradeTransfer
#print axioms
  VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_coreBounds_and_negativeGradeTransfer
