import VOA.DeligneAudit.D4LevelReductionCoreRank
import VOA.DeligneAudit.D4LevelReductionConditionalCapstone

/-! The D4 classical-freeness capstone from the interior truncated core bounds alone. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- Interior core bounds and the proved character realization imply D4 classical freeness. -/
theorem d4_classicallyFree_of_coreBounds
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4
      D4Lie.W4 D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1
          ⟨D4Lie.explicitPresentation4.gen i,
            D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  DeligneSeries.D4_classicallyFree_final (fusionTotalDim_of_coreBounds h)
    D4Char.d4_demazureRealization

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_coreBounds
