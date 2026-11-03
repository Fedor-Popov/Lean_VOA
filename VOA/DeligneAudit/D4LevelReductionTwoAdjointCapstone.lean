import VOA.DeligneAudit.D4LevelReductionSingleAdjointBound
import VOA.DeligneAudit.D4LevelReductionCoreCapstone

/-! The D4 classical-freeness capstone with only the higher adjoint core bounds remaining. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- The proved single-adjoint family reduces the D4 hypothesis to at least two adjoint sites. -/
theorem d4_classicallyFree_of_twoAdjointCoreBounds
    (h : ∀ a b c : ℕ, 2 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4
      D4Lie.W4 D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1
          ⟨D4Lie.explicitPresentation4.gen i,
            D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal := by
  apply d4_classicallyFree_of_coreBounds
  intro a b c ha hc
  by_cases hone : a = 1
  · subst a
    exact truncatedCoreRankBound_singleAdjoint b c hc
  · exact h a b c (by omega) hc

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_twoAdjointCoreBounds
