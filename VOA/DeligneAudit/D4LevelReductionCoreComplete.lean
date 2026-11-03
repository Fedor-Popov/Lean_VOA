import VOA.DeligneAudit.D4LevelReductionConvertedDescent

/-! The full universal core presentation and the remaining core rank estimate. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.UnivG

/-- The concrete universal evaluation satisfies all parabolic, Cartan, and converted relations. -/
theorem universalCoreRelations (a b c : ℕ) :
    CoreRelations (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) :=
  universalCoreRelations_of_bottomImage a b c (universalCoreEvaluation a b c)
    (universalCoreEvaluation_range a b c) (universalCoreEvaluation_cartan a b c)
    (universalCoreEvaluation_converted a b c)

/-- Every nonnegative bottom triple has the full cyclic two-Grassmannian core presentation. -/
theorem universalCorePresentation (a b c : ℕ) : UniversalCorePresentation a b c := by
  refine ⟨universalCoreEvaluation a b c, universalCoreEvaluation_one a b c,
    universalCoreEvaluation_range a b c, universalCoreEvaluation_cartan a b c,
    universalCoreEvaluation_converted a b c, ?_⟩
  rw [universalCoreEvaluation_one]
  exact universalCoreBottom_cyclic a b c

/-- The core rank estimate alone implies the level bound at every nonnegative triple. -/
theorem levelTruncationBound_of_truncatedCoreRank (a b c : ℕ)
    (hbound : TruncatedCoreRankBound a b c) :
    LevelTruncationBound (a + b + c) b (2 * a + b) :=
  levelTruncationBound_of_corePresentation a b c hbound (universalCorePresentation a b c)

/-- Every single-adjoint level follows from its core rank estimate alone. -/
theorem levelTruncationBound_singleAdjoint (b c : ℕ)
    (hbound : TruncatedCoreRankBound 1 b c) :
    LevelTruncationBound (1 + b + c) b ((b : ℤ) + 2) := by
  simpa only [Nat.cast_one, mul_one, add_comm] using
    levelTruncationBound_of_truncatedCoreRank 1 b c hbound

/-- All interior single-adjoint levels in the site and grade indices reduce to the core estimate. -/
theorem levelTruncationBound_singleAdjoint_interior (m κ : ℕ) (hκ : κ + 2 ≤ m)
    (hbound : TruncatedCoreRankBound 1 κ (m - κ - 1)) :
    LevelTruncationBound m κ ((κ : ℤ) + 2) := by
  have hm : 1 + κ + (m - κ - 1) = m := by omega
  simpa only [hm] using levelTruncationBound_singleAdjoint κ (m - κ - 1) hbound

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCorePresentation
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_truncatedCoreRank
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_singleAdjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_singleAdjoint_interior
