import VOA.DeligneAudit.D4LevelReductionAdjointCount
import VOA.DeligneAudit.D4LevelReductionAdjointTransfer

/-!
The exact remaining rank inequality on the adjoint edge and its overfull vanishing case.
The multiplicity bound and the mixed cyclic quotient bound are proved separately.
The finite filtration assembling those cyclic bounds into the edge bound remains unproved.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- At a supported edge, the level bound is precisely the binomial mixed rank estimate. -/
theorem levelTruncationBound_adjoint_edge_iff (a b : ℕ) :
    LevelTruncationBound (a + b) b (2 * (a : ℤ) + b) ↔
      Module.finrank ℂ (UniversalLevelPiece (a + b) b (2 * (a : ℤ) + b)) ≤
        (a + b).choose a * 15 ^ a * 6 ^ b := by
  rw [LevelTruncationBound, levelTarget_adjoint_edge]

/-- The overfull adjoint edge satisfies the level bound because its piece is zero. -/
theorem levelTruncationBound_adjoint_edge_overfull (m a : ℕ) (ha : m < a) :
    LevelTruncationBound m ((m : ℤ) - a) ((m : ℤ) + a) := by
  have hzero := adjointEdge_eq_bot_of_overfull (demazureCurrent m)
    (demazureGenerator m) m a ha (univG_sat D4sector.f (ravFam D4sector m 0))
  have hnext := adjointEdge_next_eq_bot (demazureCurrent m) (demazureGenerator m) m a
  change Module.finrank ℂ (UniversalLevelPiece m ((m : ℤ) - a) ((m : ℤ) + a)) ≤ _
  rw [truncatedLevel_finrank_zero_of_eq_next _ _ m _ _ (hzero.trans hnext.symm)]
  exact Nat.zero_le _

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_adjoint_edge_iff
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_adjoint_edge_overfull
