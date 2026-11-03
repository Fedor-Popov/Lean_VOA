import VOA.DeligneAudit.D4LevelReductionUniversal
import VOA.DeligneAudit.D4LevelReductionCount

/-!
The remaining per-level D4 truncation bounds imply the universal `28^m` bound.
The hypothesis concerns the explicit coinvariants of the universal parent module's
letter-count and Levi-level filtration. No per-level bound is asserted here.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.DeligneSector.D4

/-- The required upper bound for one universal Levi-level coinvariant. -/
def LevelTruncationBound (m : ℕ) (κ p : ℤ) : Prop :=
  Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ levelTarget m κ p

/-- Bounds on all level coinvariants imply the all-m universal truncated D4 rank bound. -/
theorem univTruncatedRank_of_levelBounds
    (h : ∀ m κ p, LevelTruncationBound m κ p) : UnivG.UnivTruncatedRank := by
  intro m hm
  obtain ⟨hfinite, hrank⟩ := truncatedModule_rank_le_levelSum m hm
  refine ⟨hfinite, hrank.trans ?_⟩
  exact (Finset.sum_le_sum (fun i _ => h m i.1 i.2)).trans
    (levelTarget_sum_le m (levelIndices m))

/-- The same level bounds supply the total fusion-dimension input to the D4 capstone. -/
theorem fusionTotalDim_of_levelBounds
    (h : ∀ m κ p, LevelTruncationBound m κ p) : FiniteG.FusionTotalDimG D4sector :=
  UnivG.fusionTotalDimG_of_univTruncatedRank (univTruncatedRank_of_levelBounds h)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.univTruncatedRank_of_levelBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.fusionTotalDim_of_levelBounds
