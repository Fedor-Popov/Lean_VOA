import VOA.DeligneAudit.D4FusionRealizationTwoFiltrationRanks
import VOA.DeligneAudit.DeligneFusionD1TensorGGrDimension
import VOA.DeligneAudit.DeligneFusionD1TensorGGrRankCyclic

/-! Exact graded dimensions of the actual cyclic associated graded two-site model. -/
namespace VOA.DeligneAudit.D4Two
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.D1TensorG.Gr
noncomputable section

def gradedRank : ℕ → ℕ
  | 0 => 300
  | 1 => 378
  | 2 => 134
  | 3 => 28
  | 4 => 1
  | _ + 5 => 0

/-- The dimensions are derived from the genuine filtration's rank steps. -/
theorem source_graded_ranks (d : ℕ) :
    Module.finrank ℂ (cycDeg (grRep sourceRep sourceGenerator)
      (wg sourceRep sourceGenerator) d) = gradedRank d := by
  haveI : FiniteDimensional ℂ Source := Module.Finite.of_basis actualBasis
  cases d with
  | zero =>
      have h := piece_rank_step sourceRep sourceGenerator 0
      rw [Fbelow_zero] at h
      simp only [finrank_bot,Nat.add_zero] at h
      exact h.trans (source_Fbelow_ranks 0)
  | succ d =>
      have h := piece_rank_step sourceRep sourceGenerator (d+1)
      rw [source_Fbelow_ranks d,source_Fbelow_ranks (d+1)] at h
      generalize hr : Module.finrank ℂ (cycDeg (grRep sourceRep sourceGenerator)
        (wg sourceRep sourceGenerator) (d+1)) = r at h ⊢
      clear hr
      rcases d with _ | _ | _ | _ | d <;>
        simp only [prefixRank,gradedRank,Nat.reduceAdd] at h ⊢ <;> omega

/-- Restricting to the actual cyclic graded model preserves each graded piece. -/
theorem cyclic_graded_ranks (d : ℕ) :
    Module.finrank ℂ (cycDeg (cyclicRep sourceRep sourceGenerator)
      (cyclicGenerator sourceRep sourceGenerator) d) = gradedRank d :=
  (finrank_cycDeg_cyclicRep sourceRep sourceGenerator d).trans (source_graded_ranks d)

end
#print axioms source_graded_ranks
#print axioms cyclic_graded_ranks
end VOA.DeligneAudit.D4Two
