import VOA.DeligneAudit.D4FusionRealizationTwoFlags
import VOA.DeligneAudit.D4FusionRealizationTwoLevelCounts

/-! Exact ranks of the genuine two-site source filtration in every degree. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.D1TensorG.Gr
noncomputable section

def prefixRank : ℕ → ℕ
  | 0 => 300
  | 1 => 678
  | 2 => 812
  | 3 => 840
  | _ + 4 => 841

theorem source_Fbelow_eq_top (d : ℕ) (hd : 4 ≤ d) :
    Fbelow sourceRep sourceGenerator (d+1) = ⊤ := by
  rw [source_Fbelow_eq_flag]
  exact flag_top actualBasis wordLevel 4 d (fun i => wordNode_level i i.isLt) hd

/-- These ranks follow from the actual basis flag and checked finite labels. -/
theorem source_Fbelow_ranks (d : ℕ) :
    Module.finrank ℂ (Fbelow sourceRep sourceGenerator (d+1)) = prefixRank d := by
  rcases d with _ | _ | _ | _ | _ | d
  · rw [source_Fbelow_finrank]
    exact word_level_count_0
  · rw [source_Fbelow_finrank]
    exact word_level_count_1
  · rw [source_Fbelow_finrank]
    exact word_level_count_2
  · rw [source_Fbelow_finrank]
    exact word_level_count_3
  · rw [source_Fbelow_finrank]
    exact word_level_count_4
  · rw [source_Fbelow_eq_top _ (by omega),finrank_top]
    exact source_dimension

end
#print axioms source_Fbelow_ranks
end VOA.DeligneAudit.D4Two
