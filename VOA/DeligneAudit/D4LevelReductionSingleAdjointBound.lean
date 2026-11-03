import VOA.DeligneAudit.D4LevelReductionSingleAdjointCount

/-! The all-parameter single-adjoint core bound and its universal D4 level consequence. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

/-- The subset and non-subset estimates sum along the simultaneous coefficient flag. -/
theorem coreSingleAdjoint_finrank_le (b c : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing 1 b c →ₗ[ℂ] V)
    (h : CoreRelations Q 1 b c π) (hcyclic : cycSubG Q (π 1) = ⊤)
    (hhigh : ∀ e r, 1 + b + c ≤ r → Q.op e r = 0) :
    Module.finrank ℂ V ≤ (1 + b + c).choose (b + 1) *
      ((b + 1) * 15 * 6 ^ b + c * 6 ^ (b + 2)) := by
  classical
  let F := coreCommonRootCellFlag 1 b c
  let costs := (coreCellCatalog 1 b c).map (singleAdjointCellCost b)
  have hb := coreCellFiltration_finrank_le 1 b c Q π F hcyclic
    (fun i => costs.getD i 0) (by
      intro i hi
      dsimp only [costs]
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
      unfold singleAdjointCellCost
      split_ifs with hsubset
      · exact coreCell_singleAdjoint_subset_rank b c Q π h hhigh i hi hsubset
      · exact coreCell_singleAdjoint_pair_rank b c Q π h F i hi)
  have hs : (∑ i ∈ Finset.range (coreCellCatalog 1 b c).length, costs.getD i 0) =
      costs.sum := by
    simpa only [costs, List.length_map, List.map_id] using SL4T.list_sum_getD costs id
  rw [hs, singleAdjoint_cellCost_sum] at hb
  exact hb

/-- Every single-adjoint core with a positive central count satisfies the target rank bound. -/
theorem truncatedCoreRankBound_singleAdjoint (b c : ℕ) (hc : 1 ≤ c) :
    TruncatedCoreRankBound 1 b c := by
  intro V _ _ _ Q π h hcyclic hhigh
  have hb := coreSingleAdjoint_finrank_le b c Q π h hcyclic hhigh
  rw [← levelTarget_singleAdjoint b c hc] at hb
  simpa only [Nat.cast_one, mul_one, add_comm] using hb

/-- All universal D4 levels with one adjoint site and positive central count satisfy their bound. -/
theorem levelTruncationBound_singleAdjoint_positiveCenter (b c : ℕ) (hc : 1 ≤ c) :
    LevelTruncationBound (1 + b + c) b ((b : ℤ) + 2) :=
  levelTruncationBound_singleAdjoint b c (truncatedCoreRankBound_singleAdjoint b c hc)

/-- Every interior single-adjoint level satisfies its bound in the site and grade indices. -/
theorem singleAdjoint_interior_levelTruncationBound (m κ : ℕ) (hκ : κ + 2 ≤ m) :
    LevelTruncationBound m κ ((κ : ℤ) + 2) :=
  levelTruncationBound_singleAdjoint_interior m κ hκ
    (truncatedCoreRankBound_singleAdjoint κ (m - κ - 1) (by omega))

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreSingleAdjoint_finrank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedCoreRankBound_singleAdjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_singleAdjoint_positiveCenter
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_interior_levelTruncationBound
