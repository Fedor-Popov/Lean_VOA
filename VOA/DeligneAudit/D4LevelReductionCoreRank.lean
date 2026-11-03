import VOA.DeligneAudit.D4LevelReductionGradeReflection
import VOA.DeligneAudit.D4LevelReductionGradeCount

/-! Interior core bounds imply the full truncated D4 rank bound by intrinsic grade symmetry. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- The symmetric grade interval spans the entire truncated module. -/
theorem truncatedGradeSpace_interval_spans (m : ℕ) (hm : 1 ≤ m) :
    (⨆ κ ∈ Finset.Icc (-(m : ℤ)) m, truncatedGradeSpace m κ) = ⊤ := by
  apply top_unique
  rw [← truncatedGradeSpace_spans m hm]
  apply iSup_le
  intro κ
  by_cases hκ : κ ∈ Finset.Icc (-(m : ℤ)) m
  · exact le_iSup_of_le κ (le_iSup_of_le hκ le_rfl)
  · rw [truncatedGradeSpace_eq_bot_of_outside_interval m hm κ (by
      simp only [Finset.mem_Icc] at hκ
      omega)]
    exact bot_le

/-- The finite interval of intrinsic grades is an internal direct sum decomposition. -/
theorem truncatedGradeSpace_interval_isInternal (m : ℕ) (hm : 1 ≤ m) :
    DirectSum.IsInternal
      (fun κ : {κ : ℤ // κ ∈ Finset.Icc (-(m : ℤ)) m} => truncatedGradeSpace m κ) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (truncatedGradeSpace_independent m).comp Subtype.val_injective
  · simpa only [iSup_subtype] using truncatedGradeSpace_interval_spans m hm

/-- The dimension of the truncated module is the sum of its intrinsic grade dimensions. -/
theorem truncatedModule_finrank_eq_gradeSum (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank ℂ (TruncatedModule m) =
      ∑ κ ∈ Finset.Icc (-(m : ℤ)) m, Module.finrank ℂ (truncatedGradeSpace m κ) := by
  haveI := (truncatedModule_rank_le_leviCoinvariants m hm).1
  have hsum (s : Finset ℤ) :
      Module.finrank ℂ ↥(⨆ κ ∈ s, truncatedGradeSpace m κ) =
        ∑ κ ∈ s, Module.finrank ℂ (truncatedGradeSpace m κ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert κ s hκ ih =>
      have hd : Disjoint (truncatedGradeSpace m κ)
          (⨆ ν ∈ s, truncatedGradeSpace m ν) := by
        apply (truncatedGradeSpace_independent m κ).mono_right
        apply iSup_le
        intro ν
        apply iSup_le
        intro hν
        exact le_iSup_of_le ν (le_iSup_of_le (by intro he; exact hκ (he ▸ hν)) le_rfl)
      have he := Submodule.finrank_sup_add_finrank_inf_eq (truncatedGradeSpace m κ)
        (⨆ ν ∈ s, truncatedGradeSpace m ν)
      rw [hd.eq_bot, finrank_bot, add_zero, ih] at he
      rw [Finset.iSup_insert, Finset.sum_insert hκ]
      exact he
  have he := hsum (Finset.Icc (-(m : ℤ)) m)
  rwa [truncatedGradeSpace_interval_spans m hm, finrank_top] at he

/-- Grade symmetry expresses the total rank using only nonnegative grades. -/
theorem truncatedModule_finrank_eq_nonnegative_gradeSum (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank ℂ (TruncatedModule m) =
      (∑ κ ∈ Finset.Icc (0 : ℤ) m, Module.finrank ℂ (truncatedGradeSpace m κ)) +
        ∑ κ ∈ Finset.Icc (1 : ℤ) m, Module.finrank ℂ (truncatedGradeSpace m κ) := by
  rw [truncatedModule_finrank_eq_gradeSum m hm]
  exact symmetricGrade_sum m _ (truncatedGradeSpace_finrank_neg m hm)

/-- Interior core bounds control every intrinsic nonnegative grade. -/
theorem truncatedGradeSpace_rank_le_of_coreBounds
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c)
    (m : ℕ) (hm : 1 ≤ m) (κ : ℤ) (hκ : 0 ≤ κ) :
    Module.finrank ℂ (truncatedGradeSpace m κ) ≤ gradeTarget m κ := by
  apply (truncatedGradeSpace_rank_le_levelSum m hm κ).trans
  apply le_trans _ (levelTarget_grade_sum_le m κ)
  apply Finset.sum_le_sum
  intro i hi
  have hiκ := (Finset.mem_filter.mp hi).2
  exact levelTruncationBound_of_nonnegative_coreBounds h m i.1 i.2 (by omega)

/-- The all-m universal truncated rank bound requires only the interior core bounds. -/
theorem univTruncatedRank_of_coreBounds
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c) :
    UnivG.UnivTruncatedRank := by
  intro m hm
  refine ⟨(truncatedModule_rank_le_leviCoinvariants m hm).1, ?_⟩
  change Module.finrank ℂ (TruncatedModule m) ≤ 28 ^ m
  rw [truncatedModule_finrank_eq_nonnegative_gradeSum m hm,
    ← gradeTarget_nonnegative_sum m]
  apply Nat.add_le_add <;> apply Finset.sum_le_sum <;> intro κ hκ
  · exact truncatedGradeSpace_rank_le_of_coreBounds h m hm κ (Finset.mem_Icc.mp hκ).1
  · exact truncatedGradeSpace_rank_le_of_coreBounds h m hm κ (by
      have hk := (Finset.mem_Icc.mp hκ).1
      omega)

/-- The fusion dimension input follows from interior core bounds alone. -/
theorem fusionTotalDim_of_coreBounds
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c) :
    FiniteG.FusionTotalDimG DeligneSector.D4.D4sector :=
  UnivG.fusionTotalDimG_of_univTruncatedRank (univTruncatedRank_of_coreBounds h)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_interval_isInternal
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedModule_finrank_eq_gradeSum
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedModule_finrank_eq_nonnegative_gradeSum
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_rank_le_of_coreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.univTruncatedRank_of_coreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.fusionTotalDim_of_coreBounds
