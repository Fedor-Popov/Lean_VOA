import VOA.DeligneAudit.D4LevelReductionRaisingSupport

/-!
The remaining conversion window and cyclicity required by the universal core presentation.
The Grassmannian map, its full bottom Cartan image, its Cartan action, and raising lengths
beyond the central count are proved. The nonempty conversion window and cyclicity of the
whole level piece remain explicit hypotheses in the final reductions below.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.UnivG

/-- A positive-degree complete symmetric polynomial on an empty alphabet is zero. -/
theorem emptyAlphabet_complete_zero {R : Type*} [CommRing R] [Algebra ℂ R]
    (n : ℕ) (hn : 0 < n) : hsymm (Fin 0) R n = 0 := by
  have he : hsymm (Fin 0) ℂ n = 0 := by
    rw [rz_hsymm_eq_sum_vectors]
    apply Finset.sum_eq_zero
    intro u hu
    have ht := u.property
    simp only [Fin.sum_univ_zero] at ht
    omega
  rw [← map_hsymm (σ := Fin 0) (R := ℂ) (S := R) n (algebraMap ℂ R), he, map_zero]

/-- With no raising letters, each converted generator already vanishes in the core base ring. -/
theorem coreRaisingComplete_zeroLength (a b c n : ℕ) (hn : c < n) :
    coreRaisingComplete a b c 0 n = 0 := by
  unfold coreRaisingComplete
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i = n
  · subst i
    have hz : leftH (a + b + c) (a + b) a n = 0 := by
      unfold leftH
      rw [hClass_eq_zero _ _ n (by omega), map_zero]
    rw [hz, map_zero, zero_mul]
  · have hpos : 0 < n - i := by have := Finset.mem_range.mp hi; omega
    rw [emptyAlphabet_complete_zero _ hpos, mul_zero]

/-- The converted ideal at raising length zero is the zero ideal. -/
theorem coreRaisingIdeal_zeroLength (a b c : ℕ) : coreRaisingIdeal a b c 0 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [coreRaisingIdeal, Ideal.span_le]
  rintro P ⟨n, hn, rfl⟩
  rw [coreRaisingComplete_zeroLength a b c n (by omega)]
  exact Ideal.zero_mem _

/-- Only positive raising lengths up to the central count remain in the converted condition. -/
theorem universalCoreEvaluation_converted_of_window (a b c : ℕ)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j)) :
    CoreConvertedRelations (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) := by
  intro j
  by_cases hj : j = 0
  · subst j
    rw [coreRaisingIdeal_zeroLength]
    exact bot_le
  · by_cases hc : j ≤ c
    · exact hwindow j (by omega) hc
    · rw [universalCoreEvaluation_raising_overfull a b c j (by omega), LinearMap.ker_zero]
      exact le_top

/-- The nonempty converted window is the sole remaining relation assumption for this evaluation. -/
theorem universalCoreEvaluation_relations_of_window (a b c : ℕ)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j)) :
    CoreRelations (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) :=
  universalCoreRelations_of_bottomImage a b c (universalCoreEvaluation a b c)
    (universalCoreEvaluation_range a b c) (universalCoreEvaluation_cartan a b c)
    (universalCoreEvaluation_converted_of_window a b c hwindow)

/-- The concrete Grassmannian map completes the presentation given converted relations and
cyclicity of the whole level piece. -/
theorem universalCorePresentation_of_raisingWindow_and_cyclic (a b c : ℕ)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j))
    (hcyclic : cycSubG (universalCoreCurrent a b c) (universalCoreBottom a b c) = ⊤) :
    UniversalCorePresentation a b c := by
  refine ⟨universalCoreEvaluation a b c, universalCoreEvaluation_one a b c,
    universalCoreEvaluation_range a b c, universalCoreEvaluation_cartan a b c,
    universalCoreEvaluation_converted_of_window a b c hwindow, ?_⟩
  rwa [universalCoreEvaluation_one]

/-- The core estimate gives the level bound once the conversion window and cyclicity are proved. -/
theorem levelTruncationBound_of_coreRank_raisingWindow_cyclic (a b c : ℕ)
    (hbound : TruncatedCoreRankBound a b c)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j))
    (hcyclic : cycSubG (universalCoreCurrent a b c) (universalCoreBottom a b c) = ⊤) :
    LevelTruncationBound (a + b + c) b (2 * a + b) :=
  levelTruncationBound_of_corePresentation a b c hbound
    (universalCorePresentation_of_raisingWindow_and_cyclic a b c hwindow hcyclic)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.emptyAlphabet_complete_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingComplete_zeroLength
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingIdeal_zeroLength
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_converted_of_window
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_relations_of_window
#print axioms
  VOA.DeligneAudit.D4LevelReduction.universalCorePresentation_of_raisingWindow_and_cyclic
#print axioms
  VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_coreRank_raisingWindow_cyclic
