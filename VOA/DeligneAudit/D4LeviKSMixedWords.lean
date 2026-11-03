import VOA.DeligneAudit.D4LeviKSRzPresentation

/-! Finite word expansion for the mixed XZG and YZG contractions. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion

noncomputable def mixedTopWords (k s : ℕ) (bases rs : List ℕ) :
    List (List (Fin 6 × ℕ) × List ℕ) :=
  (Finset.antidiagonal s).toList.flatMap fun q =>
    (topWords k q.1 bases).flatMap fun l =>
      (modeAllocations rs q.2).map fun ts => (l, ts)

theorem mixedTopWords_mem (k s : ℕ) (bases rs : List ℕ)
    (p : List (Fin 6 × ℕ) × List ℕ) (hp : p ∈ mixedTopWords k s bases rs) :
    ∃ q ∈ (Finset.antidiagonal s).toList,
      p.1 ∈ topWords k q.1 bases ∧ p.2 ∈ modeAllocations rs q.2 := by
  simp only [mixedTopWords, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨q, hq, l, hl, ts, hts, rfl⟩ := hp
  exact ⟨q, hq, hl, hts⟩

/-- The mixed contraction has finitely many top words and transported-mode
    allocations. This retains all positional multiplicities. -/
theorem mixedTop_eq_allocated_words
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (a b t : ℕ → Module.End ℂ V)
    (k s : ℕ) (bases rs : List ℕ) :
    mixedTop a b k s bases (rs.map (transportCurrent t)).prod =
      ((mixedTopWords k s bases rs).map fun p =>
        topWordOp a b p.1 * (p.2.map t).prod).sum := by
  rw [mixedTop_eq_shiftedWordCoeff]
  simp only [mixedTopWords, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def]
  conv_lhs =>
    rw [← (Finset.antidiagonal s).toList_toFinset,
      List.sum_toFinset _ (Finset.nodup_toList _)]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [← topSum_eq_shiftedWordCoeff]
  rw [topSum_eq_topWords, shiftedWordCoeff_eq_allocations]
  simp only [List.sum_map_mul_right, List.sum_map_mul_left]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixedTop_eq_allocated_words
#print axioms VOA.DeligneAudit.D4Levi.mixedTopWords_mem
