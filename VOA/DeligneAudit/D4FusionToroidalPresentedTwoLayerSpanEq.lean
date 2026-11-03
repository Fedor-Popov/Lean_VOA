import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerSpan

/-! Exact spanning decomposition of the first positive u-degree filtration term. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem twoM_word_mem_N1 (s : ℕ) : ∀ (l : List (TLtr 28)),
    wordOpT (ρPTE 2) l ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2)) ∈ twoN 1
  | [] => by
      exact twoN_word 1 [(D4sector.c₀, 1, s)] (by simp [twoUDeg])
  | x :: l => by
      change (ρPTE 2).op x.1 x.2.1 x.2.2
        (wordOpT (ρPTE 2) l ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2))) ∈ twoN 1
      exact twoN_op 1 x.1 x.2.1 x.2.2 (twoM_word_mem_N1 s l)

theorem twoM_le_N1 (s : ℕ) : twoM s ≤ twoN 1 := by
  rw [twoM, Submodule.span_le]
  rintro v ⟨l, _, rfl⟩
  exact twoM_word_mem_N1 s l

theorem twoPositiveSpan_le_N1 : twoPositiveSpan ≤ twoN 1 := by
  rw [twoPositiveSpan, sup_le_iff]
  exact ⟨twoM_le_N1 0, twoM_le_N1 1⟩

theorem twoN_one_eq_two_generators :
    twoN 1 = twoN 2 ⊔ twoPositiveSpan := by
  apply le_antisymm
  · exact twoN_one_le_two_generators
  · exact sup_le (twoN_mono (by omega)) twoPositiveSpan_le_N1

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoM_word_mem_N1
#print axioms VOA.DeligneAudit.Toroidal.twoM_le_N1
#print axioms VOA.DeligneAudit.Toroidal.twoPositiveSpan_le_N1
#print axioms VOA.DeligneAudit.Toroidal.twoN_one_eq_two_generators
