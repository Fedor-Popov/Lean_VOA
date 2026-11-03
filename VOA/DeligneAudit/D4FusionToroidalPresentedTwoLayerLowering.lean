import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerGenerator
import VOA.DeligneAudit.D4FusionContactTruncationTable

/-! The Cartan bracket eliminates the remaining mode-one fusion tails. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_generator_cartan_mode_one (c : Fin 28) (hc : D4sector.cartan c) :
    (ρPTE 2).op c 0 1 (pTE 2) = 0 := by
  have ht : [(c, 1)] ∈ (ravFam D4sector 2 0).tails :=
    Or.inr (Or.inl ⟨c, 1, hc, by omega, rfl⟩)
  simpa [symbolLetters, wordOpT] using two_syntax_tail [(c, 1)] ht

private theorem two_negative_fusion :
    ∀ i : Fin 12, D4sector.fusion (negativeIndex i) := by
  intro i
  change 16 ≤ (negativeIndex i).val
  fin_cases i <;> decide

theorem two_generator_negative_one_one (i : Fin 12)
    (hne : negativeIndex i ≠ D4sector.c₀) :
    (ρPTE 2).op (negativeIndex i) 1 1 (pTE 2) = 0 := by
  have hq := two_generator_fusion_one_zero (negativeIndex i)
    (two_negative_fusion i) hne
  have hh := two_generator_cartan_mode_one (negativeCartan i)
    (show D4sector.cartan (negativeCartan i) from negativeCartan_lt_four i)
  have hcomm := (ρPTE 2).comm (negativeCartan i) (negativeIndex i)
    0 1 1 0 (pTE 2)
  have hsum : (∑ c : Fin 28,
      D4sector.f (negativeCartan i) (negativeIndex i) c •
        (ρPTE 2).op c 1 1 (pTE 2)) = 0 := by
    simpa [hq, hh] using hcomm.symm
  have htable : (∑ c : Fin 28,
      D4sector.f (negativeCartan i) (negativeIndex i) c •
        (ρPTE 2).op c 1 1 (pTE 2)) =
      (negativeWeight i : ℂ) • (ρPTE 2).op (negativeIndex i) 1 1 (pTE 2) := by
    change (∑ c : Fin 28, contactF (negativeCartan i) (negativeIndex i) c •
      (ρPTE 2).op c 1 1 (pTE 2)) = _
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [htable] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left (negativeWeight_ne_zero i)

theorem two_generator_fusion_one_one (c : Fin 28) (hc : D4sector.fusion c)
    (hne : c ≠ D4sector.c₀) :
    (ρPTE 2).op c 1 1 (pTE 2) = 0 := by
  obtain ⟨i, rfl⟩ := negativeIndex_covers c (show 16 ≤ c.val from hc)
  exact two_generator_negative_one_one i hne

theorem two_generator_one_other (c : Fin 28) (hne : c ≠ D4sector.c₀)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 1 s (pTE 2) = 0 := by
  by_cases h4 : c.val < 4
  · exact two_generator_cartan_one c (show D4sector.cartan c from h4) s hs
  by_cases h16 : c.val < 16
  · exact two_generator_raising_one c
      (show D4sector.raising c from ⟨by omega, h16⟩) s hs
  have hf : D4sector.fusion c := by
    change 16 ≤ c.val
    omega
  interval_cases s
  · exact two_generator_fusion_one_zero c hf hne
  · exact two_generator_fusion_one_one c hf hne

theorem two_generator_one_other_all (c : Fin 28) (hne : c ≠ D4sector.c₀)
    (s : ℕ) :
    (ρPTE 2).op c 1 s (pTE 2) = 0 := by
  by_cases hs : s ≤ 1
  · exact two_generator_one_other c hne s hs
  · have hs' : 2 ≤ s := by omega
    rw [(ρPTE 2).high_zero c 1 s hs']
    rfl

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_generator_cartan_mode_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_negative_one_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_fusion_one_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_one_other
#print axioms VOA.DeligneAudit.Toroidal.two_generator_one_other_all
