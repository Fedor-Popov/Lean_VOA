import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerSyntax

/-! Generator relations for the first positive u-degree layer. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem two_generator_raising_one (c : Fin 28) (hc : D4sector.raising c)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 1 s (pTE 2) = 0 := by
  have ht : [(c, 2 + s)] ∈ (ravFam D4sector 2 0).tails :=
    Or.inl ⟨c, 2 + s, hc, rfl⟩
  have h := two_syntax_tail [(c, 2 + s)] ht
  interval_cases s <;> simpa [symbolLetters, wordOpT] using h

theorem two_generator_cartan_one (c : Fin 28) (hc : D4sector.cartan c)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 1 s (pTE 2) = 0 := by
  have ht : [(c, 2 + s)] ∈ (ravFam D4sector 2 0).tails :=
    Or.inr (Or.inl ⟨c, 2 + s, hc, by omega, rfl⟩)
  have h := two_syntax_tail [(c, 2 + s)] ht
  interval_cases s <;> simpa [symbolLetters, wordOpT] using h

theorem two_generator_cartanN_one (c : Fin 28) (hc : D4sector.cartanN c)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 1 s (pTE 2) = 0 := by
  have ht : [(c, 2 + s)] ∈ (ravFam D4sector 2 0).tails :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨c, 2 + s, hc, by omega, rfl⟩)))
  have h := two_syntax_tail [(c, 2 + s)] ht
  interval_cases s <;> simpa [symbolLetters, wordOpT] using h

theorem two_generator_fusion_one_zero (c : Fin 28) (hc : D4sector.fusion c)
    (hne : c ≠ D4sector.c₀) :
    (ρPTE 2).op c 1 0 (pTE 2) = 0 := by
  have ht : [(c, 2)] ∈ (ravFam D4sector 2 0).tails :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by
      change [(c, 2)] = [(c, if c = (27 : Fin 28) then 4 else 2)]
      change c ≠ (27 : Fin 28) at hne
      simp [hne]⟩)))
  have h := two_syntax_tail [(c, 2)] ht
  simpa [symbolLetters] using h

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_generator_raising_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_cartan_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_cartanN_one
#print axioms VOA.DeligneAudit.Toroidal.two_generator_fusion_one_zero
