import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerOneCommute

/-! Reduction of positive-degree words to the quadratic line. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

private abbrev seedLine := Submodule.span ℂ {twoQuadraticSeed}

theorem two_one_seed_zero_of_cube
    (hc : (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0)
    (c : Fin 28) (s : ℕ) :
    (ρPTE 2).op c 1 s twoQuadraticSeed = 0 := by
  by_cases hs : 2 ≤ s
  · rw [(ρPTE 2).high_zero c 1 s hs]
    rfl
  have hs' : s ≤ 1 := by omega
  by_cases hcolour : c = D4sector.c₀
  · subst c
    interval_cases s
    · exact hc
    · change (ρPTE 2).op D4sector.c₀ 1 1
        ((ρPTE 2).op D4sector.c₀ 1 0
          ((ρPTE 2).op D4sector.c₀ 1 0 (pTE 2))) = 0
      rw [two_one_comm D4sector.c₀ D4sector.c₀ 1 0]
      rw [two_one_comm D4sector.c₀ D4sector.c₀ 1 0]
      rw [two_g0_g1_zero, map_zero]
  · change (ρPTE 2).op c 1 s
      ((ρPTE 2).op D4sector.c₀ 1 0
        ((ρPTE 2).op D4sector.c₀ 1 0 (pTE 2))) = 0
    rw [two_one_comm c D4sector.c₀ s 0]
    rw [two_one_comm c D4sector.c₀ s 0]
    rw [two_generator_one_other_all c hcolour s, map_zero]
    rfl

theorem two_one_pure_seed_of_stability
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈ seedLine)
    (c : Fin 28) (s t : ℕ) :
    ∀ (l : List (TLtr 28)), twoUDeg l = 0 →
      (ρPTE 2).op c 1 s
        (wordOpT (ρPTE 2) l ((ρPTE 2).op D4sector.c₀ 1 t (pTE 2))) ∈
          seedLine := by
  intro l
  induction l generalizing c s with
  | nil =>
      intro _
      change (ρPTE 2).op c 1 s
        ((ρPTE 2).op D4sector.c₀ 1 t (pTE 2)) ∈ seedLine
      by_cases ht : 2 ≤ t
      · rw [(ρPTE 2).high_zero D4sector.c₀ 1 t ht]
        simp
      have ht' : t ≤ 1 := by omega
      by_cases hs : 2 ≤ s
      · rw [(ρPTE 2).high_zero c 1 s hs]
        exact Submodule.zero_mem _
      have hs' : s ≤ 1 := by omega
      by_cases hcolour : c = D4sector.c₀
      · subst c
        interval_cases t
        · interval_cases s
          · exact Submodule.subset_span (by rfl)
          · rw [two_one_comm D4sector.c₀ D4sector.c₀ 1 0]
            rw [two_g0_g1_zero]
            exact Submodule.zero_mem _
        · interval_cases s
          · rw [two_g0_g1_zero]
            exact Submodule.zero_mem _
          · rw [two_g1_g1_zero]
            exact Submodule.zero_mem _
      · rw [two_one_other_on_theta c hcolour]
        exact Submodule.zero_mem _
  | cons x l ih =>
      intro hl
      have hi : x.2.1 = 0 := by
        simp only [twoUDeg] at hl
        omega
      have hl' : twoUDeg l = 0 := by
        simp only [twoUDeg] at hl
        omega
      let w := wordOpT (ρPTE 2) l
        ((ρPTE 2).op D4sector.c₀ 1 t (pTE 2))
      have hcomm := (ρPTE 2).comm c x.1 1 0 s x.2.2 w
      have heq : (ρPTE 2).op c 1 s ((ρPTE 2).op x.1 0 x.2.2 w) =
          (if s + x.2.2 < 2 then
            ∑ e : Fin 28, D4sector.f c x.1 e •
              (ρPTE 2).op e 1 (s + x.2.2) w else 0) +
            (ρPTE 2).op x.1 0 x.2.2 ((ρPTE 2).op c 1 s w) := by
        simpa only [Nat.add_zero] using (sub_eq_iff_eq_add.mp hcomm)
      have hleft : (ρPTE 2).op x.1 0 x.2.2
          ((ρPTE 2).op c 1 s w) ∈ seedLine := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ (ih c s hl')
        · intro z hz
          rcases hz with rfl
          exact hstable x.1 x.2.2
        · simp
        · intro y z _ _ hy hz
          simpa only [map_add] using Submodule.add_mem seedLine hy hz
        · intro a y _ hy
          simpa only [map_smul] using Submodule.smul_mem seedLine a hy
      have hright : (if s + x.2.2 < 2 then
          ∑ e : Fin 28, D4sector.f c x.1 e •
            (ρPTE 2).op e 1 (s + x.2.2) w else 0) ∈ seedLine := by
        split_ifs with hm
        · apply Submodule.sum_mem
          intro e _
          exact Submodule.smul_mem _ _ (ih e (s + x.2.2) hl')
        · exact Submodule.zero_mem _
      change (ρPTE 2).op c 1 s
        ((ρPTE 2).op x.1 x.2.1 x.2.2 w) ∈ seedLine
      rw [hi, heq]
      exact Submodule.add_mem _ hright hleft

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_one_seed_zero_of_cube
#print axioms VOA.DeligneAudit.Toroidal.two_one_pure_seed_of_stability
