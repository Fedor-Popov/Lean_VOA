import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerWordReduction

/-! Conditional collapse, reduced to stability and the cubic seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

private abbrev seedLine := Submodule.span ℂ {twoQuadraticSeed}

theorem two_zero_seedLine_stable
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈ seedLine)
    (c : Fin 28) (s : ℕ) (x : PTE 2) (hx : x ∈ seedLine) :
    (ρPTE 2).op c 0 s x ∈ seedLine := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl
    exact hstable c s
  · simp
  · intro y z _ _ hy hz
    simpa only [map_add] using Submodule.add_mem seedLine hy hz
  · intro a y _ hy
    simpa only [map_smul] using Submodule.smul_mem seedLine a hy

theorem two_one_seedLine_zero_of_cube
    (hc : (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0)
    (c : Fin 28) (s : ℕ) (x : PTE 2) (hx : x ∈ seedLine) :
    (ρPTE 2).op c 1 s x = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl
    exact two_one_seed_zero_of_cube hc c s
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro a y _ hy
    simp [hy]

theorem two_one_positiveSpan_seed_of_stability
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈ seedLine)
    (hc : (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0)
    (c : Fin 28) (s : ℕ) (x : PTE 2) (hx : x ∈ twoPositiveSpan) :
    (ρPTE 2).op c 1 s x ∈ seedLine := by
  have hm (t : ℕ) : twoM t ≤ seedLine.comap ((ρPTE 2).op c 1 s) := by
    rw [twoM, Submodule.span_le]
    rintro y ⟨l, hl, rfl⟩
    exact two_one_pure_seed_of_stability hstable c s t l hl
  change x ∈ twoM 0 ⊔ twoM 1 at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  rw [← hab, map_add]
  exact Submodule.add_mem seedLine (hm 0 ha) (hm 1 hb)

theorem two_udeg_ge_two_word_of_stability
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈ seedLine)
    (hc : (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0) :
    ∀ (l : List (TLtr 28)), 2 ≤ twoUDeg l →
      wordOpT (ρPTE 2) l (pTE 2) ∈ seedLine := by
  intro l
  induction l with
  | nil =>
      intro hl
      simp [twoUDeg] at hl
  | cons x l ih =>
      intro hl
      change (ρPTE 2).op x.1 x.2.1 x.2.2
        (wordOpT (ρPTE 2) l (pTE 2)) ∈ seedLine
      by_cases hh : 2 ≤ x.2.1
      · rw [two_high_op_eq_zero x.1 x.2.1 x.2.2 hh]
        exact Submodule.zero_mem _
      by_cases hz : x.2.1 = 0
      · rw [hz]
        have htail : 2 ≤ twoUDeg l := by
          simp only [twoUDeg] at hl
          omega
        exact two_zero_seedLine_stable hstable x.1 x.2.2 _ (ih htail)
      have hone : x.2.1 = 1 := by omega
      rw [hone]
      by_cases htail : 2 ≤ twoUDeg l
      · rw [two_one_seedLine_zero_of_cube hc x.1 x.2.2 _ (ih htail)]
        exact Submodule.zero_mem _
      have htail1 : twoUDeg l = 1 := by
        simp only [twoUDeg] at hl
        omega
      exact two_one_positiveSpan_seed_of_stability hstable hc x.1 x.2.2 _
        (two_degree_one_word l htail1)

theorem twoUTwoCollapse_of_stability
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈ seedLine)
    (hc : (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0) :
    TwoUTwoCollapse := by
  rw [TwoUTwoCollapse, twoN, Submodule.span_le]
  rintro y ⟨l, hl, rfl⟩
  exact two_udeg_ge_two_word_of_stability hstable hc l hl

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_zero_seedLine_stable
#print axioms VOA.DeligneAudit.Toroidal.two_one_seedLine_zero_of_cube
#print axioms VOA.DeligneAudit.Toroidal.two_one_positiveSpan_seed_of_stability
#print axioms VOA.DeligneAudit.Toroidal.two_udeg_ge_two_word_of_stability
#print axioms VOA.DeligneAudit.Toroidal.twoUTwoCollapse_of_stability
