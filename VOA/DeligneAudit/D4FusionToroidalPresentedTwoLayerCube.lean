import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerWordCollapse

/-! Seed-line stability itself forces the cubic seed to vanish. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

private abbrev H := (ρPTE 2).op (1 : Fin 28) 1 0
private abbrev G := (ρPTE 2).op D4sector.c₀ 1 0

theorem two_h1_generator_zero : H (pTE 2) = 0 := by
  exact two_generator_cartan_one (1 : Fin 28) (by
    change (1 : Fin 28).val < 4
    decide) 0 (by omega)

theorem two_h1_g0_zero : H (G (pTE 2)) = 0 := by
  have hc := two_h_theta_comm 1 1 0 0 (pTE 2) (by omega)
  have hh := two_high_op_eq_zero D4sector.c₀ 2 0 (by omega)
  simpa [H, G, two_h1_generator_zero, hh] using hc

theorem two_h1_seed_zero : H twoQuadraticSeed = 0 := by
  have hc := two_h_theta_comm 1 1 0 0 (G (pTE 2)) (by omega)
  have hh := two_high_op_eq_zero D4sector.c₀ 2 0 (by omega)
  simpa [H, G, twoQuadraticSeed, two_h1_g0_zero, hh] using hc

theorem two_g0_cube_zero_of_stability
    (hstable : ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 0 s twoQuadraticSeed ∈
        Submodule.span ℂ {twoQuadraticSeed}) :
    (ρPTE 2).op D4sector.c₀ 1 0 twoQuadraticSeed = 0 := by
  have hline (x : PTE 2)
      (hx : x ∈ Submodule.span ℂ {twoQuadraticSeed}) : H x = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      exact two_h1_seed_zero
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro a y _ hy
      simp [hy]
  have hc := two_h_theta_comm 1 0 0 0 twoQuadraticSeed (by omega)
  have hf := hline _ (hstable D4sector.c₀ 0)
  rw [hf, two_h1_seed_zero, map_zero, sub_zero] at hc
  exact neg_eq_zero.mp hc.symm

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_h1_generator_zero
#print axioms VOA.DeligneAudit.Toroidal.two_h1_g0_zero
#print axioms VOA.DeligneAudit.Toroidal.two_h1_seed_zero
#print axioms VOA.DeligneAudit.Toroidal.two_g0_cube_zero_of_stability
