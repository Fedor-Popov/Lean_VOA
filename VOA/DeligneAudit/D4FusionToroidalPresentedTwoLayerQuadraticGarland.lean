import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerQuadratic

/-! Cartan derivatives of the two Garland relations kill the mixed quadratic seeds. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.D4FusionContact

noncomputable section

private abbrev v := pTE 2
private abbrev H := (ρPTE 2).op (1 : Fin 28) 1 0
private abbrev F (s : ℕ) := (ρPTE 2).op D4sector.c₀ 0 s
private abbrev G (s : ℕ) := (ρPTE 2).op D4sector.c₀ 1 s

private theorem H_v : H v = 0 := by
  exact two_generator_cartan_one (1 : Fin 28) (by
    change (1 : Fin 28).val < 4
    decide) 0 (by omega)

private theorem H_G_zero (s : ℕ) (hs : s ≤ 1) : H (G s v) = 0 := by
  have hc := two_h_theta_comm 1 1 0 s v (by omega)
  interval_cases s
  · simpa [H, G, H_v, two_theta_two_zero] using hc
  · simpa [H, G, H_v, two_theta_two_one_zero] using hc

private theorem H_F_G (r s : ℕ) (hr : r ≤ 1) (hs : s ≤ 1) :
    H (F r (G s v)) = -(G r (G s v)) := by
  have hc := two_h_theta_comm 1 0 0 r (G s v) (by omega)
  simpa [H, F, G, H_G_zero s hs] using hc

private theorem P1_zero : F 0 (G 1 v) + F 1 (G 0 v) = 0 := by
  simpa [Psym_one, Finset.antidiagonal, F, G, v] using
    two_garland_one_zero 1 (by omega)

private theorem P2_zero : F 1 (G 1 v) = 0 := by
  have hz : (ρPTE 2).op D4sector.c₀ 1 2 (pTE 2) = 0 := by
    rw [(ρPTE 2).high_zero D4sector.c₀ 1 2 (by omega)]
    rfl
  simpa [Psym_one, Finset.antidiagonal, F, G, v, hz,
    (ρPTE 2).high_zero D4sector.c₀ 0 2 (by omega)] using
    two_garland_one_zero 2 (by omega)

private theorem G_comm (r s : ℕ) (hr : r + s < 2) (x : PTE 2) :
    G r (G s x) = G s (G r x) := by
  have hz : ∀ c : Fin 28, fZ br 27 27 c = 0 := by decide +kernel
  have hf : ∀ c : Fin 28, D4sector.f D4sector.c₀ D4sector.c₀ c = 0 := by
    intro c
    change (fZ br 27 27 c : ℂ) = 0
    exact_mod_cast hz c
  have hc := (ρPTE 2).comm D4sector.c₀ D4sector.c₀ 1 1 r s x
  simp only [if_pos hr, hf, zero_smul, Finset.sum_const_zero] at hc
  exact sub_eq_zero.mp hc

theorem two_g0_g1_zero : G 0 (G 1 v) = 0 := by
  have hp := congrArg H P1_zero
  simp only [map_add, map_zero] at hp
  rw [H_F_G 0 1 (by omega) (by omega),
    H_F_G 1 0 (by omega) (by omega)] at hp
  rw [G_comm 1 0 (by omega) v] at hp
  have h2 : G 0 (G 1 v) + G 0 (G 1 v) = 0 := by
    have hn := congrArg Neg.neg hp
    simpa only [neg_add_rev, neg_neg, neg_zero] using hn
  have hz : (2 : ℂ) • G 0 (G 1 v) = 0 := by
    simpa only [two_smul] using h2
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem two_g1_g1_zero : G 1 (G 1 v) = 0 := by
  have hp := congrArg H P2_zero
  simp only [map_zero] at hp
  rw [H_F_G 1 1 (by omega) (by omega)] at hp
  exact neg_eq_zero.mp hp

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_g0_g1_zero
#print axioms VOA.DeligneAudit.Toroidal.two_g1_g1_zero
