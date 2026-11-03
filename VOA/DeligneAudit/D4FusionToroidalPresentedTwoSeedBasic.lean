import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerOneCommute
import VOA.DeligneAudit.D4FusionContactTruncationTable

/-! Low zero-degree actions on the quadratic toroidal seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

private abbrev G := (ρPTE 2).op D4sector.c₀ 1 0

theorem two_seed_raising_v (c : Fin 28) (hc : D4sector.raising c)
    (s : ℕ) : (ρPTE 2).op c 0 s (pTE 2) = 0 := by
  by_cases hs : s ≤ 1
  · interval_cases s
    · have ht : [(c, 0)] ∈ (ravFam D4sector 2 0).tails :=
        Or.inl ⟨c, 0, hc, rfl⟩
      simpa [symbolLetters, wordOpT] using two_syntax_tail [(c, 0)] ht
    · have ht : [(c, 1)] ∈ (ravFam D4sector 2 0).tails :=
        Or.inl ⟨c, 1, hc, rfl⟩
      simpa [symbolLetters, wordOpT] using two_syntax_tail [(c, 1)] ht
  · rw [(ρPTE 2).high_zero c 0 s (by omega)]
    rfl

private theorem raising_support : ∀ c e : Fin 28,
    4 ≤ c.val → c.val < 16 → fZ br c 27 e ≠ 0 → e ≠ 27 := by
  decide +kernel

theorem two_seed_raising_zero (c : Fin 28) (hc : D4sector.raising c)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 0 s twoQuadraticSeed = 0 := by
  let Y := (ρPTE 2).op c 0 s
  let Z := ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
    (ρPTE 2).op e 1 s
  have hZ (x : PTE 2) :
      Y (G x) - G (Y x) = Z x := by
    have h := (ρPTE 2).comm c D4sector.c₀ 0 1 s 0 x
    rw [if_pos (by omega)] at h
    simpa [Y, G, Z] using h
  have hZv : Z (pTE 2) = 0 := by
    simp only [Z, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : fZ br c 27 e = 0
    · change (fZ br c 27 e : ℂ) • _ = 0
      rw [he, Int.cast_zero, zero_smul]
    · have hne : e ≠ D4sector.c₀ :=
        raising_support c e hc.1 hc.2 he
      rw [two_generator_one_other_all e hne s]
      simp
  have hZGv : Z (G (pTE 2)) = 0 := by
    simp only [Z, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : fZ br c 27 e = 0
    · change (fZ br c 27 e : ℂ) • _ = 0
      rw [he, Int.cast_zero, zero_smul]
    · have hne : e ≠ D4sector.c₀ :=
        raising_support c e hc.1 hc.2 he
      rw [two_one_other_on_theta e hne s 0]
      simp
  have hv : Y (pTE 2) = 0 := two_seed_raising_v c hc s
  have h1 := hZ (pTE 2)
  have h2 := hZ (G (pTE 2))
  rw [hv, map_zero, sub_zero, hZv] at h1
  change Y (G (G (pTE 2))) = 0
  rw [h1, map_zero, sub_zero, hZGv] at h2
  exact h2

theorem two_seed_cartan_v (c : Fin 28) (hc : D4sector.cartan c) :
    (ρPTE 2).op c 0 0 (pTE 2) = (2 * thetaD4 c : ℂ) • pTE 2 := by
  let q : Fin D4sector.n × ℂ := (c, (2 * thetaD4 c : ℂ))
  have hq : q ∈ (ravFam D4sector 2 0).eig := by
    change q ∈ (ravSpec D4sector 2 4).eig
    exact Or.inl ⟨c, hc, by simp [q, D4sector, Nat.cast_mul]⟩
  have h := mk_syntax D4sector.f 2 (JprimeSyntaxE 2)
    (swT [(q.1, 0, 0)] - q.2 • swT [])
    (Or.inr ⟨q, hq, rfl⟩)
  rw [← Submodule.mkQ_apply, map_sub, map_smul] at h
  have h1 := wordOpT_rhoPT D4sector.f 2 (JprimeSyntaxE 2) [(c, 0, 0)]
  have h0 := wordOpT_rhoPT D4sector.f 2 (JprimeSyntaxE 2) []
  change (ρPTE 2).op q.1 0 0 (pTE 2) =
    (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ (swT [(q.1, 0, 0)]) at h1
  change pTE 2 = (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ (swT []) at h0
  rw [← h1, ← h0] at h
  simpa [q] using (sub_eq_zero.mp h)

private theorem cartan_theta_table : ∀ c e : Fin 28,
    c.val < 4 → D4sector.f c D4sector.c₀ e =
      if e = D4sector.c₀ then -(thetaD4 c : ℂ) else 0 := by
  intro c e hc
  change (fZ br c 27 e : ℂ) = _
  have hz : fZ br c 27 e =
      if e = 27 then -(thetaD4 c : ℤ) else 0 := by
    have ht : ∀ h e : Fin 28, h.val < 4 →
        fZ br h 27 e = if e = 27 then -(thetaD4 h : ℤ) else 0 := by
      decide +kernel
    exact ht c e hc
  rw [hz]
  simp [D4sector]

theorem two_seed_cartan_zero (c : Fin 28) (hc : D4sector.cartan c)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 0 s twoQuadraticSeed = 0 := by
  have hcomm (x : PTE 2) :
      (ρPTE 2).op c 0 s (G x) - G ((ρPTE 2).op c 0 s x) =
        (-(thetaD4 c : ℂ)) •
        (ρPTE 2).op D4sector.c₀ 1 s x := by
    have hsum :
        (∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
          (ρPTE 2).op e 1 s x) =
          (-(thetaD4 c : ℂ)) • (ρPTE 2).op D4sector.c₀ 1 s x := by
      simp only [cartan_theta_table c _ hc, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h := (ρPTE 2).comm c D4sector.c₀ 0 1 s 0 x
    rw [if_pos (by omega)] at h
    have h' :
        (ρPTE 2).op c 0 s (G x) - G ((ρPTE 2).op c 0 s x) =
          ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
            (ρPTE 2).op e 1 s x := by
      simpa only [G, Nat.zero_add, Nat.add_zero] using h
    exact h'.trans hsum
  interval_cases s
  · have hv := two_seed_cartan_v c hc
    have h1 := hcomm (pTE 2)
    have h2 := hcomm (G (pTE 2))
    simp only [hv, map_smul] at h1
    change (ρPTE 2).op c 0 0 (G (G (pTE 2))) = 0
    rw [sub_eq_iff_eq_add.mp h2, sub_eq_iff_eq_add.mp h1]
    simp only [map_add, map_smul]
    module
  · have hv := two_generator_cartan_mode_one c hc
    have h1 := hcomm (pTE 2)
    have h2 := hcomm (G (pTE 2))
    rw [hv, map_zero, sub_zero] at h1
    change (ρPTE 2).op c 0 1 (G (G (pTE 2))) = 0
    rw [sub_eq_iff_eq_add.mp h2, h1]
    simp only [map_smul]
    rw [two_one_comm D4sector.c₀ D4sector.c₀ 1 0 (pTE 2)]
    simp [G, two_g0_g1_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_raising_v
#print axioms VOA.DeligneAudit.Toroidal.two_seed_raising_zero
#print axioms VOA.DeligneAudit.Toroidal.two_seed_cartan_v
#print axioms VOA.DeligneAudit.Toroidal.two_seed_cartan_zero
