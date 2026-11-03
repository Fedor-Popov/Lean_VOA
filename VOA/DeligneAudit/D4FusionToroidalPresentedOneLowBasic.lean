import VOA.DeligneAudit.D4FusionToroidalPresentedOneFinal

/-! The elementary low-mode actions on the toroidal one-top vector. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

private abbrev ρ := univRepG D4sector.f OneR
private abbrev w := wUG D4sector.f OneR

private theorem one_sat : Sat D4sector.f ρ w (ravSpec D4sector 1 2) := by
  simpa [OneR, ravFam_zero_right] using univG_sat D4sector.f OneR

theorem one_generator_mode_one (c : Fin 28) (hc : c ≠ D4sector.c₀) :
    ρ.op c 1 w = 0 := by
  by_cases h4 : c.val < 4
  · exact rs_cartan_pos one_sat (show D4sector.cartan c by exact h4) 1 (by omega)
  by_cases h16 : c.val < 16
  · exact rs_raising one_sat (show D4sector.raising c by exact ⟨by omega, h16⟩) 1
  have h := rs_fusion one_sat (show D4sector.fusion c by
    change 16 ≤ c.val
    omega)
  change c ≠ (27 : Fin 28) at hc
  change ρ.op c (if c = (27 : Fin 28) then 2 else 1) w = 0 at h
  simpa only [if_neg hc] using h

theorem one_generator_mode_two (c : Fin 28) : ρ.op c 2 w = 0 := by
  exact rav_high_kills_generator (m := 1) (R := ρ) (w := w)
    (by omega) (univG_sat D4sector.f OneR) c 2 (by omega)

theorem one_top_mode_one_other (c : Fin 28) (hc : c ≠ D4sector.c₀) :
    ρ.op c 1 oneTop = 0 := by
  have h := ρ.comm c D4sector.c₀ 1 1 w
  have hs : (∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 2 w) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [one_generator_mode_two e]
    simp
  have h' : ρ.op c 1 (ρ.op D4sector.c₀ 1 w) = 0 := by
    calc
      _ = ∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 2 w := by
        simpa only [one_generator_mode_one c hc, map_zero, sub_zero,
          Nat.reduceAdd] using h
      _ = 0 := hs
  simpa only [oneTop] using h'

private theorem raising_top_table :
    ∀ c e : Fin 28, 4 ≤ c.val → c.val < 16 →
      fZ br c 27 e ≠ 0 → e.val < 4 ∨ (16 ≤ e.val ∧ e.val ≠ 27) := by
  decide +kernel

theorem one_top_mode_zero_raising (c : Fin 28)
    (hc : 4 ≤ c.val ∧ c.val < 16) : ρ.op c 0 oneTop = 0 := by
  have h := ρ.comm c D4sector.c₀ 0 1 w
  have he : ρ.op c 0 w = 0 :=
    rs_raising one_sat (show D4sector.raising c by exact hc) 0
  have hs : (∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 1 w) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases hfe : fZ br c 27 e = 0
    · change (fZ br c 27 e : ℂ) • ρ.op e 1 w = 0
      rw [hfe, Int.cast_zero, zero_smul]
    · rcases raising_top_table c e hc.1 hc.2 hfe with h4 | ⟨h16, h27⟩
      · rw [rs_cartan_pos one_sat (show D4sector.cartan e by exact h4) 1
          (by omega)]
        simp
      · have he' : e ≠ D4sector.c₀ := by
          intro h
          subst e
          exact h27 rfl
        rw [one_generator_mode_one e he']
        simp
  have h' : ρ.op c 0 (ρ.op D4sector.c₀ 1 w) = 0 := by
    calc
      _ = ∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 1 w := by
        simpa only [he, map_zero, sub_zero, Nat.zero_add] using h
      _ = 0 := hs
  simpa only [oneTop] using h'

private theorem cartan_top_tableZ :
    ∀ h e : Fin 28, h.val < 4 →
      fZ br h 27 e = if e = 27 then -(thetaD4 h : ℤ) else 0 := by
  decide +kernel

private theorem cartan_top_table (h e : Fin 28) (hh : h.val < 4) :
    D4sector.f h D4sector.c₀ e =
      if e = D4sector.c₀ then -(thetaD4 h : ℂ) else 0 := by
  change (fZ br h 27 e : ℂ) = if e = 27 then -(thetaD4 h : ℂ) else 0
  rw [cartan_top_tableZ h e hh]
  split_ifs <;> simp

theorem one_top_mode_zero_cartan (c : Fin 28) (hc : c.val < 4) :
    ρ.op c 0 oneTop = 0 := by
  have hw := rs_cartan_zero one_sat (show D4sector.cartan c by exact hc)
  change ρ.op c 0 w = (((1 * thetaD4 c : ℕ) : ℂ)) • w at hw
  simp only [one_mul] at hw
  have hs : (∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 1 w) =
      -(thetaD4 c : ℂ) • ρ.op D4sector.c₀ 1 w := by
    simp only [cartan_top_table c _ hc, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h := ρ.comm c D4sector.c₀ 0 1 w
  have h' : ρ.op c 0 (ρ.op D4sector.c₀ 1 w) =
      (∑ e : Fin 28, D4sector.f c D4sector.c₀ e • ρ.op e 1 w) +
        ρ.op D4sector.c₀ 1 (ρ.op c 0 w) := by
    simpa only [Nat.zero_add] using (sub_eq_iff_eq_add.mp h)
  change ρ.op c 0 (ρ.op D4sector.c₀ 1 w) = 0
  rw [h', hw, map_smul, hs]
  module

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.one_generator_mode_one
#print axioms VOA.DeligneAudit.Toroidal.one_generator_mode_two
#print axioms VOA.DeligneAudit.Toroidal.one_top_mode_one_other
#print axioms VOA.DeligneAudit.Toroidal.one_top_mode_zero_raising
#print axioms VOA.DeligneAudit.Toroidal.one_top_mode_zero_cartan
