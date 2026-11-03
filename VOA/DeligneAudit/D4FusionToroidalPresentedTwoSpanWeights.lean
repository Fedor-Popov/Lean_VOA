import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanBoundRoute

/-! Raising and Cartan-zero relations for both degree-one generators. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector

noncomputable section

theorem twoGen_raising (s : ℕ) (c : Fin 28) (hc : D4sector.raising c)
    (r : ℕ) : twoCurrent.op c r (twoGen s) = 0 := by
  by_cases hr : r ≤ 1
  · have hsum : (if r + s < 2 then
        ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
          (ρPTE 2).op e 1 (r + s) (pTE 2) else 0) = 0 := by
      split_ifs
      · apply Finset.sum_eq_zero
        intro e _
        by_cases he : e = D4sector.c₀
        · subst e
          have hz := D4sector.raising_table c hc D4sector.c₀
          simp [hz]
        · rw [two_generator_one_other_all e he]
          simp
      · rfl
    have hcomm := (ρPTE 2).comm c D4sector.c₀ 0 1 r s (pTE 2)
    have hz := hcomm.trans hsum
    have hv := two_seed_raising_v c hc r
    have hzero : (ρPTE 2).op c 0 r (twoGen s) = 0 := by
      change (ρPTE 2).op c 0 r
        ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2)) = 0
      rw [sub_eq_zero.mp hz, hv, map_zero]
    simpa [twoCurrent, hr] using hzero
  · have hr' : ¬ r ≤ 1 := hr
    simp [twoCurrent, hr']

private theorem twoGen_cartan_table : ∀ c e : Fin 28,
    c.val < 4 → D4sector.f c D4sector.c₀ e =
      if e = D4sector.c₀ then -(thetaD4 c : ℂ) else 0 := by
  intro c e hc
  change (fZ br c 27 e : ℂ) = _
  have ht : ∀ h e : Fin 28, h.val < 4 →
      fZ br h 27 e = if e = 27 then -(thetaD4 h : ℤ) else 0 := by
    decide +kernel
  rw [ht c e hc]
  simp [D4sector]

theorem twoGen_cartan_zero (s : ℕ) (c : Fin 28)
    (hc : D4sector.cartan c) :
    twoCurrent.op c 0 (twoGen s) =
      ((D4sector.thetaH c : ℕ) : ℂ) • twoGen s := by
  have hcomm := (ρPTE 2).comm c D4sector.c₀ 0 1 0 s (pTE 2)
  have hsum : (if s < 2 then
      ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
        (ρPTE 2).op e 1 s (pTE 2) else 0) =
      -(thetaD4 c : ℂ) • twoGen s := by
    by_cases hs : s < 2
    · simp only [if_pos hs, twoGen_cartan_table c _ hc, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · have hz : twoGen s = 0 := by
        change (ρPTE 2).op D4sector.c₀ 1 s (pTE 2) = 0
        rw [(ρPTE 2).high_zero D4sector.c₀ 1 s (by omega)]
        rfl
      simp [hs, hz]
  have hcomm' :
      (ρPTE 2).op c 0 0 (twoGen s) -
        (ρPTE 2).op D4sector.c₀ 1 s ((ρPTE 2).op c 0 0 (pTE 2)) =
        (if s < 2 then
          ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
            (ρPTE 2).op e 1 s (pTE 2) else 0) := by
    simpa only [Nat.zero_add] using hcomm
  have hz := hcomm'.trans hsum
  have hv := two_seed_cartan_v c hc
  have heq : (ρPTE 2).op c 0 0 (twoGen s) =
      (thetaD4 c : ℂ) • twoGen s := by
    rw [sub_eq_iff_eq_add.mp hz, hv, map_smul]
    change -(thetaD4 c : ℂ) • twoGen s +
      (2 * thetaD4 c : ℂ) • twoGen s =
        (thetaD4 c : ℂ) • twoGen s
    module
  simpa [twoCurrent, D4sector] using heq

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoGen_raising
#print axioms VOA.DeligneAudit.Toroidal.twoGen_cartan_zero
