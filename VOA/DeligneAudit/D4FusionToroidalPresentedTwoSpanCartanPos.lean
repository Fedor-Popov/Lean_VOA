import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanWeights

/-! Positive Cartan modes on the two cyclic current generators. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector

noncomputable section

theorem twoGen_one_cartan_pos (c : Fin 28) (hc : D4sector.cartan c)
    (r : ℕ) (hr : 1 ≤ r) : twoCurrent.op c r (twoGen 1) = 0 := by
  by_cases hr1 : r = 1
  · subst r
    have hv := two_generator_cartan_mode_one c hc
    have hcomm := (ρPTE 2).comm c D4sector.c₀ 0 1 1 1 (pTE 2)
    have hz : (ρPTE 2).op c 0 1
        ((ρPTE 2).op D4sector.c₀ 1 1 (pTE 2)) = 0 := by
      simp only [show ¬ 1 + 1 < 2 by omega, if_false] at hcomm
      rw [hv, map_zero, sub_zero] at hcomm
      exact hcomm
    simpa [twoCurrent, twoGen] using hz
  · have hr2 : ¬ r ≤ 1 := by omega
    simp [twoCurrent, hr2]

theorem twoGen_zero_cartan_one_mem (c : Fin 28)
    (hc : D4sector.cartan c) :
    twoCurrent.op c 1 (twoGen 0) ∈ twoM 1 := by
  have hv := two_generator_cartan_mode_one c hc
  have hcomm := (ρPTE 2).comm c D4sector.c₀ 0 1 1 0 (pTE 2)
  have hsum : (∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
      (ρPTE 2).op e 1 1 (pTE 2)) ∈ twoM 1 := by
    apply Submodule.sum_mem
    intro e _
    by_cases he : e = D4sector.c₀
    · subst e
      exact Submodule.smul_mem _ _ (twoM_word 1 [] rfl)
    · rw [two_generator_one_other_all e he]
      simp
  have hcomm' :
      (ρPTE 2).op c 0 1 (twoGen 0) -
        (ρPTE 2).op D4sector.c₀ 1 0 ((ρPTE 2).op c 0 1 (pTE 2)) =
        ∑ e : Fin 28, D4sector.f c D4sector.c₀ e •
          (ρPTE 2).op e 1 1 (pTE 2) := by
    simpa only [Nat.add_zero, Nat.zero_add, if_pos (by omega)] using hcomm
  rw [hv, map_zero, sub_zero] at hcomm'
  have hz : (ρPTE 2).op c 0 1 (twoGen 0) ∈ twoM 1 :=
    hcomm' ▸ hsum
  simpa [twoCurrent] using hz

theorem twoOne_cartan_pos (c : Fin 28) (hc : D4sector.cartan c)
    (r : ℕ) (hr : 1 ≤ r) : twoOneCurrent.op c r twoOneGen = 0 := by
  by_cases hr1 : r = 1
  · subst r
    change (twoM 1).mkQ (twoCurrent.op c 1 (twoGen 0)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (twoGen_zero_cartan_one_mem c hc)
  · have hr2 : ¬ r ≤ 1 := by omega
    change (twoM 1).mkQ (twoCurrent.op c r (twoGen 0)) = 0
    simp [twoCurrent, hr2]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_cartan_pos
#print axioms VOA.DeligneAudit.Toroidal.twoGen_zero_cartan_one_mem
#print axioms VOA.DeligneAudit.Toroidal.twoOne_cartan_pos
