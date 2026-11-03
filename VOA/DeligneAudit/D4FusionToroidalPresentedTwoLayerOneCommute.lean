import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerHighAll

/-! Degree-one toroidal letters commute after the high-letter vanishing. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem two_one_comm (a b : Fin 28) (r s : ℕ) (x : PTE 2) :
    (ρPTE 2).op a 1 r ((ρPTE 2).op b 1 s x) =
      (ρPTE 2).op b 1 s ((ρPTE 2).op a 1 r x) := by
  have hc := (ρPTE 2).comm a b 1 1 r s x
  have hsum : (if r + s < 2 then
      ∑ e : Fin 28, D4sector.f a b e •
        (ρPTE 2).op e 2 (r + s) x else 0) = 0 := by
    split_ifs with hmode
    · apply Finset.sum_eq_zero
      intro e _
      rw [two_high_op_eq_zero e 2 (r + s) (by omega)]
      simp
    · rfl
  have hz := hc.trans hsum
  exact sub_eq_zero.mp hz

theorem two_one_other_on_theta (c : Fin 28) (hc : c ≠ D4sector.c₀)
    (s t : ℕ) :
    (ρPTE 2).op c 1 s
      ((ρPTE 2).op D4sector.c₀ 1 t (pTE 2)) = 0 := by
  rw [two_one_comm]
  rw [two_generator_one_other_all c hc s]
  simp

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_one_comm
#print axioms VOA.DeligneAudit.Toroidal.two_one_other_on_theta
