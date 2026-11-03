import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerSpanBasic

/-! Move a single u-letter through a pure u-degree-zero word. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem two_one_on_pure : ∀ (l : List (TLtr 28)), twoUDeg l = 0 →
    ∀ (c : Fin 28) (s : ℕ),
      (ρPTE 2).op c 1 s (wordOpT (ρPTE 2) l (pTE 2)) ∈ twoPositiveSpan := by
  intro l
  induction l with
  | nil =>
      intro _ c s
      by_cases hc : c = D4sector.c₀
      · subst c
        by_cases hs : s ≤ 1
        · interval_cases s
          · exact twoM_zero_mem
          · exact twoM_one_mem
        · have hs' : 2 ≤ s := by omega
          rw [(ρPTE 2).high_zero D4sector.c₀ 1 s hs']
          exact Submodule.zero_mem _
      · change (ρPTE 2).op c 1 s (pTE 2) ∈ twoPositiveSpan
        rw [two_generator_one_other_all c hc s]
        exact Submodule.zero_mem _
  | cons x l ih =>
      intro hl c s
      have hi : x.2.1 = 0 := by
        simp only [twoUDeg] at hl
        omega
      have hl' : twoUDeg l = 0 := by
        simp only [twoUDeg] at hl
        omega
      let w := wordOpT (ρPTE 2) l (pTE 2)
      have hcomm := (ρPTE 2).comm c x.1 1 0 s x.2.2 w
      have heq : (ρPTE 2).op c 1 s ((ρPTE 2).op x.1 0 x.2.2 w) =
          (if s + x.2.2 < 2 then
            ∑ e : Fin 28, D4sector.f c x.1 e •
              (ρPTE 2).op e 1 (s + x.2.2) w else 0) +
            (ρPTE 2).op x.1 0 x.2.2 ((ρPTE 2).op c 1 s w) := by
        simpa only [Nat.add_zero] using (sub_eq_iff_eq_add.mp hcomm)
      have hleft : (ρPTE 2).op x.1 0 x.2.2
          ((ρPTE 2).op c 1 s w) ∈ twoPositiveSpan :=
        twoPositiveSpan_op_zero x.1 x.2.2 (ih hl' c s)
      have hright : (if s + x.2.2 < 2 then
          ∑ e : Fin 28, D4sector.f c x.1 e •
            (ρPTE 2).op e 1 (s + x.2.2) w else 0) ∈ twoPositiveSpan := by
        split_ifs with hmode
        · apply Submodule.sum_mem
          intro e _
          exact Submodule.smul_mem _ _ (ih hl' e (s + x.2.2))
        · exact Submodule.zero_mem _
      change (ρPTE 2).op c 1 s
        ((ρPTE 2).op x.1 x.2.1 x.2.2 w) ∈ twoPositiveSpan
      rw [hi, heq]
      exact Submodule.add_mem _ hright hleft

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_one_on_pure
