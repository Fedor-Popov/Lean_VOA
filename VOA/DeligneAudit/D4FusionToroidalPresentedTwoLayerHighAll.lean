import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerHigh

/-! High u-degree operators vanish on the entire presented module. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem two_high_word : ∀ (l : List (TLtr 28)) (c : Fin 28) (i s : ℕ),
    2 ≤ i → (ρPTE 2).op c i s (wordOpT (ρPTE 2) l (pTE 2)) = 0 := by
  intro l
  induction l with
  | nil =>
      intro c i s hi
      exact two_high_v c i s hi
  | cons x l ih =>
      intro c i s hi
      let w := wordOpT (ρPTE 2) l (pTE 2)
      have hcomm := (ρPTE 2).comm c x.1 i x.2.1 s x.2.2 w
      have hleft : (ρPTE 2).op x.1 x.2.1 x.2.2
          ((ρPTE 2).op c i s w) = 0 := by
        rw [ih c i s hi]
        simp
      have hright : (if s + x.2.2 < 2 then
          ∑ e : Fin 28, D4sector.f c x.1 e •
            (ρPTE 2).op e (i + x.2.1) (s + x.2.2) w else 0) = 0 := by
        split_ifs with hs
        · apply Finset.sum_eq_zero
          intro e _
          rw [ih e (i + x.2.1) (s + x.2.2) (by omega)]
          simp
        · rfl
      change (if s + x.2.2 < 2 then
        ∑ e : Fin 28, D4sector.f c x.1 e •
          ((ρPTE 2).op e (i + x.2.1) (s + x.2.2)) w else 0) = 0 at hright
      have hcomm' := hcomm.trans hright
      simpa [hleft, w, wordOpT] using hcomm'

theorem two_high_op_eq_zero (c : Fin 28) (i s : ℕ) (hi : 2 ≤ i) :
    (ρPTE 2).op c i s = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ
      (Set.range fun l : List (TLtr 28) => wordOpT (ρPTE 2) l (pTE 2)) := by
    rw [PTE_cyclic 2]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact two_high_word l c i s hi
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx => simpa only [map_smul] using congrArg (a • ·) hx

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_high_word
#print axioms VOA.DeligneAudit.Toroidal.two_high_op_eq_zero
