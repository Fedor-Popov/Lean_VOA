import VOA.DeligneAudit.SL4TMixedSecondLeviFiltration

/-! Levi generation with a coefficient space whose positive Cartan modes need not vanish. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem secondLevi_positive_on_radical
    (he : ∀ i s, a2Positive i → ρ.op i s w = 0) : ∀ (r : List (Fin 8 × ℕ)),
    r.Forall (fun x => a2Radical x.1) →
    ∀ (a : Fin 8) (s : ℕ), a2Positive a →
      ρ.op a s (wordOp ρ r w) ∈ a2LeviSpan ρ w := by
  intro r
  induction r with
  | nil =>
      intro _ a s ha
      rcases ha with rfl | rfl
      · change ρ.op 0 s w ∈ a2LeviSpan ρ w
        rw [he 0 s (by simp [a2Positive])]
        exact (a2LeviSpan ρ w).zero_mem
      · change ρ.op 2 s w ∈ a2LeviSpan ρ w
        rw [he 2 s (by simp [a2Positive])]
        exact (a2LeviSpan ρ w).zero_mem
  | cons x r ih =>
      intro hr a s ha
      rcases x with ⟨b, t⟩
      simp only [List.forall_cons] at hr
      have hb := hr.1
      have htail := hr.2
      apply swap_mem ρ w a b s t (wordOp ρ r w)
      · exact radical_inv ρ w b t hb (ih htail a s ha)
      · intro c hc
        have hlevi : a2Levi c := by
          by_contra hn
          exact hc (a2_positive_radical_bracket a b c ha hb hn)
        exact levi_inv ρ w c (s + t) hlevi (normal_mem ρ w [] r (by simp) htail)

theorem secondLevi_positive_on_normal
    (he : ∀ i s, a2Positive i → ρ.op i s w = 0) : ∀ (l r : List (Fin 8 × ℕ)),
    l.Forall (fun x => a2Levi x.1) →
    r.Forall (fun x => a2Radical x.1) →
    ∀ (a : Fin 8) (s : ℕ), a2Positive a →
      ρ.op a s (wordOp ρ (l ++ r) w) ∈ a2LeviSpan ρ w := by
  intro l
  induction l with
  | nil =>
      intro r _ hr a s ha
      exact secondLevi_positive_on_radical ρ w he r hr a s ha
  | cons x l ih =>
      intro r hl hr a s ha
      rcases x with ⟨b, t⟩
      simp only [List.forall_cons] at hl
      have hb := hl.1
      have htail := hl.2
      apply swap_mem ρ w a b s t (wordOp ρ (l ++ r) w)
      · exact levi_inv ρ w b t hb (ih r htail hr a s ha)
      · intro c hc
        have hpos : a2Positive c := by
          by_contra hn
          exact hc (a2_positive_levi_bracket a b c ha hb hn)
        exact ih r htail hr c (s + t) hpos

theorem secondLevi_positive_inv (he : ∀ i s, a2Positive i → ρ.op i s w = 0)
    (a : Fin 8) (s : ℕ) (ha : a2Positive a)
    {v : V} (hv : v ∈ a2LeviSpan ρ w) :
    ρ.op a s v ∈ a2LeviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact secondLevi_positive_on_normal ρ w he l r hl hr a s ha
  | zero => simp
  | add x y _ _ hx hy => simpa using (a2LeviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (a2LeviSpan ρ w).smul_mem c hx

/-- PBW/Levi generation: all current words are spanned by Levi words on
negative radical monomials. -/
theorem secondLevi_cyclic_eq_leviSpan (he : ∀ i s, a2Positive i → ρ.op i s w = 0) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w = a2LeviSpan ρ w := by
  apply le_antisymm
  · rw [VOA.DeligneAudit.UnivG.cycSubG, Submodule.span_le]
    rintro z ⟨l, rfl⟩
    induction l with
    | nil => exact normal_mem ρ w [] [] (by simp) (by simp)
    | cons x l ih =>
        rcases x with ⟨a, s⟩
        have hcase : a2Positive a ∨ a2Levi a ∨ a2Radical a := by
          fin_cases a <;> simp [a2Positive, a2Levi, a2Radical]
        rcases hcase with hp | hl | hr
        · exact secondLevi_positive_inv ρ w he a s hp ih
        · exact levi_inv ρ w a s hl ih
        · exact radical_inv ρ w a s hr ih
  · rw [a2LeviSpan, Submodule.span_le]
    rintro z ⟨l, r, _, _, rfl⟩
    exact VOA.DeligneAudit.UnivG.wordOp_mem_cycSubG ρ w (l ++ r)


end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_on_radical
#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_on_normal
#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_inv
#print axioms VOA.DeligneAudit.SL4T.secondLevi_cyclic_eq_leviSpan
