import VOA.DeligneAudit.LeviTypeA3GenerationCore

/-! Positive radical straightening and the final Levi generation statement. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V) (weight : Fin 3 → ℕ)

private theorem positive_on_radical
    (h : LocalWeylRel ρ w weight) : ∀ (r : List (Fin 15 × ℕ)),
    r.Forall (fun x => a3Radical x.1) →
    ∀ (a : Fin 15) (s : ℕ), a3Positive a →
      ρ.op a s (wordOp ρ r w) ∈ a3LeviSpan ρ w := by
  intro r
  induction r with
  | nil =>
      intro _ a s ha
      rcases ha with rfl | rfl | rfl
      · change ρ.op 0 s w ∈ a3LeviSpan ρ w
        rw [h.raising 0 (by decide) s]
        exact (a3LeviSpan ρ w).zero_mem
      · change ρ.op 1 s w ∈ a3LeviSpan ρ w
        rw [h.raising 1 (by decide) s]
        exact (a3LeviSpan ρ w).zero_mem
      · change ρ.op 2 s w ∈ a3LeviSpan ρ w
        rw [h.raising 2 (by decide) s]
        exact (a3LeviSpan ρ w).zero_mem
  | cons x r ih =>
      intro hr a s ha
      rcases x with ⟨b, t⟩
      simp only [List.forall_cons] at hr
      have hb := hr.1
      have htail := hr.2
      apply a3_swap_mem ρ w a b s t (wordOp ρ r w)
      · exact a3_radical_inv ρ w b t hb (ih htail a s ha)
      · intro c hc
        have hlevi : a3Levi c := by
          by_contra hn
          exact hc (a3_positive_radical_bracket a b c ha hb hn)
        exact a3_levi_inv ρ w c (s + t) hlevi (a3_normal_mem ρ w [] r (by simp) htail)

private theorem positive_on_normal
    (h : LocalWeylRel ρ w weight) : ∀ (l r : List (Fin 15 × ℕ)),
    l.Forall (fun x => a3Levi x.1) →
    r.Forall (fun x => a3Radical x.1) →
    ∀ (a : Fin 15) (s : ℕ), a3Positive a →
      ρ.op a s (wordOp ρ (l ++ r) w) ∈ a3LeviSpan ρ w := by
  intro l
  induction l with
  | nil =>
      intro r _ hr a s ha
      exact positive_on_radical ρ w weight h r hr a s ha
  | cons x l ih =>
      intro r hl hr a s ha
      rcases x with ⟨b, t⟩
      simp only [List.forall_cons] at hl
      have hb := hl.1
      have htail := hl.2
      apply a3_swap_mem ρ w a b s t (wordOp ρ (l ++ r) w)
      · exact a3_levi_inv ρ w b t hb (ih r htail hr a s ha)
      · intro c hc
        have hpos : a3Positive c := by
          by_contra hn
          exact hc (a3_positive_levi_bracket a b c ha hb hn)
        exact ih r htail hr c (s + t) hpos

private theorem positive_inv (h : LocalWeylRel ρ w weight)
    (a : Fin 15) (s : ℕ) (ha : a3Positive a)
    {v : V} (hv : v ∈ a3LeviSpan ρ w) :
    ρ.op a s v ∈ a3LeviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact positive_on_normal ρ w weight h l r hl hr a s ha
  | zero => simp
  | add x y _ _ hx hy => simpa using (a3LeviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (a3LeviSpan ρ w).smul_mem c hx

/-- PBW/Levi generation: all current words are spanned by Levi words on
negative radical monomials. -/
theorem a3_cycSubG_eq_leviSpan (h : LocalWeylRel ρ w weight) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w = a3LeviSpan ρ w := by
  apply le_antisymm
  · rw [VOA.DeligneAudit.UnivG.cycSubG, Submodule.span_le]
    rintro z ⟨l, rfl⟩
    induction l with
    | nil => exact a3_normal_mem ρ w [] [] (by simp) (by simp)
    | cons x l ih =>
        rcases x with ⟨a, s⟩
        have hcase : a3Positive a ∨ a3Levi a ∨ a3Radical a := by
          exact a3_colour_cases a
        rcases hcase with hp | hl | hr
        · exact positive_inv ρ w weight h a s hp ih
        · exact a3_levi_inv ρ w a s hl ih
        · exact a3_radical_inv ρ w a s hr ih
  · rw [a3LeviSpan, Submodule.span_le]
    rintro z ⟨l, r, _, _, rfl⟩
    exact VOA.DeligneAudit.UnivG.wordOp_mem_cycSubG ρ w (l ++ r)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_cycSubG_eq_leviSpan
