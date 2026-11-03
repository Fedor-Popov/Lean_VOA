import VOA.DeligneAudit.LeviTypeA2CertPBW

/-! Levi generation of an arbitrary cyclic local Weyl module for `sl₃[t]`. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The span of Levi words applied to negative radical words on `w`. -/
def a2LeviSpan : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l r : List (Fin 8 × ℕ),
    l.Forall (fun x => a2Levi x.1) ∧
    r.Forall (fun x => a2Radical x.1) ∧ z = wordOp ρ (l ++ r) w}

theorem normal_mem (l r : List (Fin 8 × ℕ))
    (hl : l.Forall (fun x => a2Levi x.1))
    (hr : r.Forall (fun x => a2Radical x.1)) :
    wordOp ρ (l ++ r) w ∈ a2LeviSpan ρ w :=
  Submodule.subset_span ⟨l, r, hl, hr, rfl⟩

theorem levi_inv (a : Fin 8) (s : ℕ) (ha : a2Levi a)
    {v : V} (hv : v ∈ a2LeviSpan ρ w) :
    ρ.op a s v ∈ a2LeviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact normal_mem ρ w ((a, s) :: l) r
        (by simp only [List.forall_cons]; exact ⟨ha, hl⟩) hr
  | zero => simp
  | add x y _ _ hx hy => simpa using (a2LeviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (a2LeviSpan ρ w).smul_mem c hx

theorem swap_mem (a b : Fin 8) (s t : ℕ) (v : V)
    (hleft : ρ.op b t (ρ.op a s v) ∈ a2LeviSpan ρ w)
    (hbr : ∀ c, VOA.AffineSl3.bracketTable a b c ≠ 0 →
      ρ.op c (s + t) v ∈ a2LeviSpan ρ w) :
    ρ.op a s (ρ.op b t v) ∈ a2LeviSpan ρ w := by
  have hsum : (∑ c : Fin 8,
      VOA.AffineSl3.bracketTable a b c • ρ.op c (s + t) v) ∈
      a2LeviSpan ρ w := by
    apply Submodule.sum_mem
    intro c _
    by_cases hc : VOA.AffineSl3.bracketTable a b c = 0
    · simp [hc]
    · exact (a2LeviSpan ρ w).smul_mem _ (hbr c hc)
  have h := ρ.comm a b s t v
  have heq : ρ.op a s (ρ.op b t v) =
      ρ.op b t (ρ.op a s v) +
        ∑ c : Fin 8, VOA.AffineSl3.bracketTable a b c • ρ.op c (s + t) v := by
    calc
      _ = (ρ.op a s (ρ.op b t v) - ρ.op b t (ρ.op a s v)) +
          ρ.op b t (ρ.op a s v) := (sub_add_cancel _ _).symm
      _ = (∑ c : Fin 8, VOA.AffineSl3.bracketTable a b c •
          ρ.op c (s + t) v) + ρ.op b t (ρ.op a s v) := by rw [h]
      _ = _ := add_comm _ _
  rw [heq]
  exact (a2LeviSpan ρ w).add_mem hleft hsum

private theorem radical_on_normal : ∀ (l r : List (Fin 8 × ℕ)),
    l.Forall (fun x => a2Levi x.1) →
    r.Forall (fun x => a2Radical x.1) →
    ∀ (a : Fin 8) (s : ℕ), a2Radical a →
      ρ.op a s (wordOp ρ (l ++ r) w) ∈ a2LeviSpan ρ w := by
  intro l
  induction l with
  | nil =>
      intro r _ hr a s ha
      exact normal_mem ρ w [] ((a, s) :: r) (by simp)
        (by simp only [List.forall_cons]; exact ⟨ha, hr⟩)
  | cons x l ih =>
      intro r hl hr a s ha
      rcases x with ⟨b, t⟩
      simp only [List.forall_cons] at hl
      have hb := hl.1
      have htail := hl.2
      apply swap_mem ρ w a b s t (wordOp ρ (l ++ r) w)
      · exact levi_inv ρ w b t hb (ih r htail hr a s ha)
      · intro c hc
        have hrad : a2Radical c := by
          by_contra hn
          exact hc (a2_radical_levi_bracket a b c ha hb hn)
        exact ih r htail hr c (s + t) hrad

theorem radical_inv (a : Fin 8) (s : ℕ) (ha : a2Radical a)
    {v : V} (hv : v ∈ a2LeviSpan ρ w) :
    ρ.op a s v ∈ a2LeviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact radical_on_normal ρ w l r hl hr a s ha
  | zero => simp
  | add x y _ _ hx hy => simpa using (a2LeviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (a2LeviSpan ρ w).smul_mem c hx

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.levi_inv
#print axioms VOA.DeligneAudit.A3Sector.swap_mem
#print axioms VOA.DeligneAudit.A3Sector.radical_inv
