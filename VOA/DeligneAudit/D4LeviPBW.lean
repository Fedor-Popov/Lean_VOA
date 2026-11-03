import VOA.DeligneAudit.D4LeviPBWTable

/-! PBW straightening for the gl4 Levi and its six-letter negative radical. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.Sparse

def IsLevi (a : Fin 28) : Prop := ∃ i : Fin 16, leviIndex i = a
def IsRadical (a : Fin 28) : Prop := ∃ i : Fin 6, radicalColour i = a
def IsPositive (a : Fin 28) : Prop := ∃ i : Fin 6, positiveColour i = a

theorem every_colour (a : Fin 28) : IsPositive a ∨ IsLevi a ∨ IsRadical a :=
  colour_cases a

theorem levi_radical_zero (a b c : Fin 28) (ha : IsLevi a)
    (hb : IsRadical b) (hc : ¬ IsRadical c) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 a b c = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hno : ∀ k : Fin 6, radicalColour k ≠ c := fun k hk => hc ⟨k, hk⟩
  have h := levi_radical_closed i j c hno
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, h]

theorem radical_levi_zero (a b c : Fin 28) (ha : IsRadical a)
    (hb : IsLevi b) (hc : ¬ IsRadical c) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 a b c = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hno : ∀ k : Fin 6, radicalColour k ≠ c := fun k hk => hc ⟨k, hk⟩
  have h := radical_levi_closed i j c hno
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, h]

theorem positive_radical_zero (a b c : Fin 28) (ha : IsPositive a)
    (hb : IsRadical b) (hc : ¬ IsLevi c) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 a b c = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hno : ∀ k : Fin 16, leviIndex k ≠ c := fun k hk => hc ⟨k, hk⟩
  have h := positive_radical_closed i j c hno
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, h]

theorem positive_levi_zero (a b c : Fin 28) (ha : IsPositive a)
    (hb : IsLevi b) (hc : ¬ IsPositive c) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 a b c = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hno : ∀ k : Fin 6, positiveColour k ≠ c := fun k hk => hc ⟨k, hk⟩
  have h := positive_levi_closed i j c hno
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, h]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.fD4 V) (w : V)

/-- Levi words applied to radical words on the generator. -/
def leviSpan : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l r : List (Fin 28 × ℕ),
    l.Forall (fun x => IsLevi x.1) ∧
    r.Forall (fun x => IsRadical x.1) ∧ z = wordOp ρ (l ++ r) w}

theorem normal_mem (l r : List (Fin 28 × ℕ))
    (hl : l.Forall (fun x => IsLevi x.1))
    (hr : r.Forall (fun x => IsRadical x.1)) :
    wordOp ρ (l ++ r) w ∈ leviSpan ρ w :=
  Submodule.subset_span ⟨l, r, hl, hr, rfl⟩

theorem levi_inv (a : Fin 28) (s : ℕ) (ha : IsLevi a)
    {v : V} (hv : v ∈ leviSpan ρ w) : ρ.op a s v ∈ leviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact normal_mem ρ w ((a, s) :: l) r
        (by simp only [List.forall_cons]; exact ⟨ha, hl⟩) hr
  | zero => simp
  | add x y _ _ hx hy => simpa using (leviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (leviSpan ρ w).smul_mem c hx

theorem swap_mem (a b : Fin 28) (s t : ℕ) (v : V)
    (hleft : ρ.op b t (ρ.op a s v) ∈ leviSpan ρ w)
    (hbr : ∀ c, VOA.DeligneAudit.DeligneSector.D4.fD4 a b c ≠ 0 →
      ρ.op c (s + t) v ∈ leviSpan ρ w) :
    ρ.op a s (ρ.op b t v) ∈ leviSpan ρ w := by
  have hsum : (∑ c : Fin 28,
      VOA.DeligneAudit.DeligneSector.D4.fD4 a b c • ρ.op c (s + t) v) ∈
      leviSpan ρ w := by
    apply Submodule.sum_mem
    intro c _
    by_cases hc : VOA.DeligneAudit.DeligneSector.D4.fD4 a b c = 0
    · simp [hc]
    · exact (leviSpan ρ w).smul_mem _ (hbr c hc)
  have h := ρ.comm a b s t v
  have heq : ρ.op a s (ρ.op b t v) =
      ρ.op b t (ρ.op a s v) +
        ∑ c : Fin 28, VOA.DeligneAudit.DeligneSector.D4.fD4 a b c •
          ρ.op c (s + t) v := by
    calc
      _ = (ρ.op a s (ρ.op b t v) - ρ.op b t (ρ.op a s v)) +
            ρ.op b t (ρ.op a s v) := (sub_add_cancel _ _).symm
      _ = (∑ c : Fin 28, VOA.DeligneAudit.DeligneSector.D4.fD4 a b c •
            ρ.op c (s + t) v) + ρ.op b t (ρ.op a s v) := by rw [h]
      _ = _ := add_comm _ _
  rw [heq]
  exact (leviSpan ρ w).add_mem hleft hsum

private theorem radical_on_normal : ∀ (l r : List (Fin 28 × ℕ)),
    l.Forall (fun x => IsLevi x.1) → r.Forall (fun x => IsRadical x.1) →
    ∀ (a : Fin 28) (s : ℕ), IsRadical a →
      ρ.op a s (wordOp ρ (l ++ r) w) ∈ leviSpan ρ w := by
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
      apply swap_mem ρ w a b s t (wordOp ρ (l ++ r) w)
      · exact levi_inv ρ w b t hl.1 (ih r hl.2 hr a s ha)
      · intro c hc
        have hrad : IsRadical c := by
          by_contra hn
          exact hc (radical_levi_zero a b c ha hl.1 hn)
        exact ih r hl.2 hr c (s + t) hrad

theorem radical_inv (a : Fin 28) (s : ℕ) (ha : IsRadical a)
    {v : V} (hv : v ∈ leviSpan ρ w) : ρ.op a s v ∈ leviSpan ρ w := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, r, hl, hr, rfl⟩ := hz
      exact radical_on_normal ρ w l r hl hr a s ha
  | zero => simp
  | add x y _ _ hx hy => simpa using (leviSpan ρ w).add_mem hx hy
  | smul c x _ hx => simpa using (leviSpan ρ w).smul_mem c hx

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.every_colour
#print axioms VOA.DeligneAudit.D4Levi.levi_radical_zero
#print axioms VOA.DeligneAudit.D4Levi.radical_levi_zero
#print axioms VOA.DeligneAudit.D4Levi.positive_radical_zero
#print axioms VOA.DeligneAudit.D4Levi.positive_levi_zero
#print axioms VOA.DeligneAudit.D4Levi.normal_mem
#print axioms VOA.DeligneAudit.D4Levi.levi_inv
#print axioms VOA.DeligneAudit.D4Levi.swap_mem
#print axioms VOA.DeligneAudit.D4Levi.radical_inv
