import VOA.DeligneAudit.D4LeviRaiseComm

/-! A simple raising current replaces one radical letter and moves to a higher key. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- Lists obtained by one nonzero simple-Levi raising replacement. -/
inductive RaiseReplaces (i : Fin 3) (r : ℕ) :
    List (Fin 6 × ℕ) → List (Fin 6 × ℕ) → Prop
  | head {j s k n l} (h : raiseAction i j = some (k, n)) :
      RaiseReplaces i r ((j, s) :: l) ((k, r + s) :: l)
  | tail {j s l q} (h : RaiseReplaces i r l q) :
      RaiseReplaces i r ((j, s) :: l) ((j, s) :: q)

theorem keyHeight_cons (m : ℕ) (j : Fin 6) (s : ℕ)
    (l : List (Fin 6 × ℕ)) :
    keyHeight m (wordKey ((j, s) :: l)) =
      keyHeight m (wordKey l) + keyHeight 0 (wordKey [(j, 0)]) := by
  fin_cases j <;> simp [wordKey, keyHeight] <;> omega

theorem raise_replaces_height (m : ℕ) (i : Fin 3) (r : ℕ)
    {l q : List (Fin 6 × ℕ)} (h : RaiseReplaces i r l q) :
    keyHeight m (wordKey l) + 2 = keyHeight m (wordKey q) := by
  induction h with
  | head h =>
      conv_lhs => rw [keyHeight_cons]
      conv_rhs => rw [keyHeight_cons]
      have hh := raise_height 0 i _ _ _ h
      omega
  | tail _ ih =>
      conv_lhs => rw [keyHeight_cons]
      conv_rhs => rw [keyHeight_cons]
      omega

theorem raise_replaces_higher (m : ℕ) (i : Fin 3) (r : ℕ)
    {l q : List (Fin 6 × ℕ)} (h : RaiseReplaces i r l q) :
    keyLess m (wordKey l) (wordKey q) := by
  left
  have hh := raise_replaces_height m i r h
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

def raiseWordSpan (i : Fin 3) (r : ℕ)
    (l : List (Fin 6 × ℕ)) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ q, RaiseReplaces i r l q ∧ z = radicalWord ρ w q}

theorem radical_op_raiseWordSpan (i : Fin 3) (r : ℕ)
    (j : Fin 6) (s : ℕ) (l : List (Fin 6 × ℕ))
    {v : V} (hv : v ∈ raiseWordSpan ρ w i r l) :
    ρ.op (radicalColour j) s v ∈
      raiseWordSpan ρ w i r ((j, s) :: l) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, hq, rfl⟩ := hz
      apply Submodule.subset_span
      exact ⟨(j, s) :: q, RaiseReplaces.tail hq, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (raiseWordSpan ρ w i r ((j, s) :: l)).add_mem hx hy
  | smul c x _ hx =>
      simpa using (raiseWordSpan ρ w i r ((j, s) :: l)).smul_mem c hx

theorem simple_raise_word_span
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (l : List (Fin 6 × ℕ)) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r
      (radicalWord ρ w l) ∈ raiseWordSpan ρ w i r l := by
  induction l with
  | nil =>
      have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
        simpa [ravFam] using h
      have he : D4sector.raising
          (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) := by
        change 4 ≤ (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)).val ∧
          (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)).val < 16
        fin_cases i <;> decide
      change ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r w ∈ _
      rw [rs_raising hs he r]
      exact Submodule.zero_mem _
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      let u := radicalWord ρ w l
      have hc := simple_raise_comm ρ i j r s u
      have hfirst : ρ.op (radicalColour j) s
          (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r u) ∈
          raiseWordSpan ρ w i r ((j, s) :: l) :=
        radical_op_raiseWordSpan ρ w i r j s l ih
      have hsecond :
          (match raiseAction i j with
          | none => (0 : V)
          | some (k, n) => (n : ℂ) • ρ.op (radicalColour k) (r + s) u) ∈
            raiseWordSpan ρ w i r ((j, s) :: l) := by
        cases ha : raiseAction i j with
        | none => exact Submodule.zero_mem _
        | some p =>
            rcases p with ⟨k, n⟩
            apply (raiseWordSpan ρ w i r ((j, s) :: l)).smul_mem
            apply Submodule.subset_span
            exact ⟨(k, r + s) :: l, RaiseReplaces.head ha, rfl⟩
      change ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r
        (ρ.op (radicalColour j) s u) ∈ _
      rw [sub_eq_iff_eq_add.mp hc]
      exact (raiseWordSpan ρ w i r ((j, s) :: l)).add_mem hsecond hfirst

theorem raiseWordSpan_le_higher (i : Fin 3) (r : ℕ)
    (l : List (Fin 6 × ℕ)) :
    raiseWordSpan ρ w i r l ≤ higherOrbit ρ w m (wordKey l) := by
  rw [raiseWordSpan, Submodule.span_le]
  rintro z ⟨q, hq, rfl⟩
  apply keyOrbit_le_higher ρ w m (wordKey l) (wordKey q)
    (raise_replaces_higher m i r hq)
  exact keyLayer_le_orbit ρ w (wordKey q) (radicalWord_mem_key ρ w q)

theorem simple_raise_word_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (l : List (Fin 6 × ℕ)) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r
      (radicalWord ρ w l) ∈ higherOrbit ρ w m (wordKey l) :=
  raiseWordSpan_le_higher ρ w m i r l (simple_raise_word_span ρ w m h i r l)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyHeight_cons
#print axioms VOA.DeligneAudit.D4Levi.raise_replaces_height
#print axioms VOA.DeligneAudit.D4Levi.raise_replaces_higher
#print axioms VOA.DeligneAudit.D4Levi.radical_op_raiseWordSpan
#print axioms VOA.DeligneAudit.D4Levi.simple_raise_word_span
#print axioms VOA.DeligneAudit.D4Levi.raiseWordSpan_le_higher
#print axioms VOA.DeligneAudit.D4Levi.simple_raise_word_higher
