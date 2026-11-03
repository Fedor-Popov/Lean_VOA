import VOA.DeligneAudit.LeviTypeA3ExtraCartanPositive

/-! Stability of the eight-colour Levi closure under the remaining Cartan current. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem a3_extra_bracket_outside (i : Fin 8) (c : Fin 15)
    (hc : c ∉ Set.range a3LeviColour) :
    bracketTable 12 (a3LeviColour i) c = 0 := by
  have hz : bracketInt 12 (a3LeviColour i) c = 0 := by
    fin_cases c
    all_goals
      first
      | exact False.elim (hc ⟨0, rfl⟩)
      | exact False.elim (hc ⟨1, rfl⟩)
      | exact False.elim (hc ⟨2, rfl⟩)
      | exact False.elim (hc ⟨3, rfl⟩)
      | exact False.elim (hc ⟨4, rfl⟩)
      | exact False.elim (hc ⟨5, rfl⟩)
      | exact False.elim (hc ⟨6, rfl⟩)
      | exact False.elim (hc ⟨7, rfl⟩)
      | fin_cases i <;> decide
  simp [bracketTable, hz]

private theorem extra_comm_sum_mem (S : Submodule ℂ V)
    (i : Fin 8) (r s : ℕ) {v : V}
    (hv : v ∈ a3LeviClosure ρ S) :
    (∑ c : Fin 15,
      bracketTable 12 (a3LeviColour i) c • ρ.op c (r + s) v) ∈
        a3LeviClosure ρ S := by
  apply Submodule.sum_mem
  intro c _
  by_cases hc : c ∈ Set.range a3LeviColour
  · obtain ⟨j, rfl⟩ := hc
    exact (a3LeviClosure ρ S).smul_mem _
      (a3LeviClosure_inv ρ S j (r + s) hv)
  · simp [a3_extra_bracket_outside i c hc]

theorem a3LeviClosure_extra_inv (S : Submodule ℂ V)
    (hS : ∀ r, S ≤ S.comap (ρ.op 12 r)) (r : ℕ) :
    a3LeviClosure ρ S ≤ (a3LeviClosure ρ S).comap (ρ.op 12 r) := by
  rw [a3LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hv, rfl⟩
  have hword : ∀ xs : List (Fin 8 × ℕ),
      ρ.op 12 r
        (wordOp ρ (xs.map fun x => (a3LeviColour x.1, x.2)) v) ∈
          a3LeviClosure ρ S := by
    intro xs
    induction xs with
    | nil =>
        exact a3LeviClosure_contains ρ S (hS r hv)
    | cons x xs ih =>
        rcases x with ⟨i, s⟩
        let u := wordOp ρ (xs.map fun x => (a3LeviColour x.1, x.2)) v
        have hu : u ∈ a3LeviClosure ρ S :=
          Submodule.subset_span ⟨xs, v, hv, rfl⟩
        have hcomm := ρ.comm 12 (a3LeviColour i) r s u
        have hsum := extra_comm_sum_mem ρ S i r s hu
        have hfirst := a3LeviClosure_inv ρ S i s ih
        change ρ.op 12 r (ρ.op (a3LeviColour i) s u) ∈ _
        rw [sub_eq_iff_eq_add.mp hcomm]
        exact (a3LeviClosure ρ S).add_mem hsum hfirst
  exact hword l

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_extra_bracket_outside
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_extra_inv
