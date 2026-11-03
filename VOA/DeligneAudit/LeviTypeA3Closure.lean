import VOA.DeligneAudit.LeviTypeA3Table

/-! The stable closure under the eight-colour `sl₃` Levi current algebra. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

/-- Span of embedded `sl₃[t]` words applied to vectors of `S`. -/
def a3LeviClosure (S : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (l : List (Fin 8 × ℕ)) (v : V),
    v ∈ S ∧ z = wordOp ρ (l.map (fun x => (a3LeviColour x.1, x.2))) v}

theorem a3LeviClosure_contains (S : Submodule ℂ V) :
    S ≤ a3LeviClosure ρ S := by
  intro v hv
  exact Submodule.subset_span ⟨[], v, hv, rfl⟩

theorem a3LeviClosure_inv (S : Submodule ℂ V) (a : Fin 8) (r : ℕ) :
    a3LeviClosure ρ S ≤
      (a3LeviClosure ρ S).comap (ρ.op (a3LeviColour a) r) := by
  rw [a3LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hv, rfl⟩
  exact Submodule.subset_span ⟨(a, r) :: l, v, hv, rfl⟩

theorem a3LeviClosure_mono {S T : Submodule ℂ V} (h : S ≤ T) :
    a3LeviClosure ρ S ≤ a3LeviClosure ρ T := by
  apply Submodule.span_mono
  rintro z ⟨l, v, hv, rfl⟩
  exact ⟨l, v, h hv, rfl⟩

theorem a3LeviClosure_le_of_inv (S T : Submodule ℂ V)
    (hS : S ≤ T)
    (hT : ∀ a r, T ≤ T.comap (ρ.op (a3LeviColour a) r)) :
    a3LeviClosure ρ S ≤ T := by
  rw [a3LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hv, rfl⟩
  have hword : ∀ xs : List (Fin 8 × ℕ),
      wordOp ρ (xs.map (fun x => (a3LeviColour x.1, x.2))) v ∈ T := by
    intro xs
    induction xs with
    | nil => exact hS hv
    | cons x xs ih =>
        rcases x with ⟨a, r⟩
        exact hT a r ih
  exact hword l

theorem a3LeviClosure_idem (S : Submodule ℂ V) :
    a3LeviClosure ρ (a3LeviClosure ρ S) = a3LeviClosure ρ S := by
  apply le_antisymm
  · exact a3LeviClosure_le_of_inv ρ _ _ le_rfl
      (fun a r => a3LeviClosure_inv ρ S a r)
  · exact a3LeviClosure_contains ρ _

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_contains
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_inv
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_mono
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_le_of_inv
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_idem
