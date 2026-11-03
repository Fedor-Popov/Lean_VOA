import VOA.DeligneAudit.LeviTypeA2CertKeyRel

/-! The canonical Levi-stable closure of a subspace of the current module. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- Span of Levi current words applied to vectors of `S`. -/
def a2LeviClosure (S : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (l : List (Fin 8 × ℕ)) (v : V),
    l.Forall (fun x => a2Levi x.1) ∧ v ∈ S ∧ z = wordOp ρ l v}

theorem a2LeviClosure_contains (S : Submodule ℂ V) :
    S ≤ a2LeviClosure ρ S := by
  intro v hv
  exact Submodule.subset_span ⟨[], v, by simp, hv, rfl⟩

theorem a2LeviClosure_inv (S : Submodule ℂ V)
    (a : Fin 8) (r : ℕ) (ha : a2Levi a) :
    a2LeviClosure ρ S ≤ (a2LeviClosure ρ S).comap (ρ.op a r) := by
  rw [a2LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hl, hv, rfl⟩
  exact Submodule.subset_span
    ⟨(a, r) :: l, v, by simp only [List.forall_cons]; exact ⟨ha, hl⟩, hv, rfl⟩

theorem a2LeviClosure_mono {S T : Submodule ℂ V} (h : S ≤ T) :
    a2LeviClosure ρ S ≤ a2LeviClosure ρ T := by
  apply Submodule.span_mono
  rintro z ⟨l, v, hl, hv, rfl⟩
  exact ⟨l, v, hl, h hv, rfl⟩

theorem a2LeviClosure_idem (S : Submodule ℂ V) :
    a2LeviClosure ρ (a2LeviClosure ρ S) = a2LeviClosure ρ S := by
  apply le_antisymm
  · rw [a2LeviClosure, Submodule.span_le]
    rintro z ⟨l, v, hl, hv, rfl⟩
    have hword : ∀ (xs : List (Fin 8 × ℕ)),
        xs.Forall (fun x => a2Levi x.1) →
        wordOp ρ xs v ∈ a2LeviClosure ρ S := by
      intro xs
      induction xs with
      | nil => intro _; exact hv
      | cons x xs ih =>
          intro hxs
          rcases x with ⟨a, r⟩
          simp only [List.forall_cons] at hxs
          exact a2LeviClosure_inv ρ S a r hxs.1 (ih hxs.2)
    exact hword l hl
  · exact a2LeviClosure_contains ρ _

variable (w : V)

/-- Every radical key vector satisfies the node-two local Weyl relations
modulo the canonical Levi closure of all strictly higher keys. -/
theorem a2_key_local_weyl_levi_quotient (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    A2KeyLocalWeylRelModulo ρ q k
      (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)) v := by
  apply a2_key_local_weyl_rel_mod ρ w p q h k _
    (a2LeviClosure_contains ρ _)
  · intro r a ha
    rcases ha with rfl | rfl | rfl
    · exact a2LeviClosure_inv ρ _ 1 r (Or.inl rfl)
    · exact a2LeviClosure_inv ρ _ 4 r (Or.inr (Or.inl rfl))
    · exact a2LeviClosure_inv ρ _ 7 r (Or.inr (Or.inr (Or.inr rfl)))
  · exact hv

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_contains
#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_inv
#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_mono
#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_idem
#print axioms VOA.DeligneAudit.A3Sector.a2_key_local_weyl_levi_quotient
