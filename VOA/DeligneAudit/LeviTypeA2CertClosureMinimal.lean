import VOA.DeligneAudit.LeviTypeA2CertSl2OtherKey

/-! Minimality of the canonical Levi closure. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- Any Levi-stable submodule containing `S` contains its Levi closure. -/
theorem a2LeviClosure_le_of_inv (S T : Submodule ℂ V)
    (hST : S ≤ T)
    (hT : ∀ (a : Fin 8) (r : ℕ), a2Levi a →
      T ≤ T.comap (ρ.op a r)) :
    a2LeviClosure ρ S ≤ T := by
  rw [a2LeviClosure, Submodule.span_le]
  rintro z ⟨l, v, hl, hv, rfl⟩
  induction l with
  | nil => exact hST hv
  | cons x l ih =>
      rcases x with ⟨a, r⟩
      simp only [List.forall_cons] at hl
      exact hT a r hl.1 (ih hl.2)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_le_of_inv
