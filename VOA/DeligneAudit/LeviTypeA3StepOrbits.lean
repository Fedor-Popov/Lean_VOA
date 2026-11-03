import VOA.DeligneAudit.LeviTypeA3OrbitSum

/-! Each filtration step is spanned by Levi orbits of quotient basis lifts. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem a3_step_orbits_of_closed (F S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (hF : a3LeviClosure ρ F = F) :
    ∃ v : Fin (Module.finrank ℂ (S ⧸ F.comap S.subtype)) → S,
      F ⊔ a3LeviClosure ρ S =
        F ⊔ ⨆ j, a3LeviClosure ρ (ℂ ∙ (v j : V)) := by
  obtain ⟨v, hv⟩ := a3_keyQuot_basis_lifts F S
  refine ⟨v, ?_⟩
  apply le_antisymm
  · apply sup_le le_sup_left
    calc
      a3LeviClosure ρ S ≤
          a3LeviClosure ρ
            (F ⊔ Submodule.span ℂ (Set.range fun j => (v j : V))) :=
        a3LeviClosure_mono ρ hv
      _ = F ⊔ ⨆ j, a3LeviClosure ρ (ℂ ∙ (v j : V)) := by
        rw [a3LeviClosure_sup, hF, a3LeviClosure_span_range]
  · apply sup_le le_sup_left
    apply iSup_le
    intro j
    have hj : ℂ ∙ (v j : V) ≤ S := by
      rw [Submodule.span_le]
      intro x hx
      have heq : x = (v j : V) := Set.mem_singleton_iff.mp hx
      subst x
      exact (v j).property
    exact (a3LeviClosure_mono ρ hj).trans le_sup_right

variable (w : V)

theorem a3KeyPrefix_step_orbits {n i : ℕ} (hi : i < n)
    (k : Fin n → A3RadicalKey) (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    let F := a3KeyPrefix ρ w k i
    let S := a3KeyLayer ρ w (k ⟨i, hi⟩)
    ∃ v : Fin (Module.finrank ℂ (S ⧸ F.comap S.subtype)) → S,
      a3KeyPrefix ρ w k (i + 1) =
        F ⊔ ⨆ j, a3LeviClosure ρ (ℂ ∙ (v j : V)) := by
  let F := a3KeyPrefix ρ w k i
  let S := a3KeyLayer ρ w (k ⟨i, hi⟩)
  letI : FiniteDimensional ℂ S := a3KeyLayer_finite ρ w a b c _ h
  have hclosed : a3LeviClosure ρ F = F := a3LeviClosure_idem ρ _
  obtain ⟨v, hv⟩ := a3_step_orbits_of_closed ρ F S hclosed
  refine ⟨v, ?_⟩
  rw [a3KeyPrefix_step ρ w hi k]
  exact hv

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_step_orbits_of_closed
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefix_step_orbits
