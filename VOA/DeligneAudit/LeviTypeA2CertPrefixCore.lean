import VOA.DeligneAudit.LeviTypeA2CertFiltration

/-! Levi closure distributes over joins of radical key spaces. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

theorem a2LeviClosure_bot :
    a2LeviClosure ρ (⊥ : Submodule ℂ V) = ⊥ := by
  apply le_antisymm
  · apply a2LeviClosure_le_of_inv ρ ⊥ ⊥ le_rfl
    intro a r _
    exact bot_le
  · exact bot_le

theorem a2LeviClosure_sup (S T : Submodule ℂ V) :
    a2LeviClosure ρ (S ⊔ T) =
      a2LeviClosure ρ S ⊔ a2LeviClosure ρ T := by
  apply le_antisymm
  · apply a2LeviClosure_le_of_inv ρ (S ⊔ T) _
    · exact sup_le_sup
        (a2LeviClosure_contains ρ S) (a2LeviClosure_contains ρ T)
    · intro a r ha x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr
        ⟨ρ.op a r u, a2LeviClosure_inv ρ S a r ha hu,
          ρ.op a r v, a2LeviClosure_inv ρ T a r ha hv, by simp⟩
  · exact sup_le
      (a2LeviClosure_mono ρ le_sup_left)
      (a2LeviClosure_mono ρ le_sup_right)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_bot
#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_sup
