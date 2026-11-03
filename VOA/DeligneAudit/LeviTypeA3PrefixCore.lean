import VOA.DeligneAudit.LeviTypeA3OrbitRank

/-! Elementary algebra of the Levi closure. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem a3LeviClosure_bot :
    a3LeviClosure ρ (⊥ : Submodule ℂ V) = ⊥ := by
  apply le_antisymm
  · apply a3LeviClosure_le_of_inv ρ ⊥ ⊥ le_rfl
    intro a r
    exact bot_le
  · exact bot_le

theorem a3LeviClosure_sup (S T : Submodule ℂ V) :
    a3LeviClosure ρ (S ⊔ T) =
      a3LeviClosure ρ S ⊔ a3LeviClosure ρ T := by
  apply le_antisymm
  · apply a3LeviClosure_le_of_inv ρ (S ⊔ T) _
    · exact sup_le_sup
        (a3LeviClosure_contains ρ S) (a3LeviClosure_contains ρ T)
    · intro a r x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr
        ⟨ρ.op (a3LeviColour a) r u, a3LeviClosure_inv ρ S a r hu,
          ρ.op (a3LeviColour a) r v, a3LeviClosure_inv ρ T a r hv,
          by simp⟩
  · exact sup_le
      (a3LeviClosure_mono ρ le_sup_left)
      (a3LeviClosure_mono ρ le_sup_right)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_bot
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_sup
