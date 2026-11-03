import VOA.DeligneAudit.LeviTypeA3BasisLifts

/-! Levi closure commutes with sums of submodules. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem a3LeviClosure_iSup {ι : Sort*} (S : ι → Submodule ℂ V) :
    a3LeviClosure ρ (⨆ j, S j) = ⨆ j, a3LeviClosure ρ (S j) := by
  apply le_antisymm
  · apply a3LeviClosure_le_of_inv ρ _ _
    · apply iSup_le
      intro j
      exact (a3LeviClosure_contains ρ (S j)).trans
        (le_iSup (fun j => a3LeviClosure ρ (S j)) j)
    · intro a r x hx
      refine Submodule.iSup_induction
        (p := fun j => a3LeviClosure ρ (S j))
        (motive := fun x => ρ.op (a3LeviColour a) r x ∈
          ⨆ j, a3LeviClosure ρ (S j))
        hx ?_ ?_ ?_
      · intro j x hxj
        exact (le_iSup (fun j => a3LeviClosure ρ (S j)) j)
          (a3LeviClosure_inv ρ (S j) a r hxj)
      · simp
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  · apply iSup_le
    intro j
    exact a3LeviClosure_mono ρ (le_iSup (fun j => S j) j)

theorem a3LeviClosure_span_range {ι : Type*} (v : ι → V) :
    a3LeviClosure ρ (Submodule.span ℂ (Set.range v)) =
      ⨆ j, a3LeviClosure ρ (ℂ ∙ v j) := by
  rw [Submodule.span_range_eq_iSup, a3LeviClosure_iSup]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_iSup
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosure_span_range
