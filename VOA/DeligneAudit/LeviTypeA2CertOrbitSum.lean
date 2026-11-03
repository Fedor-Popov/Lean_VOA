import VOA.DeligneAudit.LeviTypeA2CertBasisLifts

/-! Levi closure commutes with an arbitrary sum of submodules. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

theorem a2LeviClosure_iSup {ι : Sort*} (S : ι → Submodule ℂ V) :
    a2LeviClosure ρ (⨆ j, S j) = ⨆ j, a2LeviClosure ρ (S j) := by
  apply le_antisymm
  · apply a2LeviClosure_le_of_inv ρ _ _
    · apply iSup_le
      intro j
      exact (a2LeviClosure_contains ρ (S j)).trans
        (le_iSup (fun j => a2LeviClosure ρ (S j)) j)
    · intro a r ha x hx
      refine Submodule.iSup_induction
        (p := fun j => a2LeviClosure ρ (S j))
        (motive := fun x => ρ.op a r x ∈ ⨆ j, a2LeviClosure ρ (S j))
        hx ?_ ?_ ?_
      · intro j x hxj
        exact (le_iSup (fun j => a2LeviClosure ρ (S j)) j)
          (a2LeviClosure_inv ρ (S j) a r ha hxj)
      · simp
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  · apply iSup_le
    intro j
    exact a2LeviClosure_mono ρ
      (le_iSup (fun j => S j) j)

theorem a2LeviClosure_span_range {ι : Type*} (v : ι → V) :
    a2LeviClosure ρ (Submodule.span ℂ (Set.range v)) =
      ⨆ j, a2LeviClosure ρ (ℂ ∙ v j) := by
  rw [Submodule.span_range_eq_iSup, a2LeviClosure_iSup]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_iSup
#print axioms VOA.DeligneAudit.A3Sector.a2LeviClosure_span_range
