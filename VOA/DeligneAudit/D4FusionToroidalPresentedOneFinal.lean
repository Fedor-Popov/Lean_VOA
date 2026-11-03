import VOA.DeligneAudit.D4FusionToroidalPresentedOneRank

/-! The exact remaining multiplicity-one action identities. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem presentedOne_finiteDimensional : FiniteDimensional ℂ (PTE 1) := by
  letI : FiniteDimensional ℂ OneU := rav_finiteDimensional 1 (by omega)
  exact Module.Finite.equiv presentedOneEquiv.symm

def OneTopLowKilled : Prop :=
  ∀ c : Fin 28,
    (univRepG D4sector.f OneR).op c 0 oneTop = 0 ∧
      (univRepG D4sector.f OneR).op c 1 oneTop = 0

theorem oneTopLineKilled_of_low (h : OneTopLowKilled) : OneTopLineKilled := by
  intro c r
  by_cases hr : 2 ≤ r
  · exact oneTop_killed_high c r hr
  · have hr0 : r = 0 ∨ r = 1 := by omega
    rcases hr0 with rfl | rfl
    · exact (h c).1
    · exact (h c).2

theorem presentedRankBoundE_one (h : OneTopLowKilled) :
    PresentedRankBoundE 1 (le_refl 1) :=
  presentedRankBoundE_one_of_line_killed (oneTopLineKilled_of_low h)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.presentedOne_finiteDimensional
#print axioms VOA.DeligneAudit.Toroidal.oneTopLineKilled_of_low
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_one
