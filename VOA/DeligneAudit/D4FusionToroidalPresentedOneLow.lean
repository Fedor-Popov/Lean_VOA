import VOA.DeligneAudit.D4FusionToroidalPresentedOneLowTheta
import VOA.DeligneAudit.D4FusionToroidalPresentedOneLowRoots

/-! The unconditional multiplicity-one low-mode relations and rank bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.DeligneSector.D4 VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem oneTopLowKilled : OneTopLowKilled := by
  intro c
  constructor
  · by_cases h4 : c.val < 4
    · exact one_top_mode_zero_cartan c h4
    by_cases h16 : c.val < 16
    · exact one_top_mode_zero_raising c ⟨by omega, h16⟩
    obtain ⟨i, hi⟩ := negativeIndex_covers c (by omega)
    simpa only [hi] using one_top_mode_zero_lowering i
  · by_cases hc : c = D4sector.c₀
    · subst c
      exact one_top_mode_one_theta
    · exact one_top_mode_one_other c hc

theorem presentedRankBoundE_one' : PresentedRankBoundE 1 (le_refl 1) :=
  presentedRankBoundE_one oneTopLowKilled

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.oneTopLowKilled
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_one'
