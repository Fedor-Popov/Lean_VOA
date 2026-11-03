import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedFusion
import VOA.DeligneAudit.D4FusionToroidalPresentedTwoFinal

/-! All low zero-degree letters kill the quadratic toroidal seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_seed_low_zero (c : Fin 28) (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op c 0 s twoQuadraticSeed = 0 := by
  by_cases hc4 : c.val < 4
  · exact two_seed_cartan_zero c hc4 s hs
  by_cases hc16 : c.val < 16
  · exact two_seed_raising_zero c ⟨by omega, hc16⟩ s hs
  exact two_seed_all_negative_zero s hs c (by omega)

theorem twoSeedLowStability : TwoSeedLowStability := by
  intro c s hs
  rw [two_seed_low_zero c s hs]
  exact Submodule.zero_mem _

theorem presentedRankBoundE_two_of_span (h : TwoPositiveSpanBound) :
    PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of_low_stability h twoSeedLowStability

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_low_zero
#print axioms VOA.DeligneAudit.Toroidal.twoSeedLowStability
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of_span
