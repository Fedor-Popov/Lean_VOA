import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerCube

/-! The precise remaining seed facts for the presented multiplicity-two bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def TwoSeedStability : Prop :=
  ∀ (c : Fin 28) (s : ℕ),
    (ρPTE 2).op c 0 s twoQuadraticSeed ∈
      Submodule.span ℂ {twoQuadraticSeed}

def TwoSeedLowStability : Prop :=
  ∀ (c : Fin 28) (s : ℕ), s ≤ 1 →
    (ρPTE 2).op c 0 s twoQuadraticSeed ∈
      Submodule.span ℂ {twoQuadraticSeed}

theorem twoSeedStability_of_low (h : TwoSeedLowStability) :
    TwoSeedStability := by
  intro c s
  by_cases hs : s ≤ 1
  · exact h c s hs
  have hs' : 2 ≤ s := by omega
  rw [(ρPTE 2).high_zero c 0 s hs']
  exact Submodule.zero_mem _

theorem twoUTwoCollapse_of_seed_stability
    (hs : TwoSeedStability) : TwoUTwoCollapse :=
  twoUTwoCollapse_of_stability hs (two_g0_cube_zero_of_stability hs)

theorem two_second_layer_bound_of_seed_stability
    (hs : TwoSeedStability) :
    FiniteDimensional ℂ twoN2inN1 ∧ Module.finrank ℂ twoN2inN1 ≤ 1 :=
  two_second_layer_bound_of_collapse (twoUTwoCollapse_of_seed_stability hs)

theorem presentedRankBoundE_two_of_seed_stability
    (h : TwoPositiveSpanBound) (hs : TwoSeedStability) :
    PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of' h (twoUTwoCollapse_of_seed_stability hs)

theorem presentedRankBoundE_two_of_low_stability
    (h : TwoPositiveSpanBound) (hs : TwoSeedLowStability) :
    PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of_seed_stability h (twoSeedStability_of_low hs)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoUTwoCollapse_of_seed_stability
#print axioms VOA.DeligneAudit.Toroidal.twoSeedStability_of_low
#print axioms VOA.DeligneAudit.Toroidal.two_second_layer_bound_of_seed_stability
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of_seed_stability
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of_low_stability
