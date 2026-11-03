import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanCenter

/-! The highest-root mode-one fusion actions follow from the Garland relations. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem twoGen_one_theta_fusion :
    twoCurrent.op D4sector.c₀ 1 (twoGen 1) = 0 := by
  have hz : (ρPTE 2).op D4sector.c₀ 1 2 (pTE 2) = 0 := by
    rw [(ρPTE 2).high_zero D4sector.c₀ 1 2 (by omega)]
    rfl
  have h := two_garland_one_zero 2 (by omega)
  simpa [Psym_one, Finset.antidiagonal, twoCurrent, twoGen, hz,
    (ρPTE 2).high_zero D4sector.c₀ 0 2 (by omega)] using h

theorem twoGen_zero_theta_fusion_mem :
    twoCurrent.op D4sector.c₀ 1 (twoGen 0) ∈ twoM 1 := by
  have hp :
      (ρPTE 2).op D4sector.c₀ 0 0 (twoGen 1) +
        (ρPTE 2).op D4sector.c₀ 0 1 (twoGen 0) = 0 := by
    simpa [Psym_one, Finset.antidiagonal, twoGen] using
      two_garland_one_zero 1 (by omega)
  have hleft : (ρPTE 2).op D4sector.c₀ 0 0 (twoGen 1) ∈ twoM 1 :=
    twoM_op_zero 1 D4sector.c₀ 0 (twoM_word 1 [] rfl)
  have hright : (ρPTE 2).op D4sector.c₀ 0 1 (twoGen 0) ∈ twoM 1 := by
    have heq := eq_neg_of_add_eq_zero_right hp
    rw [heq]
    exact Submodule.neg_mem _ hleft
  simpa [twoCurrent] using hright

theorem twoOne_theta_fusion :
    twoOneCurrent.op D4sector.c₀ 1 twoOneGen = 0 := by
  change (twoM 1).mkQ (twoCurrent.op D4sector.c₀ 1 (twoGen 0)) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    twoGen_zero_theta_fusion_mem

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_theta_fusion
#print axioms VOA.DeligneAudit.Toroidal.twoGen_zero_theta_fusion_mem
#print axioms VOA.DeligneAudit.Toroidal.twoOne_theta_fusion
