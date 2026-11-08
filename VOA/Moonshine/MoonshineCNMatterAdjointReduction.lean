import VOA.Moonshine.MoonshineCNGeneratorPrimary

/-! The generator adjoints imply the desired Lie invariance once the actual
opposite iterate identity is proved. That identity is the sole residual hypothesis. -/

namespace VOA.Moonshine.ConwayNorton

open AutMonster IntegralLattice LatGen
open scoped TensorProduct BigOperators

theorem moonshineMatterOppositeModes_charge_adjoint (α : lorentzianLattice.carrier)
    (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm (mode (moonshineMatterNearVOA.Y
      (VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice α)) n x) y =
      moonshineMatterForm x (moonshineMatterOppositeModes n
        (VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice α) y) := by
  have hz : moonshineMatterNearVOA.L 1
      (VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice α) = 0 := by
    have h := moonshineMatterLatticeVirasoroOne_pow (latChargeGen lorentzianLattice α) 1
    simp only [pow_one] at h
    rw [h]
    change VnatVOA.vacuum ⊗ₜ[ℂ] (mode (frameStateField lorentzianComplexFrame
      lorentzian_even (latticeConformalVector lorentzianLattice)) (1 + 1) _) = 0
    rw [mode_frameStateField_omega_eq_frameVirasoroMode,
      frameChargeState_virasoroOne lorentzianComplexFrame lorentzian_even,
      TensorProduct.tmul_zero]
  rw [moonshineMatterOppositeModes,
    moonshineMatterNearVOA.oppositeModes_homogeneous _
      (moonshineMatterLatticeGenerator_mem_weight (chargeState_mem_latticeWeight _ α)),
    moonshineMatterNearVOA.oppositeModeAtWeight_primary _ _ hz,
    LinearMap.smul_apply, map_smul]
  exact moonshineMatterForm_chargeGenerator_adjoint α n x y

theorem moonshineMatterOppositeModes_current_adjoint (a : Fin (rank lorentzianLattice))
    (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm (mode (moonshineMatterNearVOA.Y
      (VnatVOA.vacuum ⊗ₜ[ℂ] frameWordState lorentzianLattice [(0, a)] 0)) n x) y =
      moonshineMatterForm x (moonshineMatterOppositeModes n
        (VnatVOA.vacuum ⊗ₜ[ℂ] frameWordState lorentzianLattice [(0, a)] 0) y) := by
  have hz : moonshineMatterNearVOA.L 1
      (VnatVOA.vacuum ⊗ₜ[ℂ] frameWordState lorentzianLattice [(0, a)] 0) = 0 := by
    have h := moonshineMatterLatticeVirasoroOne_pow
      (frameWordState lorentzianLattice [(0, a)] 0) 1
    simp only [pow_one] at h
    rw [h]
    change VnatVOA.vacuum ⊗ₜ[ℂ] (mode (frameStateField lorentzianComplexFrame
      lorentzian_even (latticeConformalVector lorentzianLattice)) (1 + 1) _) = 0
    rw [mode_frameStateField_omega_eq_frameVirasoroMode,
      frameCurrentState_virasoroOne, TensorProduct.tmul_zero]
  rw [moonshineMatterOppositeModes,
    moonshineMatterNearVOA.oppositeModes_homogeneous _
      (moonshineMatterLatticeGenerator_mem_weight
        (frameCurrentState_mem_weight lorentzianComplexFrame lorentzian_even a)),
    moonshineMatterNearVOA.oppositeModeAtWeight_primary 1 n hz,
    show (2 * 1 - n - 2 : ℤ) = -n by ring,
    LinearMap.smul_apply, map_smul]
  simpa only [zpow_one, neg_one_smul] using moonshineMatterForm_currentGenerator_adjoint a n x y

theorem moonshineMatterOppositeModes_vnat_adjoint {N : ℤ} {a : Vnat}
    (ha : a ∈ VnatVOA.grading N) (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm (mode (moonshineMatterNearVOA.Y
      (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum)) n x) y =
      moonshineMatterForm x (moonshineMatterOppositeModes n
        (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum) y) := by
  have hz : (moonshineMatterNearVOA.L 1 ^ (N.toNat + 1))
      (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum) = 0 := by
    rw [moonshineMatterVnatVirasoroOne_pow,
      VertexOperatorAlgebra.L_one_pow_eq_zero VnatVOA ha (by omega), TensorProduct.zero_tmul]
  rw [moonshineMatterOppositeModes,
    moonshineMatterNearVOA.oppositeModes_homogeneous _
      (moonshineMatterVnatGenerator_mem_weight ha),
    moonshineMatterNearVOA.oppositeModeAtWeight_eq_sum N n (N.toNat + 1) hz]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    moonshineMatterVnatVirasoroOne_pow, smul_eq_mul]
  exact moonshineMatterForm_vnatGenerator_fhl N a ha n x y

/-- All actual matter fields are adjoint, conditional only on their opposite iterate law. -/
theorem moonshineMatterOppositeModes_adjoint_of_iterate
    (hIter : moonshineMatterNearVOA.OppositeIterateIdentity
      moonshineMatterVirasoroOne_locallyNilpotent)
    (u : moonshineMatterSpace) (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm (mode (moonshineMatterNearVOA.Y u) n x) y =
      moonshineMatterForm x (moonshineMatterOppositeModes n u y) := by
  let S := moonshineMatterNearVOA.oppositeIntertwinedStates
    moonshineMatterVirasoroOne_locallyNilpotent moonshineMatterForm
  have htop : S = ⊤ := by
    apply moonshineMatter_generated_by_tensor_generators
    · intro a
      let T := S.comap ((TensorProduct.mk ℂ Vnat LorentzianFockSpace).flip
        lorentzianNearVOA.vacuum)
      have hT : T = ⊤ := by
        apply top_unique
        rw [← VnatVOA.isInternal.submodule_iSup_eq_top]
        refine iSup_le fun N b hb => ?_
        exact fun n x y => moonshineMatterOppositeModes_vnat_adjoint hb n x y
      change a ∈ T
      rw [hT]
      trivial
    · exact fun α n x y => moonshineMatterOppositeModes_charge_adjoint α n x y
    · exact fun a n x y => moonshineMatterOppositeModes_current_adjoint a n x y
    · exact fun _ hu _ hv ℓ => moonshineMatterNearVOA.mode_mem_oppositeIntertwinedStates
        moonshineMatterVirasoroOne_locallyNilpotent hIter moonshineMatterForm hu hv ℓ
  have hu : u ∈ S := by rw [htop]; trivial
  exact hu n x y

/-- The exact remaining hypothesis for the Monster Lie form, with all generators discharged. -/
theorem monsterLieBilinearForm_invariant_of_oppositeIterate
    (hIter : moonshineMatterNearVOA.OppositeIterateIdentity
      moonshineMatterVirasoroOne_locallyNilpotent)
    (u v w : monsterLieAlgebra) :
    monsterLieBilinearForm ⁅u, v⁆ w = monsterLieBilinearForm u ⁅v, w⁆ :=
  monsterLieBilinearForm_invariant_of_oppositeAdjoint
    (fun a b c => moonshineMatterOppositeModes_adjoint_of_iterate hIter a 0 b c) u v w

end VOA.Moonshine.ConwayNorton
