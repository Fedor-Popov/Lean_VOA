import VOA.Moonshine.MoonshineCNMatterOpposite

/-! Actual generator weights and `L₁` actions for comparison with the opposite modes. -/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN AutMonster TensorFieldLift
open scoped TensorProduct BigOperators

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem frameChargeState_virasoroOne (hEven : L.Even) (α : L.carrier) :
    frameVirasoroMode F 1 (latChargeGen L α) = 0 := by
  simpa only [pow_one] using frameVirasoroOne_pow_eq_zero F hEven α
    (chargeState_mem_latticeWeight L α) (latState_mem_momentum L (vacuumN _) α)
    1 (by simp)

include F in
theorem frameCurrentState_mem_weight (hEven : L.Even) (a : Fin (rank L)) :
    frameWordState L [(0, a)] 0 ∈ gradingLatGen L 1 := by
  have hv : latVacuumGen L ∈ gradingLatGen L 0 := by
    simpa only [LatGen.halfNorm_zero, latChargeGen_zero] using chargeState_mem_latticeWeight L 0
  have h := frameCurrent_gradedField F hEven a 0 0 (latVacuumGen L) hv
  rw [← frameStateField_currentState F hEven a, frameStateField_cre0] at h
  simpa only [add_zero] using h

theorem frameCurrentState_virasoroOne (a : Fin (rank L)) :
    frameVirasoroMode F 1 (frameWordState L [(0, a)] 0) = 0 := by
  have hosc : frameOscillator F 0 1 = 0 := by
    rw [frameOscillator_eq_sum]
    exact Finset.sum_eq_zero fun b _ => by rw [frameCoordinate_zero, zero_smul]
  have hL : LvirN (rank L) 1 1 (MvPolynomial.X (0, a)) = 0 := by
    have h := LvirN_oscN (rank L) 1 one_ne_zero a 1 (-1) (vacuumN (rank L))
    simpa only [oscN_neg_one_vacuum, Int.cast_neg, Int.cast_one, neg_neg,
      one_smul, add_neg_cancel, oscN_zero, LinearMap.zero_apply,
      LvirN_vacuum (rank L) 1 (by norm_num : (-1 : ℤ) ≤ 1), map_zero, add_zero] using h
  rw [frameWordState_eq, wordStateN_cons, wordStateN_nil, mul_one]
  change frameVirasoroMode F 1 (latStateGen L (MvPolynomial.X (0, a)) 0) = 0
  rw [frameVirasoroMode_tmul, if_neg (by norm_num : (1 : ℤ) ≠ 0), hosc,
    LinearMap.zero_apply, hL]
  simp [latStateGen]

theorem moonshineMatterLatticeVirasoroOne_pow (b : LorentzianFockSpace) (j : ℕ) :
    (moonshineMatterNearVOA.L 1 ^ j) (VnatVOA.vacuum ⊗ₜ[ℂ] b) =
      VnatVOA.vacuum ⊗ₜ[ℂ] ((lorentzianNearVOA.L 1 ^ j) b) := by
  have hv : nearVirasoroMode VnatVOA.toNearVOA 1 VnatVOA.vacuum = 0 :=
    (VnatVOA.creation VnatVOA.conformalVector).2 2 (by norm_num)
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change mode (nearTensorField VnatVOA.toNearVOA lorentzianNearVOA
        (nearTensorConformalVector VnatVOA.toNearVOA lorentzianNearVOA)) (1 + 1) _ = _
      rw [nearTensorField_conformal_mode]
      simp only [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, hv, TensorProduct.zero_tmul, zero_add,
        pow_succ', Module.End.mul_apply]
      rfl

theorem moonshineMatterVnatVirasoroOne_pow (a : Vnat) (j : ℕ) :
    (moonshineMatterNearVOA.L 1 ^ j) (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum) =
      ((VnatVOA.L 1 ^ j) a) ⊗ₜ[ℂ] lorentzianNearVOA.vacuum := by
  have hv : nearVirasoroMode lorentzianNearVOA 1 lorentzianNearVOA.vacuum = 0 :=
    (lorentzianNearVOA.creation lorentzianNearVOA.conformalVector).2 2 (by norm_num)
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change mode (nearTensorField VnatVOA.toNearVOA lorentzianNearVOA
        (nearTensorConformalVector VnatVOA.toNearVOA lorentzianNearVOA)) (1 + 1) _ = _
      rw [nearTensorField_conformal_mode]
      simp only [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, hv, TensorProduct.tmul_zero, add_zero,
        pow_succ', Module.End.mul_apply]
      rfl

theorem moonshineMatterVnatGenerator_mem_weight {N : ℤ} {a : Vnat}
    (ha : a ∈ VnatVOA.grading N) :
    a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum ∈ moonshineMatterNearVOA.grading N := by
  simpa only [add_zero] using nearTensorGrading_tmul VnatVOA.toNearVOA lorentzianNearVOA
    ha lorentzianNearVOA.vacuum_mem

theorem moonshineMatterLatticeGenerator_mem_weight {N : ℤ} {b : LorentzianFockSpace}
    (hb : b ∈ lorentzianNearVOA.grading N) :
    VnatVOA.vacuum ⊗ₜ[ℂ] b ∈ moonshineMatterNearVOA.grading N := by
  simpa only [zero_add] using nearTensorGrading_tmul VnatVOA.toNearVOA lorentzianNearVOA
    VnatVOA.vacuum_mem hb

end VOA.Moonshine.ConwayNorton
