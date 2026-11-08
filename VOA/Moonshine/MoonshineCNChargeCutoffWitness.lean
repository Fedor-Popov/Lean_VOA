import VOA.Moonshine.MoonshineCNGeneratorPrimary

/-! A kernel-checked witness that total weight alone cannot supply the FHL cutoff. -/

namespace VOA.NearVOA

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

theorem virasoroOne_translation_primary {N : ℤ} {u : H}
    (hu : u ∈ V.grading N) (hL : V.L 1 u = 0) :
    V.L 1 (V.L (-1) u) = (2 * (N : ℂ)) • u := by
  have hc : ⁅V.L 1, V.L (-1)⁆ = (2 : ℂ) • V.L 0 := by
    simpa only [L_def] using (show
      ⁅mode (V.Y V.conformalVector) (1 + 1), mode (V.Y V.conformalVector) (-1 + 1)⁆ =
        (2 : ℂ) • mode (V.Y V.conformalVector) (0 + 1) by
      have h := V.virasoro 1 (-1)
      norm_num at h ⊢
      exact h)
  have h := LinearMap.congr_fun hc u
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply, hL, map_zero, sub_zero] at h
  rw [show V.L 0 u = (N : ℂ) • u from V.L0_grading u hu, smul_smul] at h
  exact h

end VOA.NearVOA

namespace VOA.Moonshine.ConwayNorton

noncomputable def lorentzianNegativeChargeDescendant : LorentzianFockSpace :=
  lorentzianNearVOA.L (-1) (lorentzianChargeState ![1, -1])

theorem lorentzianNegativeChargeDescendant_weight :
    lorentzianNegativeChargeDescendant ∈ lorentzianNearVOA.grading 0 := by
  have hu : lorentzianChargeState ![1, -1] ∈ lorentzianNearVOA.grading (-1) := by
    simpa [lorentzianEnergy] using lorentzianChargeState_mem_weight ![1, -1]
  simpa only [sub_neg_eq_add, neg_add_cancel] using
    lorentzianNearVOA.virasoroMode_mem_weight hu (-1)

/-- At total weight zero the first omitted FHL term is explicitly nonzero. -/
theorem lorentzianNegativeChargeDescendant_virasoroOne :
    lorentzianNearVOA.L 1 lorentzianNegativeChargeDescendant =
      (-2 : ℂ) • lorentzianChargeState ![1, -1] := by
  have hu : lorentzianChargeState ![1, -1] ∈ lorentzianNearVOA.grading (-1) := by
    simpa [lorentzianEnergy] using lorentzianChargeState_mem_weight ![1, -1]
  have hL : lorentzianNearVOA.L 1 (lorentzianChargeState ![1, -1]) = 0 := by
    change mode (frameStateField lorentzianComplexFrame lorentzian_even
      (latticeConformalVector lorentzianLattice)) (1 + 1) _ = 0
    rw [mode_frameStateField_omega_eq_frameVirasoroMode]
    exact frameChargeState_virasoroOne lorentzianComplexFrame lorentzian_even _
  simpa using lorentzianNearVOA.virasoroOne_translation_primary hu hL

theorem lorentzianVirasoroOne_weightZero_not_zero :
    ∃ u ∈ lorentzianNearVOA.grading 0, lorentzianNearVOA.L 1 u ≠ 0 := by
  refine ⟨lorentzianNegativeChargeDescendant, lorentzianNegativeChargeDescendant_weight, ?_⟩
  rw [lorentzianNegativeChargeDescendant_virasoroOne]
  apply smul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0)
  intro hz
  have h := lorentzianChargeCoefficient_charge_eq ![1, -1] ![1, -1]
  rw [hz, map_zero, if_pos rfl] at h
  exact zero_ne_one h

end VOA.Moonshine.ConwayNorton
