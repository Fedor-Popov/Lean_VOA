import VOA.Classification.COne.OrbIcoSBinary
import VOA.Classification.COne.OrbIcoSMeasurements

/-! Nonvanishing of the explicit icosahedral seed, its norm, and its binary transvectants. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open VOA OrbPrim OrbSpan OrbC2c OrbIco VOA.LatGen VOA.LatGen.Triplet MvPolynomial

theorem fpoly_ne_zero : fpoly ≠ 0 := by
  intro h
  have hc := cf_f 0 (by omega)
  rw [h, map_zero] at hc
  have hr := congrArg Complex.re hc
  simp [f0] at hr
  linarith [gp_re_pos]

theorem Xico_ambient_ne_zero : (Xico : LatModuleGen (latP 1)) ≠ 0 := by
  intro h
  change (TavI J6).val = 0 at h
  rw [TavI_coe icoInv_J6, T2_J6] at h
  exact fpoly_ne_zero (Tb_inj (n := 6) fpoly_mem h)

theorem Xico_ne_zero : Xico ≠ 0 := by
  intro h
  apply Xico_ambient_ne_zero
  exact congrArg Subtype.val h

/-- Positive norm of the actual primary; no channel identification is used. -/
theorem Xico_norm_ne_zero :
    (v2mVirUnitary 1 le_rfl).form (Xico : LatModuleGen (latP 1)) Xico ≠ 0 := by
  intro h
  have hp := (v2mVirUnitary 1 le_rfl).pos _ Xico_ambient_ne_zero
  rw [h] at hp
  exact (lt_irrefl 0) hp

theorem ico_transvectant_six_ne_zero : transvectantC 6 fpoly fpoly ≠ 0 := by
  rw [ico_transvectant_six]
  exact mul_ne_zero (C_ne_zero.mpr sixthScalar_ne_zero) fpoly_ne_zero

theorem ico_transvectant_twelve_ne_zero : transvectantC 12 fpoly fpoly ≠ 0 := by
  rw [ico_transvectant_twelve]
  exact C_ne_zero.mpr twelfthScalar_ne_zero

end VOA.Classification.COne.OrbIcoS
