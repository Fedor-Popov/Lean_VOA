import VOA.Classification.COne.OrbOctaRCPrimary
import VOA.Classification.COne.OrbOctaRCWardValues
import VOA.Classification.COne.OrbOctaRCNorm16
import VOA.Classification.COne.OrbOctaRCNorm18

/-! Actual mode measurements for the octahedral primary. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e LatMod OrbSpan OrbOctaR

theorem charged_mode32 : chargedProbe dualState16 (W.smul X (-1) X) =
    (2 : ℂ) * candidateB32 := by
  change (v2mVirUnitary 1 le_rfl).form
    ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) (-1) X) dualState16 = _
  rw [dualState16_eq_combo,
    form_self_combo _ _ X_ambient_primary _ (-1) 16 _ wc16_degrees]
  norm_num only [show (-1 : ℤ) + 16 = 15 by norm_num]
  rw [primary_ground_coupling]
  have h := congrArg (fun q : ℚ => (q : ℂ)) ward16_candidate
  push_cast at h
  simpa only [mul_comm] using h

theorem charged_mode34 : chargedProbe dualState18 (W.smul X (-3) X) =
    (2 : ℂ) * candidateB34 := by
  change (v2mVirUnitary 1 le_rfl).form
    ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) (-3) X) dualState18 = _
  rw [dualState18_eq_combo,
    form_self_combo _ _ X_ambient_primary _ (-3) 18 _ wc18_degrees]
  norm_num only [show (-3 : ℤ) + 18 = 15 by norm_num]
  rw [primary_ground_coupling]
  have h := congrArg (fun q : ℚ => (q : ℂ)) ward18_candidate
  push_cast at h
  simpa only [mul_comm] using h

end VOA.Classification.COne.OrbOctaRC
