import VOA.Classification.COne.OrbOctaRCCombo16Block02
import VOA.Classification.COne.OrbOctaRCCombo18Block03
import VOA.Classification.COne.OrbOctaRCCharged
import VOA.Classification.COne.OrbOctaRCWard
import VOA.Classification.COne.OrbOctaRNumbers

/-! Certified descendant expressions for the charged dual vectors. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e LatMod OrbOctaR

set_option maxHeartbeats 3000000 in
-- Identify the assembled vector with the checked dual.
set_option maxRecDepth 8192 in
theorem dual16_combo_check : reduceTwo dual16Parts.flatten = wp16_52 := by
  decide +kernel

theorem dualState16_eq_combo : dualState16 =
    virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) wc16_52 := by
  unfold dualState16
  rw [← evRc_reduceTwo_of_sq _ _ charge_square_two,
    dual16_combo_check, wp16_52_sound]

set_option maxHeartbeats 2000000 in
-- The descendant words have the prescribed level and positive indices.
set_option maxRecDepth 8192 in
theorem wc16_degrees : ∀ t ∈ wc16_52, t.2.sum = 16 ∧ ∀ k ∈ t.2, 0 < k := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Exact primary-field measurement after commuting the Virasoro operators.
set_option maxRecDepth 8192 in
theorem ward16_candidate : (1862784 / 5 : ℚ) * wardSum 16 (-1) wc16_52 =
    2 * candidateB32 := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Identify the assembled vector with the checked dual.
set_option maxRecDepth 8192 in
theorem dual18_combo_check : reduceTwo dual18Parts.flatten = wp18_88 := by
  decide +kernel

theorem dualState18_eq_combo : dualState18 =
    virCombo (V2m 1 le_rfl) (latChargeGen (latP 1) (4 : ℤ)) wc18_88 := by
  unfold dualState18
  rw [← evRc_reduceTwo_of_sq _ _ charge_square_two,
    dual18_combo_check, wp18_88_sound]

set_option maxHeartbeats 2000000 in
-- The descendant words have the prescribed level and positive indices.
set_option maxRecDepth 8192 in
theorem wc18_degrees : ∀ t ∈ wc18_88, t.2.sum = 18 ∧ ∀ k ∈ t.2, 0 < k := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Exact primary-field measurement after commuting the Virasoro operators.
set_option maxRecDepth 8192 in
theorem ward18_candidate : (1862784 / 5 : ℚ) * wardSum 16 (-3) wc18_88 =
    2 * candidateB34 := by
  decide +kernel

end VOA.Classification.COne.OrbOctaRC
