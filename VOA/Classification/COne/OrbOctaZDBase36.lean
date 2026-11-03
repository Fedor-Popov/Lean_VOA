import VOA.Classification.COne.OrbOctaZDLow

/-! The charged endpoint of the spin-six channel in the octahedral self-product. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbOctaRC OrbPrim OrbRat6 OrbC2c OrbC2e PlusC2Eval PlusC2 PlusUnitary OrbC2g OrbC2h

set_option maxHeartbeats 1000000 in
-- Only the bottom coefficient of the already certified second screening is needed.
theorem screen2_bottom_check :
    exponentialActionOne 4 2 (-5) screenState2 = [(-453024, [])] := by
  decide +kernel

set_option maxHeartbeats 500000 in
-- The weight of this charge-seven output is below its charged vacuum.
theorem screen1_below_check :
    exponentialActionOne 4 3 (-5) screenState1 = [] := by
  decide +kernel

theorem pair02 : V2v.smul (wv 4 0) (-5) (wv 4 2) =
    (-56628 / 7 : ℂ) • wv 6 0 := by
  have h : wv 4 2 = (1 / 56 : ℂ) • vn 4 2 := by
    rw [wv, cnk]; norm_num [Nat.factorial]
  rw [h, vn4_2_value, wv_zero, PreVertexAlgebra.smul_smul_right,
    exponentialActionOne_sound]
  norm_num only [Nat.cast_ofNat, Int.reduceAdd]
  rw [screen2_bottom_check]
  simp only [evRc_cons, evRc_nil, evalWord, add_zero, Rat.cast_neg, Rat.cast_ofNat]
  change (1 / 56 : ℂ) • OrbOctaRC.sector 6 ((-453024 : ℂ) • 1) = _
  rw [map_smul, smul_smul]
  norm_num
  rw [wv_zero]
  rfl

theorem pair01 : V2v.smul (wv 4 0) (-5) (wv 4 1) = 0 := by
  have h : wv 4 1 = (1 / 8 : ℂ) • vn 4 1 := by
    rw [wv, cnk]; norm_num [Nat.factorial]
  rw [h, vn4_1_value, wv_zero, PreVertexAlgebra.smul_smul_right,
    exponentialActionOne_sound]
  norm_num only [Nat.cast_ofNat, Int.reduceAdd]
  rw [screen1_below_check, evRc_nil, map_zero, smul_zero]

theorem pair00 : V2v.smul (wv 4 0) (-5) (wv 4 0) = 0 := by
  rw [wv_zero]
  change V2v.smul (latChargeGen (latP 1) (4 : ℤ)) (-5)
    (latStateGen (latP 1) (HeisenbergN.vacuumN _) (4 : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

end VOA.Classification.COne.OrbOctaZD
