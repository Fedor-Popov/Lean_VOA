import VOA.Classification.COne.OrbOctaZDModes

/-! A short charged endpoint for the spin-nine channel. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 VOA.LatGen VOA.LatGen.Triplet
  HeisenbergN VOA.IntegralLattice

private theorem g0 : gco (-8) 0 = 1 := gco_zero _

private theorem g1 : gco (-8) 1 = 8 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0]

private theorem g2 : gco (-8) 2 = 36 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1]

private theorem g3 : gco (-8) 3 = 120 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2]

private theorem g4 : gco (-8) 4 = 330 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3]

private theorem g5 : gco (-8) 5 = 792 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4]

private theorem g6 : gco (-8) 6 = 1716 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5]

private theorem g7 : gco (-8) 7 = 3432 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6]

private theorem g8 : gco (-8) 8 = 6435 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6, g7]

private theorem g9 : gco (-8) 9 = 11440 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6, g7, g8]

private theorem g10 : gco (-8) 10 = 19448 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]

private theorem g11 : gco (-8) 11 = 31824 := by
  rw [gco_succ]
  norm_num [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]

theorem fo_charge_six : fo (latChargeGen (latP 1) (6 : ℤ)) =
    latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) 11) (5 : ℤ) := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0
    (latStateGen (latP 1) (vacuumN _) (6 : ℤ)) = _
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_pos (by norm_num),
    PlusCharacterTable.rankOne_cocycle, one_smul]
  norm_num
  rfl

theorem EEVec_four_schur11 :
    EEVec (latP 1) (4 : ℤ) (-11) (vSchur (latP 1) (-1 : ℤ) 11) =
      (31824 : ℂ) • vacuumN (rank (latP 1)) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) (4 : ℤ) _
    (Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 11)]
  rw [show max (0 : ℤ) (-11) = 0 by norm_num,
    show ((11 : ℕ) : ℤ) + (-11) = 0 by norm_num,
    Finset.Icc_self, Finset.sum_singleton, show ((0 : ℤ) - (-11)).toNat = 11 by rfl,
    show (0 : ℤ).toNat = 0 by rfl, vSchur_zero, one_mul,
    aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ 11 11 le_rfl,
    Nat.sub_self, vSchur_zero, latP_form]
  norm_num only [Nat.cast_one, mul_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, mul_neg, one_mul]
  rw [g11]
  rfl

theorem base46_00 : V2v.smul (wv 4 0) (-30) (wv 6 0) = 0 := by
  rw [wv_zero, wv_zero]
  change V2v.smul (latChargeGen (latP 1) (4 : ℤ)) (-30)
    (latStateGen (latP 1) (vacuumN _) (6 : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

theorem base46_01 : V2v.smul (wv 4 0) (-30) (wv 6 1) = (2652 : ℂ) • wv 9 0 := by
  have h : wv 6 1 = (1 / 12 : ℂ) • fo (latChargeGen (latP 1) (6 : ℤ)) := by
    rw [wv, cnk, vn]
    norm_num [Nat.factorial]
  rw [h, fo_charge_six, wv_zero, PreVertexAlgebra.smul_smul_right,
    smul_chargeGen_state, PlusCharacterTable.rankOne_cocycle, one_smul, latP_form]
  norm_num only [Nat.cast_ofNat, Int.reduceMul, Int.reduceNeg, Int.reduceSub, Int.reduceAdd]
  rw [EEVec_four_schur11, latStateGen_csmul, smul_smul, wv_zero]
  norm_num
  rfl

theorem base46_10 : V2v.smul (wv 4 1) (-30) (wv 6 0) = (-3978 : ℂ) • wv 9 0 := by
  have h := congrArg fo base46_00
  rw [fo_smul, fo_wv0 4 (by norm_num), fo_wv0 6 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, base46_01,
    smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 8 : ℂ) • v) (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  exact hs

end VOA.Classification.COne.OrbOctaZD
