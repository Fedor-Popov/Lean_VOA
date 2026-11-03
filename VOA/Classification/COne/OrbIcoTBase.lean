import VOA.Classification.COne.OrbIcoTScreen6
import VOA.Classification.COne.OrbIcoTScreenVOA

/-! Exact nonzero base value for the sixth channel of two spin-six primaries. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim OrbRat6

theorem vn6_sc0 : vn 6 0 = latStateGen (latP 1) (shEval sc0) (6 : ℤ) := by
  simp only [vn, pow_zero, Module.End.one_apply, sc0, shEval_cons, shEval_nil,
    shWord_nil, Rat.cast_one, one_smul, add_zero]
  rfl

theorem vn6_sc1 : vn 6 1 =
    latStateGen (latP 1) (shEval sc1) (5 : ℤ) := by
  rw [show 1 = 0 + 1 by rfl, vn_succ, vn6_sc0]
  exact fo_screen sc0 sc1 11 6 (by norm_num) sc1_sound

theorem vn6_sc2 : vn 6 2 =
    latStateGen (latP 1) (shEval sc2) (4 : ℤ) := by
  rw [show 2 = 1 + 1 by rfl, vn_succ, vn6_sc1]
  exact fo_screen sc1 sc2 9 5 (by norm_num) sc2_sound

theorem vn6_sc3 : vn 6 3 =
    latStateGen (latP 1) (shEval sc3) (3 : ℤ) := by
  rw [show 3 = 2 + 1 by rfl, vn_succ, vn6_sc2]
  exact fo_screen sc2 sc3 7 4 (by norm_num) sc3_sound

theorem vn6_sc4 : vn 6 4 =
    latStateGen (latP 1) (shEval sc4) (2 : ℤ) := by
  rw [show 4 = 3 + 1 by rfl, vn_succ, vn6_sc3]
  exact fo_screen sc3 sc4 5 3 (by norm_num) sc4_sound

theorem vn6_sc5 : vn 6 5 =
    latStateGen (latP 1) (shEval sc5) (1 : ℤ) := by
  rw [show 5 = 4 + 1 by rfl, vn_succ, vn6_sc4]
  exact fo_screen sc4 sc5 3 2 (by norm_num) sc5_sound

theorem vn6_sc6 : vn 6 6 =
    latStateGen (latP 1) (shEval sc6) (0 : ℤ) := by
  rw [show 6 = 5 + 1 by rfl, vn_succ, vn6_sc5]
  exact fo_screen sc5 sc6 1 1 (by norm_num) sc6_sound

set_option maxHeartbeats 3000000 in
-- Exact rational top coefficient of the certified six-screening polynomial.
set_option maxRecDepth 4096 in
theorem sc6_top : topSum sc6 = -1064605983217920 := by
  decide +kernel

theorem wv6_sc6 : wv 6 6 =
    (1 / 665280 : ℂ) • latStateGen (latP 1) (shEval sc6) (0 : ℤ) := by
  rw [wv, vn6_sc6]
  congr 1
  norm_num [cnk, Nat.factorial]

/-- The actual VOA product defining the sixth-channel normalization. -/
theorem w60_w66 : V2v.smul (wv 6 0) 35 (wv 6 6) =
    (-33604986844 / 21 : ℂ) • wv 6 0 := by
  rw [wv6_sc6, PreVertexAlgebra.smul_smul_right, wv_zero]
  rw [smul_chargeGen_state, PlusCharacterTable.rankOne_cocycle, one_smul, latP_form]
  rw [show -(35 : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) * ((6 : ℕ) : ℤ) * 0 =
    -((36 : ℕ) : ℤ) by norm_num, show ((6 : ℕ) : ℤ) = (6 : ℤ) by norm_num,
    EEVec_top sc6 36 sc6_degrees, sc6_top]
  rw [latStateGen_csmul, smul_smul]
  norm_num
  rfl

theorem sixth_base_ne_zero : (-33604986844 / 21 : ℂ) ≠ 0 := by norm_num

def mu6 : ℂ := -763749701 / 228614400

theorem mu6_ne_zero : mu6 ≠ 0 := by norm_num [mu6]

theorem mu6_base : mu6 * 479001600 = (-33604986844 / 21 : ℂ) := by norm_num [mu6]

end VOA.Classification.COne.OrbIcoT
