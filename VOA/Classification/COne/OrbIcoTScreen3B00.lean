import VOA.Classification.COne.OrbIcoTScreen2

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc3_0 : RawPoly ℕ :=
  [(6, [7, 9, 11]),
   (-4, [7, 10, 10]),
   (-4, [8, 8, 11]),
   (2, [9, 9, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc3_0_check : normR (shScreen 7 [(2, [9, 11])]) = sc3_0 := by
  decide +kernel

theorem sc3_0_sound : shEval sc3_0 =
    EEVec (latP 1) (-1 : ℤ) ((7 : ℕ) : ℤ) (((2 : ℚ) : ℂ) • shWord [9, 11]) :=
  shScreen_single 7 2 [9, 11] sc3_0 sc3_0_check

def sc3_1 : RawPoly ℕ :=
  [(-2, [7, 10, 10]),
   (-2, [8, 8, 11]),
   (12, [8, 9, 10]),
   (-8, [9, 9, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc3_1_check : normR (shScreen 7 [(-2, [10, 10])]) = sc3_1 := by
  decide +kernel

theorem sc3_1_sound : shEval sc3_1 =
    EEVec (latP 1) (-1 : ℤ) ((7 : ℕ) : ℤ) (((-2 : ℚ) : ℂ) • shWord [10, 10]) :=
  shScreen_single 7 (-2) [10, 10] sc3_1 sc3_1_check

end VOA.Classification.COne.OrbIcoT
