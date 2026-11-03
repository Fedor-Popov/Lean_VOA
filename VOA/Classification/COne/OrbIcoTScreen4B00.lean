import VOA.Classification.COne.OrbIcoTScreen3

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc4_0 : RawPoly ℕ :=
  [(24, [5, 7, 9, 11]),
   (-12, [5, 7, 10, 10]),
   (-12, [5, 8, 8, 11]),
   (6, [5, 9, 9, 9]),
   (-12, [6, 6, 9, 11]),
   (24, [6, 7, 9, 10]),
   (-48, [6, 8, 8, 10]),
   (12, [6, 8, 9, 9]),
   (6, [7, 7, 7, 11]),
   (12, [7, 7, 8, 10]),
   (12, [7, 7, 9, 9]),
   (-12, [7, 8, 8, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_0_check : normR (shScreen 5 [(6, [7, 9, 11])]) = sc4_0 := by
  decide +kernel

theorem sc4_0_sound : shEval sc4_0 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (((6 : ℚ) : ℂ) • shWord [7, 9, 11]) :=
  shScreen_single 5 6 [7, 9, 11] sc4_0 sc4_0_check

def sc4_1 : RawPoly ℕ :=
  [(-12, [5, 7, 10, 10]),
   (-6, [5, 8, 8, 11]),
   (36, [5, 8, 9, 10]),
   (-24, [5, 9, 9, 9]),
   (12, [6, 6, 10, 10]),
   (-24, [6, 7, 9, 10]),
   (36, [6, 8, 8, 10]),
   (-12, [7, 7, 8, 10]),
   (-24, [7, 7, 9, 9]),
   (18, [7, 8, 8, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_1_check : normR (shScreen 5 [(-6, [7, 10, 10])]) = sc4_1 := by
  decide +kernel

theorem sc4_1_sound : shEval sc4_1 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (((-6 : ℚ) : ℂ) • shWord [7, 10, 10]) :=
  shScreen_single 5 (-6) [7, 10, 10] sc4_1 sc4_1_check

def sc4_2 : RawPoly ℕ :=
  [(-6, [5, 8, 8, 11]),
   (-12, [6, 6, 9, 11]),
   (12, [6, 6, 10, 10]),
   (36, [6, 7, 8, 11]),
   (-24, [6, 7, 9, 10]),
   (36, [6, 8, 8, 10]),
   (-12, [6, 8, 9, 9]),
   (-24, [7, 7, 7, 11]),
   (-24, [7, 7, 9, 9]),
   (18, [7, 8, 8, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_2_check : normR (shScreen 5 [(-6, [8, 8, 11])]) = sc4_2 := by
  decide +kernel

theorem sc4_2_sound : shEval sc4_2 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (((-6 : ℚ) : ℂ) • shWord [8, 8, 11]) :=
  shScreen_single 5 (-6) [8, 8, 11] sc4_2 sc4_2_check

def sc4_3 : RawPoly ℕ :=
  [(12, [5, 8, 9, 10]),
   (12, [6, 7, 8, 11]),
   (-24, [6, 7, 9, 10]),
   (-72, [6, 8, 8, 10]),
   (12, [6, 8, 9, 9]),
   (12, [7, 7, 8, 10]),
   (96, [7, 7, 9, 9]),
   (-24, [7, 8, 8, 9]),
   (-24, [8, 8, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_3_check : normR (shScreen 5 [(12, [8, 9, 10])]) = sc4_3 := by
  decide +kernel

theorem sc4_3_sound : shEval sc4_3 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (((12 : ℚ) : ℂ) • shWord [8, 9, 10]) :=
  shScreen_single 5 12 [8, 9, 10] sc4_3 sc4_3_check

end VOA.Classification.COne.OrbIcoT
