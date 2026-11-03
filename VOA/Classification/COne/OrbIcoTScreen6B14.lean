import VOA.Classification.COne.OrbIcoTScreen6B13

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc6_56 : RawPoly ℕ :=
  [(-480, [1, 6, 7, 7, 7, 8]),
   (960, [2, 5, 7, 7, 7, 8]),
   (2880, [2, 6, 6, 7, 7, 8]),
   (960, [2, 6, 7, 7, 7, 7]),
   (-480, [3, 4, 7, 7, 7, 8]),
   (-7200, [3, 5, 6, 7, 7, 8]),
   (-1920, [3, 5, 7, 7, 7, 7]),
   (-5760, [3, 6, 6, 6, 7, 8]),
   (-6240, [3, 6, 6, 7, 7, 7]),
   (2880, [4, 4, 6, 7, 7, 8]),
   (960, [4, 4, 7, 7, 7, 7]),
   (-480, [4, 5, 5, 5, 6, 11]),
   (960, [4, 5, 5, 5, 7, 10]),
   (-480, [4, 5, 5, 5, 8, 9]),
   (2880, [4, 5, 5, 6, 6, 10]),
   (-7200, [4, 5, 5, 6, 7, 9]),
   (2880, [4, 5, 5, 6, 8, 8]),
   (2880, [4, 5, 5, 7, 7, 8]),
   (-5760, [4, 5, 6, 6, 6, 9]),
   (28800, [4, 5, 6, 6, 7, 8]),
   (-960, [4, 5, 6, 7, 7, 7]),
   (11520, [4, 6, 6, 6, 6, 8]),
   (15360, [4, 6, 6, 6, 7, 7]),
   (960, [5, 5, 5, 5, 6, 10]),
   (-1920, [5, 5, 5, 5, 7, 9]),
   (960, [5, 5, 5, 5, 8, 8]),
   (-6240, [5, 5, 5, 6, 6, 9]),
   (-960, [5, 5, 5, 6, 7, 8]),
   (-11520, [5, 5, 5, 7, 7, 7]),
   (15360, [5, 5, 6, 6, 6, 8]),
   (-54720, [5, 5, 6, 6, 7, 7]),
   (17280, [5, 6, 6, 6, 6, 7]),
   (3840, [6, 6, 6, 6, 6, 6])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc6_56_check : normR (shScreen 1 [(-480, [6, 7, 7, 7, 8])]) = sc6_56 := by
  decide +kernel

theorem sc6_56_sound : shEval sc6_56 =
    EEVec (latP 1) (-1 : ℤ) ((1 : ℕ) : ℤ) (((-480 : ℚ) : ℂ) • shWord [6, 7, 7, 7, 8]) :=
  shScreen_single 1 (-480) [6, 7, 7, 7, 8] sc6_56 sc6_56_check

def sc6_57 : RawPoly ℕ :=
  [(120, [1, 7, 7, 7, 7, 7]),
   (-1200, [2, 6, 7, 7, 7, 7]),
   (600, [3, 5, 7, 7, 7, 7]),
   (4800, [3, 6, 6, 7, 7, 7]),
   (-4800, [4, 5, 6, 7, 7, 7]),
   (-9600, [4, 6, 6, 6, 7, 7]),
   (120, [5, 5, 5, 5, 5, 11]),
   (-1200, [5, 5, 5, 5, 6, 10]),
   (600, [5, 5, 5, 5, 7, 9]),
   (4800, [5, 5, 5, 6, 6, 9]),
   (-4800, [5, 5, 5, 6, 7, 8]),
   (2400, [5, 5, 5, 7, 7, 7]),
   (-9600, [5, 5, 6, 6, 6, 8]),
   (21600, [5, 5, 6, 6, 7, 7]),
   (-3840, [6, 6, 6, 6, 6, 6])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc6_57_check : normR (shScreen 1 [(120, [7, 7, 7, 7, 7])]) = sc6_57 := by
  decide +kernel

theorem sc6_57_sound : shEval sc6_57 =
    EEVec (latP 1) (-1 : ℤ) ((1 : ℕ) : ℤ) (((120 : ℚ) : ℂ) • shWord [7, 7, 7, 7, 7]) :=
  shScreen_single 1 120 [7, 7, 7, 7, 7] sc6_57 sc6_57_check

end VOA.Classification.COne.OrbIcoT
