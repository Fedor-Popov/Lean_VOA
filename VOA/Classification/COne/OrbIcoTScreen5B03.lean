import VOA.Classification.COne.OrbIcoTScreen5B02

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc5_12 : RawPoly ℕ :=
  [(48, [3, 7, 7, 8, 10]),
   (-192, [4, 6, 7, 8, 10]),
   (-96, [4, 7, 7, 7, 10]),
   (-96, [4, 7, 7, 8, 9]),
   (48, [5, 5, 6, 8, 11]),
   (-48, [5, 5, 6, 9, 10]),
   (-48, [5, 5, 7, 8, 10]),
   (192, [5, 5, 7, 9, 9]),
   (-48, [5, 5, 8, 8, 9]),
   (-384, [5, 6, 6, 8, 10]),
   (384, [5, 6, 6, 9, 9]),
   (720, [5, 6, 7, 7, 10]),
   (96, [5, 6, 7, 8, 9]),
   (-192, [5, 6, 8, 8, 8]),
   (576, [5, 7, 7, 7, 9]),
   (-48, [5, 7, 7, 8, 8]),
   (-384, [6, 6, 6, 7, 10]),
   (-576, [6, 6, 6, 8, 9]),
   (288, [6, 6, 7, 7, 9]),
   (-576, [6, 6, 7, 8, 8]),
   (336, [6, 7, 7, 7, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_12_check : normR (shScreen 3 [(48, [7, 7, 8, 10])]) = sc5_12 := by
  decide +kernel

theorem sc5_12_sound : shEval sc5_12 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((48 : ℚ) : ℂ) • shWord [7, 7, 8, 10]) :=
  shScreen_single 3 48 [7, 7, 8, 10] sc5_12 sc5_12_check

def sc5_13 : RawPoly ℕ :=
  [(24, [3, 7, 7, 9, 9]),
   (-96, [4, 6, 7, 9, 9]),
   (-96, [4, 7, 7, 8, 9]),
   (24, [5, 5, 7, 7, 11]),
   (-96, [5, 5, 7, 8, 10]),
   (120, [5, 5, 7, 9, 9]),
   (-96, [5, 6, 7, 7, 10]),
   (768, [5, 6, 7, 8, 9]),
   (-384, [5, 6, 8, 8, 8]),
   (192, [5, 7, 7, 7, 9]),
   (96, [5, 7, 7, 8, 8]),
   (-384, [6, 6, 6, 8, 9]),
   (96, [6, 6, 7, 7, 9]),
   (-384, [6, 6, 7, 8, 8]),
   (192, [6, 7, 7, 7, 8]),
   (24, [7, 7, 7, 7, 7])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_13_check : normR (shScreen 3 [(24, [7, 7, 9, 9])]) = sc5_13 := by
  decide +kernel

theorem sc5_13_sound : shEval sc5_13 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((24 : ℚ) : ℂ) • shWord [7, 7, 9, 9]) :=
  shScreen_single 3 24 [7, 7, 9, 9] sc5_13 sc5_13_check

def sc5_14 : RawPoly ℕ :=
  [(-72, [3, 7, 8, 8, 9]),
   (144, [4, 6, 8, 8, 9]),
   (288, [4, 7, 7, 8, 9]),
   (144, [4, 7, 8, 8, 8]),
   (-72, [5, 5, 8, 8, 9]),
   (-72, [5, 6, 6, 7, 11]),
   (144, [5, 6, 6, 8, 10]),
   (-72, [5, 6, 6, 9, 9]),
   (288, [5, 6, 7, 7, 10]),
   (-1008, [5, 6, 7, 8, 9]),
   (144, [5, 6, 8, 8, 8]),
   (-864, [5, 7, 7, 7, 9]),
   (-432, [5, 7, 7, 8, 8]),
   (144, [6, 6, 6, 7, 10]),
   (144, [6, 6, 6, 8, 9]),
   (-432, [6, 6, 7, 7, 9]),
   (2592, [6, 6, 7, 8, 8]),
   (-720, [6, 7, 7, 7, 8]),
   (-288, [7, 7, 7, 7, 7])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_14_check : normR (shScreen 3 [(-72, [7, 8, 8, 9])]) = sc5_14 := by
  decide +kernel

theorem sc5_14_sound : shEval sc5_14 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-72 : ℚ) : ℂ) • shWord [7, 8, 8, 9]) :=
  shScreen_single 3 (-72) [7, 8, 8, 9] sc5_14 sc5_14_check

def sc5_15 : RawPoly ℕ :=
  [(24, [3, 8, 8, 8, 8]),
   (-192, [4, 7, 8, 8, 8]),
   (96, [5, 6, 8, 8, 8]),
   (576, [5, 7, 7, 8, 8]),
   (24, [6, 6, 6, 6, 11]),
   (-192, [6, 6, 6, 7, 10]),
   (96, [6, 6, 6, 8, 9]),
   (576, [6, 6, 7, 7, 9]),
   (-1008, [6, 6, 7, 8, 8]),
   (-384, [6, 7, 7, 7, 8]),
   (384, [7, 7, 7, 7, 7])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_15_check : normR (shScreen 3 [(24, [8, 8, 8, 8])]) = sc5_15 := by
  decide +kernel

theorem sc5_15_sound : shEval sc5_15 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((24 : ℚ) : ℂ) • shWord [8, 8, 8, 8]) :=
  shScreen_single 3 24 [8, 8, 8, 8] sc5_15 sc5_15_check

end VOA.Classification.COne.OrbIcoT
