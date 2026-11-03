import VOA.Classification.COne.OrbIcoTScreen5B01

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc5_8 : RawPoly ℕ :=
  [(-48, [3, 6, 7, 9, 10]),
   (-48, [4, 5, 7, 8, 11]),
   (48, [4, 5, 7, 9, 10]),
   (192, [4, 5, 8, 8, 10]),
   (-144, [4, 5, 8, 9, 9]),
   (192, [4, 6, 6, 9, 10]),
   (192, [4, 6, 7, 8, 10]),
   (-192, [4, 6, 7, 9, 9]),
   (288, [4, 6, 8, 8, 9]),
   (-48, [4, 7, 7, 7, 10]),
   (-192, [4, 7, 7, 8, 9]),
   (96, [4, 7, 8, 8, 8]),
   (-144, [5, 5, 6, 9, 10]),
   (-192, [5, 5, 7, 8, 10]),
   (-576, [5, 5, 7, 9, 9]),
   (288, [5, 5, 8, 8, 9]),
   (288, [5, 6, 6, 8, 10]),
   (288, [5, 6, 6, 9, 9]),
   (-192, [5, 6, 7, 7, 10]),
   (-720, [5, 6, 7, 8, 9]),
   (480, [5, 6, 8, 8, 8]),
   (-192, [5, 7, 7, 7, 9]),
   (-96, [5, 7, 7, 8, 8]),
   (96, [6, 6, 6, 7, 10]),
   (480, [6, 6, 6, 8, 9]),
   (-96, [6, 6, 7, 7, 9]),
   (-48, [6, 7, 7, 7, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_8_check : normR (shScreen 3 [(-48, [6, 7, 9, 10])]) = sc5_8 := by
  decide +kernel

theorem sc5_8_sound : shEval sc5_8 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-48 : ℚ) : ℂ) • shWord [6, 7, 9, 10]) :=
  shScreen_single 3 (-48) [6, 7, 9, 10] sc5_8 sc5_8_check

def sc5_9 : RawPoly ℕ :=
  [(-48, [3, 6, 8, 8, 10]),
   (48, [4, 5, 8, 8, 10]),
   (-48, [4, 6, 6, 8, 11]),
   (48, [4, 6, 6, 9, 10]),
   (672, [4, 6, 7, 8, 10]),
   (-384, [4, 6, 7, 9, 9]),
   (288, [4, 6, 8, 8, 9]),
   (-192, [4, 7, 7, 7, 10]),
   (-192, [4, 7, 7, 8, 9]),
   (144, [4, 7, 8, 8, 8]),
   (-384, [5, 5, 7, 8, 10]),
   (-192, [5, 5, 8, 8, 9]),
   (288, [5, 6, 6, 8, 10]),
   (-192, [5, 6, 6, 9, 9]),
   (-192, [5, 6, 7, 7, 10]),
   (384, [5, 6, 7, 8, 9]),
   (240, [5, 6, 8, 8, 8]),
   (-768, [5, 7, 7, 7, 9]),
   (144, [6, 6, 6, 7, 10]),
   (240, [6, 6, 6, 8, 9]),
   (288, [6, 6, 7, 8, 8]),
   (-192, [6, 7, 7, 7, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_9_check : normR (shScreen 3 [(-48, [6, 8, 8, 10])]) = sc5_9 := by
  decide +kernel

theorem sc5_9_sound : shEval sc5_9 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-48 : ℚ) : ℂ) • shWord [6, 8, 8, 10]) :=
  shScreen_single 3 (-48) [6, 8, 8, 10] sc5_9 sc5_9_check

def sc5_10 : RawPoly ℕ :=
  [(48, [3, 6, 8, 9, 9]),
   (-48, [4, 5, 8, 9, 9]),
   (48, [4, 6, 7, 7, 11]),
   (-192, [4, 6, 7, 8, 10]),
   (-48, [4, 6, 7, 9, 9]),
   (-384, [4, 6, 8, 8, 9]),
   (-96, [4, 7, 7, 7, 10]),
   (720, [4, 7, 7, 8, 9]),
   (-384, [4, 7, 8, 8, 8]),
   (192, [5, 5, 7, 9, 9]),
   (384, [5, 5, 8, 8, 9]),
   (-48, [5, 6, 6, 9, 9]),
   (-96, [5, 6, 7, 7, 10]),
   (96, [5, 6, 7, 8, 9]),
   (-576, [5, 6, 8, 8, 8]),
   (576, [5, 7, 7, 7, 9]),
   (288, [5, 7, 7, 8, 8]),
   (-192, [6, 6, 6, 8, 9]),
   (-48, [6, 6, 7, 7, 9]),
   (-576, [6, 6, 7, 8, 8]),
   (336, [6, 7, 7, 7, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_10_check : normR (shScreen 3 [(48, [6, 8, 9, 9])]) = sc5_10 := by
  decide +kernel

theorem sc5_10_sound : shEval sc5_10 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((48 : ℚ) : ℂ) • shWord [6, 8, 9, 9]) :=
  shScreen_single 3 48 [6, 8, 9, 9] sc5_10 sc5_10_check

def sc5_11 : RawPoly ℕ :=
  [(-24, [3, 7, 7, 7, 11]),
   (144, [4, 6, 7, 7, 11]),
   (48, [4, 7, 7, 7, 10]),
   (-48, [5, 5, 5, 9, 11]),
   (48, [5, 5, 5, 10, 10]),
   (144, [5, 5, 6, 8, 11]),
   (-144, [5, 5, 6, 9, 10]),
   (-144, [5, 5, 7, 7, 11]),
   (144, [5, 5, 7, 8, 10]),
   (-72, [5, 5, 7, 9, 9]),
   (-288, [5, 6, 6, 7, 11]),
   (576, [5, 6, 6, 8, 10]),
   (-288, [5, 6, 6, 9, 9]),
   (-720, [5, 6, 7, 7, 10]),
   (288, [5, 6, 7, 8, 9]),
   (-96, [5, 7, 7, 7, 9]),
   (192, [6, 6, 6, 6, 11]),
   (192, [6, 6, 6, 7, 10]),
   (192, [6, 6, 6, 8, 9]),
   (-144, [6, 6, 7, 7, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_11_check : normR (shScreen 3 [(-24, [7, 7, 7, 11])]) = sc5_11 := by
  decide +kernel

theorem sc5_11_sound : shEval sc5_11 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-24 : ℚ) : ℂ) • shWord [7, 7, 7, 11]) :=
  shScreen_single 3 (-24) [7, 7, 7, 11] sc5_11 sc5_11_check

end VOA.Classification.COne.OrbIcoT
