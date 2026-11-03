import VOA.Classification.COne.OrbIcoTScreen5B00

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc5_4 : RawPoly ℕ :=
  [(-48, [3, 5, 9, 9, 9]),
   (144, [3, 6, 8, 9, 9]),
   (-24, [3, 7, 7, 7, 11]),
   (144, [3, 7, 7, 8, 10]),
   (-144, [3, 7, 7, 9, 9]),
   (-288, [3, 7, 8, 8, 9]),
   (192, [3, 8, 8, 8, 8]),
   (48, [4, 4, 9, 9, 9]),
   (-144, [4, 5, 8, 9, 9]),
   (144, [4, 6, 7, 9, 9]),
   (576, [4, 6, 8, 8, 9]),
   (48, [4, 7, 7, 7, 10]),
   (-720, [4, 7, 7, 8, 9]),
   (192, [4, 7, 8, 8, 8]),
   (-72, [5, 5, 7, 9, 9]),
   (-288, [5, 5, 8, 8, 9]),
   (288, [5, 6, 7, 8, 9]),
   (192, [5, 6, 8, 8, 8]),
   (-96, [5, 7, 7, 7, 9]),
   (-144, [5, 7, 7, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_4_check : normR (shScreen 3 [(-24, [5, 9, 9, 9])]) = sc5_4 := by
  decide +kernel

theorem sc5_4_sound : shEval sc5_4 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-24 : ℚ) : ℂ) • shWord [5, 9, 9, 9]) :=
  shScreen_single 3 (-24) [5, 9, 9, 9] sc5_4 sc5_4_check

def sc5_5 : RawPoly ℕ :=
  [(-24, [3, 6, 6, 9, 11]),
   (-72, [4, 4, 7, 9, 11]),
   (48, [4, 4, 7, 10, 10]),
   (48, [4, 4, 8, 8, 11]),
   (-24, [4, 4, 9, 9, 9]),
   (144, [4, 5, 6, 9, 11]),
   (-96, [4, 5, 7, 8, 11]),
   (-288, [4, 5, 7, 9, 10]),
   (384, [4, 5, 8, 8, 10]),
   (-96, [4, 5, 8, 9, 9]),
   (144, [4, 6, 6, 8, 11]),
   (144, [4, 6, 6, 9, 10]),
   (-48, [4, 6, 7, 7, 11]),
   (-96, [4, 6, 7, 8, 10]),
   (-96, [4, 6, 7, 9, 9]),
   (96, [4, 6, 8, 8, 9]),
   (-96, [5, 5, 5, 9, 11]),
   (-96, [5, 5, 7, 7, 11]),
   (-192, [5, 5, 7, 8, 10]),
   (-192, [5, 5, 7, 9, 9]),
   (192, [5, 5, 8, 8, 9]),
   (72, [5, 6, 6, 7, 11]),
   (288, [5, 6, 6, 8, 10]),
   (72, [5, 6, 6, 9, 9]),
   (-192, [5, 6, 7, 7, 10]),
   (-96, [5, 6, 7, 8, 9]),
   (48, [6, 6, 6, 7, 10]),
   (48, [6, 6, 6, 8, 9]),
   (-24, [6, 6, 7, 7, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_5_check : normR (shScreen 3 [(-24, [6, 6, 9, 11])]) = sc5_5 := by
  decide +kernel

theorem sc5_5_sound : shEval sc5_5 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((-24 : ℚ) : ℂ) • shWord [6, 6, 9, 11]) :=
  shScreen_single 3 (-24) [6, 6, 9, 11] sc5_5 sc5_5_check

def sc5_6 : RawPoly ℕ :=
  [(24, [3, 6, 6, 10, 10]),
   (24, [4, 4, 7, 10, 10]),
   (24, [4, 4, 8, 8, 11]),
   (-144, [4, 4, 8, 9, 10]),
   (96, [4, 4, 9, 9, 9]),
   (-144, [4, 5, 6, 10, 10]),
   (384, [4, 5, 7, 9, 10]),
   (-288, [4, 5, 8, 8, 10]),
   (-288, [4, 6, 6, 9, 10]),
   (96, [4, 6, 7, 8, 10]),
   (192, [4, 6, 7, 9, 9]),
   (-144, [4, 6, 8, 8, 9]),
   (96, [5, 5, 5, 10, 10]),
   (192, [5, 5, 7, 8, 10]),
   (384, [5, 5, 7, 9, 9]),
   (-288, [5, 5, 8, 8, 9]),
   (-144, [5, 6, 6, 8, 10]),
   (-288, [5, 6, 6, 9, 9]),
   (384, [5, 6, 7, 8, 9]),
   (-96, [5, 6, 8, 8, 8]),
   (-96, [6, 6, 6, 8, 9]),
   (24, [6, 6, 7, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_6_check : normR (shScreen 3 [(24, [6, 6, 10, 10])]) = sc5_6 := by
  decide +kernel

theorem sc5_6_sound : shEval sc5_6 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((24 : ℚ) : ℂ) • shWord [6, 6, 10, 10]) :=
  shScreen_single 3 24 [6, 6, 10, 10] sc5_6 sc5_6_check

def sc5_7 : RawPoly ℕ :=
  [(48, [3, 6, 7, 8, 11]),
   (96, [4, 5, 6, 9, 11]),
   (-96, [4, 5, 6, 10, 10]),
   (-96, [4, 5, 7, 8, 11]),
   (96, [4, 5, 7, 9, 10]),
   (-96, [4, 5, 8, 8, 10]),
   (48, [4, 5, 8, 9, 9]),
   (-288, [4, 6, 6, 8, 11]),
   (96, [4, 6, 6, 9, 10]),
   (48, [4, 6, 7, 7, 11]),
   (-480, [4, 6, 7, 8, 10]),
   (240, [4, 6, 7, 9, 9]),
   (-96, [4, 6, 8, 8, 9]),
   (192, [4, 7, 7, 7, 10]),
   (-48, [4, 7, 7, 8, 9]),
   (48, [5, 5, 6, 8, 11]),
   (96, [5, 5, 6, 9, 10]),
   (384, [5, 5, 7, 7, 11]),
   (192, [5, 5, 7, 9, 9]),
   (-96, [5, 5, 8, 8, 9]),
   (-96, [5, 6, 6, 7, 11]),
   (-768, [5, 6, 6, 8, 10]),
   (240, [5, 6, 6, 9, 9]),
   (960, [5, 6, 7, 7, 10]),
   (-384, [5, 6, 7, 8, 9]),
   (192, [5, 7, 7, 7, 9]),
   (-96, [6, 6, 6, 6, 11]),
   (-288, [6, 6, 6, 7, 10]),
   (-192, [6, 6, 6, 8, 9]),
   (144, [6, 6, 7, 7, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc5_7_check : normR (shScreen 3 [(48, [6, 7, 8, 11])]) = sc5_7 := by
  decide +kernel

theorem sc5_7_sound : shEval sc5_7 =
    EEVec (latP 1) (-1 : ℤ) ((3 : ℕ) : ℤ) (((48 : ℚ) : ℂ) • shWord [6, 7, 8, 11]) :=
  shScreen_single 3 48 [6, 7, 8, 11] sc5_7 sc5_7_check

end VOA.Classification.COne.OrbIcoT
