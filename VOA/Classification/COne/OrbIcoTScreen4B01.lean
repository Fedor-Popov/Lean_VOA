import VOA.Classification.COne.OrbIcoTScreen4B00

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc4_4 : RawPoly ℕ :=
  [(-6, [5, 9, 9, 9]),
   (36, [6, 8, 9, 9]),
   (-6, [7, 7, 7, 11]),
   (36, [7, 7, 8, 10]),
   (-36, [7, 7, 9, 9]),
   (-72, [7, 8, 8, 9]),
   (48, [8, 8, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_4_check : normR (shScreen 5 [(-6, [9, 9, 9])]) = sc4_4 := by
  decide +kernel

theorem sc4_4_sound : shEval sc4_4 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (((-6 : ℚ) : ℂ) • shWord [9, 9, 9]) :=
  shScreen_single 5 (-6) [9, 9, 9] sc4_4 sc4_4_check

end VOA.Classification.COne.OrbIcoT
