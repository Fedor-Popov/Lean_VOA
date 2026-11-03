import VOA.Classification.COne.OrbIcoTScreen1

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc2_0 : RawPoly ℕ :=
  [(2, [9, 11]),
   (-2, [10, 10])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc2_0_check : normR (shScreen 9 [(1, [11])]) = sc2_0 := by
  decide +kernel

theorem sc2_0_sound : shEval sc2_0 =
    EEVec (latP 1) (-1 : ℤ) ((9 : ℕ) : ℤ) (((1 : ℚ) : ℂ) • shWord [11]) :=
  shScreen_single 9 1 [11] sc2_0 sc2_0_check

end VOA.Classification.COne.OrbIcoT
