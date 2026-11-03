import VOA.Classification.COne.OrbIcoTSchurTop

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc1_0 : RawPoly ℕ :=
  [(1, [11])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc1_0_check : normR (shScreen 11 [(1, [])]) = sc1_0 := by
  decide +kernel

theorem sc1_0_sound : shEval sc1_0 =
    EEVec (latP 1) (-1 : ℤ) ((11 : ℕ) : ℤ) (((1 : ℚ) : ℂ) • shWord []) :=
  shScreen_single 11 1 [] sc1_0 sc1_0_check

end VOA.Classification.COne.OrbIcoT
