import VOA.Classification.COne.OrbIcoTScreen2B00

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc2 : RawPoly ℕ := sc2_0

theorem sc2_sound : shEval sc2 =
    EEVec (latP 1) (-1 : ℤ) ((9 : ℕ) : ℤ) (shEval sc1) := by
  have hs : List.Forall₂ (fun (t : ℚ × List ℕ) Q => shEval Q =
      EEVec (latP 1) (-1 : ℤ) ((9 : ℕ) : ℤ) ((t.1 : ℂ) • shWord t.2))
      [(1, [11])] [sc2_0] :=
    .cons sc2_0_sound .nil
  have h := shScreen_blocks 9 _ _ hs
  change shEval sc2 = EEVec (latP 1) (-1 : ℤ) ((9 : ℕ) : ℤ) (shEval [(1, [11])])
  rw [← h]
  simp only [sc2, List.flatten_cons, List.flatten_nil,
    shEval_append, shEval_nil, add_zero]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc2_degrees : ∀ t ∈ sc2, t.2.sum = 20 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoT
