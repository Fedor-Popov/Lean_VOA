import VOA.Classification.COne.OrbIcoTScreen1B00

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc0 : RawPoly ℕ :=
  [(1, [])]

def sc1 : RawPoly ℕ := sc1_0

theorem sc1_sound : shEval sc1 =
    EEVec (latP 1) (-1 : ℤ) ((11 : ℕ) : ℤ) (shEval sc0) := by
  have hs : List.Forall₂ (fun (t : ℚ × List ℕ) Q => shEval Q =
      EEVec (latP 1) (-1 : ℤ) ((11 : ℕ) : ℤ) ((t.1 : ℂ) • shWord t.2))
      [(1, [])] [sc1_0] :=
    .cons sc1_0_sound .nil
  have h := shScreen_blocks 11 _ _ hs
  change shEval sc1 = EEVec (latP 1) (-1 : ℤ) ((11 : ℕ) : ℤ) (shEval [(1, [])])
  rw [← h]
  simp only [sc1, List.flatten_cons, List.flatten_nil,
    shEval_append, shEval_nil, add_zero]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc1_degrees : ∀ t ∈ sc1, t.2.sum = 11 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoT
