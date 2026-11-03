import VOA.Classification.COne.OrbIcoTScreen3B00

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc3_2 : RawPoly ℕ :=
  [(6, [7, 9, 11]),
   (-6, [7, 10, 10]),
   (-6, [8, 8, 11]),
   (12, [8, 9, 10]),
   (-6, [9, 9, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc3_2_check : normR (sc3_0 ++ sc3_1) = sc3_2 := by
  decide +kernel

theorem sc3_2_sound : shEval sc3_2 = shEval sc3_0 + shEval sc3_1 :=
  shEval_merge sc3_0 sc3_1 sc3_2 sc3_2_check

def sc3 : RawPoly ℕ := sc3_2

theorem sc3_sound : shEval sc3 =
    EEVec (latP 1) (-1 : ℤ) ((7 : ℕ) : ℤ) (shEval sc2) := by
  have hs : List.Forall₂ (fun (t : ℚ × List ℕ) Q => shEval Q =
      EEVec (latP 1) (-1 : ℤ) ((7 : ℕ) : ℤ) ((t.1 : ℂ) • shWord t.2))
      [(2, [9, 11]),
   (-2, [10, 10])] [sc3_0, sc3_1] :=
    .cons sc3_0_sound <|
    .cons sc3_1_sound .nil
  have h := shScreen_blocks 7 _ _ hs
  change shEval sc3 = EEVec (latP 1) (-1 : ℤ) ((7 : ℕ) : ℤ) (shEval [(2, [9, 11]),
   (-2, [10, 10])])
  rw [← h]
  simp only [sc3, sc3_2_sound, List.flatten_cons, List.flatten_nil,
    shEval_append, shEval_nil, add_zero]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc3_degrees : ∀ t ∈ sc3, t.2.sum = 27 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoT
