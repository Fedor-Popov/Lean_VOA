import VOA.Classification.COne.OrbIcoTScreen4B01

/-! Input blocks for the exact Schur-product screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval

def sc4_5 : RawPoly ℕ :=
  [(24, [5, 7, 9, 11]),
   (-24, [5, 7, 10, 10]),
   (-18, [5, 8, 8, 11]),
   (36, [5, 8, 9, 10]),
   (-18, [5, 9, 9, 9]),
   (-12, [6, 6, 9, 11]),
   (12, [6, 6, 10, 10]),
   (-12, [6, 8, 8, 10]),
   (12, [6, 8, 9, 9]),
   (6, [7, 7, 7, 11]),
   (-12, [7, 7, 9, 9]),
   (6, [7, 8, 8, 9])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_5_check : normR (sc4_0 ++ sc4_1) = sc4_5 := by
  decide +kernel

theorem sc4_5_sound : shEval sc4_5 = shEval sc4_0 + shEval sc4_1 :=
  shEval_merge sc4_0 sc4_1 sc4_5 sc4_5_check

def sc4_6 : RawPoly ℕ :=
  [(-6, [5, 8, 8, 11]),
   (12, [5, 8, 9, 10]),
   (-12, [6, 6, 9, 11]),
   (12, [6, 6, 10, 10]),
   (48, [6, 7, 8, 11]),
   (-48, [6, 7, 9, 10]),
   (-36, [6, 8, 8, 10]),
   (-24, [7, 7, 7, 11]),
   (12, [7, 7, 8, 10]),
   (72, [7, 7, 9, 9]),
   (-6, [7, 8, 8, 9]),
   (-24, [8, 8, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_6_check : normR (sc4_2 ++ sc4_3) = sc4_6 := by
  decide +kernel

theorem sc4_6_sound : shEval sc4_6 = shEval sc4_2 + shEval sc4_3 :=
  shEval_merge sc4_2 sc4_3 sc4_6 sc4_6_check

def sc4_7 : RawPoly ℕ :=
  [(24, [5, 7, 9, 11]),
   (-24, [5, 7, 10, 10]),
   (-24, [5, 8, 8, 11]),
   (48, [5, 8, 9, 10]),
   (-18, [5, 9, 9, 9]),
   (-24, [6, 6, 9, 11]),
   (24, [6, 6, 10, 10]),
   (48, [6, 7, 8, 11]),
   (-48, [6, 7, 9, 10]),
   (-48, [6, 8, 8, 10]),
   (12, [6, 8, 9, 9]),
   (-18, [7, 7, 7, 11]),
   (12, [7, 7, 8, 10]),
   (60, [7, 7, 9, 9]),
   (-24, [8, 8, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_7_check : normR (sc4_5 ++ sc4_6) = sc4_7 := by
  decide +kernel

theorem sc4_7_sound : shEval sc4_7 = shEval sc4_5 + shEval sc4_6 :=
  shEval_merge sc4_5 sc4_6 sc4_7 sc4_7_check

def sc4_8 : RawPoly ℕ :=
  [(24, [5, 7, 9, 11]),
   (-24, [5, 7, 10, 10]),
   (-24, [5, 8, 8, 11]),
   (48, [5, 8, 9, 10]),
   (-24, [5, 9, 9, 9]),
   (-24, [6, 6, 9, 11]),
   (24, [6, 6, 10, 10]),
   (48, [6, 7, 8, 11]),
   (-48, [6, 7, 9, 10]),
   (-48, [6, 8, 8, 10]),
   (48, [6, 8, 9, 9]),
   (-24, [7, 7, 7, 11]),
   (48, [7, 7, 8, 10]),
   (24, [7, 7, 9, 9]),
   (-72, [7, 8, 8, 9]),
   (24, [8, 8, 8, 8])]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_8_check : normR (sc4_7 ++ sc4_4) = sc4_8 := by
  decide +kernel

theorem sc4_8_sound : shEval sc4_8 = shEval sc4_7 + shEval sc4_4 :=
  shEval_merge sc4_7 sc4_4 sc4_8 sc4_8_check

def sc4 : RawPoly ℕ := sc4_8

theorem sc4_sound : shEval sc4 =
    EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (shEval sc3) := by
  have hs : List.Forall₂ (fun (t : ℚ × List ℕ) Q => shEval Q =
      EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) ((t.1 : ℂ) • shWord t.2))
      [(6, [7, 9, 11]),
   (-6, [7, 10, 10]),
   (-6, [8, 8, 11]),
   (12, [8, 9, 10]),
   (-6, [9, 9, 9])] [sc4_0, sc4_1, sc4_2, sc4_3, sc4_4] :=
    .cons sc4_0_sound <|
    .cons sc4_1_sound <|
    .cons sc4_2_sound <|
    .cons sc4_3_sound <|
    .cons sc4_4_sound .nil
  have h := shScreen_blocks 5 _ _ hs
  change shEval sc4 = EEVec (latP 1) (-1 : ℤ) ((5 : ℕ) : ℤ) (shEval [(6, [7, 9, 11]),
   (-6, [7, 10, 10]),
   (-6, [8, 8, 11]),
   (12, [8, 9, 10]),
   (-6, [9, 9, 9])])
  rw [← h]
  simp only [sc4, sc4_8_sound, sc4_7_sound, sc4_6_sound, sc4_5_sound, List.flatten_cons,
    List.flatten_nil,
    shEval_append, shEval_nil, add_zero, add_assoc]

set_option maxHeartbeats 3000000 in
-- Certify a small input block before assembling the linear combination.
set_option maxRecDepth 4096 in
theorem sc4_degrees : ∀ t ∈ sc4, t.2.sum = 32 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoT
