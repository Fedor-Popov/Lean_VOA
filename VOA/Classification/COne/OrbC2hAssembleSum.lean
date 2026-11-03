import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2g LatMod

theorem iterateS_sum_value (n : ℤ) (i : ℕ) (S A B C D E F G H T : SectorVector)
    (hA : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (n+i) (evaluate S) = evaluate A)
    (hB : (V2m 4 four_ge_one).smul (ls 4 JR) i (evaluate S) = evaluate B)
    (hC : (V2m 4 four_ge_one).smul (ls 4 JR) (n+i) (evaluate S) = evaluate C)
    (hD : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) i (evaluate S) = evaluate D)
    (hE : (V2m 4 four_ge_one).smul (ls 4 JR) (-2-i) (evaluate A) = evaluate E)
    (hF : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-2+n-i) (evaluate B) = evaluate F)
    (hG : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-2-i) (evaluate C) = evaluate G)
    (hH : (V2m 4 four_ge_one).smul (ls 4 JR) (-2+n-i) (evaluate D) = evaluate H)
    (hT : scaleVector (i+1)
      (zipMany 100000 [E, scaleVector (-1) F, scaleVector (-1) G, H]) = T) :
    evaluate (iterateS n i S) = evaluate T := by
  have h := congrArg evaluate hT
  simp only [evaluate_scaleVector, evaluate_zipMany, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at h
  simpa only [iterateS, evaluate_compact, evaluate_scaleVector, evaluate_append,
    evaluate_neutralS, evaluate_eS, hA, hB, hC, hD, hE, hF, hG, hH, add_assoc] using h

end VOA.Classification.COne.OrbC2h
