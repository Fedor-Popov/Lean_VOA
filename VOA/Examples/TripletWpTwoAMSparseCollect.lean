/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoAMSparseModesB

/-! # Collection of the fourteen three-current outer-mode certificates -/

namespace VOA.LatGen.WpTwoAMSparseCompute

open VOA.SparseRational

private theorem intIccListQ_neg_four_nine_collect :
    intIccListQ (-4) 9 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  norm_num [intIccListQ, natRangeQ, Int.toNat]

/-- The three-current source is checked by fourteen independent outer-mode
certificates and then collected structurally. -/
theorem hPartZeroZeroZeroSparseQ_eq :
    hPartZeroZeroZeroSparseQ = hPartZeroZeroZeroExpectedQ := by
  rw [hPartZeroZeroZeroSparseQ, aWordActSparseQ]
  norm_num [aWordWeightQ]
  rw [sumSparseIcc, intIccListQ_neg_four_nine_collect]
  rw [scaleQ_sumQ (1 / 6) (by norm_num)]
  simp only [List.map_cons, List.map_nil]
  change sumQ
      [hOuterZeroZeroZeroSparseQ (-4), hOuterZeroZeroZeroSparseQ (-3),
       hOuterZeroZeroZeroSparseQ (-2), hOuterZeroZeroZeroSparseQ (-1),
       hOuterZeroZeroZeroSparseQ 0, hOuterZeroZeroZeroSparseQ 1,
       hOuterZeroZeroZeroSparseQ 2, hOuterZeroZeroZeroSparseQ 3,
       hOuterZeroZeroZeroSparseQ 4, hOuterZeroZeroZeroSparseQ 5,
       hOuterZeroZeroZeroSparseQ 6, hOuterZeroZeroZeroSparseQ 7,
       hOuterZeroZeroZeroSparseQ 8, hOuterZeroZeroZeroSparseQ 9] =
        hPartZeroZeroZeroExpectedQ
  have hnegFour : hOuterZeroZeroZeroSparseQ (-4) = hOuterNegFourExpectedQ := by
    simpa [hOuterNegFourSparseQ] using hOuterNegFourSparseQ_eq
  rw [hnegFour, hOuterNegThreeSparseQ_eq, hOuterNegTwoSparseQ_eq,
    hOuterNegOneSparseQ_eq, hOuterZeroSparseQ_eq, hOuterOneSparseQ_eq,
    hOuterTwoSparseQ_eq, hOuterThreeSparseQ_eq, hOuterFourSparseQ_eq,
    hOuterFiveSparseQ_eq, hOuterSixSparseQ_eq, hOuterSevenSparseQ_eq,
    hOuterEightSparseQ_eq, hOuterNineSparseQ_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hOuterNegFourExpectedQ, hPartZeroZeroZeroExpectedQ, sumQ, addQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

end VOA.LatGen.WpTwoAMSparseCompute
