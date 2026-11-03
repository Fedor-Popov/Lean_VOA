/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoAMSparseCompute

/-! # Outer-mode sparse certificates, modes `-4` through `2` -/

namespace VOA.LatGen.WpTwoAMSparseCompute

open VOA.SparseRational

def hOuterZeroZeroZeroSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1 / 6)
    (if 0 ≤ m then
      aFieldActSparseQ 0 m (aWordActSparseQ [0, 0] (4 - m) 3 sThreeSparseQ)
    else
      aWordActSparseQ [0, 0] (4 - m) ((4 : ℤ) + m).toNat
        (aFieldActSparseQ 0 m sThreeSparseQ))

def hOuterNegFourSparseQ : SparseRational.Poly ℕ := hOuterZeroZeroZeroSparseQ (-4)

def hOuterNegFourExpectedQ : SparseRational.Poly ℕ := normalizeQ
  [(4 / 3, [0, 8]), (4 / 3, [1, 7]), (4 / 3, [2, 6]),
   (4 / 3, [3, 5]), (2 / 3, [4, 4])]

private theorem intIccListQ_neg_one_nine :
    intIccListQ (-1) 9 = [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  norm_num [intIccListQ, natRangeQ, Int.toNat]

theorem hOuterNegFourSparseQ_eq :
    hOuterNegFourSparseQ = hOuterNegFourExpectedQ := by
  rw [hOuterNegFourSparseQ, hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num [aWordWeightQ]
  rw [sumSparseIcc, intIccListQ_neg_one_nine]
  simp only [List.map_cons, List.map_nil, sumQ]
  norm_num (config := { maxSteps := 1000000 })
    [hOuterNegFourExpectedQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
    intIccListQ, natRangeQ, Int.toNat, Function.comp_apply, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

theorem hOuterNegThreeSparseQ_eq :
    hOuterZeroZeroZeroSparseQ (-3) = normalizeQ
      [(4 / 3, [0, 0, 7]), (4 / 3, [0, 1, 6]), (4 / 3, [0, 2, 5]),
       (4 / 3, [0, 3, 4]), (16 / 3, [9])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num [aWordWeightQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterNegTwoSparseQ_eq :
    hOuterZeroZeroZeroSparseQ (-2) = normalizeQ
      [(2 / 3, [0, 0, 0, 6]), (2 / 3, [0, 0, 1, 5]),
       (2 / 3, [0, 0, 2, 4]), (1 / 3, [0, 0, 3, 3]),
       (2 / 3, [0, 1, 6]), (16 / 3, [0, 8]), (2 / 3, [1, 1, 5]),
       (2 / 3, [1, 2, 4]), (1 / 3, [1, 3, 3]), (16 / 3, [9])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num [aWordWeightQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterNegOneSparseQ_eq : hOuterZeroZeroZeroSparseQ (-1) = [] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

set_option maxHeartbeats 1000000 in
theorem hOuterZeroSparseQ_eq : hOuterZeroZeroZeroSparseQ 0 = normalizeQ
    [(1 / 18, [0, 0, 0, 0, 0, 4]), (1 / 18, [0, 0, 0, 0, 1, 3]),
     (1 / 36, [0, 0, 0, 0, 2, 2]), (1 / 6, [0, 0, 0, 1, 4]),
     (2 / 3, [0, 0, 0, 6]), (1 / 6, [0, 0, 1, 1, 3]),
     (1 / 12, [0, 0, 1, 2, 2]), (1 / 9, [0, 0, 2, 4]),
     (4 / 3, [0, 0, 7]), (1 / 9, [0, 1, 2, 3]), (2 / 3, [0, 1, 6]),
     (1 / 18, [0, 2, 2, 2]), (4 / 3, [0, 8])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

set_option maxHeartbeats 1000000 in
theorem hOuterOneSparseQ_eq : hOuterZeroZeroZeroSparseQ 1 = normalizeQ
    [(1 / 18, [0, 0, 0, 0, 1, 3]), (1 / 18, [0, 0, 0, 1, 1, 2]),
     (1 / 6, [0, 0, 1, 1, 3]), (2 / 3, [0, 0, 1, 5]),
     (1 / 6, [0, 1, 1, 1, 2]), (1 / 9, [0, 1, 2, 3]),
     (4 / 3, [0, 1, 6]), (1 / 9, [1, 1, 2, 2]),
     (2 / 3, [1, 1, 5]), (4 / 3, [1, 7])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

set_option maxHeartbeats 1000000 in
theorem hOuterTwoSparseQ_eq : hOuterZeroZeroZeroSparseQ 2 = normalizeQ
    [(1 / 18, [0, 0, 0, 0, 2, 2]), (1 / 36, [0, 0, 0, 1, 1, 2]),
     (1 / 6, [0, 0, 1, 2, 2]), (2 / 3, [0, 0, 2, 4]),
     (1 / 12, [0, 1, 1, 1, 2]), (1 / 9, [0, 2, 2, 2]),
     (4 / 3, [0, 2, 5]), (1 / 18, [1, 1, 2, 2]),
     (2 / 3, [1, 2, 4]), (4 / 3, [2, 6])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

end VOA.LatGen.WpTwoAMSparseCompute
