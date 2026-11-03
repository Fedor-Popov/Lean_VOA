/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoAMSparseModesA

/-! # Outer-mode sparse certificates, modes `3` through `9` -/

namespace VOA.LatGen.WpTwoAMSparseCompute

open VOA.SparseRational

set_option maxHeartbeats 1000000 in
theorem hOuterThreeSparseQ_eq : hOuterZeroZeroZeroSparseQ 3 = normalizeQ
    [(1 / 18, [0, 0, 0, 0, 1, 3]), (1 / 6, [0, 0, 1, 1, 3]),
     (2 / 3, [0, 0, 3, 3]), (1 / 9, [0, 1, 2, 3]),
     (4 / 3, [0, 3, 4]), (2 / 3, [1, 3, 3]), (4 / 3, [3, 5])] := by
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
theorem hOuterFourSparseQ_eq : hOuterZeroZeroZeroSparseQ 4 = normalizeQ
    [(1 / 36, [0, 0, 0, 0, 0, 4]), (1 / 12, [0, 0, 0, 1, 4]),
     (13 / 18, [0, 0, 2, 4]), (4 / 3, [0, 3, 4]),
     (2 / 3, [1, 2, 4]), (4 / 3, [4, 4])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterFiveSparseQ_eq : hOuterZeroZeroZeroSparseQ 5 = normalizeQ
    [(2 / 3, [0, 0, 1, 5]), (4 / 3, [0, 2, 5]),
     (2 / 3, [1, 1, 5]), (4 / 3, [3, 5])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterSixSparseQ_eq : hOuterZeroZeroZeroSparseQ 6 = normalizeQ
    [(2 / 3, [0, 0, 0, 6]), (2, [0, 1, 6]), (4 / 3, [2, 6])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterSevenSparseQ_eq : hOuterZeroZeroZeroSparseQ 7 =
    normalizeQ [(4 / 3, [0, 0, 7]), (4 / 3, [1, 7])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterEightSparseQ_eq : hOuterZeroZeroZeroSparseQ 8 =
    normalizeQ [(4, [0, 8])] := by
  rw [hOuterZeroZeroZeroSparseQ]
  norm_num
  rw [aWordActSparseQ]
  norm_num (config := { maxSteps := 1000000 })
    [aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    Int.toNat, Function.comp_apply, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem hOuterNineSparseQ_eq : hOuterZeroZeroZeroSparseQ 9 =
    normalizeQ [(16 / 3, [9])] := by
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
