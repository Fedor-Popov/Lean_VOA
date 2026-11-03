/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part1

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- This vanishing mode/monomial replay is independently kernel-checked.
theorem hEntryMode2Part2_eq :
    hEntryModePartSparseQ 2 2 = hEntry0Mode2Part2ExpectedQ := by
  unfold hEntryModePartSparseQ
  norm_num (config := { maxSteps := 1000000 })
    [hLeftPartSparseQ, l3hExpectedQ, hEntry0Mode2Part2ExpectedQ,
    voaModeActSparseQ, zhuStateActSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

#print axioms hEntryMode2Part2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
