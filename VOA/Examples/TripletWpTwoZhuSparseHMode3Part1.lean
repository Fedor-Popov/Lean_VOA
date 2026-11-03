/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part2

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- This exact mode/monomial replay is isolated so its kernel check stays bounded.
theorem hEntryMode3Part1_eq :
    hEntryModePartSparseQ 3 1 = hEntry0Mode3Part1ExpectedQ := by
  unfold hEntryModePartSparseQ
  norm_num (config := { maxSteps := 1000000 })
    [hLeftPartSparseQ, l3hExpectedQ, hEntry0Mode3Part1ExpectedQ,
    voaModeActSparseQ, zhuStateActSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

#print axioms hEntryMode3Part1_eq

end VOA.LatGen.WpTwoZhuSparseCompute
