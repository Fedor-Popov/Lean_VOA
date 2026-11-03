/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode1Part0Outer

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

macro "close_h_mode1_part0_outer" : tactic => `(tactic|
  (unfold hMode1Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode1Part0OuterNeg7ExpectedQ, hMode1Part0OuterNeg6ExpectedQ,
    hMode1Part0OuterNeg5ExpectedQ, hMode1Part0OuterNeg4ExpectedQ,
    hMode1Part0OuterNeg3ExpectedQ, hMode1Part0OuterNeg2ExpectedQ,
    hMode1Part0OuterNeg1ExpectedQ, hMode1Part0Outer0ExpectedQ,
    hMode1Part0Outer1ExpectedQ, hMode1Part0Outer2ExpectedQ,
    hMode1Part0Outer3ExpectedQ, hMode1Part0Outer4ExpectedQ,
    hMode1Part0Outer5ExpectedQ, hMode1Part0Outer6ExpectedQ,
    hMode1Part0Outer7ExpectedQ, hMode1Part0Outer8ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0OuterNeg5_eq :
    hMode1Part0OuterSparseQ (-5) = hMode1Part0OuterNeg5ExpectedQ := by
  close_h_mode1_part0_outer
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0OuterNeg4_eq :
    hMode1Part0OuterSparseQ (-4) = hMode1Part0OuterNeg4ExpectedQ := by
  close_h_mode1_part0_outer

#print axioms hMode1Part0OuterNeg5_eq
#print axioms hMode1Part0OuterNeg4_eq

end VOA.LatGen.WpTwoZhuSparseCompute
