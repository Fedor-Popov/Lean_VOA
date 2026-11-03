/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part0OuterNeg

/-! # First nonnegative outer modes for the cubic H branch at Zhu mode three -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

macro "close_h_mode3_part0_outer_nonneg" : tactic => `(tactic|
  (unfold hMode3Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode3Part0Outer0ExpectedQ, hMode3Part0Outer1ExpectedQ,
    hMode3Part0Outer2ExpectedQ, hMode3Part0Outer3ExpectedQ,
    hMode3Part0Outer4ExpectedQ, hMode3Part0Outer5ExpectedQ,
    hMode3Part0Outer6ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer0_eq :
    hMode3Part0OuterSparseQ 0 = hMode3Part0Outer0ExpectedQ := by
  close_h_mode3_part0_outer_nonneg
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer1_eq :
    hMode3Part0OuterSparseQ 1 = hMode3Part0Outer1ExpectedQ := by
  close_h_mode3_part0_outer_nonneg
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer2_eq :
    hMode3Part0OuterSparseQ 2 = hMode3Part0Outer2ExpectedQ := by
  close_h_mode3_part0_outer_nonneg

#print axioms hMode3Part0Outer2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
