/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part0Outer

/-! # Negative outer-mode certificates for the cubic H branch at Zhu mode three -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

macro "close_h_mode3_part0_outer" : tactic => `(tactic|
  (unfold hMode3Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode3Part0OuterNeg7ExpectedQ, hMode3Part0OuterNeg6ExpectedQ,
    hMode3Part0OuterNeg5ExpectedQ, hMode3Part0OuterNeg4ExpectedQ,
    hMode3Part0OuterNeg3ExpectedQ, hMode3Part0OuterNeg2ExpectedQ,
    hMode3Part0OuterNeg1ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg7_eq :
    hMode3Part0OuterSparseQ (-7) = hMode3Part0OuterNeg7ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg6_eq :
    hMode3Part0OuterSparseQ (-6) = hMode3Part0OuterNeg6ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg5_eq :
    hMode3Part0OuterSparseQ (-5) = hMode3Part0OuterNeg5ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg4_eq :
    hMode3Part0OuterSparseQ (-4) = hMode3Part0OuterNeg4ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg3_eq :
    hMode3Part0OuterSparseQ (-3) = hMode3Part0OuterNeg3ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg2_eq :
    hMode3Part0OuterSparseQ (-2) = hMode3Part0OuterNeg2ExpectedQ := by
  close_h_mode3_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0OuterNeg1_eq :
    hMode3Part0OuterSparseQ (-1) = hMode3Part0OuterNeg1ExpectedQ := by
  close_h_mode3_part0_outer

#print axioms hMode3Part0OuterNeg1_eq

end VOA.LatGen.WpTwoZhuSparseCompute
