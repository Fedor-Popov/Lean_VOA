/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode1Part0OuterNegB

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

macro "close_h_mode1_part0_outer_pos_a" : tactic => `(tactic|
  (unfold hMode1Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode1Part0Outer0ExpectedQ, hMode1Part0Outer1ExpectedQ,
    hMode1Part0Outer2ExpectedQ, hMode1Part0Outer3ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer0_eq :
    hMode1Part0OuterSparseQ 0 = hMode1Part0Outer0ExpectedQ := by
  close_h_mode1_part0_outer_pos_a
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer1_eq :
    hMode1Part0OuterSparseQ 1 = hMode1Part0Outer1ExpectedQ := by
  close_h_mode1_part0_outer_pos_a
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer2_eq :
    hMode1Part0OuterSparseQ 2 = hMode1Part0Outer2ExpectedQ := by
  close_h_mode1_part0_outer_pos_a
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer3_eq :
    hMode1Part0OuterSparseQ 3 = hMode1Part0Outer3ExpectedQ := by
  close_h_mode1_part0_outer_pos_a

#print axioms hMode1Part0Outer3_eq

end VOA.LatGen.WpTwoZhuSparseCompute
