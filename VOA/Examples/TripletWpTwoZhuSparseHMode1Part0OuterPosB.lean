/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode1Part0OuterPosA

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

macro "close_h_mode1_part0_outer_pos_b" : tactic => `(tactic|
  (unfold hMode1Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode1Part0Outer4ExpectedQ, hMode1Part0Outer5ExpectedQ,
    hMode1Part0Outer6ExpectedQ, hMode1Part0Outer7ExpectedQ,
    hMode1Part0Outer8ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer4_eq :
    hMode1Part0OuterSparseQ 4 = hMode1Part0Outer4ExpectedQ := by
  close_h_mode1_part0_outer_pos_b
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer5_eq :
    hMode1Part0OuterSparseQ 5 = hMode1Part0Outer5ExpectedQ := by
  close_h_mode1_part0_outer_pos_b
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer6_eq :
    hMode1Part0OuterSparseQ 6 = hMode1Part0Outer6ExpectedQ := by
  close_h_mode1_part0_outer_pos_b
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer7_eq :
    hMode1Part0OuterSparseQ 7 = hMode1Part0Outer7ExpectedQ := by
  close_h_mode1_part0_outer_pos_b
set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode1Part0Outer8_eq :
    hMode1Part0OuterSparseQ 8 = hMode1Part0Outer8ExpectedQ := by
  close_h_mode1_part0_outer_pos_b

#print axioms hMode1Part0Outer8_eq

end VOA.LatGen.WpTwoZhuSparseCompute
