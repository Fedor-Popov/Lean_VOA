/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNeg5Base
import VOA.Examples.TripletWpTwoZhuSparseLhs4Base

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem hMode0Part0OuterNeg5Block0_eq :
    hMode0Part0OuterNeg5BlockSparseQ 0 =
      hMode0Part0OuterNeg5Block0ExpectedQ := by
  change scaleQ (-1575 / 4096) (aWordActSparseQ [0, 0] 6 2 []) = []
  rw [VOA.LatGen.WpTwoZhuSparseLhs.aWordActSparseQ_empty]
  simp [scaleQ]

set_option maxHeartbeats 1000000 in
-- One independently normalized right-state block of the difficult summand.
theorem hMode0Part0OuterNeg5Block1_eq :
    hMode0Part0OuterNeg5BlockSparseQ 1 =
      hMode0Part0OuterNeg5Block1ExpectedQ := by
  unfold hMode0Part0OuterNeg5BlockSparseQ
  norm_num (config := { maxSteps := 1000000 })
    [hMode0Part0Neg5InnerBlockExpectedQ,
    hMode0Part0Neg5InnerBlock1ExpectedQ,
    hMode0Part0OuterNeg5Block1ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg5Block1_eq
end AxiomAudit
