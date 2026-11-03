/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNeg5Block1

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One independently normalized right-state block of the difficult summand.
theorem hMode0Part0OuterNeg5Block2_eq :
    hMode0Part0OuterNeg5BlockSparseQ 2 =
      hMode0Part0OuterNeg5Block2ExpectedQ := by
  unfold hMode0Part0OuterNeg5BlockSparseQ
  norm_num (config := { maxSteps := 1000000 })
    [hMode0Part0Neg5InnerBlockExpectedQ,
    hMode0Part0Neg5InnerBlock2ExpectedQ,
    hMode0Part0OuterNeg5Block2ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg5Block2_eq
end AxiomAudit
