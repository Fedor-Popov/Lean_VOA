/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNeg5Block2

/-! # Collection of the three right-state blocks at outer mode `m = -5` -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- Source-pruning leaves two one-monomial blocks, each certified independently.
theorem hMode0Part0OuterNeg5_eq :
    hMode0Part0OuterSparseQ (-5) = hMode0Part0OuterN5ExpectedQ := by
  unfold hMode0Part0OuterSparseQ
  norm_num only [Int.reduceNeg, Int.reduceLE, ↓reduceIte, Int.reduceAdd]
  rw [hMode0Part0Neg5_inner_eq_expected]
  simp only [if_false]
  have hsplit :
      scaleQ (-(1575 / 4096))
          (aWordActSparseQ [0, 0] 6 (Int.toNat 2)
            hMode0Part0Neg5InnerExpectedQ) =
        sumQ [hMode0Part0OuterNeg5BlockSparseQ 0,
          hMode0Part0OuterNeg5BlockSparseQ 1,
          hMode0Part0OuterNeg5BlockSparseQ 2] := by
    norm_num (config := { maxSteps := 1000000 })
      [hMode0Part0Neg5InnerExpectedQ,
      hMode0Part0OuterNeg5BlockSparseQ,
      hMode0Part0Neg5InnerBlockExpectedQ,
      hMode0Part0Neg5InnerBlock0ExpectedQ,
      hMode0Part0Neg5InnerBlock1ExpectedQ,
      hMode0Part0Neg5InnerBlock2ExpectedQ,
      aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
      aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
      annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
      normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
      List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]
  rw [hsplit, hMode0Part0OuterNeg5Block0_eq,
    hMode0Part0OuterNeg5Block1_eq, hMode0Part0OuterNeg5Block2_eq]
  norm_num [hMode0Part0OuterNeg5Block0ExpectedQ,
    hMode0Part0OuterNeg5Block1ExpectedQ,
    hMode0Part0OuterNeg5Block2ExpectedQ,
    hMode0Part0OuterN5ExpectedQ, sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg5_eq
end AxiomAudit
