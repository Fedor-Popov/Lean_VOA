/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0
import VOA.Examples.TripletWpTwoZhuSparseHRightBlocks

/-! # Source-pruned extreme negative modes of the lowest cubic H branch -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem hMode0Part0Neg7_source_prune :
    aFieldActSparseQ 0 (-7) l3hExpectedQ =
      aFieldActSparseQ 0 (-7) (l3hBlockSparseQ 2) := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hExpectedQ, l3hBlockSparseQ, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ, normalizeQ,
    insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

theorem hMode0Part0Neg6_source_prune :
    aFieldActSparseQ 0 (-6) l3hExpectedQ =
      aFieldActSparseQ 0 (-6) (l3hBlockSparseQ 1) := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hExpectedQ, l3hBlockSparseQ, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ, normalizeQ,
    insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

set_option maxHeartbeats 1000000 in
-- Pruning the vanishing right-state blocks keeps this extreme mode bounded.
theorem hMode0Part0OuterNeg7_eq :
    hMode0Part0OuterSparseQ (-7) = hMode0Part0OuterN7ExpectedQ := by
  unfold hMode0Part0OuterSparseQ
  norm_num only [Int.reduceNeg, Int.reduceLE, ↓reduceIte, Int.reduceAdd]
  rw [hMode0Part0Neg7_source_prune]
  norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, hMode0Part0OuterN7ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

set_option maxHeartbeats 1000000 in
-- Pruning the vanishing right-state blocks keeps this extreme mode bounded.
theorem hMode0Part0OuterNeg6_eq :
    hMode0Part0OuterSparseQ (-6) = hMode0Part0OuterN6ExpectedQ := by
  unfold hMode0Part0OuterSparseQ
  norm_num only [Int.reduceNeg, Int.reduceLE, ↓reduceIte, Int.reduceAdd]
  rw [hMode0Part0Neg6_source_prune]
  norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, hMode0Part0OuterN6ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg7_eq
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg6_eq
end AxiomAudit
