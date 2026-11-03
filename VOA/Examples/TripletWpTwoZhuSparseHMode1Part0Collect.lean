/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode1Part0OuterPosB

/-! # Collection of the cubic H branch at Zhu mode one -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem hEntryMode1Part0_eq_outer_sum :
    hEntryModePartSparseQ 1 0 = sumQ
      [hMode1Part0OuterSparseQ (-7), hMode1Part0OuterSparseQ (-6),
       hMode1Part0OuterSparseQ (-5), hMode1Part0OuterSparseQ (-4),
       hMode1Part0OuterSparseQ (-3), hMode1Part0OuterSparseQ (-2),
       hMode1Part0OuterSparseQ (-1), hMode1Part0OuterSparseQ 0,
       hMode1Part0OuterSparseQ 1, hMode1Part0OuterSparseQ 2,
       hMode1Part0OuterSparseQ 3, hMode1Part0OuterSparseQ 4,
       hMode1Part0OuterSparseQ 5, hMode1Part0OuterSparseQ 6,
       hMode1Part0OuterSparseQ 7, hMode1Part0OuterSparseQ 8] := by
  unfold hEntryModePartSparseQ voaModeActSparseQ zhuStateActSparseQ bindQ
  norm_num [hLeftPartSparseQ, sumQ]
  rw [aWordActSparseQ]
  norm_num only [aWordWeightQ, Int.reduceNeg, Int.reduceAdd]
  rw [max_eq_right (by norm_num : (-1 : ℤ) ≤ 8)]
  simp only [zero_sub]
  change scaleQ (-(4725 / 2048)) (scaleQ 3 (scaleQ (1 / 6)
      (sumSparseIcc (-7) 8 fun m =>
        if 0 ≤ m then
          aFieldActSparseQ 0 m (aWordActSparseQ [0, 0] (-m) 6 l3hExpectedQ)
        else
          aWordActSparseQ [0, 0] (-m) (7 + m).toNat
            (aFieldActSparseQ 0 m l3hExpectedQ)))) = _
  unfold sumSparseIcc
  rw [scaleQ_sumQ (1 / 6) (by norm_num),
    scaleQ_sumQ 3 (by norm_num),
    scaleQ_sumQ (-(4725 / 2048)) (by norm_num)]
  norm_num [intIccListQ, natRangeQ, hMode1Part0OuterSparseQ,
    Function.comp_apply, Int.toNat, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, sumQ]

set_option maxHeartbeats 1000000 in
-- The sixteen independently checked outer ledgers merge to the cubic branch.
theorem hEntryMode1Part0_eq :
    hEntryModePartSparseQ 1 0 = hEntry0Mode1Part0ExpectedQ := by
  rw [hEntryMode1Part0_eq_outer_sum,
    hMode1Part0OuterNeg7_eq, hMode1Part0OuterNeg6_eq,
    hMode1Part0OuterNeg5_eq, hMode1Part0OuterNeg4_eq,
    hMode1Part0OuterNeg3_eq, hMode1Part0OuterNeg2_eq,
    hMode1Part0OuterNeg1_eq, hMode1Part0Outer0_eq,
    hMode1Part0Outer1_eq, hMode1Part0Outer2_eq,
    hMode1Part0Outer3_eq, hMode1Part0Outer4_eq,
    hMode1Part0Outer5_eq, hMode1Part0Outer6_eq,
    hMode1Part0Outer7_eq, hMode1Part0Outer8_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hMode1Part0OuterNeg7ExpectedQ, hMode1Part0OuterNeg6ExpectedQ,
    hMode1Part0OuterNeg5ExpectedQ, hMode1Part0OuterNeg4ExpectedQ,
    hMode1Part0OuterNeg3ExpectedQ, hMode1Part0OuterNeg2ExpectedQ,
    hMode1Part0OuterNeg1ExpectedQ, hMode1Part0Outer0ExpectedQ,
    hMode1Part0Outer1ExpectedQ, hMode1Part0Outer2ExpectedQ,
    hMode1Part0Outer3ExpectedQ, hMode1Part0Outer4ExpectedQ,
    hMode1Part0Outer5ExpectedQ, hMode1Part0Outer6ExpectedQ,
    hMode1Part0Outer7ExpectedQ, hMode1Part0Outer8ExpectedQ,
    hEntry0Mode1Part0ExpectedQ, sumQ, addQ, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord, List.map_cons, List.map_nil]

#print axioms hEntryMode1Part0_eq_outer_sum
#print axioms hEntryMode1Part0_eq

end VOA.LatGen.WpTwoZhuSparseCompute
