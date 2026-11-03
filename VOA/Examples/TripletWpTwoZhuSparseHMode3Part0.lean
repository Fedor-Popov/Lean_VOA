/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part0OuterNonnegB

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem hEntryMode3Part0_eq :
    hEntryModePartSparseQ 3 0 = hEntry0Mode3Part0ExpectedQ := by
  unfold hEntryModePartSparseQ
  norm_num only [Nat.choose, hLeftPartSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, bindQ, List.map_cons, List.map_nil, sumQ,
    addQ_nil_right]
  rw [aWordActSparseQ, sumSparseIcc,
    scaleQ_sumQ (1 / 6) (by norm_num),
    scaleQ_sumQ 1 (by norm_num),
    scaleQ_sumQ (-(4725 / 2048)) (by norm_num)]
  norm_num [aWordWeightQ, intIccListQ, natRangeQ, Int.toNat]
  have hneg : (-(4725 / 2048) : ℚ) = ((-4725 : ℚ) / 2048) := by
    norm_num
  rw [hneg]
  change sumQ [hMode3Part0OuterSparseQ (-7),
    hMode3Part0OuterSparseQ (-6), hMode3Part0OuterSparseQ (-5),
    hMode3Part0OuterSparseQ (-4), hMode3Part0OuterSparseQ (-3),
    hMode3Part0OuterSparseQ (-2), hMode3Part0OuterSparseQ (-1),
    hMode3Part0OuterSparseQ 0, hMode3Part0OuterSparseQ 1,
    hMode3Part0OuterSparseQ 2, hMode3Part0OuterSparseQ 3,
    hMode3Part0OuterSparseQ 4, hMode3Part0OuterSparseQ 5,
    hMode3Part0OuterSparseQ 6] = hEntry0Mode3Part0ExpectedQ
  rw [hMode3Part0OuterNeg7_eq, hMode3Part0OuterNeg6_eq,
    hMode3Part0OuterNeg5_eq, hMode3Part0OuterNeg4_eq,
    hMode3Part0OuterNeg3_eq, hMode3Part0OuterNeg2_eq,
    hMode3Part0OuterNeg1_eq, hMode3Part0Outer0_eq,
    hMode3Part0Outer1_eq, hMode3Part0Outer2_eq,
    hMode3Part0Outer3_eq, hMode3Part0Outer4_eq,
    hMode3Part0Outer5_eq, hMode3Part0Outer6_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hMode3Part0OuterNeg7ExpectedQ, hMode3Part0OuterNeg6ExpectedQ,
    hMode3Part0OuterNeg5ExpectedQ, hMode3Part0OuterNeg4ExpectedQ,
    hMode3Part0OuterNeg3ExpectedQ, hMode3Part0OuterNeg2ExpectedQ,
    hMode3Part0OuterNeg1ExpectedQ, hMode3Part0Outer0ExpectedQ,
    hMode3Part0Outer1ExpectedQ, hMode3Part0Outer2ExpectedQ,
    hMode3Part0Outer3ExpectedQ, hMode3Part0Outer4ExpectedQ,
    hMode3Part0Outer5ExpectedQ, hMode3Part0Outer6ExpectedQ,
    hEntry0Mode3Part0ExpectedQ, sumQ, addQ, compareWord]

#print axioms hEntryMode3Part0_eq

end VOA.LatGen.WpTwoZhuSparseCompute
