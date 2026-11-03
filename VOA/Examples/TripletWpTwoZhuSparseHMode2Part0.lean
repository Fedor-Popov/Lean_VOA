/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0OuterNonnegB

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem hEntryMode2Part0_eq :
    hEntryModePartSparseQ 2 0 = hEntry0Mode2Part0ExpectedQ := by
  unfold hEntryModePartSparseQ
  norm_num only [Nat.choose, hLeftPartSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, bindQ, List.map_cons, List.map_nil, sumQ,
    addQ_nil_right]
  rw [aWordActSparseQ, sumSparseIcc,
    scaleQ_sumQ (1 / 6) (by norm_num),
    scaleQ_sumQ 3 (by norm_num),
    scaleQ_sumQ (-(4725 / 2048)) (by norm_num)]
  norm_num [aWordWeightQ, intIccListQ, natRangeQ, Int.toNat]
  have hneg : (-(4725 / 2048) : ℚ) = ((-4725 : ℚ) / 2048) := by
    norm_num
  rw [hneg]
  change sumQ [hMode2Part0OuterSparseQ (-7),
    hMode2Part0OuterSparseQ (-6), hMode2Part0OuterSparseQ (-5),
    hMode2Part0OuterSparseQ (-4), hMode2Part0OuterSparseQ (-3),
    hMode2Part0OuterSparseQ (-2), hMode2Part0OuterSparseQ (-1),
    hMode2Part0OuterSparseQ 0, hMode2Part0OuterSparseQ 1,
    hMode2Part0OuterSparseQ 2, hMode2Part0OuterSparseQ 3,
    hMode2Part0OuterSparseQ 4, hMode2Part0OuterSparseQ 5,
    hMode2Part0OuterSparseQ 6, hMode2Part0OuterSparseQ 7] =
      hEntry0Mode2Part0ExpectedQ
  rw [hMode2Part0OuterNeg7_eq, hMode2Part0OuterNeg6_eq,
    hMode2Part0OuterNeg5_eq, hMode2Part0OuterNeg4_eq,
    hMode2Part0OuterNeg3_eq, hMode2Part0OuterNeg2_eq,
    hMode2Part0OuterNeg1_eq, hMode2Part0Outer0_eq,
    hMode2Part0Outer1_eq, hMode2Part0Outer2_eq,
    hMode2Part0Outer3_eq, hMode2Part0Outer4_eq,
    hMode2Part0Outer5_eq, hMode2Part0Outer6_eq,
    hMode2Part0Outer7_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hMode2Part0OuterNeg7ExpectedQ, hMode2Part0OuterNeg6ExpectedQ,
    hMode2Part0OuterNeg5ExpectedQ, hMode2Part0OuterNeg4ExpectedQ,
    hMode2Part0OuterNeg3ExpectedQ, hMode2Part0OuterNeg2ExpectedQ,
    hMode2Part0OuterNeg1ExpectedQ, hMode2Part0Outer0ExpectedQ,
    hMode2Part0Outer1ExpectedQ, hMode2Part0Outer2ExpectedQ,
    hMode2Part0Outer3ExpectedQ, hMode2Part0Outer4ExpectedQ,
    hMode2Part0Outer5ExpectedQ, hMode2Part0Outer6ExpectedQ,
    hMode2Part0Outer7ExpectedQ, hEntry0Mode2Part0ExpectedQ,
    sumQ, addQ, compareWord]

#print axioms hEntryMode2Part0_eq

end VOA.LatGen.WpTwoZhuSparseCompute
