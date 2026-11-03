/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterBlockSemantics
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock4
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock5
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock6
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock7
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock8
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBlock9

/-! # Evaluated assembly of the final nonnegative mode-zero cubic summands

The sparse evaluator is linear, so the three independently certified right-state blocks may be
merged after evaluation.  This is the state equality needed by the Zhu certificate; no equality
between the underlying sparse list representations is asserted.
-/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open VOA.SparseRational
open VOA.LatGen.WpTwoZhuSparseCompute

theorem hMode0Part0Outer4ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer4ExpectedQ = sumQ [hMode0Part0Outer4Block0ExpectedQ,
      hMode0Part0Outer4Block1ExpectedQ, hMode0Part0Outer4Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer4ExpectedQ, hMode0Part0Outer4Block0ExpectedQ,
    hMode0Part0Outer4Block1ExpectedQ, hMode0Part0Outer4Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer5ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer5ExpectedQ = sumQ [hMode0Part0Outer5Block0ExpectedQ,
      hMode0Part0Outer5Block1ExpectedQ, hMode0Part0Outer5Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer5ExpectedQ, hMode0Part0Outer5Block0ExpectedQ,
    hMode0Part0Outer5Block1ExpectedQ, hMode0Part0Outer5Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer6ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer6ExpectedQ = sumQ [hMode0Part0Outer6Block0ExpectedQ,
      hMode0Part0Outer6Block1ExpectedQ, hMode0Part0Outer6Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer6ExpectedQ, hMode0Part0Outer6Block0ExpectedQ,
    hMode0Part0Outer6Block1ExpectedQ, hMode0Part0Outer6Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer7ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer7ExpectedQ = sumQ [hMode0Part0Outer7Block0ExpectedQ,
      hMode0Part0Outer7Block1ExpectedQ, hMode0Part0Outer7Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer7ExpectedQ, hMode0Part0Outer7Block0ExpectedQ,
    hMode0Part0Outer7Block1ExpectedQ, hMode0Part0Outer7Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer8ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer8ExpectedQ = sumQ [hMode0Part0Outer8Block0ExpectedQ,
      hMode0Part0Outer8Block1ExpectedQ, hMode0Part0Outer8Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer8ExpectedQ, hMode0Part0Outer8Block0ExpectedQ,
    hMode0Part0Outer8Block1ExpectedQ, hMode0Part0Outer8Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer9ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer9ExpectedQ = sumQ [hMode0Part0Outer9Block0ExpectedQ,
      hMode0Part0Outer9Block1ExpectedQ, hMode0Part0Outer9Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer9ExpectedQ, hMode0Part0Outer9Block0ExpectedQ,
    hMode0Part0Outer9Block1ExpectedQ, hMode0Part0Outer9Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem eval_hMode0Part0Outer4_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 4) =
      evalZhuSparseQ hMode0Part0Outer4ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 4 (by omega),
    hMode0Part0Outer4Block0_eq, hMode0Part0Outer4Block1_eq,
    hMode0Part0Outer4Block2_eq, ← hMode0Part0Outer4ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer5_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 5) =
      evalZhuSparseQ hMode0Part0Outer5ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 5 (by omega),
    hMode0Part0Outer5Block0_eq, hMode0Part0Outer5Block1_eq,
    hMode0Part0Outer5Block2_eq, ← hMode0Part0Outer5ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer6_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 6) =
      evalZhuSparseQ hMode0Part0Outer6ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 6 (by omega),
    hMode0Part0Outer6Block0_eq, hMode0Part0Outer6Block1_eq,
    hMode0Part0Outer6Block2_eq, ← hMode0Part0Outer6ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer7_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 7) =
      evalZhuSparseQ hMode0Part0Outer7ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 7 (by omega),
    hMode0Part0Outer7Block0_eq, hMode0Part0Outer7Block1_eq,
    hMode0Part0Outer7Block2_eq, ← hMode0Part0Outer7ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer8_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 8) =
      evalZhuSparseQ hMode0Part0Outer8ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 8 (by omega),
    hMode0Part0Outer8Block0_eq, hMode0Part0Outer8Block1_eq,
    hMode0Part0Outer8Block2_eq, ← hMode0Part0Outer8ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer9_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 9) =
      evalZhuSparseQ hMode0Part0Outer9ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 9 (by omega),
    hMode0Part0Outer9Block0_eq, hMode0Part0Outer9Block1_eq,
    hMode0Part0Outer9Block2_eq, ← hMode0Part0Outer9ExpectedQ_eq_sum_blocks]

#print axioms eval_hMode0Part0Outer4_eq_expected
#print axioms eval_hMode0Part0Outer5_eq_expected
#print axioms eval_hMode0Part0Outer6_eq_expected
#print axioms eval_hMode0Part0Outer7_eq_expected
#print axioms eval_hMode0Part0Outer8_eq_expected
#print axioms eval_hMode0Part0Outer9_eq_expected

end VOA.LatGen.WpTwoZhuSparseSemantics
