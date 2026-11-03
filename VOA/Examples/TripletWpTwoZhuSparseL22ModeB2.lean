/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB1Collect

/-! # Sparse normal-order data for mode 2 of the second L22 circle -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l22BMode2FirstSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128) (scaleQ 6
    (virModeSparseQ m (8 + m).toNat
      (virModeSparseQ (-3 - m) 5 (reifyVirWordSparseQ [3, 2]))))

def l22BMode2SecondSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128) (scaleQ 6
    (virModeSparseQ (-3 - m) (5 - m).toNat
      (virModeSparseQ m 5 (reifyVirWordSparseQ [3, 2]))))

macro "close_l22_b2_summand" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
      [l22BMode2FirstNeg8ExpectedQ,
      l22BMode2FirstNeg7ExpectedQ,
      l22BMode2FirstNeg6ExpectedQ,
      l22BMode2FirstNeg5ExpectedQ,
      l22BMode2FirstNeg4ExpectedQ,
      l22BMode2FirstNeg3ExpectedQ,
      l22BMode2FirstNeg2ExpectedQ,
      l22BMode2SecondNeg1ExpectedQ,
      l22BMode2Second0ExpectedQ,
      l22BMode2Second1ExpectedQ,
      l22BMode2Second2ExpectedQ,
      l22BMode2Second3ExpectedQ,
      l22BMode2Second4ExpectedQ,
      l22BMode2Second5ExpectedQ, vir32ExpectedQ,
      virModeSparseQ, omegaSparseQ, voaModeActSparseQ, zhuStateActSparseQ,
      aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
      aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
      annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
      normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
      List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
