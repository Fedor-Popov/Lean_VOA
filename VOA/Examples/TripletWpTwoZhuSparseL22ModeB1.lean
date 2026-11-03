/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesBRestExpected

/-! # Summand certificate for mode 1 of the second L22 circle -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l22BMode1FirstSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128) (scaleQ 4
    (virModeSparseQ m (9 + m).toNat
      (virModeSparseQ (-4 - m) 5 (reifyVirWordSparseQ [3, 2]))))

def l22BMode1SecondSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128) (scaleQ 4
    (virModeSparseQ (-4 - m) (5 - m).toNat
      (virModeSparseQ m 5 (reifyVirWordSparseQ [3, 2]))))

macro "close_l22_b1_summand" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
      [l22BMode1FirstNeg9ExpectedQ,
      l22BMode1FirstNeg8ExpectedQ,
      l22BMode1FirstNeg7ExpectedQ,
      l22BMode1FirstNeg6ExpectedQ,
      l22BMode1FirstNeg5ExpectedQ,
      l22BMode1FirstNeg4ExpectedQ,
      l22BMode1FirstNeg3ExpectedQ,
      l22BMode1FirstNeg2ExpectedQ,
      l22BMode1SecondNeg1ExpectedQ,
      l22BMode1Second0ExpectedQ,
      l22BMode1Second1ExpectedQ,
      l22BMode1Second2ExpectedQ,
      l22BMode1Second3ExpectedQ,
      l22BMode1Second4ExpectedQ,
      l22BMode1Second5ExpectedQ, vir32ExpectedQ,
      virModeSparseQ, omegaSparseQ, voaModeActSparseQ, zhuStateActSparseQ,
      aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
      aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
      annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
      normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
      List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
