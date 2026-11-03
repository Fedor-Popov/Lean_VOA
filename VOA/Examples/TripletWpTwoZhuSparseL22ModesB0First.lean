/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0Expected

/-! # First normal-order half of the second L22 circle's lowest mode -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l22BMode0FirstSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128)
    (virModeSparseQ m (10 + m).toNat
      (virModeSparseQ (-5 - m) 5 (reifyVirWordSparseQ [3, 2])))

macro "close_l22_b0_first" : tactic => `(tactic|
  (unfold l22BMode0FirstSparseQ
   rw [reifyVir32SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l22BMode0FirstNeg10ExpectedQ,
    l22BMode0FirstNeg9ExpectedQ,
    l22BMode0FirstNeg8ExpectedQ,
    l22BMode0FirstNeg7ExpectedQ,
    l22BMode0FirstNeg6ExpectedQ,
    l22BMode0FirstNeg5ExpectedQ,
    l22BMode0FirstNeg4ExpectedQ,
    l22BMode0FirstNeg3ExpectedQ,
    l22BMode0FirstNeg2ExpectedQ, vir32ExpectedQ,
    virModeSparseQ, omegaSparseQ, voaModeActSparseQ, zhuStateActSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
