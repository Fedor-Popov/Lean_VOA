/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0First

/-! # Second normal-order half of the second L22 circle's lowest mode -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l22BMode0SecondSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (1669 / 128)
    (virModeSparseQ (-5 - m) (5 - m).toNat
      (virModeSparseQ m 5 (reifyVirWordSparseQ [3, 2])))

macro "close_l22_b0_second" : tactic => `(tactic|
  (unfold l22BMode0SecondSparseQ
   rw [reifyVir32SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l22BMode0SecondNeg1ExpectedQ,
    l22BMode0Second0ExpectedQ,
    l22BMode0Second1ExpectedQ,
    l22BMode0Second2ExpectedQ,
    l22BMode0Second3ExpectedQ,
    l22BMode0Second4ExpectedQ,
    l22BMode0Second5ExpectedQ, vir32ExpectedQ,
    virModeSparseQ, omegaSparseQ, voaModeActSparseQ, zhuStateActSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
