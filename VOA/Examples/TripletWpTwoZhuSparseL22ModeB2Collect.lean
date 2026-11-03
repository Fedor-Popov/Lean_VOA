/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB2SecondA

/-! # Staged mode-2 normal-order certificate: Collect -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second3_eq :
    l22BMode2SecondSparseQ (3) =
      l22BMode2Second3ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second4_eq :
    l22BMode2SecondSparseQ (4) =
      l22BMode2Second4ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second5_eq :
    l22BMode2SecondSparseQ (5) =
      l22BMode2Second5ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand

theorem l22CircleBMode2_eq :
    l22CircleBModeSparseQ 2 = l22Entry1Mode2ExpectedQ := by
  unfold l22CircleBModeSparseQ
  rw [vir22ModeSparseQ]
  norm_num only [Nat.choose]
  rw [scaleQ_addQ 6 (by norm_num),
    scaleQ_sumQ 6 (by norm_num),
    scaleQ_sumQ 6 (by norm_num),
    scaleQ_addQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ (sumQ [l22BMode2FirstSparseQ (-8), l22BMode2FirstSparseQ (-7), l22BMode2FirstSparseQ (-6), l22BMode2FirstSparseQ (-5), l22BMode2FirstSparseQ (-4), l22BMode2FirstSparseQ (-3), l22BMode2FirstSparseQ (-2)])
    (sumQ [l22BMode2SecondSparseQ (-1), l22BMode2SecondSparseQ (0), l22BMode2SecondSparseQ (1), l22BMode2SecondSparseQ (2), l22BMode2SecondSparseQ (3), l22BMode2SecondSparseQ (4), l22BMode2SecondSparseQ (5)]) = l22Entry1Mode2ExpectedQ
  rw [l22BMode2FirstNeg8_eq,
    l22BMode2FirstNeg7_eq,
    l22BMode2FirstNeg6_eq,
    l22BMode2FirstNeg5_eq,
    l22BMode2FirstNeg4_eq,
    l22BMode2FirstNeg3_eq,
    l22BMode2FirstNeg2_eq,
    l22BMode2SecondNeg1_eq,
    l22BMode2Second0_eq,
    l22BMode2Second1_eq,
    l22BMode2Second2_eq,
    l22BMode2Second3_eq,
    l22BMode2Second4_eq,
    l22BMode2Second5_eq]
  norm_num (config := { maxSteps := 1000000 })
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
    l22BMode2Second5ExpectedQ, l22Entry1Mode2ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleBMode2_eq
end AxiomAudit
