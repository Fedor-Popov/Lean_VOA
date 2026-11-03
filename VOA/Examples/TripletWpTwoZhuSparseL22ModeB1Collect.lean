/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB1SecondA

/-! # Staged mode-one normal-order certificate: Collect -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second3_eq :
    l22BMode1SecondSparseQ (3) =
      l22BMode1Second3ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second4_eq :
    l22BMode1SecondSparseQ (4) =
      l22BMode1Second4ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second5_eq :
    l22BMode1SecondSparseQ (5) =
      l22BMode1Second5ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand

theorem l22CircleBMode1_eq :
    l22CircleBModeSparseQ 1 = l22Entry1Mode1ExpectedQ := by
  unfold l22CircleBModeSparseQ
  rw [vir22ModeSparseQ]
  norm_num only [Nat.choose]
  rw [scaleQ_addQ 4 (by norm_num), scaleQ_sumQ 4 (by norm_num),
    scaleQ_sumQ 4 (by norm_num),
    scaleQ_addQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ
      (sumQ [l22BMode1FirstSparseQ (-9), l22BMode1FirstSparseQ (-8),
        l22BMode1FirstSparseQ (-7), l22BMode1FirstSparseQ (-6),
        l22BMode1FirstSparseQ (-5), l22BMode1FirstSparseQ (-4),
        l22BMode1FirstSparseQ (-3), l22BMode1FirstSparseQ (-2)])
      (sumQ [l22BMode1SecondSparseQ (-1), l22BMode1SecondSparseQ 0,
        l22BMode1SecondSparseQ 1, l22BMode1SecondSparseQ 2,
        l22BMode1SecondSparseQ 3, l22BMode1SecondSparseQ 4,
        l22BMode1SecondSparseQ 5]) = l22Entry1Mode1ExpectedQ
  rw [l22BMode1FirstNeg9_eq, l22BMode1FirstNeg8_eq,
    l22BMode1FirstNeg7_eq, l22BMode1FirstNeg6_eq,
    l22BMode1FirstNeg5_eq, l22BMode1FirstNeg4_eq,
    l22BMode1FirstNeg3_eq, l22BMode1FirstNeg2_eq,
    l22BMode1SecondNeg1_eq, l22BMode1Second0_eq,
    l22BMode1Second1_eq, l22BMode1Second2_eq,
    l22BMode1Second3_eq, l22BMode1Second4_eq,
    l22BMode1Second5_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l22BMode1FirstNeg9ExpectedQ, l22BMode1FirstNeg8ExpectedQ,
    l22BMode1FirstNeg7ExpectedQ, l22BMode1FirstNeg6ExpectedQ,
    l22BMode1FirstNeg5ExpectedQ, l22BMode1FirstNeg4ExpectedQ,
    l22BMode1FirstNeg3ExpectedQ, l22BMode1FirstNeg2ExpectedQ,
    l22BMode1SecondNeg1ExpectedQ, l22BMode1Second0ExpectedQ,
    l22BMode1Second1ExpectedQ, l22BMode1Second2ExpectedQ,
    l22BMode1Second3ExpectedQ, l22BMode1Second4ExpectedQ,
    l22BMode1Second5ExpectedQ, l22Entry1Mode1ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleBMode1_eq
end AxiomAudit
