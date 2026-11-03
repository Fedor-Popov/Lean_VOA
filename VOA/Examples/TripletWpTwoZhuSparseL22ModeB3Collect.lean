/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB3SecondA

/-! # Staged mode-3 normal-order certificate: Collect -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second3_eq :
    l22BMode3SecondSparseQ (3) =
      l22BMode3Second3ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second4_eq :
    l22BMode3SecondSparseQ (4) =
      l22BMode3Second4ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second5_eq :
    l22BMode3SecondSparseQ (5) =
      l22BMode3Second5ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand

theorem l22CircleBMode3_eq :
    l22CircleBModeSparseQ 3 = l22Entry1Mode3ExpectedQ := by
  unfold l22CircleBModeSparseQ
  rw [vir22ModeSparseQ]
  norm_num only [Nat.choose]
  rw [scaleQ_addQ 4 (by norm_num),
    scaleQ_sumQ 4 (by norm_num),
    scaleQ_sumQ 4 (by norm_num),
    scaleQ_addQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ (sumQ [l22BMode3FirstSparseQ (-7), l22BMode3FirstSparseQ (-6), l22BMode3FirstSparseQ (-5), l22BMode3FirstSparseQ (-4), l22BMode3FirstSparseQ (-3), l22BMode3FirstSparseQ (-2)])
    (sumQ [l22BMode3SecondSparseQ (-1), l22BMode3SecondSparseQ (0), l22BMode3SecondSparseQ (1), l22BMode3SecondSparseQ (2), l22BMode3SecondSparseQ (3), l22BMode3SecondSparseQ (4), l22BMode3SecondSparseQ (5)]) = l22Entry1Mode3ExpectedQ
  rw [l22BMode3FirstNeg7_eq,
    l22BMode3FirstNeg6_eq,
    l22BMode3FirstNeg5_eq,
    l22BMode3FirstNeg4_eq,
    l22BMode3FirstNeg3_eq,
    l22BMode3FirstNeg2_eq,
    l22BMode3SecondNeg1_eq,
    l22BMode3Second0_eq,
    l22BMode3Second1_eq,
    l22BMode3Second2_eq,
    l22BMode3Second3_eq,
    l22BMode3Second4_eq,
    l22BMode3Second5_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l22BMode3FirstNeg7ExpectedQ,
    l22BMode3FirstNeg6ExpectedQ,
    l22BMode3FirstNeg5ExpectedQ,
    l22BMode3FirstNeg4ExpectedQ,
    l22BMode3FirstNeg3ExpectedQ,
    l22BMode3FirstNeg2ExpectedQ,
    l22BMode3SecondNeg1ExpectedQ,
    l22BMode3Second0ExpectedQ,
    l22BMode3Second1ExpectedQ,
    l22BMode3Second2ExpectedQ,
    l22BMode3Second3ExpectedQ,
    l22BMode3Second4ExpectedQ,
    l22BMode3Second5ExpectedQ, l22Entry1Mode3ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleBMode3_eq
end AxiomAudit
