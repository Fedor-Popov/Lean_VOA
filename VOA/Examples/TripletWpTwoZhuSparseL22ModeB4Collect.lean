/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB4SecondA

/-! # Staged mode-4 normal-order certificate: Collect -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second3_eq :
    l22BMode4SecondSparseQ (3) =
      l22BMode4Second3ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second4_eq :
    l22BMode4SecondSparseQ (4) =
      l22BMode4Second4ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second5_eq :
    l22BMode4SecondSparseQ (5) =
      l22BMode4Second5ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand

theorem l22CircleBMode4_eq :
    l22CircleBModeSparseQ 4 = l22Entry1Mode4ExpectedQ := by
  unfold l22CircleBModeSparseQ
  rw [vir22ModeSparseQ]
  norm_num only [Nat.choose]
  rw [scaleQ_addQ 1 (by norm_num),
    scaleQ_sumQ 1 (by norm_num),
    scaleQ_sumQ 1 (by norm_num),
    scaleQ_addQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ (sumQ [l22BMode4FirstSparseQ (-6), l22BMode4FirstSparseQ (-5), l22BMode4FirstSparseQ (-4), l22BMode4FirstSparseQ (-3), l22BMode4FirstSparseQ (-2)])
    (sumQ [l22BMode4SecondSparseQ (-1), l22BMode4SecondSparseQ (0), l22BMode4SecondSparseQ (1), l22BMode4SecondSparseQ (2), l22BMode4SecondSparseQ (3), l22BMode4SecondSparseQ (4), l22BMode4SecondSparseQ (5)]) = l22Entry1Mode4ExpectedQ
  rw [l22BMode4FirstNeg6_eq,
    l22BMode4FirstNeg5_eq,
    l22BMode4FirstNeg4_eq,
    l22BMode4FirstNeg3_eq,
    l22BMode4FirstNeg2_eq,
    l22BMode4SecondNeg1_eq,
    l22BMode4Second0_eq,
    l22BMode4Second1_eq,
    l22BMode4Second2_eq,
    l22BMode4Second3_eq,
    l22BMode4Second4_eq,
    l22BMode4Second5_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l22BMode4FirstNeg6ExpectedQ,
    l22BMode4FirstNeg5ExpectedQ,
    l22BMode4FirstNeg4ExpectedQ,
    l22BMode4FirstNeg3ExpectedQ,
    l22BMode4FirstNeg2ExpectedQ,
    l22BMode4SecondNeg1ExpectedQ,
    l22BMode4Second0ExpectedQ,
    l22BMode4Second1ExpectedQ,
    l22BMode4Second2ExpectedQ,
    l22BMode4Second3ExpectedQ,
    l22BMode4Second4ExpectedQ,
    l22BMode4Second5ExpectedQ, l22Entry1Mode4ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleBMode4_eq
end AxiomAudit
