/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB1FirstB

/-! # Staged mode-one normal-order certificate: SecondA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1SecondNeg1_eq :
    l22BMode1SecondSparseQ (-1) =
      l22BMode1SecondNeg1ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second0_eq :
    l22BMode1SecondSparseQ (0) =
      l22BMode1Second0ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second1_eq :
    l22BMode1SecondSparseQ (1) =
      l22BMode1Second1ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1Second2_eq :
    l22BMode1SecondSparseQ (2) =
      l22BMode1Second2ExpectedQ := by
  unfold l22BMode1SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode1Second2_eq
end AxiomAudit
