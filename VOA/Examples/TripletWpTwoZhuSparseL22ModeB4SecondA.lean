/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB4FirstB

/-! # Staged mode-4 normal-order certificate: SecondA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4SecondNeg1_eq :
    l22BMode4SecondSparseQ (-1) =
      l22BMode4SecondNeg1ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second0_eq :
    l22BMode4SecondSparseQ (0) =
      l22BMode4Second0ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second1_eq :
    l22BMode4SecondSparseQ (1) =
      l22BMode4Second1ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4Second2_eq :
    l22BMode4SecondSparseQ (2) =
      l22BMode4Second2ExpectedQ := by
  unfold l22BMode4SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode4Second2_eq
end AxiomAudit
