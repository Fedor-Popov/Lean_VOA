/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB3FirstB

/-! # Staged mode-3 normal-order certificate: SecondA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3SecondNeg1_eq :
    l22BMode3SecondSparseQ (-1) =
      l22BMode3SecondNeg1ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second0_eq :
    l22BMode3SecondSparseQ (0) =
      l22BMode3Second0ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second1_eq :
    l22BMode3SecondSparseQ (1) =
      l22BMode3Second1ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3Second2_eq :
    l22BMode3SecondSparseQ (2) =
      l22BMode3Second2ExpectedQ := by
  unfold l22BMode3SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode3Second2_eq
end AxiomAudit
