/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB2FirstB

/-! # Staged mode-2 normal-order certificate: SecondA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2SecondNeg1_eq :
    l22BMode2SecondSparseQ (-1) =
      l22BMode2SecondNeg1ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second0_eq :
    l22BMode2SecondSparseQ (0) =
      l22BMode2Second0ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second1_eq :
    l22BMode2SecondSparseQ (1) =
      l22BMode2Second1ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2Second2_eq :
    l22BMode2SecondSparseQ (2) =
      l22BMode2Second2ExpectedQ := by
  unfold l22BMode2SecondSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode2Second2_eq
end AxiomAudit
