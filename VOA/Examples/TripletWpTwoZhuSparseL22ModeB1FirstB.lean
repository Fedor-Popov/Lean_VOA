/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB1FirstA

/-! # Staged mode-one normal-order certificate: FirstB -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg5_eq :
    l22BMode1FirstSparseQ (-5) =
      l22BMode1FirstNeg5ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg4_eq :
    l22BMode1FirstSparseQ (-4) =
      l22BMode1FirstNeg4ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg3_eq :
    l22BMode1FirstSparseQ (-3) =
      l22BMode1FirstNeg3ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 2000000 in
-- The isolated double-creation summand is the unique larger reduction.
theorem l22BMode1FirstNeg2_eq :
    l22BMode1FirstSparseQ (-2) =
      l22BMode1FirstNeg2ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode1FirstNeg2_eq
end AxiomAudit
