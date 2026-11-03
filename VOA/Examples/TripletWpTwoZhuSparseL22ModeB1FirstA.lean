/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB1

/-! # Staged mode-one normal-order certificate: FirstA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg9_eq :
    l22BMode1FirstSparseQ (-9) =
      l22BMode1FirstNeg9ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg8_eq :
    l22BMode1FirstSparseQ (-8) =
      l22BMode1FirstNeg8ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg7_eq :
    l22BMode1FirstSparseQ (-7) =
      l22BMode1FirstNeg7ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode1FirstNeg6_eq :
    l22BMode1FirstSparseQ (-6) =
      l22BMode1FirstNeg6ExpectedQ := by
  unfold l22BMode1FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b1_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode1FirstNeg6_eq
end AxiomAudit
