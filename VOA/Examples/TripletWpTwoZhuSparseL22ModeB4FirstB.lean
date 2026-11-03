/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB4FirstA

/-! # Staged mode-4 normal-order certificate: FirstB -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4FirstNeg3_eq :
    l22BMode4FirstSparseQ (-3) =
      l22BMode4FirstNeg3ExpectedQ := by
  unfold l22BMode4FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4FirstNeg2_eq :
    l22BMode4FirstSparseQ (-2) =
      l22BMode4FirstNeg2ExpectedQ := by
  unfold l22BMode4FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode4FirstNeg2_eq
end AxiomAudit
