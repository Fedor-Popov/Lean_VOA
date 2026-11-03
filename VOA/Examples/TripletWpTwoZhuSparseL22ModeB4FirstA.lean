/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB4

/-! # Staged mode-4 normal-order certificate: FirstA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4FirstNeg6_eq :
    l22BMode4FirstSparseQ (-6) =
      l22BMode4FirstNeg6ExpectedQ := by
  unfold l22BMode4FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4FirstNeg5_eq :
    l22BMode4FirstSparseQ (-5) =
      l22BMode4FirstNeg5ExpectedQ := by
  unfold l22BMode4FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode4FirstNeg4_eq :
    l22BMode4FirstSparseQ (-4) =
      l22BMode4FirstNeg4ExpectedQ := by
  unfold l22BMode4FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b4_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode4FirstNeg4_eq
end AxiomAudit
