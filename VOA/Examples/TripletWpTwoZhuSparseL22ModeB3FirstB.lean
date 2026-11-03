/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB3FirstA

/-! # Staged mode-3 normal-order certificate: FirstB -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg4_eq :
    l22BMode3FirstSparseQ (-4) =
      l22BMode3FirstNeg4ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg3_eq :
    l22BMode3FirstSparseQ (-3) =
      l22BMode3FirstNeg3ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg2_eq :
    l22BMode3FirstSparseQ (-2) =
      l22BMode3FirstNeg2ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode3FirstNeg2_eq
end AxiomAudit
