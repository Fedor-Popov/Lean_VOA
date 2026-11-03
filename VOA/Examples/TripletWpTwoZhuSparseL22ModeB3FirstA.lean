/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB3

/-! # Staged mode-3 normal-order certificate: FirstA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg7_eq :
    l22BMode3FirstSparseQ (-7) =
      l22BMode3FirstNeg7ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg6_eq :
    l22BMode3FirstSparseQ (-6) =
      l22BMode3FirstNeg6ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode3FirstNeg5_eq :
    l22BMode3FirstSparseQ (-5) =
      l22BMode3FirstNeg5ExpectedQ := by
  unfold l22BMode3FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b3_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode3FirstNeg5_eq
end AxiomAudit
