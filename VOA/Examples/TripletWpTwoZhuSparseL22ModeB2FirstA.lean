/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB2

/-! # Staged mode-2 normal-order certificate: FirstA -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2FirstNeg8_eq :
    l22BMode2FirstSparseQ (-8) =
      l22BMode2FirstNeg8ExpectedQ := by
  unfold l22BMode2FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2FirstNeg7_eq :
    l22BMode2FirstSparseQ (-7) =
      l22BMode2FirstNeg7ExpectedQ := by
  unfold l22BMode2FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2FirstNeg6_eq :
    l22BMode2FirstSparseQ (-6) =
      l22BMode2FirstNeg6ExpectedQ := by
  unfold l22BMode2FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand
set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode2FirstNeg5_eq :
    l22BMode2FirstSparseQ (-5) =
      l22BMode2FirstNeg5ExpectedQ := by
  unfold l22BMode2FirstSparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l22_b2_summand

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode2FirstNeg5_eq
end AxiomAudit
