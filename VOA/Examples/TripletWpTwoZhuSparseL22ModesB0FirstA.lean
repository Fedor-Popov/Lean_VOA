/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0First

/-! # Staged lowest-mode normal-order certificate: first half A -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg10_eq :
    l22BMode0FirstSparseQ (-10) = l22BMode0FirstNeg10ExpectedQ := by
  close_l22_b0_first

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg9_eq :
    l22BMode0FirstSparseQ (-9) = l22BMode0FirstNeg9ExpectedQ := by
  close_l22_b0_first

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg8_eq :
    l22BMode0FirstSparseQ (-8) = l22BMode0FirstNeg8ExpectedQ := by
  close_l22_b0_first

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0FirstNeg8_eq
end AxiomAudit
