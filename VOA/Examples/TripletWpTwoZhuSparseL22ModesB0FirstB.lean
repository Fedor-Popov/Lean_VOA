/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0FirstA

/-! # Staged lowest-mode normal-order certificate: first half B -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg7_eq :
    l22BMode0FirstSparseQ (-7) = l22BMode0FirstNeg7ExpectedQ := by
  close_l22_b0_first

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg6_eq :
    l22BMode0FirstSparseQ (-6) = l22BMode0FirstNeg6ExpectedQ := by
  close_l22_b0_first

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg5_eq :
    l22BMode0FirstSparseQ (-5) = l22BMode0FirstNeg5ExpectedQ := by
  close_l22_b0_first

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0FirstNeg5_eq
end AxiomAudit
