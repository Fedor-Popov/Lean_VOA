/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0FirstE
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0Second

/-! # Staged lowest-mode normal-order certificate: second half A -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0SecondNeg1_eq :
    l22BMode0SecondSparseQ (-1) = l22BMode0SecondNeg1ExpectedQ := by
  close_l22_b0_second

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second0_eq :
    l22BMode0SecondSparseQ (0) = l22BMode0Second0ExpectedQ := by
  close_l22_b0_second

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0Second0_eq
end AxiomAudit
