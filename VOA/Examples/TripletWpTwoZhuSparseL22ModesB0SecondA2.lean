/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0SecondA

/-! # Staged lowest-mode normal-order certificate: second half A2 -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second1_eq :
    l22BMode0SecondSparseQ (1) = l22BMode0Second1ExpectedQ := by
  close_l22_b0_second

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second2_eq :
    l22BMode0SecondSparseQ (2) = l22BMode0Second2ExpectedQ := by
  close_l22_b0_second

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0Second2_eq
end AxiomAudit
