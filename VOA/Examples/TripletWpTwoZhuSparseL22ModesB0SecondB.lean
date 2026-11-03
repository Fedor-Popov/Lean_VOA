/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0SecondA2

/-! # Staged lowest-mode normal-order certificate: second half B -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second3_eq :
    l22BMode0SecondSparseQ (3) = l22BMode0Second3ExpectedQ := by
  close_l22_b0_second

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second4_eq :
    l22BMode0SecondSparseQ (4) = l22BMode0Second4ExpectedQ := by
  close_l22_b0_second

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0Second5_eq :
    l22BMode0SecondSparseQ (5) = l22BMode0Second5ExpectedQ := by
  close_l22_b0_second

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0Second5_eq
end AxiomAudit
