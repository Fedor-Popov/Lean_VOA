/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0FirstB

/-! # Staged lowest-mode normal-order certificate: first half C -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One exact normal-order summand.
theorem l22BMode0FirstNeg4_eq :
    l22BMode0FirstSparseQ (-4) = l22BMode0FirstNeg4ExpectedQ := by
  close_l22_b0_first

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0FirstNeg4_eq
end AxiomAudit
