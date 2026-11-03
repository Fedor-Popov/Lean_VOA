/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0FirstC

/-! # Staged lowest-mode normal-order certificate: first half D -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 2000000 in
-- This minimal normal-order summand needs a larger exact-reduction budget.
theorem l22BMode0FirstNeg3_eq :
    l22BMode0FirstSparseQ (-3) = l22BMode0FirstNeg3ExpectedQ := by
  close_l22_b0_first

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22BMode0FirstNeg3_eq
end AxiomAudit
