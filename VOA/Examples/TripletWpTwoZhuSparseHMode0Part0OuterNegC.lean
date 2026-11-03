/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNegB

/-! # Final negative outer modes of the lowest cubic H branch -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One independently normalized summand of the finite outer-mode expansion.
theorem hMode0Part0OuterNeg2_eq :
    hMode0Part0OuterSparseQ (-2) = hMode0Part0OuterN2ExpectedQ := by
  close_h_mode0_part0_outer

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0OuterNeg2_eq
end AxiomAudit
