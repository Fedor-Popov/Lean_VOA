/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesA

/-! # The middle normal-product mode for the first `L(-2)^2 1` Zhu circle -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
-- The nested omega-mode calculation is exact but needs a larger local reduction budget.
theorem l22CircleAMode2_eq :
    l22CircleAModeSparseQ 2 = l22CircleAMode2ExpectedQ := by
  close_l22_a_mode
  norm_num [Nat.choose, l22CircleAMode2ExpectedQ, scaleQ]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleAMode2_eq
end AxiomAudit
