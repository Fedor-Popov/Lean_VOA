/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0OuterNegB

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0OuterNeg2_eq :
    hMode2Part0OuterSparseQ (-2) = hMode2Part0OuterNeg2ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0OuterNeg1_eq :
    hMode2Part0OuterSparseQ (-1) = hMode2Part0OuterNeg1ExpectedQ := by
  close_h_mode2_part0_outer

#print axioms hMode2Part0OuterNeg1_eq

end VOA.LatGen.WpTwoZhuSparseCompute
