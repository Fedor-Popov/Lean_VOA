/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0OuterNegC

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer0_eq :
    hMode2Part0OuterSparseQ 0 = hMode2Part0Outer0ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer1_eq :
    hMode2Part0OuterSparseQ 1 = hMode2Part0Outer1ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer2_eq :
    hMode2Part0OuterSparseQ 2 = hMode2Part0Outer2ExpectedQ := by
  close_h_mode2_part0_outer

#print axioms hMode2Part0Outer2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
