/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0OuterNegA

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0OuterNeg4_eq :
    hMode2Part0OuterSparseQ (-4) = hMode2Part0OuterNeg4ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0OuterNeg3_eq :
    hMode2Part0OuterSparseQ (-3) = hMode2Part0OuterNeg3ExpectedQ := by
  close_h_mode2_part0_outer

#print axioms hMode2Part0OuterNeg3_eq

end VOA.LatGen.WpTwoZhuSparseCompute
