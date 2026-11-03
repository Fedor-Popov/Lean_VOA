/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0OuterNonnegA

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer3_eq :
    hMode2Part0OuterSparseQ 3 = hMode2Part0Outer3ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer4_eq :
    hMode2Part0OuterSparseQ 4 = hMode2Part0Outer4ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer5_eq :
    hMode2Part0OuterSparseQ 5 = hMode2Part0Outer5ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer6_eq :
    hMode2Part0OuterSparseQ 6 = hMode2Part0Outer6ExpectedQ := by
  close_h_mode2_part0_outer
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode2Part0Outer7_eq :
    hMode2Part0OuterSparseQ 7 = hMode2Part0Outer7ExpectedQ := by
  close_h_mode2_part0_outer

#print axioms hMode2Part0Outer7_eq

end VOA.LatGen.WpTwoZhuSparseCompute
