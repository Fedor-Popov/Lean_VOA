/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part0OuterNonnegA

/-! # Final nonnegative outer modes for the cubic H branch at Zhu mode three -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer3_eq :
    hMode3Part0OuterSparseQ 3 = hMode3Part0Outer3ExpectedQ := by
  close_h_mode3_part0_outer_nonneg
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer4_eq :
    hMode3Part0OuterSparseQ 4 = hMode3Part0Outer4ExpectedQ := by
  close_h_mode3_part0_outer_nonneg
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer5_eq :
    hMode3Part0OuterSparseQ 5 = hMode3Part0Outer5ExpectedQ := by
  close_h_mode3_part0_outer_nonneg
set_option maxHeartbeats 1000000 in
-- One summand of the finite outer-mode expansion.
theorem hMode3Part0Outer6_eq :
    hMode3Part0OuterSparseQ 6 = hMode3Part0Outer6ExpectedQ := by
  close_h_mode3_part0_outer_nonneg

#print axioms hMode3Part0Outer6_eq

end VOA.LatGen.WpTwoZhuSparseCompute
