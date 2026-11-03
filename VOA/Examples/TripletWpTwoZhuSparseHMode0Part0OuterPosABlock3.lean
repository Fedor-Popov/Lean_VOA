/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosABlock2

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer3Block0_eq :
    hMode0Part0OuterBlockSparseQ 3 0 = hMode0Part0Outer3Block0ExpectedQ := by
  unfold hMode0Part0Outer3Block0ExpectedQ
  close_h_mode0_part0_outer_block

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer3Block1_eq :
    hMode0Part0OuterBlockSparseQ 3 1 = hMode0Part0Outer3Block1ExpectedQ := by
  unfold hMode0Part0Outer3Block1ExpectedQ
  close_h_mode0_part0_outer_block

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer3Block2_eq :
    hMode0Part0OuterBlockSparseQ 3 2 = hMode0Part0Outer3Block2ExpectedQ := by
  unfold hMode0Part0Outer3Block2ExpectedQ
  close_h_mode0_part0_outer_block

#print axioms hMode0Part0Outer3Block0_eq
#print axioms hMode0Part0Outer3Block1_eq
#print axioms hMode0Part0Outer3Block2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
