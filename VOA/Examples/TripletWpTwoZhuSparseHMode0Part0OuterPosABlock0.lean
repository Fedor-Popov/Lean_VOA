/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosABlocks

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer0Block0_eq :
    hMode0Part0OuterBlockSparseQ 0 0 = hMode0Part0Outer0Block0ExpectedQ := by
  unfold hMode0Part0Outer0Block0ExpectedQ
  close_h_mode0_part0_outer_block

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer0Block1_eq :
    hMode0Part0OuterBlockSparseQ 0 1 = hMode0Part0Outer0Block1ExpectedQ := by
  unfold hMode0Part0Outer0Block1ExpectedQ
  close_h_mode0_part0_outer_block

set_option maxHeartbeats 1000000 in
-- Exact normalization of one three-monomial right-state block.
theorem hMode0Part0Outer0Block2_eq :
    hMode0Part0OuterBlockSparseQ 0 2 = hMode0Part0Outer0Block2ExpectedQ := by
  unfold hMode0Part0Outer0Block2ExpectedQ
  close_h_mode0_part0_outer_block

#print axioms hMode0Part0Outer0Block0_eq
#print axioms hMode0Part0Outer0Block1_eq
#print axioms hMode0Part0Outer0Block2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
