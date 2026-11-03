/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBCBlocks

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer7Block0_eq :
    hMode0Part0OuterBlockSparseQ 7 0 = hMode0Part0Outer7Block0ExpectedQ := by
  unfold hMode0Part0Outer7Block0ExpectedQ
  close_h_mode0_part0_outer_block
set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer7Block1_eq :
    hMode0Part0OuterBlockSparseQ 7 1 = hMode0Part0Outer7Block1ExpectedQ := by
  unfold hMode0Part0Outer7Block1ExpectedQ
  close_h_mode0_part0_outer_block
set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer7Block2_eq :
    hMode0Part0OuterBlockSparseQ 7 2 = hMode0Part0Outer7Block2ExpectedQ := by
  unfold hMode0Part0Outer7Block2ExpectedQ
  close_h_mode0_part0_outer_block

#print axioms hMode0Part0Outer7Block0_eq
#print axioms hMode0Part0Outer7Block1_eq
#print axioms hMode0Part0Outer7Block2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
