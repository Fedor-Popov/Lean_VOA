/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBCBlocks

namespace VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer4Block0_eq :
    hMode0Part0OuterBlockSparseQ 4 0 = hMode0Part0Outer4Block0ExpectedQ := by
  unfold hMode0Part0Outer4Block0ExpectedQ
  close_h_mode0_part0_outer_block
set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer4Block1_eq :
    hMode0Part0OuterBlockSparseQ 4 1 = hMode0Part0Outer4Block1ExpectedQ := by
  unfold hMode0Part0Outer4Block1ExpectedQ
  close_h_mode0_part0_outer_block
set_option maxHeartbeats 1000000 in
-- A single right-state block keeps this exact sparse replay below the deterministic cap.
theorem hMode0Part0Outer4Block2_eq :
    hMode0Part0OuterBlockSparseQ 4 2 = hMode0Part0Outer4Block2ExpectedQ := by
  unfold hMode0Part0Outer4Block2ExpectedQ
  close_h_mode0_part0_outer_block

#print axioms hMode0Part0Outer4Block0_eq
#print axioms hMode0Part0Outer4Block1_eq
#print axioms hMode0Part0Outer4Block2_eq

end VOA.LatGen.WpTwoZhuSparseCompute
