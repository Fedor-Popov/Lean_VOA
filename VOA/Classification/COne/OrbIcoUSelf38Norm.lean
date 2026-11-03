import VOA.Classification.COne.OrbIcoUPair

/-! The pure c = 1 norm of the L(-2) tower at level 38 and seed weight 36.
This is a tower normalization, not a dual-state or mode-product measurement. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC OrbSpan

def self38Norm : ℚ :=
  6304440516031519429191441887890499609651486365273471062890625 / 8

set_option maxHeartbeats 5000000 in
-- Evaluate the ordered Virasoro word pairing, collecting identical words at each step.
set_option maxRecDepth 8192 in
theorem self38_pairing :
    pairWords 1 36 (List.replicate 19 2) (List.replicate 19 2) = self38Norm := by
  decide +kernel

theorem self38Norm_pos : 0 < self38Norm := by
  norm_num [self38Norm]

end VOA.Classification.COne.OrbIcoU
