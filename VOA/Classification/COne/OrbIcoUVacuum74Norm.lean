import VOA.Classification.COne.OrbIcoUPair

/-! The pure c = 1 norm of the L(-2) tower at level 74 and seed weight 0.
This is a tower normalization, not a dual-state or mode-product measurement. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC OrbSpan

def vacuum74Norm : ℚ :=
  (161042531908166298370255444236912464513742818465 * 10 ^ 60 +
    419415794306050220515787030266646148122089910334014892578125) / 8

set_option maxHeartbeats 5000000 in
-- Evaluate the ordered Virasoro word pairing, collecting identical words at each step.
set_option maxRecDepth 8192 in
theorem vacuum74_pairing :
    pairWords 1 0 (List.replicate 37 2) (List.replicate 37 2) = vacuum74Norm := by
  decide +kernel

theorem vacuum74Norm_pos : 0 < vacuum74Norm := by
  norm_num [vacuum74Norm]

end VOA.Classification.COne.OrbIcoU
