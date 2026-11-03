import VOA.Classification.COne.OrbIcoUPair

/-! The pure c = 1 norm of the L(-2) tower at level 76 and seed weight 0.
This is a tower normalization, not a dual-state or mode-product measurement. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC OrbSpan

def vacuum76Norm : ℚ :=
  (908763007557782421703351471828897037251050724600361 * 10 ^ 60 +
    763327269041394370586211794684213852953364014846038818359375) / 8

set_option maxHeartbeats 5000000 in
-- Evaluate the ordered Virasoro word pairing, collecting identical words at each step.
set_option maxRecDepth 8192 in
theorem vacuum76_pairing :
    pairWords 1 0 (List.replicate 38 2) (List.replicate 38 2) = vacuum76Norm := by
  decide +kernel

theorem vacuum76Norm_pos : 0 < vacuum76Norm := by
  norm_num [vacuum76Norm]

end VOA.Classification.COne.OrbIcoU
