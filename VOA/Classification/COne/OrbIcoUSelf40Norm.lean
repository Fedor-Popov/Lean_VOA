import VOA.Classification.COne.OrbIcoUPair

/-! The pure c = 1 norm of the L(-2) tower at level 40 and seed weight 36.
This is a tower normalization, not a dual-state or mode-product measurement. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbOctaRC OrbSpan

def self40Norm : ℚ :=
  13901291337849500341367129362798551639281527435428003693673828125 / 4

set_option maxHeartbeats 5000000 in
-- Evaluate the ordered Virasoro word pairing, collecting identical words at each step.
set_option maxRecDepth 8192 in
theorem self40_pairing :
    pairWords 1 36 (List.replicate 20 2) (List.replicate 20 2) = self40Norm := by
  decide +kernel

theorem self40Norm_pos : 0 < self40Norm := by
  norm_num [self40Norm]

end VOA.Classification.COne.OrbIcoU
