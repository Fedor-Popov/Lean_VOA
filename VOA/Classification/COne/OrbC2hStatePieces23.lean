import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch23_0
import VOA.Classification.COne.OrbC2hStateBatch23_1
import VOA.Classification.COne.OrbC2hStateNode19
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node23Pieces : List (SectorVector × SectorVector) := [(node23Piece0Input, node23Piece0Output), (node23Piece1Input, node23Piece1Output), (node23Piece2Input, node23Piece2Output), (node23Piece3Input, node23Piece3Output), (node23Piece4Input, node23Piece4Output), (node23Piece5Input, node23Piece5Output), (node23Piece6Input, node23Piece6Output), (node23Piece7Input, node23Piece7Output), (node23Piece8Input, node23Piece8Output), (node23Piece9Input, node23Piece9Output), (node23Piece10Input, node23Piece10Output), (node23Piece11Input, node23Piece11Output), (node23Piece12Input, node23Piece12Output), (node23Piece13Input, node23Piece13Output), (node23Piece14Input, node23Piece14Output), (node23Piece15Input, node23Piece15Output), (node23Piece16Input, node23Piece16Output), (node23Piece17Input, node23Piece17Output), (node23Piece18Input, node23Piece18Output), (node23Piece19Input, node23Piece19Output), (node23Piece20Input, node23Piece20Output), (node23Piece21Input, node23Piece21Output)]

theorem node23Pieces_input : VectorCertificate (node23Pieces.flatMap Prod.fst) node19 := by decide +kernel

theorem node23Pieces_each : ∀ p ∈ node23Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-7) (evaluate p.1) = evaluate p.2 := by
  simp only [node23Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node23Piece0_value, node23Piece1_value, node23Piece2_value, node23Piece3_value, node23Piece4_value, node23Piece5_value, node23Piece6_value, node23Piece7_value, node23Piece8_value, node23Piece9_value, node23Piece10_value, node23Piece11_value, node23Piece12_value, node23Piece13_value, node23Piece14_value, node23Piece15_value, node23Piece16_value, node23Piece17_value, node23Piece18_value, node23Piece19_value, node23Piece20_value, node23Piece21_value, by simp⟩
end VOA.Classification.COne.OrbC2h
