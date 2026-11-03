import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch91_0
import VOA.Classification.COne.OrbC2hStateBatch91_1
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

def node91Pieces : List (SectorVector × SectorVector) := [(node91Piece0Input, node91Piece0Output), (node91Piece1Input, node91Piece1Output), (node91Piece2Input, node91Piece2Output), (node91Piece3Input, node91Piece3Output), (node91Piece4Input, node91Piece4Output), (node91Piece5Input, node91Piece5Output), (node91Piece6Input, node91Piece6Output), (node91Piece7Input, node91Piece7Output), (node91Piece8Input, node91Piece8Output), (node91Piece9Input, node91Piece9Output), (node91Piece10Input, node91Piece10Output), (node91Piece11Input, node91Piece11Output), (node91Piece12Input, node91Piece12Output), (node91Piece13Input, node91Piece13Output), (node91Piece14Input, node91Piece14Output), (node91Piece15Input, node91Piece15Output), (node91Piece16Input, node91Piece16Output), (node91Piece17Input, node91Piece17Output), (node91Piece18Input, node91Piece18Output), (node91Piece19Input, node91Piece19Output), (node91Piece20Input, node91Piece20Output), (node91Piece21Input, node91Piece21Output)]

theorem node91Pieces_input : VectorCertificate (node91Pieces.flatMap Prod.fst) node19 := by decide +kernel

theorem node91Pieces_each : ∀ p ∈ node91Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-9) (evaluate p.1) = evaluate p.2 := by
  simp only [node91Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node91Piece0_value, node91Piece1_value, node91Piece2_value, node91Piece3_value, node91Piece4_value, node91Piece5_value, node91Piece6_value, node91Piece7_value, node91Piece8_value, node91Piece9_value, node91Piece10_value, node91Piece11_value, node91Piece12_value, node91Piece13_value, node91Piece14_value, node91Piece15_value, node91Piece16_value, node91Piece17_value, node91Piece18_value, node91Piece19_value, node91Piece20_value, node91Piece21_value, by simp⟩
end VOA.Classification.COne.OrbC2h
