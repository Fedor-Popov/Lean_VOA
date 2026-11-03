import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch89_0
import VOA.Classification.COne.OrbC2hStateBatch89_1
import VOA.Classification.COne.OrbC2hStateNode17
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node89Pieces : List (SectorVector × SectorVector) := [(node89Piece0Input, node89Piece0Output), (node89Piece1Input, node89Piece1Output), (node89Piece2Input, node89Piece2Output), (node89Piece3Input, node89Piece3Output), (node89Piece4Input, node89Piece4Output), (node89Piece5Input, node89Piece5Output), (node89Piece6Input, node89Piece6Output), (node89Piece7Input, node89Piece7Output), (node89Piece8Input, node89Piece8Output), (node89Piece9Input, node89Piece9Output), (node89Piece10Input, node89Piece10Output), (node89Piece11Input, node89Piece11Output), (node89Piece12Input, node89Piece12Output), (node89Piece13Input, node89Piece13Output), (node89Piece14Input, node89Piece14Output), (node89Piece15Input, node89Piece15Output), (node89Piece16Input, node89Piece16Output), (node89Piece17Input, node89Piece17Output), (node89Piece18Input, node89Piece18Output), (node89Piece19Input, node89Piece19Output), (node89Piece20Input, node89Piece20Output), (node89Piece21Input, node89Piece21Output)]

theorem node89Pieces_input : VectorCertificate (node89Pieces.flatMap Prod.fst) node17 := by decide +kernel

theorem node89Pieces_each : ∀ p ∈ node89Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9) (evaluate p.1) = evaluate p.2 := by
  simp only [node89Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node89Piece0_value, node89Piece1_value, node89Piece2_value, node89Piece3_value, node89Piece4_value, node89Piece5_value, node89Piece6_value, node89Piece7_value, node89Piece8_value, node89Piece9_value, node89Piece10_value, node89Piece11_value, node89Piece12_value, node89Piece13_value, node89Piece14_value, node89Piece15_value, node89Piece16_value, node89Piece17_value, node89Piece18_value, node89Piece19_value, node89Piece20_value, node89Piece21_value, by simp⟩
end VOA.Classification.COne.OrbC2h
