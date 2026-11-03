import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch15_0
import VOA.Classification.COne.OrbC2hStateBatch15_1
import VOA.Classification.COne.OrbC2hStateNode11
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node15Pieces : List (SectorVector × SectorVector) := [(node15Piece0Input, node15Piece0Output), (node15Piece1Input, node15Piece1Output), (node15Piece2Input, node15Piece2Output), (node15Piece3Input, node15Piece3Output), (node15Piece4Input, node15Piece4Output), (node15Piece5Input, node15Piece5Output), (node15Piece6Input, node15Piece6Output), (node15Piece7Input, node15Piece7Output), (node15Piece8Input, node15Piece8Output), (node15Piece9Input, node15Piece9Output), (node15Piece10Input, node15Piece10Output), (node15Piece11Input, node15Piece11Output), (node15Piece12Input, node15Piece12Output), (node15Piece13Input, node15Piece13Output), (node15Piece14Input, node15Piece14Output), (node15Piece15Input, node15Piece15Output), (node15Piece16Input, node15Piece16Output), (node15Piece17Input, node15Piece17Output), (node15Piece18Input, node15Piece18Output), (node15Piece19Input, node15Piece19Output), (node15Piece20Input, node15Piece20Output), (node15Piece21Input, node15Piece21Output), (node15Piece22Input, node15Piece22Output), (node15Piece23Input, node15Piece23Output), (node15Piece24Input, node15Piece24Output), (node15Piece25Input, node15Piece25Output), (node15Piece26Input, node15Piece26Output)]

theorem node15Pieces_input : VectorCertificate (node15Pieces.flatMap Prod.fst) node11 := by decide +kernel

theorem node15Pieces_each : ∀ p ∈ node15Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-6) (evaluate p.1) = evaluate p.2 := by
  simp only [node15Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node15Piece0_value, node15Piece1_value, node15Piece2_value, node15Piece3_value, node15Piece4_value, node15Piece5_value, node15Piece6_value, node15Piece7_value, node15Piece8_value, node15Piece9_value, node15Piece10_value, node15Piece11_value, node15Piece12_value, node15Piece13_value, node15Piece14_value, node15Piece15_value, node15Piece16_value, node15Piece17_value, node15Piece18_value, node15Piece19_value, node15Piece20_value, node15Piece21_value, node15Piece22_value, node15Piece23_value, node15Piece24_value, node15Piece25_value, node15Piece26_value, by simp⟩
end VOA.Classification.COne.OrbC2h
