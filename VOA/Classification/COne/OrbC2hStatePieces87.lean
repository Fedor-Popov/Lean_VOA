import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch87_0
import VOA.Classification.COne.OrbC2hStateBatch87_1
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

def node87Pieces : List (SectorVector × SectorVector) := [(node87Piece0Input, node87Piece0Output), (node87Piece1Input, node87Piece1Output), (node87Piece2Input, node87Piece2Output), (node87Piece3Input, node87Piece3Output), (node87Piece4Input, node87Piece4Output), (node87Piece5Input, node87Piece5Output), (node87Piece6Input, node87Piece6Output), (node87Piece7Input, node87Piece7Output), (node87Piece8Input, node87Piece8Output), (node87Piece9Input, node87Piece9Output), (node87Piece10Input, node87Piece10Output), (node87Piece11Input, node87Piece11Output), (node87Piece12Input, node87Piece12Output), (node87Piece13Input, node87Piece13Output), (node87Piece14Input, node87Piece14Output), (node87Piece15Input, node87Piece15Output), (node87Piece16Input, node87Piece16Output), (node87Piece17Input, node87Piece17Output), (node87Piece18Input, node87Piece18Output), (node87Piece19Input, node87Piece19Output), (node87Piece20Input, node87Piece20Output), (node87Piece21Input, node87Piece21Output), (node87Piece22Input, node87Piece22Output), (node87Piece23Input, node87Piece23Output), (node87Piece24Input, node87Piece24Output), (node87Piece25Input, node87Piece25Output), (node87Piece26Input, node87Piece26Output)]

theorem node87Pieces_input : VectorCertificate (node87Pieces.flatMap Prod.fst) node11 := by decide +kernel

theorem node87Pieces_each : ∀ p ∈ node87Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-8) (evaluate p.1) = evaluate p.2 := by
  simp only [node87Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node87Piece0_value, node87Piece1_value, node87Piece2_value, node87Piece3_value, node87Piece4_value, node87Piece5_value, node87Piece6_value, node87Piece7_value, node87Piece8_value, node87Piece9_value, node87Piece10_value, node87Piece11_value, node87Piece12_value, node87Piece13_value, node87Piece14_value, node87Piece15_value, node87Piece16_value, node87Piece17_value, node87Piece18_value, node87Piece19_value, node87Piece20_value, node87Piece21_value, node87Piece22_value, node87Piece23_value, node87Piece24_value, node87Piece25_value, node87Piece26_value, by simp⟩
end VOA.Classification.COne.OrbC2h
