import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch21_0
import VOA.Classification.COne.OrbC2hStateBatch21_1
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

def node21Pieces : List (SectorVector × SectorVector) := [(node21Piece0Input, node21Piece0Output), (node21Piece1Input, node21Piece1Output), (node21Piece2Input, node21Piece2Output), (node21Piece3Input, node21Piece3Output), (node21Piece4Input, node21Piece4Output), (node21Piece5Input, node21Piece5Output), (node21Piece6Input, node21Piece6Output), (node21Piece7Input, node21Piece7Output), (node21Piece8Input, node21Piece8Output), (node21Piece9Input, node21Piece9Output), (node21Piece10Input, node21Piece10Output), (node21Piece11Input, node21Piece11Output), (node21Piece12Input, node21Piece12Output), (node21Piece13Input, node21Piece13Output), (node21Piece14Input, node21Piece14Output), (node21Piece15Input, node21Piece15Output), (node21Piece16Input, node21Piece16Output), (node21Piece17Input, node21Piece17Output), (node21Piece18Input, node21Piece18Output), (node21Piece19Input, node21Piece19Output), (node21Piece20Input, node21Piece20Output), (node21Piece21Input, node21Piece21Output)]

theorem node21Pieces_input : VectorCertificate (node21Pieces.flatMap Prod.fst) node17 := by decide +kernel

theorem node21Pieces_each : ∀ p ∈ node21Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-7) (evaluate p.1) = evaluate p.2 := by
  simp only [node21Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node21Piece0_value, node21Piece1_value, node21Piece2_value, node21Piece3_value, node21Piece4_value, node21Piece5_value, node21Piece6_value, node21Piece7_value, node21Piece8_value, node21Piece9_value, node21Piece10_value, node21Piece11_value, node21Piece12_value, node21Piece13_value, node21Piece14_value, node21Piece15_value, node21Piece16_value, node21Piece17_value, node21Piece18_value, node21Piece19_value, node21Piece20_value, node21Piece21_value, by simp⟩
end VOA.Classification.COne.OrbC2h
