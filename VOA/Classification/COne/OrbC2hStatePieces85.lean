import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch85_0
import VOA.Classification.COne.OrbC2hStateBatch85_1
import VOA.Classification.COne.OrbC2hStateNode9
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node85Pieces : List (SectorVector × SectorVector) := [(node85Piece0Input, node85Piece0Output), (node85Piece1Input, node85Piece1Output), (node85Piece2Input, node85Piece2Output), (node85Piece3Input, node85Piece3Output), (node85Piece4Input, node85Piece4Output), (node85Piece5Input, node85Piece5Output), (node85Piece6Input, node85Piece6Output), (node85Piece7Input, node85Piece7Output), (node85Piece8Input, node85Piece8Output), (node85Piece9Input, node85Piece9Output), (node85Piece10Input, node85Piece10Output), (node85Piece11Input, node85Piece11Output), (node85Piece12Input, node85Piece12Output), (node85Piece13Input, node85Piece13Output), (node85Piece14Input, node85Piece14Output), (node85Piece15Input, node85Piece15Output), (node85Piece16Input, node85Piece16Output), (node85Piece17Input, node85Piece17Output), (node85Piece18Input, node85Piece18Output), (node85Piece19Input, node85Piece19Output), (node85Piece20Input, node85Piece20Output), (node85Piece21Input, node85Piece21Output), (node85Piece22Input, node85Piece22Output), (node85Piece23Input, node85Piece23Output), (node85Piece24Input, node85Piece24Output), (node85Piece25Input, node85Piece25Output), (node85Piece26Input, node85Piece26Output), (node85Piece27Input, node85Piece27Output), (node85Piece28Input, node85Piece28Output), (node85Piece29Input, node85Piece29Output)]

theorem node85Pieces_input : VectorCertificate (node85Pieces.flatMap Prod.fst) node9 := by decide +kernel

theorem node85Pieces_each : ∀ p ∈ node85Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-8) (evaluate p.1) = evaluate p.2 := by
  simp only [node85Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node85Piece0_value, node85Piece1_value, node85Piece2_value, node85Piece3_value, node85Piece4_value, node85Piece5_value, node85Piece6_value, node85Piece7_value, node85Piece8_value, node85Piece9_value, node85Piece10_value, node85Piece11_value, node85Piece12_value, node85Piece13_value, node85Piece14_value, node85Piece15_value, node85Piece16_value, node85Piece17_value, node85Piece18_value, node85Piece19_value, node85Piece20_value, node85Piece21_value, node85Piece22_value, node85Piece23_value, node85Piece24_value, node85Piece25_value, node85Piece26_value, node85Piece27_value, node85Piece28_value, node85Piece29_value, by simp⟩
end VOA.Classification.COne.OrbC2h
