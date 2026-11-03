import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch13_0
import VOA.Classification.COne.OrbC2hStateBatch13_1
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

def node13Pieces : List (SectorVector × SectorVector) := [(node13Piece0Input, node13Piece0Output), (node13Piece1Input, node13Piece1Output), (node13Piece2Input, node13Piece2Output), (node13Piece3Input, node13Piece3Output), (node13Piece4Input, node13Piece4Output), (node13Piece5Input, node13Piece5Output), (node13Piece6Input, node13Piece6Output), (node13Piece7Input, node13Piece7Output), (node13Piece8Input, node13Piece8Output), (node13Piece9Input, node13Piece9Output), (node13Piece10Input, node13Piece10Output), (node13Piece11Input, node13Piece11Output), (node13Piece12Input, node13Piece12Output), (node13Piece13Input, node13Piece13Output), (node13Piece14Input, node13Piece14Output), (node13Piece15Input, node13Piece15Output), (node13Piece16Input, node13Piece16Output), (node13Piece17Input, node13Piece17Output), (node13Piece18Input, node13Piece18Output), (node13Piece19Input, node13Piece19Output), (node13Piece20Input, node13Piece20Output), (node13Piece21Input, node13Piece21Output), (node13Piece22Input, node13Piece22Output), (node13Piece23Input, node13Piece23Output), (node13Piece24Input, node13Piece24Output), (node13Piece25Input, node13Piece25Output), (node13Piece26Input, node13Piece26Output), (node13Piece27Input, node13Piece27Output), (node13Piece28Input, node13Piece28Output), (node13Piece29Input, node13Piece29Output)]

theorem node13Pieces_input : VectorCertificate (node13Pieces.flatMap Prod.fst) node9 := by decide +kernel

theorem node13Pieces_each : ∀ p ∈ node13Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6) (evaluate p.1) = evaluate p.2 := by
  simp only [node13Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node13Piece0_value, node13Piece1_value, node13Piece2_value, node13Piece3_value, node13Piece4_value, node13Piece5_value, node13Piece6_value, node13Piece7_value, node13Piece8_value, node13Piece9_value, node13Piece10_value, node13Piece11_value, node13Piece12_value, node13Piece13_value, node13Piece14_value, node13Piece15_value, node13Piece16_value, node13Piece17_value, node13Piece18_value, node13Piece19_value, node13Piece20_value, node13Piece21_value, node13Piece22_value, node13Piece23_value, node13Piece24_value, node13Piece25_value, node13Piece26_value, node13Piece27_value, node13Piece28_value, node13Piece29_value, by simp⟩
end VOA.Classification.COne.OrbC2h
