import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch7_1
import VOA.Classification.COne.OrbC2hStateBatch7_2
import VOA.Classification.COne.OrbC2hStateNode3
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node7Pieces : List (SectorVector × SectorVector) := [(node7Piece0Input, node7Piece0Output), (node7Piece1Input, node7Piece1Output), (node7Piece2Input, node7Piece2Output), (node7Piece3Input, node7Piece3Output), (node7Piece4Input, node7Piece4Output), (node7Piece5Input, node7Piece5Output), (node7Piece6Input, node7Piece6Output), (node7Piece7Input, node7Piece7Output), (node7Piece8Input, node7Piece8Output), (node7Piece9Input, node7Piece9Output), (node7Piece10Input, node7Piece10Output), (node7Piece11Input, node7Piece11Output), (node7Piece12Input, node7Piece12Output), (node7Piece13Input, node7Piece13Output), (node7Piece14Input, node7Piece14Output), (node7Piece15Input, node7Piece15Output), (node7Piece16Input, node7Piece16Output), (node7Piece17Input, node7Piece17Output), (node7Piece18Input, node7Piece18Output), (node7Piece19Input, node7Piece19Output), (node7Piece20Input, node7Piece20Output), (node7Piece21Input, node7Piece21Output), (node7Piece22Input, node7Piece22Output), (node7Piece23Input, node7Piece23Output), (node7Piece24Input, node7Piece24Output), (node7Piece25Input, node7Piece25Output), (node7Piece26Input, node7Piece26Output), (node7Piece27Input, node7Piece27Output), (node7Piece28Input, node7Piece28Output), (node7Piece29Input, node7Piece29Output), (node7Piece30Input, node7Piece30Output), (node7Piece31Input, node7Piece31Output), (node7Piece32Input, node7Piece32Output), (node7Piece33Input, node7Piece33Output), (node7Piece34Input, node7Piece34Output), (node7Piece35Input, node7Piece35Output), (node7Piece36Input, node7Piece36Output), (node7Piece37Input, node7Piece37Output)]

theorem node7Pieces_input : VectorCertificate (node7Pieces.flatMap Prod.fst) node3 := by decide +kernel

theorem node7Pieces_each : ∀ p ∈ node7Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-5) (evaluate p.1) = evaluate p.2 := by
  simp only [node7Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node7Piece0_value, node7Piece1_value, node7Piece2_value, node7Piece3_value, node7Piece4_value, node7Piece5_value, node7Piece6_value, node7Piece7_value, node7Piece8_value, node7Piece9_value, node7Piece10_value, node7Piece11_value, node7Piece12_value, node7Piece13_value, node7Piece14_value, node7Piece15_value, node7Piece16_value, node7Piece17_value, node7Piece18_value, node7Piece19_value, node7Piece20_value, node7Piece21_value, node7Piece22_value, node7Piece23_value, node7Piece24_value, node7Piece25_value, node7Piece26_value, node7Piece27_value, node7Piece28_value, node7Piece29_value, node7Piece30_value, node7Piece31_value, node7Piece32_value, node7Piece33_value, node7Piece34_value, node7Piece35_value, node7Piece36_value, node7Piece37_value, by simp⟩
end VOA.Classification.COne.OrbC2h
