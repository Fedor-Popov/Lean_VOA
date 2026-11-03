import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch81_1
import VOA.Classification.COne.OrbC2hStateBatch81_2
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

def node81Pieces : List (SectorVector × SectorVector) := [(node81Piece0Input, node81Piece0Output), (node81Piece1Input, node81Piece1Output), (node81Piece2Input, node81Piece2Output), (node81Piece3Input, node81Piece3Output), (node81Piece4Input, node81Piece4Output), (node81Piece5Input, node81Piece5Output), (node81Piece6Input, node81Piece6Output), (node81Piece7Input, node81Piece7Output), (node81Piece8Input, node81Piece8Output), (node81Piece9Input, node81Piece9Output), (node81Piece10Input, node81Piece10Output), (node81Piece11Input, node81Piece11Output), (node81Piece12Input, node81Piece12Output), (node81Piece13Input, node81Piece13Output), (node81Piece14Input, node81Piece14Output), (node81Piece15Input, node81Piece15Output), (node81Piece16Input, node81Piece16Output), (node81Piece17Input, node81Piece17Output), (node81Piece18Input, node81Piece18Output), (node81Piece19Input, node81Piece19Output), (node81Piece20Input, node81Piece20Output), (node81Piece21Input, node81Piece21Output), (node81Piece22Input, node81Piece22Output), (node81Piece23Input, node81Piece23Output), (node81Piece24Input, node81Piece24Output), (node81Piece25Input, node81Piece25Output), (node81Piece26Input, node81Piece26Output), (node81Piece27Input, node81Piece27Output), (node81Piece28Input, node81Piece28Output), (node81Piece29Input, node81Piece29Output), (node81Piece30Input, node81Piece30Output), (node81Piece31Input, node81Piece31Output), (node81Piece32Input, node81Piece32Output), (node81Piece33Input, node81Piece33Output), (node81Piece34Input, node81Piece34Output), (node81Piece35Input, node81Piece35Output), (node81Piece36Input, node81Piece36Output), (node81Piece37Input, node81Piece37Output)]

theorem node81Pieces_input : VectorCertificate (node81Pieces.flatMap Prod.fst) node3 := by decide +kernel

theorem node81Pieces_each : ∀ p ∈ node81Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-7) (evaluate p.1) = evaluate p.2 := by
  simp only [node81Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node81Piece0_value, node81Piece1_value, node81Piece2_value, node81Piece3_value, node81Piece4_value, node81Piece5_value, node81Piece6_value, node81Piece7_value, node81Piece8_value, node81Piece9_value, node81Piece10_value, node81Piece11_value, node81Piece12_value, node81Piece13_value, node81Piece14_value, node81Piece15_value, node81Piece16_value, node81Piece17_value, node81Piece18_value, node81Piece19_value, node81Piece20_value, node81Piece21_value, node81Piece22_value, node81Piece23_value, node81Piece24_value, node81Piece25_value, node81Piece26_value, node81Piece27_value, node81Piece28_value, node81Piece29_value, node81Piece30_value, node81Piece31_value, node81Piece32_value, node81Piece33_value, node81Piece34_value, node81Piece35_value, node81Piece36_value, node81Piece37_value, by simp⟩
end VOA.Classification.COne.OrbC2h
