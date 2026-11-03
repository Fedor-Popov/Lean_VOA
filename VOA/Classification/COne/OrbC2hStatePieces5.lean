import VOA.Classification.COne.OrbC2hStateBatch5_1
import VOA.Classification.COne.OrbC2hStateBatch5_2
import VOA.Classification.COne.OrbC2hStateNode4
import VOA.Classification.COne.OrbC2hChargedSectors
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node5Pieces : List (SectorVector × SectorVector) := [(node5Piece0Input, node5Piece0Output), (node5Piece1Input, node5Piece1Output), (node5Piece2Input, node5Piece2Output), (node5Piece3Input, node5Piece3Output), (node5Piece4Input, node5Piece4Output), (node5Piece5Input, node5Piece5Output), (node5Piece6Input, node5Piece6Output), (node5Piece7Input, node5Piece7Output), (node5Piece8Input, node5Piece8Output), (node5Piece9Input, node5Piece9Output), (node5Piece10Input, node5Piece10Output), (node5Piece11Input, node5Piece11Output), (node5Piece12Input, node5Piece12Output), (node5Piece13Input, node5Piece13Output), (node5Piece14Input, node5Piece14Output), (node5Piece15Input, node5Piece15Output), (node5Piece16Input, node5Piece16Output), (node5Piece17Input, node5Piece17Output), (node5Piece18Input, node5Piece18Output), (node5Piece19Input, node5Piece19Output), (node5Piece20Input, node5Piece20Output), (node5Piece21Input, node5Piece21Output), (node5Piece22Input, node5Piece22Output), (node5Piece23Input, node5Piece23Output), (node5Piece24Input, node5Piece24Output), (node5Piece25Input, node5Piece25Output), (node5Piece26Input, node5Piece26Output), (node5Piece27Input, node5Piece27Output), (node5Piece28Input, node5Piece28Output), (node5Piece29Input, node5Piece29Output), (node5Piece30Input, node5Piece30Output), (node5Piece31Input, node5Piece31Output), (node5Piece32Input, node5Piece32Output), (node5Piece33Input, node5Piece33Output), (node5Piece34Input, node5Piece34Output), (node5Piece35Input, node5Piece35Output), (node5Piece36Input, node5Piece36Output), (node5Piece37Input, node5Piece37Output), (node5Piece38Input, node5Piece38Output), (node5Piece39Input, node5Piece39Output), (node5Piece40Input, node5Piece40Output), (node5Piece41Input, node5Piece41Output), (node5Piece42Input, node5Piece42Output), (node5Piece43Input, node5Piece43Output)]

theorem node5Pieces_input : VectorCertificate (node5Pieces.flatMap Prod.fst) node1 := by decide +kernel

theorem node5Pieces_each : ∀ p ∈ node5Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5) (evaluate p.1) = evaluate p.2 := by
  simp only [node5Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node5Piece0_value, node5Piece1_value, node5Piece2_value, node5Piece3_value, node5Piece4_value, node5Piece5_value, node5Piece6_value, node5Piece7_value, node5Piece8_value, node5Piece9_value, node5Piece10_value, node5Piece11_value, node5Piece12_value, node5Piece13_value, node5Piece14_value, node5Piece15_value, node5Piece16_value, node5Piece17_value, node5Piece18_value, node5Piece19_value, node5Piece20_value, node5Piece21_value, node5Piece22_value, node5Piece23_value, node5Piece24_value, node5Piece25_value, node5Piece26_value, node5Piece27_value, node5Piece28_value, node5Piece29_value, node5Piece30_value, node5Piece31_value, node5Piece32_value, node5Piece33_value, node5Piece34_value, node5Piece35_value, node5Piece36_value, node5Piece37_value, node5Piece38_value, node5Piece39_value, node5Piece40_value, node5Piece41_value, node5Piece42_value, node5Piece43_value, by simp⟩
end VOA.Classification.COne.OrbC2h
