import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch79_1
import VOA.Classification.COne.OrbC2hStateBatch79_2
import VOA.Classification.COne.OrbC2hStateNode1
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node79Pieces : List (SectorVector × SectorVector) := [(node79Piece0Input, node79Piece0Output), (node79Piece1Input, node79Piece1Output), (node79Piece2Input, node79Piece2Output), (node79Piece3Input, node79Piece3Output), (node79Piece4Input, node79Piece4Output), (node79Piece5Input, node79Piece5Output), (node79Piece6Input, node79Piece6Output), (node79Piece7Input, node79Piece7Output), (node79Piece8Input, node79Piece8Output), (node79Piece9Input, node79Piece9Output), (node79Piece10Input, node79Piece10Output), (node79Piece11Input, node79Piece11Output), (node79Piece12Input, node79Piece12Output), (node79Piece13Input, node79Piece13Output), (node79Piece14Input, node79Piece14Output), (node79Piece15Input, node79Piece15Output), (node79Piece16Input, node79Piece16Output), (node79Piece17Input, node79Piece17Output), (node79Piece18Input, node79Piece18Output), (node79Piece19Input, node79Piece19Output), (node79Piece20Input, node79Piece20Output), (node79Piece21Input, node79Piece21Output), (node79Piece22Input, node79Piece22Output), (node79Piece23Input, node79Piece23Output), (node79Piece24Input, node79Piece24Output), (node79Piece25Input, node79Piece25Output), (node79Piece26Input, node79Piece26Output), (node79Piece27Input, node79Piece27Output), (node79Piece28Input, node79Piece28Output), (node79Piece29Input, node79Piece29Output), (node79Piece30Input, node79Piece30Output), (node79Piece31Input, node79Piece31Output), (node79Piece32Input, node79Piece32Output), (node79Piece33Input, node79Piece33Output), (node79Piece34Input, node79Piece34Output), (node79Piece35Input, node79Piece35Output), (node79Piece36Input, node79Piece36Output), (node79Piece37Input, node79Piece37Output), (node79Piece38Input, node79Piece38Output), (node79Piece39Input, node79Piece39Output), (node79Piece40Input, node79Piece40Output), (node79Piece41Input, node79Piece41Output), (node79Piece42Input, node79Piece42Output), (node79Piece43Input, node79Piece43Output)]

theorem node79Pieces_input : VectorCertificate (node79Pieces.flatMap Prod.fst) node1 := by decide +kernel

theorem node79Pieces_each : ∀ p ∈ node79Pieces,
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-7) (evaluate p.1) = evaluate p.2 := by
  simp only [node79Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node79Piece0_value, node79Piece1_value, node79Piece2_value, node79Piece3_value, node79Piece4_value, node79Piece5_value, node79Piece6_value, node79Piece7_value, node79Piece8_value, node79Piece9_value, node79Piece10_value, node79Piece11_value, node79Piece12_value, node79Piece13_value, node79Piece14_value, node79Piece15_value, node79Piece16_value, node79Piece17_value, node79Piece18_value, node79Piece19_value, node79Piece20_value, node79Piece21_value, node79Piece22_value, node79Piece23_value, node79Piece24_value, node79Piece25_value, node79Piece26_value, node79Piece27_value, node79Piece28_value, node79Piece29_value, node79Piece30_value, node79Piece31_value, node79Piece32_value, node79Piece33_value, node79Piece34_value, node79Piece35_value, node79Piece36_value, node79Piece37_value, node79Piece38_value, node79Piece39_value, node79Piece40_value, node79Piece41_value, node79Piece42_value, node79Piece43_value, by simp⟩
end VOA.Classification.COne.OrbC2h
