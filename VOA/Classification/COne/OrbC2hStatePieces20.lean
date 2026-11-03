import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch20_1
import VOA.Classification.COne.OrbC2hStateBatch20_2
import VOA.Classification.COne.OrbC2hStateNode16
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node20Pieces : List (SectorVector × SectorVector) := [(node20Piece0Input, node20Piece0Output), (node20Piece1Input, node20Piece1Output), (node20Piece2Input, node20Piece2Output), (node20Piece3Input, node20Piece3Output), (node20Piece4Input, node20Piece4Output), (node20Piece5Input, node20Piece5Output), (node20Piece6Input, node20Piece6Output), (node20Piece7Input, node20Piece7Output), (node20Piece8Input, node20Piece8Output), (node20Piece9Input, node20Piece9Output), (node20Piece10Input, node20Piece10Output), (node20Piece11Input, node20Piece11Output), (node20Piece12Input, node20Piece12Output), (node20Piece13Input, node20Piece13Output), (node20Piece14Input, node20Piece14Output), (node20Piece15Input, node20Piece15Output), (node20Piece16Input, node20Piece16Output), (node20Piece17Input, node20Piece17Output), (node20Piece18Input, node20Piece18Output), (node20Piece19Input, node20Piece19Output), (node20Piece20Input, node20Piece20Output), (node20Piece21Input, node20Piece21Output), (node20Piece22Input, node20Piece22Output), (node20Piece23Input, node20Piece23Output), (node20Piece24Input, node20Piece24Output), (node20Piece25Input, node20Piece25Output), (node20Piece26Input, node20Piece26Output), (node20Piece27Input, node20Piece27Output), (node20Piece28Input, node20Piece28Output), (node20Piece29Input, node20Piece29Output), (node20Piece30Input, node20Piece30Output), (node20Piece31Input, node20Piece31Output), (node20Piece32Input, node20Piece32Output), (node20Piece33Input, node20Piece33Output), (node20Piece34Input, node20Piece34Output), (node20Piece35Input, node20Piece35Output), (node20Piece36Input, node20Piece36Output), (node20Piece37Input, node20Piece37Output), (node20Piece38Input, node20Piece38Output), (node20Piece39Input, node20Piece39Output), (node20Piece40Input, node20Piece40Output), (node20Piece41Input, node20Piece41Output), (node20Piece42Input, node20Piece42Output), (node20Piece43Input, node20Piece43Output), (node20Piece44Input, node20Piece44Output), (node20Piece45Input, node20Piece45Output), (node20Piece46Input, node20Piece46Output)]

theorem node20Pieces_input : VectorCertificate (node20Pieces.flatMap Prod.fst) node16 := by decide +kernel

theorem node20Pieces_each : ∀ p ∈ node20Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-4) (evaluate p.1) = evaluate p.2 := by
  simp only [node20Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node20Piece0_value, node20Piece1_value, node20Piece2_value, node20Piece3_value, node20Piece4_value, node20Piece5_value, node20Piece6_value, node20Piece7_value, node20Piece8_value, node20Piece9_value, node20Piece10_value, node20Piece11_value, node20Piece12_value, node20Piece13_value, node20Piece14_value, node20Piece15_value, node20Piece16_value, node20Piece17_value, node20Piece18_value, node20Piece19_value, node20Piece20_value, node20Piece21_value, node20Piece22_value, node20Piece23_value, node20Piece24_value, node20Piece25_value, node20Piece26_value, node20Piece27_value, node20Piece28_value, node20Piece29_value, node20Piece30_value, node20Piece31_value, node20Piece32_value, node20Piece33_value, node20Piece34_value, node20Piece35_value, node20Piece36_value, node20Piece37_value, node20Piece38_value, node20Piece39_value, node20Piece40_value, node20Piece41_value, node20Piece42_value, node20Piece43_value, node20Piece44_value, node20Piece45_value, node20Piece46_value, by simp⟩
end VOA.Classification.COne.OrbC2h
