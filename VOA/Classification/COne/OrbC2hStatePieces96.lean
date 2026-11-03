import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch96_1
import VOA.Classification.COne.OrbC2hStateBatch96_2
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

def node96Pieces : List (SectorVector × SectorVector) := [(node96Piece0Input, node96Piece0Output), (node96Piece1Input, node96Piece1Output), (node96Piece2Input, node96Piece2Output), (node96Piece3Input, node96Piece3Output), (node96Piece4Input, node96Piece4Output), (node96Piece5Input, node96Piece5Output), (node96Piece6Input, node96Piece6Output), (node96Piece7Input, node96Piece7Output), (node96Piece8Input, node96Piece8Output), (node96Piece9Input, node96Piece9Output), (node96Piece10Input, node96Piece10Output), (node96Piece11Input, node96Piece11Output), (node96Piece12Input, node96Piece12Output), (node96Piece13Input, node96Piece13Output), (node96Piece14Input, node96Piece14Output), (node96Piece15Input, node96Piece15Output), (node96Piece16Input, node96Piece16Output), (node96Piece17Input, node96Piece17Output), (node96Piece18Input, node96Piece18Output), (node96Piece19Input, node96Piece19Output), (node96Piece20Input, node96Piece20Output), (node96Piece21Input, node96Piece21Output), (node96Piece22Input, node96Piece22Output), (node96Piece23Input, node96Piece23Output), (node96Piece24Input, node96Piece24Output), (node96Piece25Input, node96Piece25Output), (node96Piece26Input, node96Piece26Output), (node96Piece27Input, node96Piece27Output), (node96Piece28Input, node96Piece28Output), (node96Piece29Input, node96Piece29Output), (node96Piece30Input, node96Piece30Output), (node96Piece31Input, node96Piece31Output), (node96Piece32Input, node96Piece32Output), (node96Piece33Input, node96Piece33Output), (node96Piece34Input, node96Piece34Output), (node96Piece35Input, node96Piece35Output), (node96Piece36Input, node96Piece36Output), (node96Piece37Input, node96Piece37Output), (node96Piece38Input, node96Piece38Output), (node96Piece39Input, node96Piece39Output), (node96Piece40Input, node96Piece40Output), (node96Piece41Input, node96Piece41Output), (node96Piece42Input, node96Piece42Output), (node96Piece43Input, node96Piece43Output), (node96Piece44Input, node96Piece44Output), (node96Piece45Input, node96Piece45Output), (node96Piece46Input, node96Piece46Output)]

theorem node96Pieces_input : VectorCertificate (node96Pieces.flatMap Prod.fst) node16 := by decide +kernel

theorem node96Pieces_each : ∀ p ∈ node96Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-6) (evaluate p.1) = evaluate p.2 := by
  simp only [node96Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node96Piece0_value, node96Piece1_value, node96Piece2_value, node96Piece3_value, node96Piece4_value, node96Piece5_value, node96Piece6_value, node96Piece7_value, node96Piece8_value, node96Piece9_value, node96Piece10_value, node96Piece11_value, node96Piece12_value, node96Piece13_value, node96Piece14_value, node96Piece15_value, node96Piece16_value, node96Piece17_value, node96Piece18_value, node96Piece19_value, node96Piece20_value, node96Piece21_value, node96Piece22_value, node96Piece23_value, node96Piece24_value, node96Piece25_value, node96Piece26_value, node96Piece27_value, node96Piece28_value, node96Piece29_value, node96Piece30_value, node96Piece31_value, node96Piece32_value, node96Piece33_value, node96Piece34_value, node96Piece35_value, node96Piece36_value, node96Piece37_value, node96Piece38_value, node96Piece39_value, node96Piece40_value, node96Piece41_value, node96Piece42_value, node96Piece43_value, node96Piece44_value, node96Piece45_value, node96Piece46_value, by simp⟩
end VOA.Classification.COne.OrbC2h
