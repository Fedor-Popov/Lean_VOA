import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node32_sector0 : RawPoly ℕ := [(-720, [0, 1, 1, 1]), (-3960, [0, 3]), (-9720, [1, 2])]

def node32_sector1 : RawPoly ℕ := [(720, [0, 1, 1, 1]), (3960, [0, 3]), (-9720, [1, 2])]

def node32 : SectorVector := [(-1, node32_sector0), (1, node32_sector1)]
theorem node32_check : VectorCertificate (neutralBoundS JR (5) nineData) node32 := by decide +kernel

theorem node32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (5) (evaluate nineData) = evaluate node32 :=
  neutralBound_value JR (5) nineData node32 node32_check

end VOA.Classification.COne.OrbC2h
