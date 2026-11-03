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
def node24_sector0 : RawPoly ℕ := [(270, [0, 1, 1, 1, 1, 1]), (540, [0, 1, 1, 3]), (1215, [0, 1, 2, 2]), (-4860, [0, 5]), (4320, [1, 1, 1, 2]), (-8100, [1, 4])]

def node24_sector1 : RawPoly ℕ := [(-270, [0, 1, 1, 1, 1, 1]), (-540, [0, 1, 1, 3]), (-1215, [0, 1, 2, 2]), (4860, [0, 5]), (4320, [1, 1, 1, 2]), (-8100, [1, 4])]

def node24 : SectorVector := [(-1, node24_sector0), (1, node24_sector1)]
theorem node24_check : VectorCertificate (neutralBoundS JR (3) nineData) node24 := by decide +kernel

theorem node24_value : (V2m 4 four_ge_one).smul (ls 4 JR) (3) (evaluate nineData) = evaluate node24 :=
  neutralBound_value JR (3) nineData node24 node24_check

end VOA.Classification.COne.OrbC2h
