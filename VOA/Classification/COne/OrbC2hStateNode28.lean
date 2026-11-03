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
def node28_sector0 : RawPoly ℕ := [(-2160, [0, 1, 1, 2]), (-5400, [0, 4]), (-720, [1, 1, 1, 1]), (-13680, [1, 3]), (-3240, [2, 2])]

def node28_sector1 : RawPoly ℕ := [(2160, [0, 1, 1, 2]), (5400, [0, 4]), (-720, [1, 1, 1, 1]), (-13680, [1, 3]), (-3240, [2, 2])]

def node28 : SectorVector := [(-1, node28_sector0), (1, node28_sector1)]
theorem node28_check : VectorCertificate (neutralBoundS JR (4) nineData) node28 := by decide +kernel

theorem node28_value : (V2m 4 four_ge_one).smul (ls 4 JR) (4) (evaluate nineData) = evaluate node28 :=
  neutralBound_value JR (4) nineData node28 node28_check

end VOA.Classification.COne.OrbC2h
