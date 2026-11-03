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
def node36_sector0 : RawPoly ℕ := [(-2160, [0, 2]), (-2160, [1, 1])]

def node36_sector1 : RawPoly ℕ := [(2160, [0, 2]), (-2160, [1, 1])]

def node36 : SectorVector := [(-1, node36_sector0), (1, node36_sector1)]
theorem node36_check : VectorCertificate (neutralBoundS JR (6) nineData) node36 := by decide +kernel

theorem node36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (6) (evaluate nineData) = evaluate node36 :=
  neutralBound_value JR (6) nineData node36 node36_check

end VOA.Classification.COne.OrbC2h
