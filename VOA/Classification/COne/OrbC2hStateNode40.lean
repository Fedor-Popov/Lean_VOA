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
def node40_sector0 : RawPoly ℕ := [(1350, [0, 1])]

def node40_sector1 : RawPoly ℕ := [(-1350, [0, 1])]

def node40 : SectorVector := [(-1, node40_sector0), (1, node40_sector1)]
theorem node40_check : VectorCertificate (neutralBoundS JR (7) nineData) node40 := by decide +kernel

theorem node40_value : (V2m 4 four_ge_one).smul (ls 4 JR) (7) (evaluate nineData) = evaluate node40 :=
  neutralBound_value JR (7) nineData node40 node40_check

end VOA.Classification.COne.OrbC2h
