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
def node52_sector0 : RawPoly ℕ := []

def node52_sector1 : RawPoly ℕ := []

def node52 : SectorVector := [(-1, node52_sector0), (1, node52_sector1)]
theorem node52_check : VectorCertificate (neutralBoundS JR (10) nineData) node52 := by decide +kernel

theorem node52_value : (V2m 4 four_ge_one).smul (ls 4 JR) (10) (evaluate nineData) = evaluate node52 :=
  neutralBound_value JR (10) nineData node52 node52_check

end VOA.Classification.COne.OrbC2h
