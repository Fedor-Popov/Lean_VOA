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
def node48_sector0 : RawPoly ℕ := []

def node48_sector1 : RawPoly ℕ := []

def node48 : SectorVector := [(-1, node48_sector0), (1, node48_sector1)]
theorem node48_check : VectorCertificate (neutralBoundS JR (9) nineData) node48 := by decide +kernel

theorem node48_value : (V2m 4 four_ge_one).smul (ls 4 JR) (9) (evaluate nineData) = evaluate node48 :=
  neutralBound_value JR (9) nineData node48 node48_check

end VOA.Classification.COne.OrbC2h
