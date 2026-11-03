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
def node68_sector0 : RawPoly ℕ := []

def node68_sector1 : RawPoly ℕ := []

def node68 : SectorVector := [(-1, node68_sector0), (1, node68_sector1)]
theorem node68_check : VectorCertificate (neutralBoundS JR (14) nineData) node68 := by decide +kernel

theorem node68_value : (V2m 4 four_ge_one).smul (ls 4 JR) (14) (evaluate nineData) = evaluate node68 :=
  neutralBound_value JR (14) nineData node68 node68_check

end VOA.Classification.COne.OrbC2h
