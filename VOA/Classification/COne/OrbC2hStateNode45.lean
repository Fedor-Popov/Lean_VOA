import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node45_sector0 : RawPoly ℕ := []

def node45_sector1 : RawPoly ℕ := [(-400, [1, 1, 1, 1]), (800, [1, 3]), (-600, [2, 2])]

def node45_sector2 : RawPoly ℕ := []

def node45 : SectorVector := [(-2, node45_sector0), (0, node45_sector1), (2, node45_sector2)]
theorem node45_check : VectorCertificate (eMemoS (8) nineData) node45 := by decide +kernel

theorem node45_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (8) (evaluate nineData) = evaluate node45 :=
  eMemo_value (8) nineData node45 node45_check

end VOA.Classification.COne.OrbC2h
