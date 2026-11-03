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
def node33_sector0 : RawPoly ℕ := []

def node33_sector1 : RawPoly ℕ := [(-24, [1, 1, 1, 1, 1, 2]), (-640, [1, 1, 1, 4]), (1200, [1, 1, 2, 3]), (-580, [1, 2, 2, 2]), (80, [1, 6]), (-144, [2, 5]), (80, [3, 4])]

def node33_sector2 : RawPoly ℕ := []

def node33 : SectorVector := [(-2, node33_sector0), (0, node33_sector1), (2, node33_sector2)]
theorem node33_check : VectorCertificate (eMemoS (5) nineData) node33 := by decide +kernel

theorem node33_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (5) (evaluate nineData) = evaluate node33 :=
  eMemo_value (5) nineData node33 node33_check

end VOA.Classification.COne.OrbC2h
