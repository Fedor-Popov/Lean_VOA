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
def node41_sector0 : RawPoly ℕ := []

def node41_sector1 : RawPoly ℕ := [(200, [1, 1, 1, 2]), (-300, [1, 4]), (200, [2, 3])]

def node41_sector2 : RawPoly ℕ := []

def node41 : SectorVector := [(-2, node41_sector0), (0, node41_sector1), (2, node41_sector2)]
theorem node41_check : VectorCertificate (eMemoS (7) nineData) node41 := by decide +kernel

theorem node41_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (7) (evaluate nineData) = evaluate node41 :=
  eMemo_value (7) nineData node41 node41_check

end VOA.Classification.COne.OrbC2h
