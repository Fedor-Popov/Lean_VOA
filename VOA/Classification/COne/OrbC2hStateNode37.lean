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
def node37_sector0 : RawPoly ℕ := []

def node37_sector1 : RawPoly ℕ := [(-48, [1, 1, 1, 1, 1, 1]), (-160, [1, 1, 1, 3]), (120, [1, 1, 2, 2]), (192, [1, 5]), (-480, [2, 4]), (320, [3, 3])]

def node37_sector2 : RawPoly ℕ := []

def node37 : SectorVector := [(-2, node37_sector0), (0, node37_sector1), (2, node37_sector2)]
theorem node37_check : VectorCertificate (eMemoS (6) nineData) node37 := by decide +kernel

theorem node37_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (6) (evaluate nineData) = evaluate node37 :=
  eMemo_value (6) nineData node37 node37_check

end VOA.Classification.COne.OrbC2h
