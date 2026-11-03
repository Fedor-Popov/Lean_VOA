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
def node29_sector0 : RawPoly ℕ := []

def node29_sector1 : RawPoly ℕ := [(192/7, [1, 1, 1, 1, 1, 1, 1, 1]), (-336, [1, 1, 1, 1, 1, 3]), (240, [1, 1, 1, 1, 2, 2]), (-64, [1, 1, 1, 5]), (-480, [1, 1, 2, 4]), (480, [1, 1, 3, 3]), (360, [1, 2, 2, 3]), (480/7, [1, 7]), (-280, [2, 2, 2, 2]), (-160, [2, 6]), (224, [3, 5]), (-120, [4, 4])]

def node29_sector2 : RawPoly ℕ := []

def node29 : SectorVector := [(-2, node29_sector0), (0, node29_sector1), (2, node29_sector2)]
theorem node29_check : VectorCertificate (eMemoS (4) nineData) node29 := by decide +kernel

theorem node29_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (4) (evaluate nineData) = evaluate node29 :=
  eMemo_value (4) nineData node29 node29_check

end VOA.Classification.COne.OrbC2h
