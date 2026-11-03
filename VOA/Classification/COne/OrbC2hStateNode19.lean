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
def node19_sector0 : RawPoly ℕ := []

def node19_sector1 : RawPoly ℕ := [(5504/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (-1472/63, [1, 1, 1, 1, 1, 1, 1, 3]), (176/3, [1, 1, 1, 1, 1, 1, 2, 2]), (-368/5, [1, 1, 1, 1, 1, 5]), (-320, [1, 1, 1, 1, 2, 4]), (-2240/9, [1, 1, 1, 1, 3, 3]), (2080/3, [1, 1, 1, 2, 2, 3]), (-960/7, [1, 1, 1, 7]), (-200, [1, 1, 2, 2, 2, 2]), (160, [1, 1, 2, 6]), (416, [1, 1, 3, 5]), (-360, [1, 1, 4, 4]), (-168, [1, 2, 2, 5]), (160, [1, 2, 3, 4]), (8320/27, [1, 3, 3, 3]), (160/3, [1, 9]), (-440, [2, 2, 2, 4]), (320/3, [2, 2, 3, 3]), (-120, [2, 8]), (960/7, [3, 7]), (-80, [4, 6]), (96/5, [5, 5])]

def node19_sector2 : RawPoly ℕ := []

def node19 : SectorVector := [(-2, node19_sector0), (0, node19_sector1), (2, node19_sector2)]
theorem node19_check : VectorCertificate (eMemoS (2) nineData) node19 := by decide +kernel

theorem node19_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (2) (evaluate nineData) = evaluate node19 :=
  eMemo_value (2) nineData node19 node19_check

end VOA.Classification.COne.OrbC2h
