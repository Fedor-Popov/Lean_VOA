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
def node25_sector0 : RawPoly ℕ := []

def node25_sector1 : RawPoly ℕ := [(288/7, [1, 1, 1, 1, 1, 1, 1, 2]), (-252, [1, 1, 1, 1, 1, 4]), (120, [1, 1, 1, 2, 2, 2]), (-160, [1, 1, 1, 6]), (384, [1, 1, 2, 5]), (-120, [1, 1, 3, 4]), (-750, [1, 2, 2, 4]), (960, [1, 2, 3, 3]), (60, [1, 8]), (-280, [2, 2, 2, 3]), (-960/7, [2, 7]), (160, [3, 6]), (-72, [4, 5])]

def node25_sector2 : RawPoly ℕ := []

def node25 : SectorVector := [(-2, node25_sector0), (0, node25_sector1), (2, node25_sector2)]
theorem node25_check : VectorCertificate (eMemoS (3) nineData) node25 := by decide +kernel

theorem node25_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (3) (evaluate nineData) = evaluate node25 :=
  eMemo_value (3) nineData node25 node25_check

end VOA.Classification.COne.OrbC2h
