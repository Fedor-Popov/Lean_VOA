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
def node11_sector0 : RawPoly ℕ := []

def node11_sector1_chunk0 : RawPoly ℕ := [(2752/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (208/21, [1, 1, 1, 1, 1, 1, 1, 4]), (-704/9, [1, 1, 1, 1, 1, 1, 2, 3]), (88, [1, 1, 1, 1, 1, 2, 2, 2]), (-104, [1, 1, 1, 1, 1, 6]), (128, [1, 1, 1, 1, 2, 5]), (-1600/3, [1, 1, 1, 1, 3, 4]), (-160, [1, 1, 1, 2, 2, 4]), (4000/9, [1, 1, 1, 2, 3, 3]), (-120, [1, 1, 1, 8]), (240, [1, 1, 2, 2, 2, 3]), (960/7, [1, 1, 2, 7]), (240, [1, 1, 3, 6]), (-192, [1, 1, 4, 5]), (-172, [1, 2, 2, 2, 2, 2]), (-220, [1, 2, 2, 6]), (704, [1, 2, 3, 5]), (-420, [1, 2, 4, 4]), (880/3, [1, 3, 3, 4]), (48, [1, 10]), (-272, [2, 2, 2, 5]), (-280, [2, 2, 3, 4]), (4960/27, [2, 3, 3, 3]), (-320/3, [2, 9])]

def node11_sector1_chunk1 : RawPoly ℕ := [(120, [3, 8]), (-480/7, [4, 7]), (16, [5, 6])]

def node11_sector1 : RawPoly ℕ := [node11_sector1_chunk0, node11_sector1_chunk1].flatten

def node11_sector2 : RawPoly ℕ := []

def node11 : SectorVector := [(-2, node11_sector0), (0, node11_sector1), (2, node11_sector2)]
theorem node11_check : VectorCertificate (eMemoS (1) nineData) node11 := by decide +kernel

theorem node11_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (1) (evaluate nineData) = evaluate node11 :=
  eMemo_value (1) nineData node11 node11_check

end VOA.Classification.COne.OrbC2h
