import VOA.Classification.COne.OrbC2hStateNode2
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node3_sector0 : RawPoly ℕ := []

def node3_sector1_chunk0 : RawPoly ℕ := [(4096/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (1664/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (320/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (2368/105, [1, 1, 1, 1, 1, 1, 1, 5]), (-80/3, [1, 1, 1, 1, 1, 1, 2, 4]), (-320/3, [1, 1, 1, 1, 1, 1, 3, 3]), (208/3, [1, 1, 1, 1, 1, 2, 2, 3]), (-624/7, [1, 1, 1, 1, 1, 7]), (40, [1, 1, 1, 1, 2, 2, 2, 2]), (-512/3, [1, 1, 1, 1, 3, 5]), (-260, [1, 1, 1, 1, 4, 4]), (320, [1, 1, 1, 2, 2, 5]), (-400/3, [1, 1, 1, 2, 3, 4]), (640/27, [1, 1, 1, 3, 3, 3]), (-320/3, [1, 1, 1, 9]), (-360, [1, 1, 2, 2, 2, 4]), (2240/3, [1, 1, 2, 2, 3, 3]), (120, [1, 1, 2, 8]), (1440/7, [1, 1, 3, 7]), (-240, [1, 1, 4, 6]), (384/5, [1, 1, 5, 5]), (-200, [1, 2, 2, 2, 2, 3]), (-1320/7, [1, 2, 2, 7]), (480, [1, 2, 3, 6])]

def node3_sector1_chunk1 : RawPoly ℕ := [(-240, [1, 2, 4, 5]), (1280/3, [1, 3, 3, 5]), (-80, [1, 3, 4, 4]), (480/11, [1, 11]), (-36, [2, 2, 2, 2, 2, 2]), (-240, [2, 2, 2, 6]), (-64, [2, 2, 3, 5]), (-270, [2, 2, 4, 4]), (400/3, [2, 3, 3, 4]), (-96, [2, 10]), (1280/27, [3, 3, 3, 3]), (320/3, [3, 9]), (-60, [4, 8]), (96/7, [5, 7])]

def node3_sector1 : RawPoly ℕ := [node3_sector1_chunk0, node3_sector1_chunk1].flatten

def node3_sector2 : RawPoly ℕ := []

def node3 : SectorVector := [(-2, node3_sector0), (0, node3_sector1), (2, node3_sector2)]
theorem node3_check : VectorCertificate (eS (0) nineData) node3 := by decide +kernel

theorem node3_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (0) (evaluate nineData) = evaluate node3 :=
  e_value (0) nineData node3 node3_check

end VOA.Classification.COne.OrbC2h
