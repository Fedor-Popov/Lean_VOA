import VOA.Classification.COne.OrbC2hStateNode1
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node2_sector0 : RawPoly ℕ := [node2_sector0_chunk0, node2_sector0_chunk1, node2_sector0_chunk2].flatten

def node2_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (-6, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (-144, [0, 1, 1, 1, 1, 1, 1, 5]), (21, [0, 1, 1, 1, 1, 1, 2, 4]), (-152, [0, 1, 1, 1, 1, 1, 3, 3]), (330, [0, 1, 1, 1, 1, 2, 2, 3]), (240, [0, 1, 1, 1, 1, 7]), (35, [0, 1, 1, 1, 2, 2, 2, 2]), (980, [0, 1, 1, 1, 2, 6]), (-1104, [0, 1, 1, 1, 3, 5]), (360, [0, 1, 1, 1, 4, 4]), (-396, [0, 1, 1, 2, 2, 5]), (-510, [0, 1, 1, 2, 3, 4]), (-880, [0, 1, 1, 3, 3, 3]), (5280, [0, 1, 1, 9]), (-2325/2, [0, 1, 2, 2, 2, 4]), (-600, [0, 1, 2, 2, 3, 3]), (2790, [0, 1, 2, 8]), (240, [0, 1, 3, 7]), (570, [0, 1, 4, 6]), (-504, [0, 1, 5, 5]), (-10, [0, 2, 2, 2, 2, 3]), (180, [0, 2, 2, 7]), (620, [0, 2, 3, 6])]

def node2_sector1_chunk1 : RawPoly ℕ := [(126, [0, 2, 4, 5]), (48, [0, 3, 3, 5]), (720, [0, 3, 4, 4]), (10800, [0, 11]), (-96, [1, 1, 1, 1, 1, 1, 1, 4]), (-112, [1, 1, 1, 1, 1, 1, 2, 3]), (88, [1, 1, 1, 1, 1, 2, 2, 2]), (-440, [1, 1, 1, 1, 1, 6]), (2400, [1, 1, 1, 1, 2, 5]), (-840, [1, 1, 1, 1, 3, 4]), (3360, [1, 1, 1, 2, 2, 4]), (400, [1, 1, 1, 2, 3, 3]), (-4200, [1, 1, 1, 8]), (-920, [1, 1, 2, 2, 2, 3]), (-2160, [1, 1, 2, 7]), (-2960, [1, 1, 3, 6]), (2304, [1, 1, 4, 5]), (-240, [1, 2, 2, 2, 2, 2]), (-2580, [1, 2, 2, 6]), (-2352, [1, 2, 3, 5]), (3690, [1, 2, 4, 4]), (480, [1, 3, 3, 4]), (-31320, [1, 10]), (-912, [2, 2, 2, 5])]

def node2_sector1_chunk2 : RawPoly ℕ := [(2820, [2, 2, 3, 4]), (1760, [2, 3, 3, 3]), (-9840, [2, 9]), (-2760, [3, 8]), (720, [4, 7]), (240, [5, 6])]

def node2_sector1 : RawPoly ℕ := [node2_sector1_chunk0, node2_sector1_chunk1, node2_sector1_chunk2].flatten

def node2 : SectorVector := [(-1, node2_sector0), (1, node2_sector1)]
theorem node2_check : VectorCertificate (neutralS JR (-3) nineData) node2 := by decide +kernel

theorem node2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3) (evaluate nineData) = evaluate node2 :=
  neutral_value JR (-3) nineData node2 node2_check

end VOA.Classification.COne.OrbC2h
