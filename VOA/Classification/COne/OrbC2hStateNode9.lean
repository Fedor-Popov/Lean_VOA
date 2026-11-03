import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node9_sector0 : RawPoly ℕ := [(68, [0, 1, 1, 1, 1, 1, 1, 1]), (580, [0, 1, 1, 1, 1, 3]), (-1230, [0, 1, 1, 1, 2, 2]), (-2232, [0, 1, 1, 5]), (-2160, [0, 1, 2, 4]), (800, [0, 1, 3, 3]), (-690, [0, 2, 2, 3]), (-6840, [0, 7]), (504, [1, 1, 1, 1, 1, 2]), (240, [1, 1, 1, 4]), (-3600, [1, 1, 2, 3]), (-4020, [1, 2, 2, 2]), (-17880, [1, 6]), (-5616, [2, 5]), (2400, [3, 4])]

def node9_sector1 : RawPoly ℕ := [(-68, [0, 1, 1, 1, 1, 1, 1, 1]), (-580, [0, 1, 1, 1, 1, 3]), (1230, [0, 1, 1, 1, 2, 2]), (2232, [0, 1, 1, 5]), (2160, [0, 1, 2, 4]), (-800, [0, 1, 3, 3]), (690, [0, 2, 2, 3]), (6840, [0, 7]), (504, [1, 1, 1, 1, 1, 2]), (240, [1, 1, 1, 4]), (-3600, [1, 1, 2, 3]), (-4020, [1, 2, 2, 2]), (-17880, [1, 6]), (-5616, [2, 5]), (2400, [3, 4])]

def node9 : SectorVector := [(-1, node9_sector0), (1, node9_sector1)]
theorem node9_check : VectorCertificate (neutralBoundS JR (1) nineData) node9 := by decide +kernel

theorem node9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (1) (evaluate nineData) = evaluate node9 :=
  neutralBound_value JR (1) nineData node9 node9_check

def node10_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (20, [0, 1, 1, 1, 1, 1, 2, 3]), (-190, [0, 1, 1, 1, 1, 2, 2, 2]), (-160, [0, 1, 1, 1, 1, 6]), (-1176, [0, 1, 1, 1, 2, 5]), (780, [0, 1, 1, 1, 3, 4]), (45, [0, 1, 1, 2, 2, 4]), (1240, [0, 1, 1, 2, 3, 3]), (-4500, [0, 1, 1, 8]), (1130, [0, 1, 2, 2, 2, 3]), (-2160, [0, 1, 2, 7]), (80, [0, 1, 3, 6]), (-360, [0, 1, 4, 5]), (30, [0, 2, 2, 2, 2, 2]), (-60, [0, 2, 2, 6]), (-240, [0, 2, 3, 5]), (-720, [0, 2, 4, 4]), (-720, [0, 3, 3, 4]), (-9720, [0, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-16, [1, 1, 1, 1, 1, 1, 2, 2]), (-528, [1, 1, 1, 1, 1, 5]), (2640, [1, 1, 1, 1, 2, 4])]

def node10_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3]), (2320, [1, 1, 1, 2, 2, 3]), (-3360, [1, 1, 1, 7]), (-480, [1, 1, 2, 2, 2, 2]), (-1200, [1, 1, 2, 6]), (-4416, [1, 1, 3, 5]), (3060, [1, 1, 4, 4]), (-3816, [1, 2, 2, 5]), (2640, [1, 2, 3, 4]), (-960, [1, 3, 3, 3]), (-27600, [1, 9]), (-600, [2, 2, 2, 4]), (2480, [2, 2, 3, 3]), (-8280, [2, 8]), (-1920, [3, 7]), (1200, [4, 6]), (-288, [5, 5])]

end VOA.Classification.COne.OrbC2h
