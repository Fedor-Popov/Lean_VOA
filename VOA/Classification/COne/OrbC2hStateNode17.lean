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
def node17_sector0 : RawPoly ℕ := [(-1140, [0, 1, 1, 1, 1, 2]), (-3240, [0, 1, 1, 4]), (120, [0, 1, 2, 3]), (390, [0, 2, 2, 2]), (-6000, [0, 6]), (-560, [1, 1, 1, 1, 1, 1]), (-4960, [1, 1, 1, 3]), (-1080, [1, 1, 2, 2]), (-16560, [1, 5]), (-720, [2, 4]), (640, [3, 3])]

def node17_sector1 : RawPoly ℕ := [(1140, [0, 1, 1, 1, 1, 2]), (3240, [0, 1, 1, 4]), (-120, [0, 1, 2, 3]), (-390, [0, 2, 2, 2]), (6000, [0, 6]), (-560, [1, 1, 1, 1, 1, 1]), (-4960, [1, 1, 1, 3]), (-1080, [1, 1, 2, 2]), (-16560, [1, 5]), (-720, [2, 4]), (640, [3, 3])]

def node17 : SectorVector := [(-1, node17_sector0), (1, node17_sector1)]
theorem node17_check : VectorCertificate (neutralBoundS JR (2) nineData) node17 := by decide +kernel

theorem node17_value : (V2m 4 four_ge_one).smul (ls 4 JR) (2) (evaluate nineData) = evaluate node17 :=
  neutralBound_value JR (2) nineData node17 node17_check

def node18_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (164, [0, 1, 1, 1, 1, 1, 1, 3]), (-123, [0, 1, 1, 1, 1, 1, 2, 2]), (-84, [0, 1, 1, 1, 1, 5]), (-1740, [0, 1, 1, 1, 2, 4]), (1180, [0, 1, 1, 1, 3, 3]), (930, [0, 1, 1, 2, 2, 3]), (-3780, [0, 1, 1, 7]), (2325/4, [0, 1, 2, 2, 2, 2]), (-1590, [0, 1, 2, 6]), (924, [0, 1, 3, 5]), (-1170, [0, 1, 4, 4]), (342, [0, 2, 2, 5]), (-1740, [0, 2, 3, 4]), (-240, [0, 3, 3, 3]), (-8700, [0, 9]), (-76, [1, 1, 1, 1, 1, 1, 1, 2]), (-570, [1, 1, 1, 1, 1, 4]), (1660, [1, 1, 1, 1, 2, 3]), (1150, [1, 1, 1, 2, 2, 2]), (-2600, [1, 1, 1, 6]), (-936, [1, 1, 2, 5]), (-1380, [1, 1, 3, 4]), (-1935, [1, 2, 2, 4])]

def node18_sector0_chunk1 : RawPoly ℕ := [(-1000, [1, 2, 3, 3]), (-24120, [1, 8]), (430, [2, 2, 2, 3]), (-6840, [2, 7]), (-1160, [3, 6]), (900, [4, 5])]

end VOA.Classification.COne.OrbC2h
