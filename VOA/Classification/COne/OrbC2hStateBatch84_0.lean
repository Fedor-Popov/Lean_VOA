import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode82
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node84Piece0Input_sector0 : RawPoly ℕ := [(3360, [])]

def node84Piece0Input : SectorVector := [(-2, node84Piece0Input_sector0)]
def node84Piece0Output_sector0 : RawPoly ℕ := [(-80640, [0, 1, 1, 4]), (-161280, [0, 1, 2, 3]), (-26880, [0, 2, 2, 2]), (-611520, [0, 6]), (13440, [1, 1, 1, 3]), (20160, [1, 1, 2, 2]), (1249920, [1, 5]), (1300320, [2, 4]), (658560, [3, 3])]

def node84Piece0Output : SectorVector := [(-2, node84Piece0Output_sector0)]

def node84Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [])]

def node84Piece0UnitInput_sector0 : RawPoly ℕ := [node84Piece0UnitInput_sector0_chunk0].flatten

def node84Piece0UnitInput : SectorVector := [(-2, node84Piece0UnitInput_sector0)]

def node84Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-24, [0, 1, 1, 4]), (-48, [0, 1, 2, 3]), (-8, [0, 2, 2, 2]), (-182, [0, 6]), (4, [1, 1, 1, 3]), (6, [1, 1, 2, 2]), (372, [1, 5]), (387, [2, 4]), (196, [3, 3])]

def node84Piece0UnitOutput_sector0 : RawPoly ℕ := [node84Piece0UnitOutput_sector0_chunk0].flatten

def node84Piece0UnitOutput : SectorVector := [(-2, node84Piece0UnitOutput_sector0)]

theorem node84Piece0_check : neutralDirectS JR (-3) node84Piece0UnitInput = node84Piece0UnitOutput := by decide +kernel

theorem node84Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece0Input) = evaluate node84Piece0Output :=
  mode_of_scaled _ _ (3360) node84Piece0UnitInput node84Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece0_check)

def node84Piece1Input_sector0 : RawPoly ℕ := [(-2048/2027025, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node84Piece1Input : SectorVector := [(0, node84Piece1Input_sector0)]
def node84Piece1Output_sector0 : RawPoly ℕ := [(-8192/2027025, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (-4096/675675, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (-8192/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (-88064/225225, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-57344/289575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (-131072/675675, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (-131072/75075, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (-131072/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (-131072/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (-65536/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (-262144/19305, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9])]

def node84Piece1Output : SectorVector := [(0, node84Piece1Output_sector0)]

def node84Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node84Piece1UnitInput_sector0 : RawPoly ℕ := [node84Piece1UnitInput_sector0_chunk0].flatten

def node84Piece1UnitInput : SectorVector := [(0, node84Piece1UnitInput_sector0)]

def node84Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (180, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (2880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (2880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (1440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (13440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9])]

def node84Piece1UnitOutput_sector0 : RawPoly ℕ := [node84Piece1UnitOutput_sector0_chunk0].flatten

def node84Piece1UnitOutput : SectorVector := [(0, node84Piece1UnitOutput_sector0)]

theorem node84Piece1_check : neutralDirectS JR (-3) node84Piece1UnitInput = node84Piece1UnitOutput := by decide +kernel

theorem node84Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece1Input) = evaluate node84Piece1Output :=
  mode_of_scaled _ _ (-2048/2027025) node84Piece1UnitInput node84Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece1_check)

def node84Piece2Input_sector0 : RawPoly ℕ := [(512/9009, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node84Piece2Input : SectorVector := [(0, node84Piece2Input_sector0)]
def node84Piece2Output_sector0 : RawPoly ℕ := [(2048/9009, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (1024/3003, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (2048/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (4096/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (12288/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (2048/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (2048/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (22016/1001, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (88064/9009, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (10240/429, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (2048/231, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (4096/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (8192/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (4096/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (2048/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (8192/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (8192/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (4096/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (24576/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (8192/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node84Piece2Output : SectorVector := [(0, node84Piece2Output_sector0)]

def node84Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node84Piece2UnitInput_sector0 : RawPoly ℕ := [node84Piece2UnitInput_sector0_chunk0].flatten

def node84Piece2UnitInput : SectorVector := [(0, node84Piece2UnitInput_sector0)]

def node84Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (420, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (156, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (936, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1872, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (936, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (468, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (1872, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1872, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (936, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (5616, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (6864, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node84Piece2UnitOutput_sector0 : RawPoly ℕ := [node84Piece2UnitOutput_sector0_chunk0].flatten

def node84Piece2UnitOutput : SectorVector := [(0, node84Piece2UnitOutput_sector0)]

theorem node84Piece2_check : neutralDirectS JR (-3) node84Piece2UnitInput = node84Piece2UnitOutput := by decide +kernel

theorem node84Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece2Input) = evaluate node84Piece2Output :=
  mode_of_scaled _ _ (512/9009) node84Piece2UnitInput node84Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece2_check)

def node84Piece3Input_sector0 : RawPoly ℕ := [(54784/51975, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5])]

def node84Piece3Input : SectorVector := [(0, node84Piece3Input_sector0)]
def node84Piece3Output_sector0 : RawPoly ℕ := [(219136/51975, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (109568/17325, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (219136/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (438272/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (438272/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (438272/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (219136/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (219136/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (438272/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (2355712/5775, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (1533952/7425, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (219136/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-876544/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (219136/1575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (438272/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (438272/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (438272/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (438272/225, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (219136/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (438272/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (438272/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (219136/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (438272/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (438272/105, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9])]

def node84Piece3Output : SectorVector := [(0, node84Piece3Output_sector0)]

def node84Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5])]

def node84Piece3UnitInput_sector0 : RawPoly ℕ := [node84Piece3UnitInput_sector0_chunk0].flatten

def node84Piece3UnitInput : SectorVector := [(0, node84Piece3UnitInput_sector0)]

def node84Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (180, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-240, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (132, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (1848, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (6600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (3960, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9])]

def node84Piece3UnitOutput_sector0 : RawPoly ℕ := [node84Piece3UnitOutput_sector0_chunk0].flatten

def node84Piece3UnitOutput : SectorVector := [(0, node84Piece3UnitOutput_sector0)]

theorem node84Piece3_check : neutralDirectS JR (-3) node84Piece3UnitInput = node84Piece3UnitOutput := by decide +kernel

theorem node84Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece3Input) = evaluate node84Piece3Output :=
  mode_of_scaled _ _ (54784/51975) node84Piece3UnitInput node84Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece3_check)

def node84Piece4Input_sector0 : RawPoly ℕ := [(3968/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4])]

def node84Piece4Input : SectorVector := [(0, node84Piece4Input_sector0)]
def node84Piece4Output_sector0_chunk0 : RawPoly ℕ := [(15872/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (7936/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (31744/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (15872/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (3968/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (111104/135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (269824/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (579328/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (31744/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (158720/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (126976/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6])]

def node84Piece4Output_sector0_chunk1 : RawPoly ℕ := [(126976/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (507904/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (31744/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (31744/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (15872/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (126976/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (63488/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (253952/21, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9])]

def node84Piece4Output_sector0 : RawPoly ℕ := [node84Piece4Output_sector0_chunk0, node84Piece4Output_sector0_chunk1].flatten

def node84Piece4Output : SectorVector := [(0, node84Piece4Output_sector0)]

def node84Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4])]

def node84Piece4UnitInput_sector0 : RawPoly ℕ := [node84Piece4UnitInput_sector0_chunk0].flatten

def node84Piece4UnitInput : SectorVector := [(0, node84Piece4UnitInput_sector0)]

def node84Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (252, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (204, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (438, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1800, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6])]

def node84Piece4UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (1920, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (540, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (4320, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (2160, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (2880, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9])]

def node84Piece4UnitOutput_sector0 : RawPoly ℕ := [node84Piece4UnitOutput_sector0_chunk0, node84Piece4UnitOutput_sector0_chunk1].flatten

def node84Piece4UnitOutput : SectorVector := [(0, node84Piece4UnitOutput_sector0)]

theorem node84Piece4_check : neutralDirectS JR (-3) node84Piece4UnitInput = node84Piece4UnitOutput := by decide +kernel

theorem node84Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece4Input) = evaluate node84Piece4Output :=
  mode_of_scaled _ _ (3968/945) node84Piece4UnitInput node84Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece4_check)

def node84Piece5Input_sector0 : RawPoly ℕ := [(512/405, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3])]

def node84Piece5Input : SectorVector := [(0, node84Piece5Input_sector0)]
def node84Piece5Output_sector0_chunk0 : RawPoly ℕ := [(2048/405, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (1024/135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (4096/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (8192/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (14336/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (4096/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (4096/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (4096/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (22016/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (4096/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (75776/405, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (106496/135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (4096/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (4096/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (2048/15, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (4096/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (16384/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (20480/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (16384/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (8192/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (8192/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (4096/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (4096/3, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (2048/3, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4])]

def node84Piece5Output_sector0_chunk1 : RawPoly ℕ := [(8192, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (32768/9, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9])]

def node84Piece5Output_sector0 : RawPoly ℕ := [node84Piece5Output_sector0_chunk0, node84Piece5Output_sector0_chunk1].flatten

def node84Piece5Output : SectorVector := [(0, node84Piece5Output_sector0)]

def node84Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3])]

def node84Piece5UnitInput_sector0 : RawPoly ℕ := [node84Piece5UnitInput_sector0_chunk0].flatten

def node84Piece5UnitInput : SectorVector := [(0, node84Piece5UnitInput_sector0)]

def node84Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (252, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (148, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (624, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (1440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1800, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (2160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (540, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4])]

def node84Piece5UnitOutput_sector0_chunk1 : RawPoly ℕ := [(6480, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (2880, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9])]

def node84Piece5UnitOutput_sector0 : RawPoly ℕ := [node84Piece5UnitOutput_sector0_chunk0, node84Piece5UnitOutput_sector0_chunk1].flatten

def node84Piece5UnitOutput : SectorVector := [(0, node84Piece5UnitOutput_sector0)]

theorem node84Piece5_check : neutralDirectS JR (-3) node84Piece5UnitInput = node84Piece5UnitOutput := by decide +kernel

theorem node84Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece5Input) = evaluate node84Piece5Output :=
  mode_of_scaled _ _ (512/405) node84Piece5UnitInput node84Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece5_check)

def node84Piece6Input_sector0 : RawPoly ℕ := [(128/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3])]

def node84Piece6Input : SectorVector := [(0, node84Piece6Input_sector0)]
def node84Piece6Output_sector0_chunk0 : RawPoly ℕ := [(512/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (256/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1024/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (11264/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (14464/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (22016/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (2560/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (33280/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7])]

def node84Piece6Output_sector0_chunk1 : RawPoly ℕ := [(9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (49152/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (4096, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9])]

def node84Piece6Output_sector0 : RawPoly ℕ := [node84Piece6Output_sector0_chunk0, node84Piece6Output_sector0_chunk1].flatten

def node84Piece6Output : SectorVector := [(0, node84Piece6Output_sector0)]

def node84Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3])]

def node84Piece6UnitInput_sector0 : RawPoly ℕ := [node84Piece6UnitInput_sector0_chunk0].flatten

def node84Piece6UnitInput : SectorVector := [(0, node84Piece6UnitInput_sector0)]

def node84Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (264, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (339, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (420, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (780, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (648, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7])]

def node84Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(648, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (324, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (2592, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (2592, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (3456, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (2016, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9])]

def node84Piece6UnitOutput_sector0 : RawPoly ℕ := [node84Piece6UnitOutput_sector0_chunk0, node84Piece6UnitOutput_sector0_chunk1].flatten

def node84Piece6UnitOutput : SectorVector := [(0, node84Piece6UnitOutput_sector0)]

theorem node84Piece6_check : neutralDirectS JR (-3) node84Piece6UnitInput = node84Piece6UnitOutput := by decide +kernel

theorem node84Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece6Input) = evaluate node84Piece6Output :=
  mode_of_scaled _ _ (128/63) node84Piece6UnitInput node84Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece6_check)

def node84Piece7Input_sector0 : RawPoly ℕ := [(128/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 7])]

def node84Piece7Input : SectorVector := [(0, node84Piece7Input_sector0)]
def node84Piece7Output_sector0_chunk0 : RawPoly ℕ := [(512/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (256/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (11264/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (16512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (3584/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-11776, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (41472/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7])]

def node84Piece7Output_sector0_chunk1 : RawPoly ℕ := [(36864/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (36864, [1, 1, 1, 1, 1, 1, 1, 15]), (12288, [1, 1, 1, 1, 1, 1, 7, 9])]

def node84Piece7Output_sector0 : RawPoly ℕ := [node84Piece7Output_sector0_chunk0, node84Piece7Output_sector0_chunk1].flatten

def node84Piece7Output : SectorVector := [(0, node84Piece7Output_sector0)]

def node84Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 7])]

def node84Piece7UnitInput_sector0 : RawPoly ℕ := [node84Piece7UnitInput_sector0_chunk0].flatten

def node84Piece7UnitInput : SectorVector := [(0, node84Piece7UnitInput_sector0)]

def node84Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (264, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-1932, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (1512, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (1512, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (1512, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (1512, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (1512, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (972, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7])]

def node84Piece7UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (864, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (432, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (6048, [1, 1, 1, 1, 1, 1, 1, 15]), (2016, [1, 1, 1, 1, 1, 1, 7, 9])]

def node84Piece7UnitOutput_sector0 : RawPoly ℕ := [node84Piece7UnitOutput_sector0_chunk0, node84Piece7UnitOutput_sector0_chunk1].flatten

def node84Piece7UnitOutput : SectorVector := [(0, node84Piece7UnitOutput_sector0)]

theorem node84Piece7_check : neutralDirectS JR (-3) node84Piece7UnitInput = node84Piece7UnitOutput := by decide +kernel

theorem node84Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece7Input) = evaluate node84Piece7Output :=
  mode_of_scaled _ _ (128/21) node84Piece7UnitInput node84Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece7_check)

def node84Piece8Input_sector0 : RawPoly ℕ := [(32/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2])]

def node84Piece8Input : SectorVector := [(0, node84Piece8Input_sector0)]
def node84Piece8Output_sector0 : RawPoly ℕ := [(128/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (64/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (1024/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (2944/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (3104/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (896/9, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (1792/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (1024/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (8192/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (1024/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (17408/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (16384/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (16384/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (1024/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (1024/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (512/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (8192/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (2048/3, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9])]

def node84Piece8Output : SectorVector := [(0, node84Piece8Output_sector0)]

def node84Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2])]

def node84Piece8UnitInput_sector0 : RawPoly ℕ := [node84Piece8UnitInput_sector0_chunk0].flatten

def node84Piece8UnitInput : SectorVector := [(0, node84Piece8UnitInput_sector0)]

def node84Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (276, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (576, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (291, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (1176, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (576, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (576, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (1632, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (4608, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (336, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (5376, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (1344, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9])]

def node84Piece8UnitOutput_sector0 : RawPoly ℕ := [node84Piece8UnitOutput_sector0_chunk0].flatten

def node84Piece8UnitOutput : SectorVector := [(0, node84Piece8UnitOutput_sector0)]

theorem node84Piece8_check : neutralDirectS JR (-3) node84Piece8UnitInput = node84Piece8UnitOutput := by decide +kernel

theorem node84Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece8Input) = evaluate node84Piece8Output :=
  mode_of_scaled _ _ (32/63) node84Piece8UnitInput node84Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece8_check)

def node84Piece9Input_sector0 : RawPoly ℕ := [(128/9, [1, 1, 1, 1, 1, 1, 1, 1, 2, 6])]

def node84Piece9Input : SectorVector := [(0, node84Piece9Input_sector0)]
def node84Piece9Output_sector0_chunk0 : RawPoly ℕ := [(512/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (256/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1024/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (11776/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (2048/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (15488/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (25088/9, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (1024/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-40192/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (18688/3, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (4096/3, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6])]

def node84Piece9Output_sector0_chunk1 : RawPoly ℕ := [(16384, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (69632/3, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (16384/3, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (16384/3, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (32768, [1, 1, 1, 1, 1, 1, 1, 15]), (28672/3, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (28672/3, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (14336/3, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (57344, [1, 1, 1, 1, 1, 1, 2, 14]), (57344/3, [1, 1, 1, 1, 1, 1, 6, 10]), (57344/3, [1, 1, 1, 1, 1, 2, 6, 9])]

def node84Piece9Output_sector0 : RawPoly ℕ := [node84Piece9Output_sector0_chunk0, node84Piece9Output_sector0_chunk1].flatten

def node84Piece9Output : SectorVector := [(0, node84Piece9Output_sector0)]

def node84Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 6])]

def node84Piece9UnitInput_sector0 : RawPoly ℕ := [node84Piece9UnitInput_sector0_chunk0].flatten

def node84Piece9UnitInput : SectorVector := [(0, node84Piece9UnitInput_sector0)]

def node84Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (276, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (363, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-942, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (438, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6])]

def node84Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1152, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (1152, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (1152, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (1152, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (1632, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (384, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (384, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (2304, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (336, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (4032, [1, 1, 1, 1, 1, 1, 2, 14]), (1344, [1, 1, 1, 1, 1, 1, 6, 10]), (1344, [1, 1, 1, 1, 1, 2, 6, 9])]

def node84Piece9UnitOutput_sector0 : RawPoly ℕ := [node84Piece9UnitOutput_sector0_chunk0, node84Piece9UnitOutput_sector0_chunk1].flatten

def node84Piece9UnitOutput : SectorVector := [(0, node84Piece9UnitOutput_sector0)]

theorem node84Piece9_check : neutralDirectS JR (-3) node84Piece9UnitInput = node84Piece9UnitOutput := by decide +kernel

theorem node84Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece9Input) = evaluate node84Piece9Output :=
  mode_of_scaled _ _ (128/9) node84Piece9UnitInput node84Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece9_check)

def node84Piece10Input_sector0 : RawPoly ℕ := [(512/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 5])]

def node84Piece10Input : SectorVector := [(0, node84Piece10Input_sector0)]
def node84Piece10Output_sector0_chunk0 : RawPoly ℕ := [(2048/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (1024/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (10240/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (20480/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (20480/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (20480/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (20480/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (10240/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (20480/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (22016/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (20480/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (88064/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (10240/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-40960/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (20480/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (10240/3, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (20480/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (16384/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5])]

def node84Piece10Output_sector0_chunk1 : RawPoly ℕ := [(163840/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (163840/21, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (163840/21, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (278528/21, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (81920/21, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (163840/7, [1, 1, 1, 1, 1, 1, 1, 15]), (16384/3, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (16384/3, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (8192/3, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (81920/3, [1, 1, 1, 1, 1, 1, 3, 13]), (16384, [1, 1, 1, 1, 1, 1, 5, 11]), (32768/3, [1, 1, 1, 1, 1, 3, 5, 9])]

def node84Piece10Output_sector0 : RawPoly ℕ := [node84Piece10Output_sector0_chunk0, node84Piece10Output_sector0_chunk1].flatten

def node84Piece10Output : SectorVector := [(0, node84Piece10Output_sector0)]

def node84Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 3, 5])]

def node84Piece10UnitInput_sector0 : RawPoly ℕ := [node84Piece10UnitInput_sector0_chunk0].flatten

def node84Piece10UnitInput : SectorVector := [(0, node84Piece10UnitInput_sector0)]

def node84Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (387, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-240, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (420, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (180, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5])]

def node84Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (960, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (960, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (1632, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (480, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (2880, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (672, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (336, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (3360, [1, 1, 1, 1, 1, 1, 3, 13]), (2016, [1, 1, 1, 1, 1, 1, 5, 11]), (1344, [1, 1, 1, 1, 1, 3, 5, 9])]

def node84Piece10UnitOutput_sector0 : RawPoly ℕ := [node84Piece10UnitOutput_sector0_chunk0, node84Piece10UnitOutput_sector0_chunk1].flatten

def node84Piece10UnitOutput : SectorVector := [(0, node84Piece10UnitOutput_sector0)]

theorem node84Piece10_check : neutralDirectS JR (-3) node84Piece10UnitInput = node84Piece10UnitOutput := by decide +kernel

theorem node84Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece10Input) = evaluate node84Piece10Output :=
  mode_of_scaled _ _ (512/63) node84Piece10UnitInput node84Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece10_check)

def node84Piece11Input_sector0 : RawPoly ℕ := [(48/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 4])]

def node84Piece11Input : SectorVector := [(0, node84Piece11Input_sector0)]
def node84Piece11Output_sector0_chunk0 : RawPoly ℕ := [(192/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (13248/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (13968/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (1344, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (73728/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (73728/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (78336/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (73728/7, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (147456/7, [1, 1, 1, 1, 1, 1, 1, 15]), (4608, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6])]

def node84Piece11Output_sector0_chunk1 : RawPoly ℕ := [(4608, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (2304, [1, 1, 1, 1, 1, 1, 4, 4, 4, 4]), (36864, [1, 1, 1, 1, 1, 1, 4, 12]), (9216, [1, 1, 1, 1, 1, 4, 4, 9])]

def node84Piece11Output_sector0 : RawPoly ℕ := [node84Piece11Output_sector0_chunk0, node84Piece11Output_sector0_chunk1].flatten

def node84Piece11Output : SectorVector := [(0, node84Piece11Output_sector0)]

def node84Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 4, 4])]

def node84Piece11UnitInput_sector0 : RawPoly ℕ := [node84Piece11UnitInput_sector0_chunk0].flatten

def node84Piece11UnitInput : SectorVector := [(0, node84Piece11UnitInput_sector0)]

def node84Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (276, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (291, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (196, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (1632, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (3072, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6])]

def node84Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(672, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (336, [1, 1, 1, 1, 1, 1, 4, 4, 4, 4]), (5376, [1, 1, 1, 1, 1, 1, 4, 12]), (1344, [1, 1, 1, 1, 1, 4, 4, 9])]

def node84Piece11UnitOutput_sector0 : RawPoly ℕ := [node84Piece11UnitOutput_sector0_chunk0, node84Piece11UnitOutput_sector0_chunk1].flatten

def node84Piece11UnitOutput : SectorVector := [(0, node84Piece11UnitOutput_sector0)]

theorem node84Piece11_check : neutralDirectS JR (-3) node84Piece11UnitInput = node84Piece11UnitOutput := by decide +kernel

theorem node84Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece11Input) = evaluate node84Piece11Output :=
  mode_of_scaled _ _ (48/7) node84Piece11UnitInput node84Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece11_check)

def node84Piece12Input_sector0 : RawPoly ℕ := [(192/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 5])]

def node84Piece12Input : SectorVector := [(0, node84Piece12Input_sector0)]
def node84Piece12Output_sector0_chunk0 : RawPoly ℕ := [(768/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (11520/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (23040/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (23040/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (23040/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (43776/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (92160/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (11520/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (23040/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (65088/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (5376, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (11520/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-46080/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (92160/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (92160/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (149760/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (92160/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5])]

def node84Piece12Output_sector0_chunk1 : RawPoly ℕ := [(92160/7, [1, 1, 1, 1, 1, 1, 1, 15]), (2304, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (23040, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (23040, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (23040, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (41472, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (11520, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (18432, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (18432, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (92160, [1, 1, 1, 1, 1, 1, 2, 14]), (18432, [1, 1, 1, 1, 1, 1, 5, 11]), (13824, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (13824, [1, 1, 1, 1, 1, 2, 2, 3, 5, 5]), (6912, [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]), (69120, [1, 1, 1, 1, 1, 2, 2, 13]), (55296, [1, 1, 1, 1, 1, 2, 5, 10]), (23040, [1, 1, 1, 1, 2, 2, 5, 9])]

def node84Piece12Output_sector0 : RawPoly ℕ := [node84Piece12Output_sector0_chunk0, node84Piece12Output_sector0_chunk1].flatten

def node84Piece12Output : SectorVector := [(0, node84Piece12Output_sector0)]

def node84Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 2, 2, 5])]

def node84Piece12UnitInput_sector0 : RawPoly ℕ := [node84Piece12UnitInput_sector0_chunk0].flatten

def node84Piece12UnitInput : SectorVector := [(0, node84Piece12UnitInput_sector0)]

def node84Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (228, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (60, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (339, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (196, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-240, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (480, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (480, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (780, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (480, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5])]

def node84Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [1, 1, 1, 1, 1, 1, 1, 15]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (840, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (840, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (840, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (1512, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (420, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (3360, [1, 1, 1, 1, 1, 1, 2, 14]), (672, [1, 1, 1, 1, 1, 1, 5, 11]), (504, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (504, [1, 1, 1, 1, 1, 2, 2, 3, 5, 5]), (252, [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]), (2520, [1, 1, 1, 1, 1, 2, 2, 13]), (2016, [1, 1, 1, 1, 1, 2, 5, 10]), (840, [1, 1, 1, 1, 2, 2, 5, 9])]

def node84Piece12UnitOutput_sector0 : RawPoly ℕ := [node84Piece12UnitOutput_sector0_chunk0, node84Piece12UnitOutput_sector0_chunk1].flatten

def node84Piece12UnitOutput : SectorVector := [(0, node84Piece12UnitOutput_sector0)]

theorem node84Piece12_check : neutralDirectS JR (-3) node84Piece12UnitInput = node84Piece12UnitOutput := by decide +kernel

theorem node84Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece12Input) = evaluate node84Piece12Output :=
  mode_of_scaled _ _ (192/7) node84Piece12UnitInput node84Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece12_check)

def node84Piece13Input_sector0 : RawPoly ℕ := [(-1088/63, [1, 1, 1, 1, 1, 1, 1, 2, 3, 4])]

def node84Piece13Input : SectorVector := [(0, node84Piece13Input_sector0)]
def node84Piece13Output_sector0_chunk0 : RawPoly ℕ := [(-4352/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-2176/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (-17408/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-4352/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-8704/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-34816/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-8704/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-34816/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-34816/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-4352/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-34816/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (-17408/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-69632/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (-17408/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (-17408/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (-4352/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-34816/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-5440, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-34816/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (-187136/63, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-73984/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (-21760/3, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (-34816/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (-34816/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7])]

def node84Piece13Output_sector0_chunk1 : RawPoly ℕ := [(-69632/21, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (-158848/21, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (-69632/21, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (-34816/21, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (-17408/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (-17408/7, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (-69632/7, [1, 1, 1, 1, 1, 1, 1, 15]), (-4352/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-34816/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (-8704, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (-34816/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (-26112, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (-34816/3, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (-8704, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (-4352, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (-34816, [1, 1, 1, 1, 1, 1, 2, 14]), (-17408/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (-17408/3, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (-69632/3, [1, 1, 1, 1, 1, 1, 3, 13]), (-17408, [1, 1, 1, 1, 1, 1, 4, 12]), (-8704, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (-8704, [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]), (-4352, [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]), (-34816, [1, 1, 1, 1, 1, 2, 3, 12])]

def node84Piece13Output_sector0_chunk2 : RawPoly ℕ := [(-26112, [1, 1, 1, 1, 1, 2, 4, 11]), (-17408, [1, 1, 1, 1, 1, 3, 4, 10]), (-43520/3, [1, 1, 1, 1, 2, 3, 4, 9])]

def node84Piece13Output_sector0 : RawPoly ℕ := [node84Piece13Output_sector0_chunk0, node84Piece13Output_sector0_chunk1, node84Piece13Output_sector0_chunk2].flatten

def node84Piece13Output : SectorVector := [(0, node84Piece13Output_sector0)]

def node84Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 2, 3, 4])]

def node84Piece13UnitInput_sector0 : RawPoly ℕ := [node84Piece13UnitInput_sector0_chunk0].flatten

def node84Piece13UnitInput : SectorVector := [(0, node84Piece13UnitInput_sector0)]

def node84Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (48, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (36, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (315, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (172, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (204, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (420, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (288, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (288, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7])]

def node84Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (438, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 15]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (504, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (1512, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (504, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (252, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (2016, [1, 1, 1, 1, 1, 1, 2, 14]), (336, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (336, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (1344, [1, 1, 1, 1, 1, 1, 3, 13]), (1008, [1, 1, 1, 1, 1, 1, 4, 12]), (504, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (504, [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]), (252, [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]), (2016, [1, 1, 1, 1, 1, 2, 3, 12])]

def node84Piece13UnitOutput_sector0_chunk2 : RawPoly ℕ := [(1512, [1, 1, 1, 1, 1, 2, 4, 11]), (1008, [1, 1, 1, 1, 1, 3, 4, 10]), (840, [1, 1, 1, 1, 2, 3, 4, 9])]

def node84Piece13UnitOutput_sector0 : RawPoly ℕ := [node84Piece13UnitOutput_sector0_chunk0, node84Piece13UnitOutput_sector0_chunk1, node84Piece13UnitOutput_sector0_chunk2].flatten

def node84Piece13UnitOutput : SectorVector := [(0, node84Piece13UnitOutput_sector0)]

theorem node84Piece13_check : neutralDirectS JR (-3) node84Piece13UnitInput = node84Piece13UnitOutput := by decide +kernel

theorem node84Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece13Input) = evaluate node84Piece13Output :=
  mode_of_scaled _ _ (-1088/63) node84Piece13UnitInput node84Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece13_check)

def node84Piece14Input_sector0 : RawPoly ℕ := [(-9472/567, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3])]

def node84Piece14Input : SectorVector := [(0, node84Piece14Input_sector0)]
def node84Piece14Output_sector0_chunk0 : RawPoly ℕ := [(-37888/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (-18944/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (-37888/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-75776/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-303104/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-37888/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-75776/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (-37888/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-407296/63, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-75776/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (-1174528/567, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (-644096/63, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (-75776/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (-75776/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (-37888/7, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (-75776/7, [1, 1, 1, 1, 1, 1, 1, 15]), (-37888/27, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (-75776/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (-75776/3, [1, 1, 1, 1, 1, 1, 3, 3, 3, 7]), (-75776/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (-37888/3, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (-75776, [1, 1, 1, 1, 1, 1, 3, 13]), (-75776/9, [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]), (-75776/9, [1, 1, 1, 1, 1, 3, 3, 3, 3, 5])]

def node84Piece14Output_sector0_chunk1 : RawPoly ℕ := [(-37888/9, [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]), (-75776, [1, 1, 1, 1, 1, 3, 3, 11]), (-378880/27, [1, 1, 1, 1, 3, 3, 3, 9])]

def node84Piece14Output_sector0 : RawPoly ℕ := [node84Piece14Output_sector0_chunk0, node84Piece14Output_sector0_chunk1].flatten

def node84Piece14Output : SectorVector := [(0, node84Piece14Output_sector0)]

def node84Piece14UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3])]

def node84Piece14UnitInput_sector0 : RawPoly ℕ := [node84Piece14UnitInput_sector0_chunk0].flatten

def node84Piece14UnitInput : SectorVector := [(0, node84Piece14UnitInput_sector0)]

def node84Piece14UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (648, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (108, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (387, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (648, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (124, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (612, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (648, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (648, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (324, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (648, [1, 1, 1, 1, 1, 1, 1, 15]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (1512, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (1512, [1, 1, 1, 1, 1, 1, 3, 3, 3, 7]), (1512, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (756, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (4536, [1, 1, 1, 1, 1, 1, 3, 13]), (504, [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]), (504, [1, 1, 1, 1, 1, 3, 3, 3, 3, 5])]

def node84Piece14UnitOutput_sector0_chunk1 : RawPoly ℕ := [(252, [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]), (4536, [1, 1, 1, 1, 1, 3, 3, 11]), (840, [1, 1, 1, 1, 3, 3, 3, 9])]

def node84Piece14UnitOutput_sector0 : RawPoly ℕ := [node84Piece14UnitOutput_sector0_chunk0, node84Piece14UnitOutput_sector0_chunk1].flatten

def node84Piece14UnitOutput : SectorVector := [(0, node84Piece14UnitOutput_sector0)]

theorem node84Piece14_check : neutralDirectS JR (-3) node84Piece14UnitInput = node84Piece14UnitOutput := by decide +kernel

theorem node84Piece14_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece14Input) = evaluate node84Piece14Output :=
  mode_of_scaled _ _ (-9472/567) node84Piece14UnitInput node84Piece14UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece14_check)

def node84Piece15Input_sector0 : RawPoly ℕ := [(64/9, [1, 1, 1, 1, 1, 1, 1, 9])]

def node84Piece15Input : SectorVector := [(0, node84Piece15Input_sector0)]
def node84Piece15Output_sector0_chunk0 : RawPoly ℕ := [(256/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (128/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (2752, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (12544/9, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (256, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (-34816, [1, 1, 1, 1, 1, 1, 1, 15]), (1792/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (10752, [1, 1, 1, 1, 1, 1, 2, 14])]

def node84Piece15Output_sector0_chunk1 : RawPoly ℕ := [(10752, [1, 1, 1, 1, 1, 1, 3, 13]), (10752, [1, 1, 1, 1, 1, 1, 4, 12]), (10752, [1, 1, 1, 1, 1, 1, 5, 11]), (10752, [1, 1, 1, 1, 1, 1, 6, 10]), (10752, [1, 1, 1, 1, 1, 1, 7, 9]), (5376, [1, 1, 1, 1, 1, 1, 8, 8]), (3584, [1, 1, 1, 1, 1, 2, 6, 9]), (3584, [1, 1, 1, 1, 1, 3, 5, 9]), (1792, [1, 1, 1, 1, 1, 4, 4, 9]), (32256, [1, 1, 1, 1, 1, 17]), (17920/3, [1, 1, 1, 1, 9, 9])]

def node84Piece15Output_sector0 : RawPoly ℕ := [node84Piece15Output_sector0_chunk0, node84Piece15Output_sector0_chunk1].flatten

def node84Piece15Output : SectorVector := [(0, node84Piece15Output_sector0)]

def node84Piece15UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 9])]

def node84Piece15UnitInput_sector0 : RawPoly ℕ := [node84Piece15UnitInput_sector0_chunk0].flatten

def node84Piece15UnitInput : SectorVector := [(0, node84Piece15UnitInput_sector0)]

def node84Piece15UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (108, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (216, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (387, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (216, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (196, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (216, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (108, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (108, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (216, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (36, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (-4896, [1, 1, 1, 1, 1, 1, 1, 15]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (1512, [1, 1, 1, 1, 1, 1, 2, 14])]

def node84Piece15UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1512, [1, 1, 1, 1, 1, 1, 3, 13]), (1512, [1, 1, 1, 1, 1, 1, 4, 12]), (1512, [1, 1, 1, 1, 1, 1, 5, 11]), (1512, [1, 1, 1, 1, 1, 1, 6, 10]), (1512, [1, 1, 1, 1, 1, 1, 7, 9]), (756, [1, 1, 1, 1, 1, 1, 8, 8]), (504, [1, 1, 1, 1, 1, 2, 6, 9]), (504, [1, 1, 1, 1, 1, 3, 5, 9]), (252, [1, 1, 1, 1, 1, 4, 4, 9]), (4536, [1, 1, 1, 1, 1, 17]), (840, [1, 1, 1, 1, 9, 9])]

def node84Piece15UnitOutput_sector0 : RawPoly ℕ := [node84Piece15UnitOutput_sector0_chunk0, node84Piece15UnitOutput_sector0_chunk1].flatten

def node84Piece15UnitOutput : SectorVector := [(0, node84Piece15UnitOutput_sector0)]

theorem node84Piece15_check : neutralDirectS JR (-3) node84Piece15UnitInput = node84Piece15UnitOutput := by decide +kernel

theorem node84Piece15_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece15Input) = evaluate node84Piece15Output :=
  mode_of_scaled _ _ (64/9) node84Piece15UnitInput node84Piece15UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece15_check)

end VOA.Classification.COne.OrbC2h
