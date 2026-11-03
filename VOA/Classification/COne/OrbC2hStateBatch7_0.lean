import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode3
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node7Piece0Input_sector0 : RawPoly ℕ := [(4096/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node7Piece0Input : SectorVector := [(0, node7Piece0Input_sector0)]
def node7Piece0Output_sector0 : RawPoly ℕ := [(16384/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (16384/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (8192/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (16384/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (155648/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (4096/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (1159168/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (1220608/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (206848/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (65536/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (131072/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (65536/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (32768/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (65536/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (65536/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (65536/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (131072/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11])]

def node7Piece0Output : SectorVector := [(0, node7Piece0Output_sector0)]

def node7Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node7Piece0UnitInput_sector0 : RawPoly ℕ := [node7Piece0UnitInput_sector0_chunk0].flatten

def node7Piece0UnitInput : SectorVector := [(0, node7Piece0UnitInput_sector0)]

def node7Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (114, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (283, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (298, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (303/2, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (264, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (792, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (5280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11])]

def node7Piece0UnitOutput_sector0 : RawPoly ℕ := [node7Piece0UnitOutput_sector0_chunk0].flatten

def node7Piece0UnitOutput : SectorVector := [(0, node7Piece0UnitOutput_sector0)]

theorem node7Piece0_check : VectorCertificate (neutralBoundS JR (-5) node7Piece0UnitInput) node7Piece0UnitOutput := by decide +kernel

theorem node7Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece0Input) = evaluate node7Piece0Output :=
  mode_of_scaled _ _ (4096/10395) node7Piece0UnitInput node7Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece0_check)

def node7Piece1Input_sector0 : RawPoly ℕ := [(1664/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node7Piece1Input : SectorVector := [(0, node7Piece1Input_sector0)]
def node7Piece1Output_sector0_chunk0 : RawPoly ℕ := [(6656/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (6656/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (3328/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (6656/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (6656/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (13312/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (83200/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (13312/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (6656/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (1664/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (6656/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (470912/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (13312/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (435968/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (84032/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-3328/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (6656/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (13312/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (39936/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (6656/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (96512/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (39936/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (39936/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (19968/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6])]

def node7Piece1Output_sector0_chunk1 : RawPoly ℕ := [(53248/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (53248/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (53248/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (26624/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (159744/7, [1, 1, 1, 1, 1, 1, 1, 13]), (53248/3, [1, 1, 1, 1, 1, 1, 3, 11])]

def node7Piece1Output_sector0 : RawPoly ℕ := [node7Piece1Output_sector0_chunk0, node7Piece1Output_sector0_chunk1].flatten

def node7Piece1Output : SectorVector := [(0, node7Piece1Output_sector0)]

def node7Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node7Piece1UnitInput_sector0 : RawPoly ℕ := [node7Piece1UnitInput_sector0_chunk0].flatten

def node7Piece1UnitInput : SectorVector := [(0, node7Piece1UnitInput_sector0)]

def node7Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (150, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (283, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (262, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (303/2, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-42, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (648, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (522, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (648, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (648, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (324, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6])]

def node7Piece1UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (864, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (864, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (432, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (2592, [1, 1, 1, 1, 1, 1, 1, 13]), (2016, [1, 1, 1, 1, 1, 1, 3, 11])]

def node7Piece1UnitOutput_sector0 : RawPoly ℕ := [node7Piece1UnitOutput_sector0_chunk0, node7Piece1UnitOutput_sector0_chunk1].flatten

def node7Piece1UnitOutput : SectorVector := [(0, node7Piece1UnitOutput_sector0)]

theorem node7Piece1_check : VectorCertificate (neutralBoundS JR (-5) node7Piece1UnitInput) node7Piece1UnitOutput := by decide +kernel

theorem node7Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece1Input) = evaluate node7Piece1Output :=
  mode_of_scaled _ _ (1664/189) node7Piece1UnitInput node7Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece1_check)

def node7Piece2Input_sector0 : RawPoly ℕ := [(320/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2])]

def node7Piece2Input : SectorVector := [(0, node7Piece2Input_sector0)]
def node7Piece2Output_sector0_chunk0 : RawPoly ℕ := [(1280/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (1280/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (640/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (5120/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1280/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (17280/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (320/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (75200/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (95360/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (16160/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (5120/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (21760/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (5120/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (10240/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (20480/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (10240/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (25600/3, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (81920/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8])]

def node7Piece2Output_sector0_chunk1 : RawPoly ℕ := [(81920/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (81920/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (81920/7, [1, 1, 1, 1, 1, 1, 1, 13]), (10240, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (10240, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (10240, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (5120, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (40960, [1, 1, 1, 1, 1, 1, 2, 12]), (20480, [1, 1, 1, 1, 1, 2, 2, 11])]

def node7Piece2Output_sector0 : RawPoly ℕ := [node7Piece2Output_sector0_chunk0, node7Piece2Output_sector0_chunk1].flatten

def node7Piece2Output : SectorVector := [(0, node7Piece2Output_sector0)]

def node7Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2])]

def node7Piece2UnitInput_sector0 : RawPoly ℕ := [node7Piece2UnitInput_sector0_chunk0].flatten

def node7Piece2UnitInput : SectorVector := [(0, node7Piece2UnitInput_sector0)]

def node7Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (162, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (235, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (298, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (303/2, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (204, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (192, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (32, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (560, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8])]

def node7Piece2UnitOutput_sector0_chunk1 : RawPoly ℕ := [(768, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 13]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (336, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (2688, [1, 1, 1, 1, 1, 1, 2, 12]), (1344, [1, 1, 1, 1, 1, 2, 2, 11])]

def node7Piece2UnitOutput_sector0 : RawPoly ℕ := [node7Piece2UnitOutput_sector0_chunk0, node7Piece2UnitOutput_sector0_chunk1].flatten

def node7Piece2UnitOutput : SectorVector := [(0, node7Piece2UnitOutput_sector0)]

theorem node7Piece2_check : VectorCertificate (neutralBoundS JR (-5) node7Piece2UnitInput) node7Piece2UnitOutput := by decide +kernel

theorem node7Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece2Input) = evaluate node7Piece2Output :=
  mode_of_scaled _ _ (320/21) node7Piece2UnitInput node7Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece2_check)

def node7Piece3Input_sector0 : RawPoly ℕ := [(2368/105, [1, 1, 1, 1, 1, 1, 1, 5])]

def node7Piece3Input : SectorVector := [(0, node7Piece3Input_sector0)]
def node7Piece3Output_sector0_chunk0 : RawPoly ℕ := [(9472/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (9472/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (4736/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (9472/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (9472/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (137344/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (9472/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (2368/105, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (9472/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (670144/105, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (9472/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (18944/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (80512/15, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (119584/35, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-175232/7, [1, 1, 1, 1, 1, 1, 1, 13]), (9472/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (18944/5, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (18944, [1, 1, 1, 1, 1, 1, 2, 12]), (9472/15, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5])]

def node7Piece3Output_sector0_chunk1 : RawPoly ℕ := [(18944, [1, 1, 1, 1, 1, 1, 3, 11]), (18944, [1, 1, 1, 1, 1, 1, 4, 10]), (194176/15, [1, 1, 1, 1, 1, 1, 5, 9]), (18944, [1, 1, 1, 1, 1, 1, 6, 8]), (9472, [1, 1, 1, 1, 1, 1, 7, 7]), (56832/5, [1, 1, 1, 1, 1, 2, 5, 8]), (56832/5, [1, 1, 1, 1, 1, 3, 5, 7]), (56832/5, [1, 1, 1, 1, 1, 4, 5, 6]), (28416/5, [1, 1, 1, 1, 1, 5, 5, 5]), (56832, [1, 1, 1, 1, 1, 15]), (18944, [1, 1, 1, 1, 5, 11])]

def node7Piece3Output_sector0 : RawPoly ℕ := [node7Piece3Output_sector0_chunk0, node7Piece3Output_sector0_chunk1].flatten

def node7Piece3Output : SectorVector := [(0, node7Piece3Output_sector0)]

def node7Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 5])]

def node7Piece3UnitInput_sector0 : RawPoly ℕ := [node7Piece3UnitInput_sector0_chunk0].flatten

def node7Piece3UnitInput : SectorVector := [(0, node7Piece3UnitInput_sector0)]

def node7Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (174, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (120, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (120, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (283, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (60, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (238, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (303/2, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-1110, [1, 1, 1, 1, 1, 1, 1, 13]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (168, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (840, [1, 1, 1, 1, 1, 1, 2, 12]), (28, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5])]

def node7Piece3UnitOutput_sector0_chunk1 : RawPoly ℕ := [(840, [1, 1, 1, 1, 1, 1, 3, 11]), (840, [1, 1, 1, 1, 1, 1, 4, 10]), (574, [1, 1, 1, 1, 1, 1, 5, 9]), (840, [1, 1, 1, 1, 1, 1, 6, 8]), (420, [1, 1, 1, 1, 1, 1, 7, 7]), (504, [1, 1, 1, 1, 1, 2, 5, 8]), (504, [1, 1, 1, 1, 1, 3, 5, 7]), (504, [1, 1, 1, 1, 1, 4, 5, 6]), (252, [1, 1, 1, 1, 1, 5, 5, 5]), (2520, [1, 1, 1, 1, 1, 15]), (840, [1, 1, 1, 1, 5, 11])]

def node7Piece3UnitOutput_sector0 : RawPoly ℕ := [node7Piece3UnitOutput_sector0_chunk0, node7Piece3UnitOutput_sector0_chunk1].flatten

def node7Piece3UnitOutput : SectorVector := [(0, node7Piece3UnitOutput_sector0)]

theorem node7Piece3_check : VectorCertificate (neutralBoundS JR (-5) node7Piece3UnitInput) node7Piece3UnitOutput := by decide +kernel

theorem node7Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece3Input) = evaluate node7Piece3Output :=
  mode_of_scaled _ _ (2368/105) node7Piece3UnitInput node7Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece3_check)

def node7Piece4Input_sector0 : RawPoly ℕ := [(-80/3, [1, 1, 1, 1, 1, 1, 2, 4])]

def node7Piece4Input : SectorVector := [(0, node7Piece4Input_sector0)]
def node7Piece4Output_sector0_chunk0 : RawPoly ℕ := [(-320/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (-320, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (-160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-1280, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (-640, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (-320, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (-2560, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (-2560, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-4960, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-2560, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-1280, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-1280, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-5120, [1, 1, 1, 1, 1, 1, 1, 13]), (-80/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (-1280, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (-2560, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-20720/3, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-1280, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (-1280, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-23840/3, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-9560/3, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (36160/3, [1, 1, 1, 1, 1, 1, 2, 12]), (-640, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-5120, [1, 1, 1, 1, 1, 1, 3, 11])]

def node7Piece4Output_sector0_chunk1 : RawPoly ℕ := [(-4000, [1, 1, 1, 1, 1, 1, 4, 10]), (-5120, [1, 1, 1, 1, 1, 1, 5, 9]), (-5120, [1, 1, 1, 1, 1, 1, 6, 8]), (-2560, [1, 1, 1, 1, 1, 1, 7, 7]), (-1920, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-3840, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-15360, [1, 1, 1, 1, 1, 2, 2, 11]), (-640, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-15360, [1, 1, 1, 1, 1, 2, 3, 10]), (-15040, [1, 1, 1, 1, 1, 2, 4, 9]), (-15360, [1, 1, 1, 1, 1, 2, 5, 8]), (-15360, [1, 1, 1, 1, 1, 2, 6, 7]), (-7680, [1, 1, 1, 1, 1, 3, 4, 8]), (-7680, [1, 1, 1, 1, 1, 4, 4, 7]), (-7680, [1, 1, 1, 1, 1, 4, 5, 6]), (-30720, [1, 1, 1, 1, 1, 15]), (-9600, [1, 1, 1, 1, 2, 2, 4, 8]), (-9600, [1, 1, 1, 1, 2, 3, 4, 7]), (-9600, [1, 1, 1, 1, 2, 4, 4, 6]), (-4800, [1, 1, 1, 1, 2, 4, 5, 5]), (-38400, [1, 1, 1, 1, 2, 14]), (-19200, [1, 1, 1, 1, 4, 12]), (-12800, [1, 1, 1, 2, 4, 11])]

def node7Piece4Output_sector0 : RawPoly ℕ := [node7Piece4Output_sector0_chunk0, node7Piece4Output_sector0_chunk1].flatten

def node7Piece4Output : SectorVector := [(0, node7Piece4Output_sector0)]

def node7Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 2, 4])]

def node7Piece4UnitInput_sector0 : RawPoly ℕ := [node7Piece4UnitInput_sector0_chunk0].flatten

def node7Piece4UnitInput : SectorVector := [(0, node7Piece4UnitInput_sector0)]

def node7Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (12, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (186, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (192, [1, 1, 1, 1, 1, 1, 1, 13]), (1, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (48, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (96, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (259, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (48, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (298, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (239/2, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-452, [1, 1, 1, 1, 1, 1, 2, 12]), (24, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 1, 3, 11])]

def node7Piece4UnitOutput_sector0_chunk1 : RawPoly ℕ := [(150, [1, 1, 1, 1, 1, 1, 4, 10]), (192, [1, 1, 1, 1, 1, 1, 5, 9]), (192, [1, 1, 1, 1, 1, 1, 6, 8]), (96, [1, 1, 1, 1, 1, 1, 7, 7]), (72, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (144, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (576, [1, 1, 1, 1, 1, 2, 2, 11]), (24, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (576, [1, 1, 1, 1, 1, 2, 3, 10]), (564, [1, 1, 1, 1, 1, 2, 4, 9]), (576, [1, 1, 1, 1, 1, 2, 5, 8]), (576, [1, 1, 1, 1, 1, 2, 6, 7]), (288, [1, 1, 1, 1, 1, 3, 4, 8]), (288, [1, 1, 1, 1, 1, 4, 4, 7]), (288, [1, 1, 1, 1, 1, 4, 5, 6]), (1152, [1, 1, 1, 1, 1, 15]), (360, [1, 1, 1, 1, 2, 2, 4, 8]), (360, [1, 1, 1, 1, 2, 3, 4, 7]), (360, [1, 1, 1, 1, 2, 4, 4, 6]), (180, [1, 1, 1, 1, 2, 4, 5, 5]), (1440, [1, 1, 1, 1, 2, 14]), (720, [1, 1, 1, 1, 4, 12]), (480, [1, 1, 1, 2, 4, 11])]

def node7Piece4UnitOutput_sector0 : RawPoly ℕ := [node7Piece4UnitOutput_sector0_chunk0, node7Piece4UnitOutput_sector0_chunk1].flatten

def node7Piece4UnitOutput : SectorVector := [(0, node7Piece4UnitOutput_sector0)]

theorem node7Piece4_check : VectorCertificate (neutralBoundS JR (-5) node7Piece4UnitInput) node7Piece4UnitOutput := by decide +kernel

theorem node7Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece4Input) = evaluate node7Piece4Output :=
  mode_of_scaled _ _ (-80/3) node7Piece4UnitInput node7Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece4_check)

def node7Piece5Input_sector0 : RawPoly ℕ := [(-320/3, [1, 1, 1, 1, 1, 1, 3, 3])]

def node7Piece5Input : SectorVector := [(0, node7Piece5Input_sector0)]
def node7Piece5Output_sector0_chunk0 : RawPoly ℕ := [(-1280/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (-1280, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-640, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (-7680, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-1280, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (-15360, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-19840, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-15360, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-7680, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-23040, [1, 1, 1, 1, 1, 1, 1, 13]), (-320/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (-7680, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-90560/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-15360, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-23040, [1, 1, 1, 1, 1, 1, 2, 12]), (-72320/3, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-16160, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (32000, [1, 1, 1, 1, 1, 1, 3, 11]), (-23040, [1, 1, 1, 1, 1, 1, 4, 10]), (-23040, [1, 1, 1, 1, 1, 1, 5, 9]), (-23040, [1, 1, 1, 1, 1, 1, 6, 8]), (-11520, [1, 1, 1, 1, 1, 1, 7, 7]), (-7680, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-15360, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4])]

def node7Piece5Output_sector0_chunk1 : RawPoly ℕ := [(-92160, [1, 1, 1, 1, 1, 2, 3, 10]), (-2560, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (-60160, [1, 1, 1, 1, 1, 3, 3, 9]), (-92160, [1, 1, 1, 1, 1, 3, 4, 8]), (-92160, [1, 1, 1, 1, 1, 3, 5, 7]), (-46080, [1, 1, 1, 1, 1, 3, 6, 6]), (-138240, [1, 1, 1, 1, 1, 15]), (-38400, [1, 1, 1, 1, 2, 3, 3, 8]), (-38400, [1, 1, 1, 1, 3, 3, 3, 7]), (-38400, [1, 1, 1, 1, 3, 3, 4, 6]), (-19200, [1, 1, 1, 1, 3, 3, 5, 5]), (-230400, [1, 1, 1, 1, 3, 13]), (-51200, [1, 1, 1, 3, 3, 11])]

def node7Piece5Output_sector0 : RawPoly ℕ := [node7Piece5Output_sector0_chunk0, node7Piece5Output_sector0_chunk1].flatten

def node7Piece5Output : SectorVector := [(0, node7Piece5Output_sector0)]

def node7Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 3, 3])]

def node7Piece5UnitInput_sector0 : RawPoly ℕ := [node7Piece5UnitInput_sector0_chunk0].flatten

def node7Piece5UnitInput : SectorVector := [(0, node7Piece5UnitInput_sector0)]

def node7Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (12, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (144, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (186, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (216, [1, 1, 1, 1, 1, 1, 1, 13]), (1, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (283, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (216, [1, 1, 1, 1, 1, 1, 2, 12]), (226, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (303/2, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-300, [1, 1, 1, 1, 1, 1, 3, 11]), (216, [1, 1, 1, 1, 1, 1, 4, 10]), (216, [1, 1, 1, 1, 1, 1, 5, 9]), (216, [1, 1, 1, 1, 1, 1, 6, 8]), (108, [1, 1, 1, 1, 1, 1, 7, 7]), (72, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (144, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4])]

def node7Piece5UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 2, 3, 10]), (24, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (564, [1, 1, 1, 1, 1, 3, 3, 9]), (864, [1, 1, 1, 1, 1, 3, 4, 8]), (864, [1, 1, 1, 1, 1, 3, 5, 7]), (432, [1, 1, 1, 1, 1, 3, 6, 6]), (1296, [1, 1, 1, 1, 1, 15]), (360, [1, 1, 1, 1, 2, 3, 3, 8]), (360, [1, 1, 1, 1, 3, 3, 3, 7]), (360, [1, 1, 1, 1, 3, 3, 4, 6]), (180, [1, 1, 1, 1, 3, 3, 5, 5]), (2160, [1, 1, 1, 1, 3, 13]), (480, [1, 1, 1, 3, 3, 11])]

def node7Piece5UnitOutput_sector0 : RawPoly ℕ := [node7Piece5UnitOutput_sector0_chunk0, node7Piece5UnitOutput_sector0_chunk1].flatten

def node7Piece5UnitOutput : SectorVector := [(0, node7Piece5UnitOutput_sector0)]

theorem node7Piece5_check : VectorCertificate (neutralBoundS JR (-5) node7Piece5UnitInput) node7Piece5UnitOutput := by decide +kernel

theorem node7Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece5Input) = evaluate node7Piece5Output :=
  mode_of_scaled _ _ (-320/3) node7Piece5UnitInput node7Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece5_check)

def node7Piece6Input_sector0 : RawPoly ℕ := [(208/3, [1, 1, 1, 1, 1, 2, 2, 3])]

def node7Piece6Input : SectorVector := [(0, node7Piece6Input_sector0)]
def node7Piece6Output_sector0_chunk0 : RawPoly ℕ := [(832/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (832, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (416, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (2496, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (3328, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (832, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (4992, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (13728, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (4992, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (2496, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (6656, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (6656, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (19968, [1, 1, 1, 1, 1, 1, 2, 12]), (6656, [1, 1, 1, 1, 1, 1, 3, 11]), (208/3, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (2496, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (48880/3, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (4992, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (54496/3, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (10504, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-2912, [1, 1, 1, 1, 1, 2, 2, 11]), (3328, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (14144, [1, 1, 1, 1, 1, 2, 3, 10]), (19968, [1, 1, 1, 1, 1, 2, 4, 9])]

def node7Piece6Output_sector0_chunk1 : RawPoly ℕ := [(19968, [1, 1, 1, 1, 1, 2, 5, 8]), (19968, [1, 1, 1, 1, 1, 2, 6, 7]), (6656, [1, 1, 1, 1, 1, 3, 3, 9]), (6656, [1, 1, 1, 1, 1, 3, 4, 8]), (6656, [1, 1, 1, 1, 1, 3, 5, 7]), (3328, [1, 1, 1, 1, 1, 3, 6, 6]), (19968, [1, 1, 1, 1, 1, 15]), (4160, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (8320, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (24960, [1, 1, 1, 1, 2, 2, 2, 10]), (4160/3, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (110240/3, [1, 1, 1, 1, 2, 2, 3, 9]), (24960, [1, 1, 1, 1, 2, 2, 4, 8]), (24960, [1, 1, 1, 1, 2, 2, 5, 7]), (12480, [1, 1, 1, 1, 2, 2, 6, 6]), (33280, [1, 1, 1, 1, 2, 3, 3, 8]), (33280, [1, 1, 1, 1, 2, 3, 4, 7]), (33280, [1, 1, 1, 1, 2, 3, 5, 6]), (99840, [1, 1, 1, 1, 2, 14]), (33280, [1, 1, 1, 1, 3, 13]), (16640, [1, 1, 1, 2, 2, 2, 3, 8]), (16640, [1, 1, 1, 2, 2, 3, 3, 7]), (16640, [1, 1, 1, 2, 2, 3, 4, 6]), (8320, [1, 1, 1, 2, 2, 3, 5, 5])]

def node7Piece6Output_sector0_chunk2 : RawPoly ℕ := [(49920, [1, 1, 1, 2, 2, 13]), (66560, [1, 1, 1, 2, 3, 12]), (16640, [1, 1, 2, 2, 3, 11])]

def node7Piece6Output_sector0 : RawPoly ℕ := [node7Piece6Output_sector0_chunk0, node7Piece6Output_sector0_chunk1, node7Piece6Output_sector0_chunk2].flatten

def node7Piece6Output : SectorVector := [(0, node7Piece6Output_sector0)]

def node7Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 2, 2, 3])]

def node7Piece6UnitInput_sector0 : RawPoly ℕ := [node7Piece6UnitInput_sector0_chunk0].flatten

def node7Piece6UnitInput : SectorVector := [(0, node7Piece6UnitInput_sector0)]

def node7Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (12, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (48, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (12, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (198, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (36, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (96, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (96, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (288, [1, 1, 1, 1, 1, 1, 2, 12]), (96, [1, 1, 1, 1, 1, 1, 3, 11]), (1, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (235, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (262, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (303/2, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-42, [1, 1, 1, 1, 1, 2, 2, 11]), (48, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (204, [1, 1, 1, 1, 1, 2, 3, 10]), (288, [1, 1, 1, 1, 1, 2, 4, 9])]

def node7Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [1, 1, 1, 1, 1, 2, 5, 8]), (288, [1, 1, 1, 1, 1, 2, 6, 7]), (96, [1, 1, 1, 1, 1, 3, 3, 9]), (96, [1, 1, 1, 1, 1, 3, 4, 8]), (96, [1, 1, 1, 1, 1, 3, 5, 7]), (48, [1, 1, 1, 1, 1, 3, 6, 6]), (288, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (120, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (360, [1, 1, 1, 1, 2, 2, 2, 10]), (20, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (530, [1, 1, 1, 1, 2, 2, 3, 9]), (360, [1, 1, 1, 1, 2, 2, 4, 8]), (360, [1, 1, 1, 1, 2, 2, 5, 7]), (180, [1, 1, 1, 1, 2, 2, 6, 6]), (480, [1, 1, 1, 1, 2, 3, 3, 8]), (480, [1, 1, 1, 1, 2, 3, 4, 7]), (480, [1, 1, 1, 1, 2, 3, 5, 6]), (1440, [1, 1, 1, 1, 2, 14]), (480, [1, 1, 1, 1, 3, 13]), (240, [1, 1, 1, 2, 2, 2, 3, 8]), (240, [1, 1, 1, 2, 2, 3, 3, 7]), (240, [1, 1, 1, 2, 2, 3, 4, 6]), (120, [1, 1, 1, 2, 2, 3, 5, 5])]

def node7Piece6UnitOutput_sector0_chunk2 : RawPoly ℕ := [(720, [1, 1, 1, 2, 2, 13]), (960, [1, 1, 1, 2, 3, 12]), (240, [1, 1, 2, 2, 3, 11])]

def node7Piece6UnitOutput_sector0 : RawPoly ℕ := [node7Piece6UnitOutput_sector0_chunk0, node7Piece6UnitOutput_sector0_chunk1, node7Piece6UnitOutput_sector0_chunk2].flatten

def node7Piece6UnitOutput : SectorVector := [(0, node7Piece6UnitOutput_sector0)]

theorem node7Piece6_check : VectorCertificate (neutralBoundS JR (-5) node7Piece6UnitInput) node7Piece6UnitOutput := by decide +kernel

theorem node7Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece6Input) = evaluate node7Piece6Output :=
  mode_of_scaled _ _ (208/3) node7Piece6UnitInput node7Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece6_check)

def node7Piece7Input_sector0 : RawPoly ℕ := [(-624/7, [1, 1, 1, 1, 1, 7])]

def node7Piece7Input : SectorVector := [(0, node7Piece7Input_sector0)]
def node7Piece7Output_sector0_chunk0 : RawPoly ℕ := [(-2496/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (-7488/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-3744/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-7488, [1, 1, 1, 1, 1, 1, 1, 13]), (-7488/7, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-14976, [1, 1, 1, 1, 1, 1, 2, 12]), (-14976, [1, 1, 1, 1, 1, 1, 3, 11]), (-14976, [1, 1, 1, 1, 1, 1, 4, 10]), (-14976, [1, 1, 1, 1, 1, 1, 5, 9]), (-14976, [1, 1, 1, 1, 1, 1, 6, 8]), (-71136/7, [1, 1, 1, 1, 1, 1, 7, 7]), (-624/7, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (-7488, [1, 1, 1, 1, 1, 2, 2, 11]), (-14976, [1, 1, 1, 1, 1, 2, 3, 10]), (-14976, [1, 1, 1, 1, 1, 2, 4, 9]), (-14976, [1, 1, 1, 1, 1, 2, 5, 8]), (-176592/7, [1, 1, 1, 1, 1, 2, 6, 7]), (-7488, [1, 1, 1, 1, 1, 3, 3, 9]), (-14976, [1, 1, 1, 1, 1, 3, 4, 8]), (-185952/7, [1, 1, 1, 1, 1, 3, 5, 7]), (-7488, [1, 1, 1, 1, 1, 3, 6, 6]), (-94536/7, [1, 1, 1, 1, 1, 4, 4, 7]), (-14976, [1, 1, 1, 1, 1, 4, 5, 6]), (-2496, [1, 1, 1, 1, 1, 5, 5, 5])]

def node7Piece7Output_sector0_chunk1 : RawPoly ℕ := [(293280, [1, 1, 1, 1, 1, 15]), (-37440/7, [1, 1, 1, 1, 2, 2, 5, 7]), (-74880/7, [1, 1, 1, 1, 2, 3, 4, 7]), (-74880, [1, 1, 1, 1, 2, 14]), (-12480/7, [1, 1, 1, 1, 3, 3, 3, 7]), (-74880, [1, 1, 1, 1, 3, 13]), (-74880, [1, 1, 1, 1, 4, 12]), (-74880, [1, 1, 1, 1, 5, 11]), (-74880, [1, 1, 1, 1, 6, 10]), (-330720/7, [1, 1, 1, 1, 7, 9]), (-37440, [1, 1, 1, 1, 8, 8]), (-149760/7, [1, 1, 1, 2, 7, 8]), (-149760/7, [1, 1, 1, 3, 7, 7]), (-149760/7, [1, 1, 1, 4, 6, 7]), (-74880/7, [1, 1, 1, 5, 5, 7]), (-149760, [1, 1, 1, 17]), (-149760/7, [1, 1, 7, 11])]

def node7Piece7Output_sector0 : RawPoly ℕ := [node7Piece7Output_sector0_chunk0, node7Piece7Output_sector0_chunk1].flatten

def node7Piece7Output : SectorVector := [(0, node7Piece7Output_sector0)]

def node7Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 7])]

def node7Piece7UnitInput_sector0 : RawPoly ℕ := [node7Piece7UnitInput_sector0_chunk0].flatten

def node7Piece7UnitInput : SectorVector := [(0, node7Piece7UnitInput_sector0)]

def node7Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (12, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (6, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 13]), (12, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (168, [1, 1, 1, 1, 1, 1, 2, 12]), (168, [1, 1, 1, 1, 1, 1, 3, 11]), (168, [1, 1, 1, 1, 1, 1, 4, 10]), (168, [1, 1, 1, 1, 1, 1, 5, 9]), (168, [1, 1, 1, 1, 1, 1, 6, 8]), (114, [1, 1, 1, 1, 1, 1, 7, 7]), (1, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (84, [1, 1, 1, 1, 1, 2, 2, 11]), (168, [1, 1, 1, 1, 1, 2, 3, 10]), (168, [1, 1, 1, 1, 1, 2, 4, 9]), (168, [1, 1, 1, 1, 1, 2, 5, 8]), (283, [1, 1, 1, 1, 1, 2, 6, 7]), (84, [1, 1, 1, 1, 1, 3, 3, 9]), (168, [1, 1, 1, 1, 1, 3, 4, 8]), (298, [1, 1, 1, 1, 1, 3, 5, 7]), (84, [1, 1, 1, 1, 1, 3, 6, 6]), (303/2, [1, 1, 1, 1, 1, 4, 4, 7]), (168, [1, 1, 1, 1, 1, 4, 5, 6]), (28, [1, 1, 1, 1, 1, 5, 5, 5])]

def node7Piece7UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-3290, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 5, 7]), (120, [1, 1, 1, 1, 2, 3, 4, 7]), (840, [1, 1, 1, 1, 2, 14]), (20, [1, 1, 1, 1, 3, 3, 3, 7]), (840, [1, 1, 1, 1, 3, 13]), (840, [1, 1, 1, 1, 4, 12]), (840, [1, 1, 1, 1, 5, 11]), (840, [1, 1, 1, 1, 6, 10]), (530, [1, 1, 1, 1, 7, 9]), (420, [1, 1, 1, 1, 8, 8]), (240, [1, 1, 1, 2, 7, 8]), (240, [1, 1, 1, 3, 7, 7]), (240, [1, 1, 1, 4, 6, 7]), (120, [1, 1, 1, 5, 5, 7]), (1680, [1, 1, 1, 17]), (240, [1, 1, 7, 11])]

def node7Piece7UnitOutput_sector0 : RawPoly ℕ := [node7Piece7UnitOutput_sector0_chunk0, node7Piece7UnitOutput_sector0_chunk1].flatten

def node7Piece7UnitOutput : SectorVector := [(0, node7Piece7UnitOutput_sector0)]

theorem node7Piece7_check : VectorCertificate (neutralBoundS JR (-5) node7Piece7UnitInput) node7Piece7UnitOutput := by decide +kernel

theorem node7Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece7Input) = evaluate node7Piece7Output :=
  mode_of_scaled _ _ (-624/7) node7Piece7UnitInput node7Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece7_check)

def node7Piece8Input_sector0 : RawPoly ℕ := [(40, [1, 1, 1, 1, 2, 2, 2, 2])]

def node7Piece8Input : SectorVector := [(0, node7Piece8Input_sector0)]
def node7Piece8Output_sector0_chunk0 : RawPoly ℕ := [(160, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (480, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (240, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (3840, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (480, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (8400, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (7680, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (7680, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (23040, [1, 1, 1, 1, 1, 2, 2, 11]), (40, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (7480, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (11920, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (6060, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (3840, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (960, [1, 1, 1, 1, 2, 2, 2, 10]), (23040, [1, 1, 1, 1, 2, 2, 3, 9]), (23040, [1, 1, 1, 1, 2, 2, 4, 8]), (23040, [1, 1, 1, 1, 2, 2, 5, 7]), (11520, [1, 1, 1, 1, 2, 2, 6, 6]), (30720, [1, 1, 1, 1, 2, 14]), (1920, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (3840, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (640, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (18880, [1, 1, 1, 2, 2, 2, 2, 9])]

def node7Piece8Output_sector0_chunk1 : RawPoly ℕ := [(30720, [1, 1, 1, 2, 2, 2, 3, 8]), (30720, [1, 1, 1, 2, 2, 2, 4, 7]), (30720, [1, 1, 1, 2, 2, 2, 5, 6]), (92160, [1, 1, 1, 2, 2, 13]), (5760, [1, 1, 2, 2, 2, 2, 2, 8]), (5760, [1, 1, 2, 2, 2, 2, 3, 7]), (5760, [1, 1, 2, 2, 2, 2, 4, 6]), (2880, [1, 1, 2, 2, 2, 2, 5, 5]), (46080, [1, 1, 2, 2, 2, 12]), (3840, [1, 2, 2, 2, 2, 11])]

def node7Piece8Output_sector0 : RawPoly ℕ := [node7Piece8Output_sector0_chunk0, node7Piece8Output_sector0_chunk1].flatten

def node7Piece8Output : SectorVector := [(0, node7Piece8Output_sector0)]

def node7Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 2, 2])]

def node7Piece8UnitInput_sector0 : RawPoly ℕ := [node7Piece8UnitInput_sector0_chunk0].flatten

def node7Piece8UnitInput : SectorVector := [(0, node7Piece8UnitInput_sector0)]

def node7Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (12, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (6, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (96, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (12, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (210, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (192, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (192, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (576, [1, 1, 1, 1, 1, 2, 2, 11]), (1, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (187, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (298, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (303/2, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (24, [1, 1, 1, 1, 2, 2, 2, 10]), (576, [1, 1, 1, 1, 2, 2, 3, 9]), (576, [1, 1, 1, 1, 2, 2, 4, 8]), (576, [1, 1, 1, 1, 2, 2, 5, 7]), (288, [1, 1, 1, 1, 2, 2, 6, 6]), (768, [1, 1, 1, 1, 2, 14]), (48, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (96, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (16, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (472, [1, 1, 1, 2, 2, 2, 2, 9])]

def node7Piece8UnitOutput_sector0_chunk1 : RawPoly ℕ := [(768, [1, 1, 1, 2, 2, 2, 3, 8]), (768, [1, 1, 1, 2, 2, 2, 4, 7]), (768, [1, 1, 1, 2, 2, 2, 5, 6]), (2304, [1, 1, 1, 2, 2, 13]), (144, [1, 1, 2, 2, 2, 2, 2, 8]), (144, [1, 1, 2, 2, 2, 2, 3, 7]), (144, [1, 1, 2, 2, 2, 2, 4, 6]), (72, [1, 1, 2, 2, 2, 2, 5, 5]), (1152, [1, 1, 2, 2, 2, 12]), (96, [1, 2, 2, 2, 2, 11])]

def node7Piece8UnitOutput_sector0 : RawPoly ℕ := [node7Piece8UnitOutput_sector0_chunk0, node7Piece8UnitOutput_sector0_chunk1].flatten

def node7Piece8UnitOutput : SectorVector := [(0, node7Piece8UnitOutput_sector0)]

theorem node7Piece8_check : VectorCertificate (neutralBoundS JR (-5) node7Piece8UnitInput) node7Piece8UnitOutput := by decide +kernel

theorem node7Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece8Input) = evaluate node7Piece8Output :=
  mode_of_scaled _ _ (40) node7Piece8UnitInput node7Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece8_check)

def node7Piece9Input_sector0 : RawPoly ℕ := [(-512/3, [1, 1, 1, 1, 3, 5])]

def node7Piece9Input : SectorVector := [(0, node7Piece9Input_sector0)]
def node7Piece9Output_sector0_chunk0 : RawPoly ℕ := [(-2048/3, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-2048, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-1024, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-10240, [1, 1, 1, 1, 1, 1, 3, 11]), (-6144, [1, 1, 1, 1, 1, 1, 5, 9]), (-2048, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-20480, [1, 1, 1, 1, 1, 2, 3, 10]), (-12288, [1, 1, 1, 1, 1, 2, 5, 8]), (-20480, [1, 1, 1, 1, 1, 3, 3, 9]), (-20480, [1, 1, 1, 1, 1, 3, 4, 8]), (-35840, [1, 1, 1, 1, 1, 3, 5, 7]), (-10240, [1, 1, 1, 1, 1, 3, 6, 6]), (-12288, [1, 1, 1, 1, 1, 4, 5, 6]), (-6144, [1, 1, 1, 1, 1, 5, 5, 5]), (-61440, [1, 1, 1, 1, 1, 15]), (-512/3, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-10240, [1, 1, 1, 1, 2, 2, 3, 9]), (-6144, [1, 1, 1, 1, 2, 2, 5, 7]), (-20480, [1, 1, 1, 1, 2, 3, 3, 8]), (-20480, [1, 1, 1, 1, 2, 3, 4, 7]), (-144896/3, [1, 1, 1, 1, 2, 3, 5, 6]), (-12288, [1, 1, 1, 1, 2, 4, 5, 5]), (-61440, [1, 1, 1, 1, 2, 14]), (-10240, [1, 1, 1, 1, 3, 3, 3, 7])]

def node7Piece9Output_sector0_chunk1 : RawPoly ℕ := [(-20480, [1, 1, 1, 1, 3, 3, 4, 6]), (-103424/3, [1, 1, 1, 1, 3, 3, 5, 5]), (-25856, [1, 1, 1, 1, 3, 4, 4, 5]), (189440, [1, 1, 1, 1, 3, 13]), (-61440, [1, 1, 1, 1, 4, 12]), (7168, [1, 1, 1, 1, 5, 11]), (-61440, [1, 1, 1, 1, 6, 10]), (-61440, [1, 1, 1, 1, 7, 9]), (-30720, [1, 1, 1, 1, 8, 8]), (-8192, [1, 1, 1, 2, 2, 3, 5, 5]), (-16384, [1, 1, 1, 2, 3, 3, 4, 5]), (-81920, [1, 1, 1, 2, 3, 12]), (-49152, [1, 1, 1, 2, 5, 10]), (-8192/3, [1, 1, 1, 3, 3, 3, 3, 5]), (-81920, [1, 1, 1, 3, 3, 11]), (-81920, [1, 1, 1, 3, 4, 10]), (-241664/3, [1, 1, 1, 3, 5, 9]), (-81920, [1, 1, 1, 3, 6, 8]), (-40960, [1, 1, 1, 3, 7, 7]), (-49152, [1, 1, 1, 4, 5, 8]), (-49152, [1, 1, 1, 5, 5, 7]), (-24576, [1, 1, 1, 5, 6, 6]), (-245760, [1, 1, 1, 17]), (-24576, [1, 1, 2, 3, 5, 8])]

def node7Piece9Output_sector0_chunk2 : RawPoly ℕ := [(-24576, [1, 1, 3, 3, 5, 7]), (-24576, [1, 1, 3, 4, 5, 6]), (-12288, [1, 1, 3, 5, 5, 5]), (-122880, [1, 1, 3, 15]), (-73728, [1, 1, 5, 13]), (-16384, [1, 3, 5, 11])]

def node7Piece9Output_sector0 : RawPoly ℕ := [node7Piece9Output_sector0_chunk0, node7Piece9Output_sector0_chunk1, node7Piece9Output_sector0_chunk2].flatten

def node7Piece9Output : SectorVector := [(0, node7Piece9Output_sector0)]

def node7Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 3, 5])]

def node7Piece9UnitInput_sector0 : RawPoly ℕ := [node7Piece9UnitInput_sector0_chunk0].flatten

def node7Piece9UnitInput : SectorVector := [(0, node7Piece9UnitInput_sector0)]

def node7Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (12, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (6, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 3, 11]), (36, [1, 1, 1, 1, 1, 1, 5, 9]), (12, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (120, [1, 1, 1, 1, 1, 2, 3, 10]), (72, [1, 1, 1, 1, 1, 2, 5, 8]), (120, [1, 1, 1, 1, 1, 3, 3, 9]), (120, [1, 1, 1, 1, 1, 3, 4, 8]), (210, [1, 1, 1, 1, 1, 3, 5, 7]), (60, [1, 1, 1, 1, 1, 3, 6, 6]), (72, [1, 1, 1, 1, 1, 4, 5, 6]), (36, [1, 1, 1, 1, 1, 5, 5, 5]), (360, [1, 1, 1, 1, 1, 15]), (1, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (60, [1, 1, 1, 1, 2, 2, 3, 9]), (36, [1, 1, 1, 1, 2, 2, 5, 7]), (120, [1, 1, 1, 1, 2, 3, 3, 8]), (120, [1, 1, 1, 1, 2, 3, 4, 7]), (283, [1, 1, 1, 1, 2, 3, 5, 6]), (72, [1, 1, 1, 1, 2, 4, 5, 5]), (360, [1, 1, 1, 1, 2, 14]), (60, [1, 1, 1, 1, 3, 3, 3, 7])]

def node7Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 1, 1, 1, 3, 3, 4, 6]), (202, [1, 1, 1, 1, 3, 3, 5, 5]), (303/2, [1, 1, 1, 1, 3, 4, 4, 5]), (-1110, [1, 1, 1, 1, 3, 13]), (360, [1, 1, 1, 1, 4, 12]), (-42, [1, 1, 1, 1, 5, 11]), (360, [1, 1, 1, 1, 6, 10]), (360, [1, 1, 1, 1, 7, 9]), (180, [1, 1, 1, 1, 8, 8]), (48, [1, 1, 1, 2, 2, 3, 5, 5]), (96, [1, 1, 1, 2, 3, 3, 4, 5]), (480, [1, 1, 1, 2, 3, 12]), (288, [1, 1, 1, 2, 5, 10]), (16, [1, 1, 1, 3, 3, 3, 3, 5]), (480, [1, 1, 1, 3, 3, 11]), (480, [1, 1, 1, 3, 4, 10]), (472, [1, 1, 1, 3, 5, 9]), (480, [1, 1, 1, 3, 6, 8]), (240, [1, 1, 1, 3, 7, 7]), (288, [1, 1, 1, 4, 5, 8]), (288, [1, 1, 1, 5, 5, 7]), (144, [1, 1, 1, 5, 6, 6]), (1440, [1, 1, 1, 17]), (144, [1, 1, 2, 3, 5, 8])]

def node7Piece9UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [1, 1, 3, 3, 5, 7]), (144, [1, 1, 3, 4, 5, 6]), (72, [1, 1, 3, 5, 5, 5]), (720, [1, 1, 3, 15]), (432, [1, 1, 5, 13]), (96, [1, 3, 5, 11])]

def node7Piece9UnitOutput_sector0 : RawPoly ℕ := [node7Piece9UnitOutput_sector0_chunk0, node7Piece9UnitOutput_sector0_chunk1, node7Piece9UnitOutput_sector0_chunk2].flatten

def node7Piece9UnitOutput : SectorVector := [(0, node7Piece9UnitOutput_sector0)]

theorem node7Piece9_check : VectorCertificate (neutralBoundS JR (-5) node7Piece9UnitInput) node7Piece9UnitOutput := by decide +kernel

theorem node7Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece9Input) = evaluate node7Piece9Output :=
  mode_of_scaled _ _ (-512/3) node7Piece9UnitInput node7Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece9_check)

def node7Piece10Input_sector0 : RawPoly ℕ := [(-260, [1, 1, 1, 1, 4, 4])]

def node7Piece10Input : SectorVector := [(0, node7Piece10Input_sector0)]
def node7Piece10Output_sector0_chunk0 : RawPoly ℕ := [(-1040, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-3120, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-1560, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-24960, [1, 1, 1, 1, 1, 1, 4, 10]), (-3120, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-49920, [1, 1, 1, 1, 1, 2, 4, 9]), (-49920, [1, 1, 1, 1, 1, 3, 4, 8]), (-54600, [1, 1, 1, 1, 1, 4, 4, 7]), (-49920, [1, 1, 1, 1, 1, 4, 5, 6]), (-99840, [1, 1, 1, 1, 1, 15]), (-260, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (-24960, [1, 1, 1, 1, 2, 2, 4, 8]), (-49920, [1, 1, 1, 1, 2, 3, 4, 7]), (-73580, [1, 1, 1, 1, 2, 4, 4, 6]), (-24960, [1, 1, 1, 1, 2, 4, 5, 5]), (-99840, [1, 1, 1, 1, 2, 14]), (-24960, [1, 1, 1, 1, 3, 3, 4, 6]), (-77480, [1, 1, 1, 1, 3, 4, 4, 5]), (-99840, [1, 1, 1, 1, 3, 13]), (-22750, [1, 1, 1, 1, 4, 4, 4, 4]), (334880, [1, 1, 1, 1, 4, 12]), (-99840, [1, 1, 1, 1, 5, 11]), (-99840, [1, 1, 1, 1, 6, 10]), (-99840, [1, 1, 1, 1, 7, 9])]

def node7Piece10Output_sector0_chunk1 : RawPoly ℕ := [(-49920, [1, 1, 1, 1, 8, 8]), (-12480, [1, 1, 1, 2, 2, 4, 4, 5]), (-24960, [1, 1, 1, 2, 3, 4, 4, 4]), (-199680, [1, 1, 1, 2, 4, 11]), (-4160, [1, 1, 1, 3, 3, 3, 4, 4]), (-199680, [1, 1, 1, 3, 4, 10]), (-122720, [1, 1, 1, 4, 4, 9]), (-199680, [1, 1, 1, 4, 5, 8]), (-199680, [1, 1, 1, 4, 6, 7]), (-399360, [1, 1, 1, 17]), (-37440, [1, 1, 2, 4, 4, 8]), (-37440, [1, 1, 3, 4, 4, 7]), (-37440, [1, 1, 4, 4, 4, 6]), (-18720, [1, 1, 4, 4, 5, 5]), (-299520, [1, 1, 4, 14]), (-24960, [1, 4, 4, 11])]

def node7Piece10Output_sector0 : RawPoly ℕ := [node7Piece10Output_sector0_chunk0, node7Piece10Output_sector0_chunk1].flatten

def node7Piece10Output : SectorVector := [(0, node7Piece10Output_sector0)]

def node7Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 4, 4])]

def node7Piece10UnitInput_sector0 : RawPoly ℕ := [node7Piece10UnitInput_sector0_chunk0].flatten

def node7Piece10UnitInput : SectorVector := [(0, node7Piece10UnitInput_sector0)]

def node7Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (12, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (6, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (96, [1, 1, 1, 1, 1, 1, 4, 10]), (12, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 2, 4, 9]), (192, [1, 1, 1, 1, 1, 3, 4, 8]), (210, [1, 1, 1, 1, 1, 4, 4, 7]), (192, [1, 1, 1, 1, 1, 4, 5, 6]), (384, [1, 1, 1, 1, 1, 15]), (1, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 2, 2, 4, 8]), (192, [1, 1, 1, 1, 2, 3, 4, 7]), (283, [1, 1, 1, 1, 2, 4, 4, 6]), (96, [1, 1, 1, 1, 2, 4, 5, 5]), (384, [1, 1, 1, 1, 2, 14]), (96, [1, 1, 1, 1, 3, 3, 4, 6]), (298, [1, 1, 1, 1, 3, 4, 4, 5]), (384, [1, 1, 1, 1, 3, 13]), (175/2, [1, 1, 1, 1, 4, 4, 4, 4]), (-1288, [1, 1, 1, 1, 4, 12]), (384, [1, 1, 1, 1, 5, 11]), (384, [1, 1, 1, 1, 6, 10]), (384, [1, 1, 1, 1, 7, 9])]

def node7Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [1, 1, 1, 1, 8, 8]), (48, [1, 1, 1, 2, 2, 4, 4, 5]), (96, [1, 1, 1, 2, 3, 4, 4, 4]), (768, [1, 1, 1, 2, 4, 11]), (16, [1, 1, 1, 3, 3, 3, 4, 4]), (768, [1, 1, 1, 3, 4, 10]), (472, [1, 1, 1, 4, 4, 9]), (768, [1, 1, 1, 4, 5, 8]), (768, [1, 1, 1, 4, 6, 7]), (1536, [1, 1, 1, 17]), (144, [1, 1, 2, 4, 4, 8]), (144, [1, 1, 3, 4, 4, 7]), (144, [1, 1, 4, 4, 4, 6]), (72, [1, 1, 4, 4, 5, 5]), (1152, [1, 1, 4, 14]), (96, [1, 4, 4, 11])]

def node7Piece10UnitOutput_sector0 : RawPoly ℕ := [node7Piece10UnitOutput_sector0_chunk0, node7Piece10UnitOutput_sector0_chunk1].flatten

def node7Piece10UnitOutput : SectorVector := [(0, node7Piece10UnitOutput_sector0)]

theorem node7Piece10_check : VectorCertificate (neutralBoundS JR (-5) node7Piece10UnitInput) node7Piece10UnitOutput := by decide +kernel

theorem node7Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece10Input) = evaluate node7Piece10Output :=
  mode_of_scaled _ _ (-260) node7Piece10UnitInput node7Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece10_check)

def node7Piece11Input_sector0 : RawPoly ℕ := [(320, [1, 1, 1, 2, 2, 5])]

def node7Piece11Input : SectorVector := [(0, node7Piece11Input_sector0)]
def node7Piece11Output_sector0_chunk0 : RawPoly ℕ := [(1280, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (3840, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (1920, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (19200, [1, 1, 1, 1, 1, 2, 2, 11]), (15360, [1, 1, 1, 1, 1, 2, 5, 8]), (3840, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (38400, [1, 1, 1, 1, 2, 2, 2, 10]), (38400, [1, 1, 1, 1, 2, 2, 3, 9]), (38400, [1, 1, 1, 1, 2, 2, 4, 8]), (71040, [1, 1, 1, 1, 2, 2, 5, 7]), (19200, [1, 1, 1, 1, 2, 2, 6, 6]), (30720, [1, 1, 1, 1, 2, 3, 5, 6]), (30720, [1, 1, 1, 1, 2, 4, 5, 5]), (153600, [1, 1, 1, 1, 2, 14]), (30720, [1, 1, 1, 1, 5, 11]), (320, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (19200, [1, 1, 1, 2, 2, 2, 2, 9]), (38400, [1, 1, 1, 2, 2, 2, 3, 8]), (38400, [1, 1, 1, 2, 2, 2, 4, 7]), (75200, [1, 1, 1, 2, 2, 2, 5, 6]), (19200, [1, 1, 1, 2, 2, 3, 3, 7]), (38400, [1, 1, 1, 2, 2, 3, 4, 6]), (76160, [1, 1, 1, 2, 2, 3, 5, 5]), (48480, [1, 1, 1, 2, 2, 4, 4, 5])]

def node7Piece11Output_sector0_chunk1 : RawPoly ℕ := [(-355200, [1, 1, 1, 2, 2, 13]), (15360, [1, 1, 1, 2, 3, 3, 4, 5]), (153600, [1, 1, 1, 2, 3, 12]), (153600, [1, 1, 1, 2, 4, 11]), (65280, [1, 1, 1, 2, 5, 10]), (153600, [1, 1, 1, 2, 6, 9]), (153600, [1, 1, 1, 2, 7, 8]), (30720, [1, 1, 1, 3, 5, 9]), (30720, [1, 1, 1, 4, 5, 8]), (30720, [1, 1, 1, 5, 5, 7]), (15360, [1, 1, 1, 5, 6, 6]), (153600, [1, 1, 1, 17]), (11520, [1, 1, 2, 2, 2, 2, 5, 5]), (23040, [1, 1, 2, 2, 2, 3, 4, 5]), (115200, [1, 1, 2, 2, 2, 12]), (3840, [1, 1, 2, 2, 3, 3, 3, 5]), (115200, [1, 1, 2, 2, 3, 11]), (115200, [1, 1, 2, 2, 4, 10]), (124800, [1, 1, 2, 2, 5, 9]), (115200, [1, 1, 2, 2, 6, 8]), (57600, [1, 1, 2, 2, 7, 7]), (92160, [1, 1, 2, 3, 5, 8]), (92160, [1, 1, 2, 4, 5, 7]), (92160, [1, 1, 2, 5, 5, 6])]

def node7Piece11Output_sector0_chunk2 : RawPoly ℕ := [(460800, [1, 1, 2, 16]), (92160, [1, 1, 5, 13]), (23040, [1, 2, 2, 2, 5, 8]), (23040, [1, 2, 2, 3, 5, 7]), (23040, [1, 2, 2, 4, 5, 6]), (11520, [1, 2, 2, 5, 5, 5]), (115200, [1, 2, 2, 15]), (92160, [1, 2, 5, 12]), (7680, [2, 2, 5, 11])]

def node7Piece11Output_sector0 : RawPoly ℕ := [node7Piece11Output_sector0_chunk0, node7Piece11Output_sector0_chunk1, node7Piece11Output_sector0_chunk2].flatten

def node7Piece11Output : SectorVector := [(0, node7Piece11Output_sector0)]

def node7Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 5])]

def node7Piece11UnitInput_sector0 : RawPoly ℕ := [node7Piece11UnitInput_sector0_chunk0].flatten

def node7Piece11UnitInput : SectorVector := [(0, node7Piece11UnitInput_sector0)]

def node7Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (12, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (6, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 2, 2, 11]), (48, [1, 1, 1, 1, 1, 2, 5, 8]), (12, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (120, [1, 1, 1, 1, 2, 2, 2, 10]), (120, [1, 1, 1, 1, 2, 2, 3, 9]), (120, [1, 1, 1, 1, 2, 2, 4, 8]), (222, [1, 1, 1, 1, 2, 2, 5, 7]), (60, [1, 1, 1, 1, 2, 2, 6, 6]), (96, [1, 1, 1, 1, 2, 3, 5, 6]), (96, [1, 1, 1, 1, 2, 4, 5, 5]), (480, [1, 1, 1, 1, 2, 14]), (96, [1, 1, 1, 1, 5, 11]), (1, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (60, [1, 1, 1, 2, 2, 2, 2, 9]), (120, [1, 1, 1, 2, 2, 2, 3, 8]), (120, [1, 1, 1, 2, 2, 2, 4, 7]), (235, [1, 1, 1, 2, 2, 2, 5, 6]), (60, [1, 1, 1, 2, 2, 3, 3, 7]), (120, [1, 1, 1, 2, 2, 3, 4, 6]), (238, [1, 1, 1, 2, 2, 3, 5, 5]), (303/2, [1, 1, 1, 2, 2, 4, 4, 5])]

def node7Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-1110, [1, 1, 1, 2, 2, 13]), (48, [1, 1, 1, 2, 3, 3, 4, 5]), (480, [1, 1, 1, 2, 3, 12]), (480, [1, 1, 1, 2, 4, 11]), (204, [1, 1, 1, 2, 5, 10]), (480, [1, 1, 1, 2, 6, 9]), (480, [1, 1, 1, 2, 7, 8]), (96, [1, 1, 1, 3, 5, 9]), (96, [1, 1, 1, 4, 5, 8]), (96, [1, 1, 1, 5, 5, 7]), (48, [1, 1, 1, 5, 6, 6]), (480, [1, 1, 1, 17]), (36, [1, 1, 2, 2, 2, 2, 5, 5]), (72, [1, 1, 2, 2, 2, 3, 4, 5]), (360, [1, 1, 2, 2, 2, 12]), (12, [1, 1, 2, 2, 3, 3, 3, 5]), (360, [1, 1, 2, 2, 3, 11]), (360, [1, 1, 2, 2, 4, 10]), (390, [1, 1, 2, 2, 5, 9]), (360, [1, 1, 2, 2, 6, 8]), (180, [1, 1, 2, 2, 7, 7]), (288, [1, 1, 2, 3, 5, 8]), (288, [1, 1, 2, 4, 5, 7]), (288, [1, 1, 2, 5, 5, 6])]

def node7Piece11UnitOutput_sector0_chunk2 : RawPoly ℕ := [(1440, [1, 1, 2, 16]), (288, [1, 1, 5, 13]), (72, [1, 2, 2, 2, 5, 8]), (72, [1, 2, 2, 3, 5, 7]), (72, [1, 2, 2, 4, 5, 6]), (36, [1, 2, 2, 5, 5, 5]), (360, [1, 2, 2, 15]), (288, [1, 2, 5, 12]), (24, [2, 2, 5, 11])]

def node7Piece11UnitOutput_sector0 : RawPoly ℕ := [node7Piece11UnitOutput_sector0_chunk0, node7Piece11UnitOutput_sector0_chunk1, node7Piece11UnitOutput_sector0_chunk2].flatten

def node7Piece11UnitOutput : SectorVector := [(0, node7Piece11UnitOutput_sector0)]

theorem node7Piece11_check : VectorCertificate (neutralBoundS JR (-5) node7Piece11UnitInput) node7Piece11UnitOutput := by decide +kernel

theorem node7Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece11Input) = evaluate node7Piece11Output :=
  mode_of_scaled _ _ (320) node7Piece11UnitInput node7Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece11_check)

def node7Piece12Input_sector0 : RawPoly ℕ := [(-400/3, [1, 1, 1, 2, 3, 4])]

def node7Piece12Input : SectorVector := [(0, node7Piece12Input_sector0)]
def node7Piece12Output_sector0_chunk0 : RawPoly ℕ := [(-1600/3, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-1600, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-800, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-6400, [1, 1, 1, 1, 1, 2, 3, 10]), (-4800, [1, 1, 1, 1, 1, 2, 4, 9]), (-3200, [1, 1, 1, 1, 1, 3, 4, 8]), (-1600, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-12800, [1, 1, 1, 1, 2, 2, 3, 9]), (-9600, [1, 1, 1, 1, 2, 2, 4, 8]), (-12800, [1, 1, 1, 1, 2, 3, 3, 8]), (-29600, [1, 1, 1, 1, 2, 3, 4, 7]), (-12800, [1, 1, 1, 1, 2, 3, 5, 6]), (-9600, [1, 1, 1, 1, 2, 4, 4, 6]), (-4800, [1, 1, 1, 1, 2, 4, 5, 5]), (-38400, [1, 1, 1, 1, 2, 14]), (-6400, [1, 1, 1, 1, 3, 3, 4, 6]), (-6400, [1, 1, 1, 1, 3, 4, 4, 5]), (-25600, [1, 1, 1, 1, 3, 13]), (-19200, [1, 1, 1, 1, 4, 12]), (-400/3, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-6400, [1, 1, 1, 2, 2, 2, 3, 8]), (-4800, [1, 1, 1, 2, 2, 2, 4, 7]), (-12800, [1, 1, 1, 2, 2, 3, 3, 7]), (-103600/3, [1, 1, 1, 2, 2, 3, 4, 6])]

def node7Piece12Output_sector0_chunk1 : RawPoly ℕ := [(-6400, [1, 1, 1, 2, 2, 3, 5, 5]), (-9600, [1, 1, 1, 2, 2, 4, 4, 5]), (-38400, [1, 1, 1, 2, 2, 13]), (-6400, [1, 1, 1, 2, 3, 3, 3, 6]), (-104800/3, [1, 1, 1, 2, 3, 3, 4, 5]), (-47800/3, [1, 1, 1, 2, 3, 4, 4, 4]), (180800/3, [1, 1, 1, 2, 3, 12]), (5600, [1, 1, 1, 2, 4, 11]), (-38400, [1, 1, 1, 2, 5, 10]), (-38400, [1, 1, 1, 2, 6, 9]), (-38400, [1, 1, 1, 2, 7, 8]), (-3200, [1, 1, 1, 3, 3, 3, 4, 4]), (-25600, [1, 1, 1, 3, 3, 11]), (-20000, [1, 1, 1, 3, 4, 10]), (-25600, [1, 1, 1, 3, 5, 9]), (-25600, [1, 1, 1, 3, 6, 8]), (-12800, [1, 1, 1, 3, 7, 7]), (-19200, [1, 1, 1, 4, 4, 9]), (-19200, [1, 1, 1, 4, 5, 8]), (-19200, [1, 1, 1, 4, 6, 7]), (-76800, [1, 1, 1, 17]), (-4800, [1, 1, 2, 2, 2, 3, 4, 5]), (-9600, [1, 1, 2, 2, 3, 3, 4, 4]), (-38400, [1, 1, 2, 2, 3, 11])]

def node7Piece12Output_sector0_chunk2 : RawPoly ℕ := [(-28800, [1, 1, 2, 2, 4, 10]), (-1600, [1, 1, 2, 3, 3, 3, 3, 4]), (-38400, [1, 1, 2, 3, 3, 10]), (-52000, [1, 1, 2, 3, 4, 9]), (-38400, [1, 1, 2, 3, 5, 8]), (-38400, [1, 1, 2, 3, 6, 7]), (-28800, [1, 1, 2, 4, 4, 8]), (-28800, [1, 1, 2, 4, 5, 7]), (-14400, [1, 1, 2, 4, 6, 6]), (-115200, [1, 1, 2, 16]), (-19200, [1, 1, 3, 3, 4, 8]), (-19200, [1, 1, 3, 4, 4, 7]), (-19200, [1, 1, 3, 4, 5, 6]), (-76800, [1, 1, 3, 15]), (-57600, [1, 1, 4, 14]), (-9600, [1, 2, 2, 3, 4, 8]), (-9600, [1, 2, 3, 3, 4, 7]), (-9600, [1, 2, 3, 4, 4, 6]), (-4800, [1, 2, 3, 4, 5, 5]), (-38400, [1, 2, 3, 14]), (-28800, [1, 2, 4, 13]), (-19200, [1, 3, 4, 12]), (-3200, [2, 3, 4, 11])]

def node7Piece12Output_sector0 : RawPoly ℕ := [node7Piece12Output_sector0_chunk0, node7Piece12Output_sector0_chunk1, node7Piece12Output_sector0_chunk2].flatten

def node7Piece12Output : SectorVector := [(0, node7Piece12Output_sector0)]

def node7Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 4])]

def node7Piece12UnitInput_sector0 : RawPoly ℕ := [node7Piece12UnitInput_sector0_chunk0].flatten

def node7Piece12UnitInput : SectorVector := [(0, node7Piece12UnitInput_sector0)]

def node7Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (12, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (6, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (48, [1, 1, 1, 1, 1, 2, 3, 10]), (36, [1, 1, 1, 1, 1, 2, 4, 9]), (24, [1, 1, 1, 1, 1, 3, 4, 8]), (12, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (96, [1, 1, 1, 1, 2, 2, 3, 9]), (72, [1, 1, 1, 1, 2, 2, 4, 8]), (96, [1, 1, 1, 1, 2, 3, 3, 8]), (222, [1, 1, 1, 1, 2, 3, 4, 7]), (96, [1, 1, 1, 1, 2, 3, 5, 6]), (72, [1, 1, 1, 1, 2, 4, 4, 6]), (36, [1, 1, 1, 1, 2, 4, 5, 5]), (288, [1, 1, 1, 1, 2, 14]), (48, [1, 1, 1, 1, 3, 3, 4, 6]), (48, [1, 1, 1, 1, 3, 4, 4, 5]), (192, [1, 1, 1, 1, 3, 13]), (144, [1, 1, 1, 1, 4, 12]), (1, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (48, [1, 1, 1, 2, 2, 2, 3, 8]), (36, [1, 1, 1, 2, 2, 2, 4, 7]), (96, [1, 1, 1, 2, 2, 3, 3, 7]), (259, [1, 1, 1, 2, 2, 3, 4, 6])]

def node7Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(48, [1, 1, 1, 2, 2, 3, 5, 5]), (72, [1, 1, 1, 2, 2, 4, 4, 5]), (288, [1, 1, 1, 2, 2, 13]), (48, [1, 1, 1, 2, 3, 3, 3, 6]), (262, [1, 1, 1, 2, 3, 3, 4, 5]), (239/2, [1, 1, 1, 2, 3, 4, 4, 4]), (-452, [1, 1, 1, 2, 3, 12]), (-42, [1, 1, 1, 2, 4, 11]), (288, [1, 1, 1, 2, 5, 10]), (288, [1, 1, 1, 2, 6, 9]), (288, [1, 1, 1, 2, 7, 8]), (24, [1, 1, 1, 3, 3, 3, 4, 4]), (192, [1, 1, 1, 3, 3, 11]), (150, [1, 1, 1, 3, 4, 10]), (192, [1, 1, 1, 3, 5, 9]), (192, [1, 1, 1, 3, 6, 8]), (96, [1, 1, 1, 3, 7, 7]), (144, [1, 1, 1, 4, 4, 9]), (144, [1, 1, 1, 4, 5, 8]), (144, [1, 1, 1, 4, 6, 7]), (576, [1, 1, 1, 17]), (36, [1, 1, 2, 2, 2, 3, 4, 5]), (72, [1, 1, 2, 2, 3, 3, 4, 4]), (288, [1, 1, 2, 2, 3, 11])]

def node7Piece12UnitOutput_sector0_chunk2 : RawPoly ℕ := [(216, [1, 1, 2, 2, 4, 10]), (12, [1, 1, 2, 3, 3, 3, 3, 4]), (288, [1, 1, 2, 3, 3, 10]), (390, [1, 1, 2, 3, 4, 9]), (288, [1, 1, 2, 3, 5, 8]), (288, [1, 1, 2, 3, 6, 7]), (216, [1, 1, 2, 4, 4, 8]), (216, [1, 1, 2, 4, 5, 7]), (108, [1, 1, 2, 4, 6, 6]), (864, [1, 1, 2, 16]), (144, [1, 1, 3, 3, 4, 8]), (144, [1, 1, 3, 4, 4, 7]), (144, [1, 1, 3, 4, 5, 6]), (576, [1, 1, 3, 15]), (432, [1, 1, 4, 14]), (72, [1, 2, 2, 3, 4, 8]), (72, [1, 2, 3, 3, 4, 7]), (72, [1, 2, 3, 4, 4, 6]), (36, [1, 2, 3, 4, 5, 5]), (288, [1, 2, 3, 14]), (216, [1, 2, 4, 13]), (144, [1, 3, 4, 12]), (24, [2, 3, 4, 11])]

def node7Piece12UnitOutput_sector0 : RawPoly ℕ := [node7Piece12UnitOutput_sector0_chunk0, node7Piece12UnitOutput_sector0_chunk1, node7Piece12UnitOutput_sector0_chunk2].flatten

def node7Piece12UnitOutput : SectorVector := [(0, node7Piece12UnitOutput_sector0)]

theorem node7Piece12_check : VectorCertificate (neutralBoundS JR (-5) node7Piece12UnitInput) node7Piece12UnitOutput := by decide +kernel

theorem node7Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece12Input) = evaluate node7Piece12Output :=
  mode_of_scaled _ _ (-400/3) node7Piece12UnitInput node7Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece12_check)

def node7Piece13Input_sector0 : RawPoly ℕ := [(640/27, [1, 1, 1, 3, 3, 3])]

def node7Piece13Input : SectorVector := [(0, node7Piece13Input_sector0)]
def node7Piece13Output_sector0_chunk0 : RawPoly ℕ := [(2560/27, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (2560/9, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (1280/9, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (2560, [1, 1, 1, 1, 1, 3, 3, 9]), (2560/9, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (5120, [1, 1, 1, 1, 2, 3, 3, 8]), (47360/9, [1, 1, 1, 1, 3, 3, 3, 7]), (5120, [1, 1, 1, 1, 3, 3, 4, 6]), (2560, [1, 1, 1, 1, 3, 3, 5, 5]), (15360, [1, 1, 1, 1, 3, 13]), (640/27, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (2560, [1, 1, 1, 2, 2, 3, 3, 7]), (181120/27, [1, 1, 1, 2, 3, 3, 3, 6]), (5120, [1, 1, 1, 2, 3, 3, 4, 5]), (15360, [1, 1, 1, 2, 3, 12]), (121600/27, [1, 1, 1, 3, 3, 3, 3, 5]), (32320/9, [1, 1, 1, 3, 3, 3, 4, 4]), (-55040/3, [1, 1, 1, 3, 3, 11]), (15360, [1, 1, 1, 3, 4, 10]), (15360, [1, 1, 1, 3, 5, 9]), (15360, [1, 1, 1, 3, 6, 8]), (7680, [1, 1, 1, 3, 7, 7]), (15360, [1, 1, 1, 17]), (2560/3, [1, 1, 2, 2, 3, 3, 3, 5])]

def node7Piece13Output_sector0_chunk1 : RawPoly ℕ := [(5120/3, [1, 1, 2, 3, 3, 3, 3, 4]), (15360, [1, 1, 2, 3, 3, 10]), (2560/9, [1, 1, 3, 3, 3, 3, 3, 3]), (83200/9, [1, 1, 3, 3, 3, 9]), (15360, [1, 1, 3, 3, 4, 8]), (15360, [1, 1, 3, 3, 5, 7]), (7680, [1, 1, 3, 3, 6, 6]), (46080, [1, 1, 3, 15]), (5120/3, [1, 2, 3, 3, 3, 8]), (5120/3, [1, 3, 3, 3, 3, 7]), (5120/3, [1, 3, 3, 3, 4, 6]), (2560/3, [1, 3, 3, 3, 5, 5]), (15360, [1, 3, 3, 13]), (5120/9, [3, 3, 3, 11])]

def node7Piece13Output_sector0 : RawPoly ℕ := [node7Piece13Output_sector0_chunk0, node7Piece13Output_sector0_chunk1].flatten

def node7Piece13Output : SectorVector := [(0, node7Piece13Output_sector0)]

def node7Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 3])]

def node7Piece13UnitInput_sector0 : RawPoly ℕ := [node7Piece13UnitInput_sector0_chunk0].flatten

def node7Piece13UnitInput : SectorVector := [(0, node7Piece13UnitInput_sector0)]

def node7Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (12, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (6, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (108, [1, 1, 1, 1, 1, 3, 3, 9]), (12, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (216, [1, 1, 1, 1, 2, 3, 3, 8]), (222, [1, 1, 1, 1, 3, 3, 3, 7]), (216, [1, 1, 1, 1, 3, 3, 4, 6]), (108, [1, 1, 1, 1, 3, 3, 5, 5]), (648, [1, 1, 1, 1, 3, 13]), (1, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (108, [1, 1, 1, 2, 2, 3, 3, 7]), (283, [1, 1, 1, 2, 3, 3, 3, 6]), (216, [1, 1, 1, 2, 3, 3, 4, 5]), (648, [1, 1, 1, 2, 3, 12]), (190, [1, 1, 1, 3, 3, 3, 3, 5]), (303/2, [1, 1, 1, 3, 3, 3, 4, 4]), (-774, [1, 1, 1, 3, 3, 11]), (648, [1, 1, 1, 3, 4, 10]), (648, [1, 1, 1, 3, 5, 9]), (648, [1, 1, 1, 3, 6, 8]), (324, [1, 1, 1, 3, 7, 7]), (648, [1, 1, 1, 17]), (36, [1, 1, 2, 2, 3, 3, 3, 5])]

def node7Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(72, [1, 1, 2, 3, 3, 3, 3, 4]), (648, [1, 1, 2, 3, 3, 10]), (12, [1, 1, 3, 3, 3, 3, 3, 3]), (390, [1, 1, 3, 3, 3, 9]), (648, [1, 1, 3, 3, 4, 8]), (648, [1, 1, 3, 3, 5, 7]), (324, [1, 1, 3, 3, 6, 6]), (1944, [1, 1, 3, 15]), (72, [1, 2, 3, 3, 3, 8]), (72, [1, 3, 3, 3, 3, 7]), (72, [1, 3, 3, 3, 4, 6]), (36, [1, 3, 3, 3, 5, 5]), (648, [1, 3, 3, 13]), (24, [3, 3, 3, 11])]

def node7Piece13UnitOutput_sector0 : RawPoly ℕ := [node7Piece13UnitOutput_sector0_chunk0, node7Piece13UnitOutput_sector0_chunk1].flatten

def node7Piece13UnitOutput : SectorVector := [(0, node7Piece13UnitOutput_sector0)]

theorem node7Piece13_check : VectorCertificate (neutralBoundS JR (-5) node7Piece13UnitInput) node7Piece13UnitOutput := by decide +kernel

theorem node7Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece13Input) = evaluate node7Piece13Output :=
  mode_of_scaled _ _ (640/27) node7Piece13UnitInput node7Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece13_check)

def node7Piece14Input_sector0 : RawPoly ℕ := [(-320/3, [1, 1, 1, 9])]

def node7Piece14Input : SectorVector := [(0, node7Piece14Input_sector0)]
def node7Piece14Output_sector0_chunk0 : RawPoly ℕ := [(-1280/3, [1, 1, 1, 1, 1, 1, 5, 9]), (-1280, [1, 1, 1, 1, 1, 2, 4, 9]), (-640, [1, 1, 1, 1, 1, 3, 3, 9]), (-11520, [1, 1, 1, 1, 1, 15]), (-1280, [1, 1, 1, 1, 2, 2, 3, 9]), (-23040, [1, 1, 1, 1, 2, 14]), (-23040, [1, 1, 1, 1, 3, 13]), (-23040, [1, 1, 1, 1, 4, 12]), (-23040, [1, 1, 1, 1, 5, 11]), (-23040, [1, 1, 1, 1, 6, 10]), (-23680, [1, 1, 1, 1, 7, 9]), (-11520, [1, 1, 1, 1, 8, 8]), (-320/3, [1, 1, 1, 2, 2, 2, 2, 9]), (-11520, [1, 1, 1, 2, 2, 13]), (-23040, [1, 1, 1, 2, 3, 12]), (-23040, [1, 1, 1, 2, 4, 11]), (-23040, [1, 1, 1, 2, 5, 10]), (-90560/3, [1, 1, 1, 2, 6, 9]), (-23040, [1, 1, 1, 2, 7, 8]), (-11520, [1, 1, 1, 3, 3, 11]), (-23040, [1, 1, 1, 3, 4, 10]), (-95360/3, [1, 1, 1, 3, 5, 9]), (-23040, [1, 1, 1, 3, 6, 8]), (-11520, [1, 1, 1, 3, 7, 7])]

def node7Piece14Output_sector0_chunk1 : RawPoly ℕ := [(-16160, [1, 1, 1, 4, 4, 9]), (-23040, [1, 1, 1, 4, 5, 8]), (-23040, [1, 1, 1, 4, 6, 7]), (-11520, [1, 1, 1, 5, 5, 7]), (-11520, [1, 1, 1, 5, 6, 6]), (727680, [1, 1, 1, 17]), (-3840, [1, 1, 2, 2, 5, 9]), (-7680, [1, 1, 2, 3, 4, 9]), (-69120, [1, 1, 2, 16]), (-1280, [1, 1, 3, 3, 3, 9]), (-69120, [1, 1, 3, 15]), (-69120, [1, 1, 4, 14]), (-69120, [1, 1, 5, 13]), (-69120, [1, 1, 6, 12]), (-69120, [1, 1, 7, 11]), (-69120, [1, 1, 8, 10]), (-7040, [1, 1, 9, 9]), (-7680, [1, 2, 8, 9]), (-7680, [1, 3, 7, 9]), (-7680, [1, 4, 6, 9]), (-3840, [1, 5, 5, 9]), (-69120, [1, 19]), (-2560, [9, 11])]

def node7Piece14Output_sector0 : RawPoly ℕ := [node7Piece14Output_sector0_chunk0, node7Piece14Output_sector0_chunk1].flatten

def node7Piece14Output : SectorVector := [(0, node7Piece14Output_sector0)]

def node7Piece14UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 9])]

def node7Piece14UnitInput_sector0 : RawPoly ℕ := [node7Piece14UnitInput_sector0_chunk0].flatten

def node7Piece14UnitInput : SectorVector := [(0, node7Piece14UnitInput_sector0)]

def node7Piece14UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 5, 9]), (12, [1, 1, 1, 1, 1, 2, 4, 9]), (6, [1, 1, 1, 1, 1, 3, 3, 9]), (108, [1, 1, 1, 1, 1, 15]), (12, [1, 1, 1, 1, 2, 2, 3, 9]), (216, [1, 1, 1, 1, 2, 14]), (216, [1, 1, 1, 1, 3, 13]), (216, [1, 1, 1, 1, 4, 12]), (216, [1, 1, 1, 1, 5, 11]), (216, [1, 1, 1, 1, 6, 10]), (222, [1, 1, 1, 1, 7, 9]), (108, [1, 1, 1, 1, 8, 8]), (1, [1, 1, 1, 2, 2, 2, 2, 9]), (108, [1, 1, 1, 2, 2, 13]), (216, [1, 1, 1, 2, 3, 12]), (216, [1, 1, 1, 2, 4, 11]), (216, [1, 1, 1, 2, 5, 10]), (283, [1, 1, 1, 2, 6, 9]), (216, [1, 1, 1, 2, 7, 8]), (108, [1, 1, 1, 3, 3, 11]), (216, [1, 1, 1, 3, 4, 10]), (298, [1, 1, 1, 3, 5, 9]), (216, [1, 1, 1, 3, 6, 8]), (108, [1, 1, 1, 3, 7, 7])]

def node7Piece14UnitOutput_sector0_chunk1 : RawPoly ℕ := [(303/2, [1, 1, 1, 4, 4, 9]), (216, [1, 1, 1, 4, 5, 8]), (216, [1, 1, 1, 4, 6, 7]), (108, [1, 1, 1, 5, 5, 7]), (108, [1, 1, 1, 5, 6, 6]), (-6822, [1, 1, 1, 17]), (36, [1, 1, 2, 2, 5, 9]), (72, [1, 1, 2, 3, 4, 9]), (648, [1, 1, 2, 16]), (12, [1, 1, 3, 3, 3, 9]), (648, [1, 1, 3, 15]), (648, [1, 1, 4, 14]), (648, [1, 1, 5, 13]), (648, [1, 1, 6, 12]), (648, [1, 1, 7, 11]), (648, [1, 1, 8, 10]), (66, [1, 1, 9, 9]), (72, [1, 2, 8, 9]), (72, [1, 3, 7, 9]), (72, [1, 4, 6, 9]), (36, [1, 5, 5, 9]), (648, [1, 19]), (24, [9, 11])]

def node7Piece14UnitOutput_sector0 : RawPoly ℕ := [node7Piece14UnitOutput_sector0_chunk0, node7Piece14UnitOutput_sector0_chunk1].flatten

def node7Piece14UnitOutput : SectorVector := [(0, node7Piece14UnitOutput_sector0)]

theorem node7Piece14_check : VectorCertificate (neutralBoundS JR (-5) node7Piece14UnitInput) node7Piece14UnitOutput := by decide +kernel

theorem node7Piece14_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece14Input) = evaluate node7Piece14Output :=
  mode_of_scaled _ _ (-320/3) node7Piece14UnitInput node7Piece14UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece14_check)

def node7Piece15Input_sector0 : RawPoly ℕ := [(-360, [1, 1, 2, 2, 2, 4])]

def node7Piece15Input : SectorVector := [(0, node7Piece15Input_sector0)]
def node7Piece15Output_sector0_chunk0 : RawPoly ℕ := [(-1440, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-4320, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (-2160, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-17280, [1, 1, 1, 1, 2, 2, 2, 10]), (-25920, [1, 1, 1, 1, 2, 2, 4, 8]), (-4320, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-34560, [1, 1, 1, 2, 2, 2, 2, 9]), (-34560, [1, 1, 1, 2, 2, 2, 3, 8]), (-84240, [1, 1, 1, 2, 2, 2, 4, 7]), (-34560, [1, 1, 1, 2, 2, 2, 5, 6]), (-51840, [1, 1, 1, 2, 2, 3, 4, 6]), (-51840, [1, 1, 1, 2, 2, 4, 4, 5]), (-207360, [1, 1, 1, 2, 2, 13]), (-103680, [1, 1, 1, 2, 4, 11]), (-360, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-17280, [1, 1, 2, 2, 2, 2, 2, 8]), (-34560, [1, 1, 2, 2, 2, 2, 3, 7]), (-75960, [1, 1, 2, 2, 2, 2, 4, 6]), (-17280, [1, 1, 2, 2, 2, 2, 5, 5]), (-17280, [1, 1, 2, 2, 2, 3, 3, 6]), (-107280, [1, 1, 2, 2, 2, 3, 4, 5]), (-43020, [1, 1, 2, 2, 2, 4, 4, 4]), (162720, [1, 1, 2, 2, 2, 12]), (-25920, [1, 1, 2, 2, 3, 3, 4, 4])]

def node7Piece15Output_sector0_chunk1 : RawPoly ℕ := [(-207360, [1, 1, 2, 2, 3, 11]), (-58320, [1, 1, 2, 2, 4, 10]), (-207360, [1, 1, 2, 2, 5, 9]), (-207360, [1, 1, 2, 2, 6, 8]), (-103680, [1, 1, 2, 2, 7, 7]), (-103680, [1, 1, 2, 3, 4, 9]), (-103680, [1, 1, 2, 4, 4, 8]), (-103680, [1, 1, 2, 4, 5, 7]), (-51840, [1, 1, 2, 4, 6, 6]), (-414720, [1, 1, 2, 16]), (-69120, [1, 1, 4, 14]), (-8640, [1, 2, 2, 2, 2, 2, 4, 5]), (-17280, [1, 2, 2, 2, 2, 3, 4, 4]), (-69120, [1, 2, 2, 2, 2, 11]), (-2880, [1, 2, 2, 2, 3, 3, 3, 4]), (-69120, [1, 2, 2, 2, 3, 10]), (-102240, [1, 2, 2, 2, 4, 9]), (-69120, [1, 2, 2, 2, 5, 8]), (-69120, [1, 2, 2, 2, 6, 7]), (-103680, [1, 2, 2, 3, 4, 8]), (-103680, [1, 2, 2, 4, 4, 7]), (-103680, [1, 2, 2, 4, 5, 6]), (-414720, [1, 2, 2, 15]), (-207360, [1, 2, 4, 13])]

def node7Piece15Output_sector0_chunk2 : RawPoly ℕ := [(-8640, [2, 2, 2, 2, 4, 8]), (-8640, [2, 2, 2, 3, 4, 7]), (-8640, [2, 2, 2, 4, 4, 6]), (-4320, [2, 2, 2, 4, 5, 5]), (-34560, [2, 2, 2, 14]), (-51840, [2, 2, 4, 12])]

def node7Piece15Output_sector0 : RawPoly ℕ := [node7Piece15Output_sector0_chunk0, node7Piece15Output_sector0_chunk1, node7Piece15Output_sector0_chunk2].flatten

def node7Piece15Output : SectorVector := [(0, node7Piece15Output_sector0)]

def node7Piece15UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 2, 2, 2, 4])]

def node7Piece15UnitInput_sector0 : RawPoly ℕ := [node7Piece15UnitInput_sector0_chunk0].flatten

def node7Piece15UnitInput : SectorVector := [(0, node7Piece15UnitInput_sector0)]

def node7Piece15UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (12, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (6, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (48, [1, 1, 1, 1, 2, 2, 2, 10]), (72, [1, 1, 1, 1, 2, 2, 4, 8]), (12, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (96, [1, 1, 1, 2, 2, 2, 2, 9]), (96, [1, 1, 1, 2, 2, 2, 3, 8]), (234, [1, 1, 1, 2, 2, 2, 4, 7]), (96, [1, 1, 1, 2, 2, 2, 5, 6]), (144, [1, 1, 1, 2, 2, 3, 4, 6]), (144, [1, 1, 1, 2, 2, 4, 4, 5]), (576, [1, 1, 1, 2, 2, 13]), (288, [1, 1, 1, 2, 4, 11]), (1, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (48, [1, 1, 2, 2, 2, 2, 2, 8]), (96, [1, 1, 2, 2, 2, 2, 3, 7]), (211, [1, 1, 2, 2, 2, 2, 4, 6]), (48, [1, 1, 2, 2, 2, 2, 5, 5]), (48, [1, 1, 2, 2, 2, 3, 3, 6]), (298, [1, 1, 2, 2, 2, 3, 4, 5]), (239/2, [1, 1, 2, 2, 2, 4, 4, 4]), (-452, [1, 1, 2, 2, 2, 12]), (72, [1, 1, 2, 2, 3, 3, 4, 4])]

def node7Piece15UnitOutput_sector0_chunk1 : RawPoly ℕ := [(576, [1, 1, 2, 2, 3, 11]), (162, [1, 1, 2, 2, 4, 10]), (576, [1, 1, 2, 2, 5, 9]), (576, [1, 1, 2, 2, 6, 8]), (288, [1, 1, 2, 2, 7, 7]), (288, [1, 1, 2, 3, 4, 9]), (288, [1, 1, 2, 4, 4, 8]), (288, [1, 1, 2, 4, 5, 7]), (144, [1, 1, 2, 4, 6, 6]), (1152, [1, 1, 2, 16]), (192, [1, 1, 4, 14]), (24, [1, 2, 2, 2, 2, 2, 4, 5]), (48, [1, 2, 2, 2, 2, 3, 4, 4]), (192, [1, 2, 2, 2, 2, 11]), (8, [1, 2, 2, 2, 3, 3, 3, 4]), (192, [1, 2, 2, 2, 3, 10]), (284, [1, 2, 2, 2, 4, 9]), (192, [1, 2, 2, 2, 5, 8]), (192, [1, 2, 2, 2, 6, 7]), (288, [1, 2, 2, 3, 4, 8]), (288, [1, 2, 2, 4, 4, 7]), (288, [1, 2, 2, 4, 5, 6]), (1152, [1, 2, 2, 15]), (576, [1, 2, 4, 13])]

def node7Piece15UnitOutput_sector0_chunk2 : RawPoly ℕ := [(24, [2, 2, 2, 2, 4, 8]), (24, [2, 2, 2, 3, 4, 7]), (24, [2, 2, 2, 4, 4, 6]), (12, [2, 2, 2, 4, 5, 5]), (96, [2, 2, 2, 14]), (144, [2, 2, 4, 12])]

def node7Piece15UnitOutput_sector0 : RawPoly ℕ := [node7Piece15UnitOutput_sector0_chunk0, node7Piece15UnitOutput_sector0_chunk1, node7Piece15UnitOutput_sector0_chunk2].flatten

def node7Piece15UnitOutput : SectorVector := [(0, node7Piece15UnitOutput_sector0)]

theorem node7Piece15_check : VectorCertificate (neutralBoundS JR (-5) node7Piece15UnitInput) node7Piece15UnitOutput := by decide +kernel

theorem node7Piece15_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece15Input) = evaluate node7Piece15Output :=
  mode_of_scaled _ _ (-360) node7Piece15UnitInput node7Piece15UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece15_check)

end VOA.Classification.COne.OrbC2h
