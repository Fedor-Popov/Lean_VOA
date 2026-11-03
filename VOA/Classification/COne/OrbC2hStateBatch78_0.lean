import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode76
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node78Piece0Input_sector0 : RawPoly ℕ := [(-2310, [0, 1])]

def node78Piece0Input : SectorVector := [(-2, node78Piece0Input_sector0)]
def node78Piece0Output_sector0 : RawPoly ℕ := [(-9240, [0, 1, 1, 1, 1, 2]), (-900900, [0, 1, 1, 4]), (-951720, [0, 1, 2, 3]), (-9240, [0, 2, 2, 2]), (-757680, [0, 6]), (443520, [1, 1, 1, 3]), (443520, [1, 1, 2, 2]), (4656960, [1, 5]), (887040, [2, 4]), (443520, [3, 3])]

def node78Piece0Output : SectorVector := [(-2, node78Piece0Output_sector0)]

def node78Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1])]

def node78Piece0UnitInput_sector0 : RawPoly ℕ := [node78Piece0UnitInput_sector0_chunk0].flatten

def node78Piece0UnitInput : SectorVector := [(-2, node78Piece0UnitInput_sector0)]

def node78Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2]), (390, [0, 1, 1, 4]), (412, [0, 1, 2, 3]), (4, [0, 2, 2, 2]), (328, [0, 6]), (-192, [1, 1, 1, 3]), (-192, [1, 1, 2, 2]), (-2016, [1, 5]), (-384, [2, 4]), (-192, [3, 3])]

def node78Piece0UnitOutput_sector0 : RawPoly ℕ := [node78Piece0UnitOutput_sector0_chunk0].flatten

def node78Piece0UnitOutput : SectorVector := [(-2, node78Piece0UnitOutput_sector0)]

theorem node78Piece0_check : VectorCertificate (neutralBoundS JR (-2) node78Piece0UnitInput) node78Piece0UnitOutput := by decide +kernel

theorem node78Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece0Input) = evaluate node78Piece0Output :=
  mode_of_scaled _ _ (-2310) node78Piece0UnitInput node78Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece0_check)

def node78Piece1Input_sector0 : RawPoly ℕ := [(-1024/184275, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2])]

def node78Piece1Input : SectorVector := [(0, node78Piece1Input_sector0)]
def node78Piece1Output_sector0 : RawPoly ℕ := [(-4096/184275, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (-8192/61425, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (-75776/61425, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-8192/61425, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (-397312/184275, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (-180224/61425, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (-4096/12285, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (-32768/2457, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (-16384/4095, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (-8192/4095, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (-8192/585, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (-8192/585, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (-16384/585, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (-8192/135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8])]

def node78Piece1Output : SectorVector := [(0, node78Piece1Output_sector0)]

def node78Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2])]

def node78Piece1UnitInput_sector0 : RawPoly ℕ := [node78Piece1UnitInput_sector0_chunk0].flatten

def node78Piece1UnitInput : SectorVector := [(0, node78Piece1UnitInput_sector0)]

def node78Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (222, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (388, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (528, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (2400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (2520, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (2520, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (5040, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (10920, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8])]

def node78Piece1UnitOutput_sector0 : RawPoly ℕ := [node78Piece1UnitOutput_sector0_chunk0].flatten

def node78Piece1UnitOutput : SectorVector := [(0, node78Piece1UnitOutput_sector0)]

theorem node78Piece1_check : VectorCertificate (neutralBoundS JR (-2) node78Piece1UnitInput) node78Piece1UnitOutput := by decide +kernel

theorem node78Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece1Input) = evaluate node78Piece1Output :=
  mode_of_scaled _ _ (-1024/184275) node78Piece1UnitInput node78Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece1_check)

def node78Piece2Input_sector0 : RawPoly ℕ := [(7808/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4])]

def node78Piece2Input : SectorVector := [(0, node78Piece2Input_sector0)]
def node78Piece2Output_sector0 : RawPoly ℕ := [(31232/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (124928/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (249856/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (249856/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (15616/1365, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (124928/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (3216896/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (124928/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (3310592/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (31232/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (249856/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (249856/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1436672/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (124928/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (124928/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (124928/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (499712/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (124928/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8])]

def node78Piece2Output : SectorVector := [(0, node78Piece2Output_sector0)]

def node78Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4])]

def node78Piece2UnitInput_sector0 : RawPoly ℕ := [node78Piece2UnitInput_sector0_chunk0].flatten

def node78Piece2UnitInput : SectorVector := [(0, node78Piece2UnitInput_sector0)]

def node78Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (198, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (412, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (424, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (52, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (1248, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1248, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (2392, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (624, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (1872, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (1872, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (7488, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (6864, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8])]

def node78Piece2UnitOutput_sector0 : RawPoly ℕ := [node78Piece2UnitOutput_sector0_chunk0].flatten

def node78Piece2UnitOutput : SectorVector := [(0, node78Piece2UnitOutput_sector0)]

theorem node78Piece2_check : VectorCertificate (neutralBoundS JR (-2) node78Piece2UnitInput) node78Piece2UnitOutput := by decide +kernel

theorem node78Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece2Input) = evaluate node78Piece2Output :=
  mode_of_scaled _ _ (7808/135135) node78Piece2UnitInput node78Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece2_check)

def node78Piece3Input_sector0 : RawPoly ℕ := [(2048/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3])]

def node78Piece3Input : SectorVector := [(0, node78Piece3Input_sector0)]
def node78Piece3Output_sector0_chunk0 : RawPoly ℕ := [(8192/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (8192/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (16384/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (16384/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (176128/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (16384/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (32768/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (8192/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (65536/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (77824/693, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (32768/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (32768/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (16384/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (32768/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (65536/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (229376/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (65536/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (131072/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (65536/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (131072/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (32768/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (65536/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node78Piece3Output_sector0_chunk1 : RawPoly ℕ := [(65536/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8])]

def node78Piece3Output_sector0 : RawPoly ℕ := [node78Piece3Output_sector0_chunk0, node78Piece3Output_sector0_chunk1].flatten

def node78Piece3Output : SectorVector := [(0, node78Piece3Output_sector0)]

def node78Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3])]

def node78Piece3UnitInput_sector0 : RawPoly ℕ := [node78Piece3UnitInput_sector0_chunk0].flatten

def node78Piece3UnitInput : SectorVector := [(0, node78Piece3UnitInput_sector0)]

def node78Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (258, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (352, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (570, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (528, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (2352, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (576, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (4752, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (3168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node78Piece3UnitOutput_sector0_chunk1 : RawPoly ℕ := [(5280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8])]

def node78Piece3UnitOutput_sector0 : RawPoly ℕ := [node78Piece3UnitOutput_sector0_chunk0, node78Piece3UnitOutput_sector0_chunk1].flatten

def node78Piece3UnitOutput : SectorVector := [(0, node78Piece3UnitOutput_sector0)]

theorem node78Piece3_check : VectorCertificate (neutralBoundS JR (-2) node78Piece3UnitInput) node78Piece3UnitOutput := by decide +kernel

theorem node78Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece3Input) = evaluate node78Piece3Output :=
  mode_of_scaled _ _ (2048/10395) node78Piece3UnitInput node78Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece3_check)

def node78Piece4Input_sector0 : RawPoly ℕ := [(-1024/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2])]

def node78Piece4Input : SectorVector := [(0, node78Piece4Input_sector0)]
def node78Piece4Output_sector0 : RawPoly ℕ := [(-4096/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (-8192/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (-2048/77, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (-8192/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (-32768/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (-69632/2079, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (-49152/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (-32768/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (-32768/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (-65536/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (-4096/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (-212992/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (-16384/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (-8192/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (-32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (-8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (-8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (-16384/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (-8192/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8])]

def node78Piece4Output : SectorVector := [(0, node78Piece4Output_sector0)]

def node78Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2])]

def node78Piece4UnitInput_sector0 : RawPoly ℕ := [node78Piece4UnitInput_sector0_chunk0].flatten

def node78Piece4UnitInput : SectorVector := [(0, node78Piece4UnitInput_sector0)]

def node78Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (270, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (340, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (1296, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (44, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (2288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (792, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (3168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (7920, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (3960, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8])]

def node78Piece4UnitOutput_sector0 : RawPoly ℕ := [node78Piece4UnitOutput_sector0_chunk0].flatten

def node78Piece4UnitOutput : SectorVector := [(0, node78Piece4UnitOutput_sector0)]

theorem node78Piece4_check : VectorCertificate (neutralBoundS JR (-2) node78Piece4UnitInput) node78Piece4UnitOutput := by decide +kernel

theorem node78Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece4Input) = evaluate node78Piece4Output :=
  mode_of_scaled _ _ (-1024/10395) node78Piece4UnitInput node78Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece4_check)

def node78Piece5Input_sector0 : RawPoly ℕ := [(256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6])]

def node78Piece5Input : SectorVector := [(0, node78Piece5Input_sector0)]
def node78Piece5Output_sector0 : RawPoly ℕ := [(1024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (2048/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (2048/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (2048/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (105472/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (2048/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (2048/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-47104/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (11264/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (382976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (22528/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (22528/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (45056/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (22528/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8])]

def node78Piece5Output : SectorVector := [(0, node78Piece5Output_sector0)]

def node78Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6])]

def node78Piece5UnitInput_sector0 : RawPoly ℕ := [node78Piece5UnitInput_sector0_chunk0].flatten

def node78Piece5UnitInput : SectorVector := [(0, node78Piece5UnitInput_sector0)]

def node78Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (270, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (412, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-552, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (44, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (1584, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (1496, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (7920, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (3960, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8])]

def node78Piece5UnitOutput_sector0 : RawPoly ℕ := [node78Piece5UnitOutput_sector0_chunk0].flatten

def node78Piece5UnitOutput : SectorVector := [(0, node78Piece5UnitOutput_sector0)]

theorem node78Piece5_check : VectorCertificate (neutralBoundS JR (-2) node78Piece5UnitInput) node78Piece5UnitOutput := by decide +kernel

theorem node78Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece5Input) = evaluate node78Piece5Output :=
  mode_of_scaled _ _ (256/315) node78Piece5UnitInput node78Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece5_check)

def node78Piece6Input_sector0 : RawPoly ℕ := [(15872/4725, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5])]

def node78Piece6Input : SectorVector := [(0, node78Piece6Input_sector0)]
def node78Piece6Output_sector0_chunk0 : RawPoly ℕ := [(63488/4725, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (126976/1575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1491968/1575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (126976/1575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (6158336/4725, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (63488/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (2793472/1575, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (126976/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (126976/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (253952/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1396736/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (507904/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (253952/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node78Piece6Output_sector0_chunk1 : RawPoly ℕ := [(507904/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (126976/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (126976/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (126976/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (253952/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (1015808/105, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece6Output_sector0 : RawPoly ℕ := [node78Piece6Output_sector0_chunk0, node78Piece6Output_sector0_chunk1].flatten

def node78Piece6Output : SectorVector := [(0, node78Piece6Output_sector0)]

def node78Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5])]

def node78Piece6UnitInput_sector0 : RawPoly ℕ := [node78Piece6UnitInput_sector0_chunk0].flatten

def node78Piece6UnitInput : SectorVector := [(0, node78Piece6UnitInput_sector0)]

def node78Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (282, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (388, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (528, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (40, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (1200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (2200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node78Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(2400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (5400, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (2160, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (2880, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece6UnitOutput_sector0 : RawPoly ℕ := [node78Piece6UnitOutput_sector0_chunk0, node78Piece6UnitOutput_sector0_chunk1].flatten

def node78Piece6UnitOutput : SectorVector := [(0, node78Piece6UnitOutput_sector0)]

theorem node78Piece6_check : VectorCertificate (neutralBoundS JR (-2) node78Piece6UnitInput) node78Piece6UnitOutput := by decide +kernel

theorem node78Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece6Input) = evaluate node78Piece6Output :=
  mode_of_scaled _ _ (15872/4725) node78Piece6UnitInput node78Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece6_check)

def node78Piece7Input_sector0 : RawPoly ℕ := [(1024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4])]

def node78Piece7Input : SectorVector := [(0, node78Piece7Input_sector0)]
def node78Piece7Output_sector0_chunk0 : RawPoly ℕ := [(4096/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (16384/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (8192/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (32768/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (26624/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (32768/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (16384/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (385024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (32768/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (16384/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (434176/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (38912/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (32768/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (16384/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (65536/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (65536/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (450560/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (32768/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node78Piece7Output_sector0_chunk1 : RawPoly ℕ := [(65536/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (98304/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (73728/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (65536/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8])]

def node78Piece7Output_sector0 : RawPoly ℕ := [node78Piece7Output_sector0_chunk0, node78Piece7Output_sector0_chunk1].flatten

def node78Piece7Output : SectorVector := [(0, node78Piece7Output_sector0)]

def node78Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4])]

def node78Piece7UnitInput_sector0 : RawPoly ℕ := [node78Piece7UnitInput_sector0_chunk0].flatten

def node78Piece7UnitInput : SectorVector := [(0, node78Piece7UnitInput_sector0)]

def node78Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (234, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (376, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (424, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (570, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (40, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (2200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node78Piece7UnitOutput_sector0_chunk1 : RawPoly ℕ := [(2880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (4320, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (3240, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (2880, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8])]

def node78Piece7UnitOutput_sector0 : RawPoly ℕ := [node78Piece7UnitOutput_sector0_chunk0, node78Piece7UnitOutput_sector0_chunk1].flatten

def node78Piece7UnitOutput : SectorVector := [(0, node78Piece7UnitOutput_sector0)]

theorem node78Piece7_check : VectorCertificate (neutralBoundS JR (-2) node78Piece7UnitInput) node78Piece7UnitOutput := by decide +kernel

theorem node78Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece7Input) = evaluate node78Piece7Output :=
  mode_of_scaled _ _ (1024/315) node78Piece7UnitInput node78Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece7_check)

def node78Piece8Input_sector0 : RawPoly ℕ := [(928/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4])]

def node78Piece8Input : SectorVector := [(0, node78Piece8Input_sector0)]
def node78Piece8Output_sector0_chunk0 : RawPoly ℕ := [(3712/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (14848/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (14848/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (29696/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (29696/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (76096/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (14848/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (118784/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (29696/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (14848/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (48256/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (14848/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (393472/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (118784/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (296960/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (118784/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (29696/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (29696/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (118784/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (3712/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (29696/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (29696/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (215296/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (14848/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5])]

def node78Piece8Output_sector0_chunk1 : RawPoly ℕ := [(29696/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (14848/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (118784/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (29696/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (29696/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (29696/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (118784/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (118784/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (29696/3, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8])]

def node78Piece8Output_sector0 : RawPoly ℕ := [node78Piece8Output_sector0_chunk0, node78Piece8Output_sector0_chunk1].flatten

def node78Piece8Output : SectorVector := [(0, node78Piece8Output_sector0)]

def node78Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4])]

def node78Piece8UnitInput_sector0 : RawPoly ℕ := [node78Piece8UnitInput_sector0_chunk0].flatten

def node78Piece8UnitInput : SectorVector := [(0, node78Piece8UnitInput_sector0)]

def node78Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (246, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (364, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (424, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (384, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (2088, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5])]

def node78Piece8UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (3456, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (3456, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (3456, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (2016, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8])]

def node78Piece8UnitOutput_sector0 : RawPoly ℕ := [node78Piece8UnitOutput_sector0_chunk0, node78Piece8UnitOutput_sector0_chunk1].flatten

def node78Piece8UnitOutput : SectorVector := [(0, node78Piece8UnitOutput_sector0)]

theorem node78Piece8_check : VectorCertificate (neutralBoundS JR (-2) node78Piece8UnitInput) node78Piece8UnitOutput := by decide +kernel

theorem node78Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece8Input) = evaluate node78Piece8Output :=
  mode_of_scaled _ _ (928/189) node78Piece8UnitInput node78Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece8_check)

def node78Piece9Input_sector0 : RawPoly ℕ := [(256/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3])]

def node78Piece9Input : SectorVector := [(0, node78Piece9Input_sector0)]
def node78Piece9Output_sector0_chunk0 : RawPoly ℕ := [(1024/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (2048/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (2048/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (4096/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (3584/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (2048/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (2048/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (80896/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (11264/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (45056/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (4096/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1024/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (59392/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5])]

def node78Piece9Output_sector0_chunk1 : RawPoly ℕ := [(2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (8192/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (8192/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (8192/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16384/21, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (8192/9, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8])]

def node78Piece9Output_sector0 : RawPoly ℕ := [node78Piece9Output_sector0_chunk0, node78Piece9Output_sector0_chunk1].flatten

def node78Piece9Output : SectorVector := [(0, node78Piece9Output_sector0)]

def node78Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3])]

def node78Piece9UnitInput_sector0 : RawPoly ℕ := [node78Piece9UnitInput_sector0_chunk0].flatten

def node78Piece9UnitInput : SectorVector := [(0, node78Piece9UnitInput_sector0)]

def node78Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (294, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (316, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (924, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (528, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (1296, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (2088, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (1296, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (1944, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5])]

def node78Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (2592, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (5184, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (1728, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (2016, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8])]

def node78Piece9UnitOutput_sector0 : RawPoly ℕ := [node78Piece9UnitOutput_sector0_chunk0, node78Piece9UnitOutput_sector0_chunk1].flatten

def node78Piece9UnitOutput : SectorVector := [(0, node78Piece9UnitOutput_sector0)]

theorem node78Piece9_check : VectorCertificate (neutralBoundS JR (-2) node78Piece9UnitInput) node78Piece9UnitOutput := by decide +kernel

theorem node78Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece9Input) = evaluate node78Piece9Output :=
  mode_of_scaled _ _ (256/567) node78Piece9UnitInput node78Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece9_check)

def node78Piece10Input_sector0 : RawPoly ℕ := [(16/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 8])]

def node78Piece10Input : SectorVector := [(0, node78Piece10Input_sector0)]
def node78Piece10Output_sector0_chunk0 : RawPoly ℕ := [(64/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1568, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (6592/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-14080, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (11136, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (4608, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (4608, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece10Output_sector0_chunk1 : RawPoly ℕ := [(4608, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (36864, [1, 1, 1, 1, 1, 1, 1, 15]), (10752, [1, 1, 1, 1, 1, 1, 8, 8])]

def node78Piece10Output_sector0 : RawPoly ℕ := [node78Piece10Output_sector0_chunk0, node78Piece10Output_sector0_chunk1].flatten

def node78Piece10Output : SectorVector := [(0, node78Piece10Output_sector0)]

def node78Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 8])]

def node78Piece10UnitInput_sector0 : RawPoly ℕ := [node78Piece10UnitInput_sector0_chunk0].flatten

def node78Piece10UnitInput : SectorVector := [(0, node78Piece10UnitInput_sector0)]

def node78Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (294, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (412, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-2640, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (1728, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (2088, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (864, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (6912, [1, 1, 1, 1, 1, 1, 1, 15]), (2016, [1, 1, 1, 1, 1, 1, 8, 8])]

def node78Piece10UnitOutput_sector0 : RawPoly ℕ := [node78Piece10UnitOutput_sector0_chunk0, node78Piece10UnitOutput_sector0_chunk1].flatten

def node78Piece10UnitOutput : SectorVector := [(0, node78Piece10UnitOutput_sector0)]

theorem node78Piece10_check : VectorCertificate (neutralBoundS JR (-2) node78Piece10UnitInput) node78Piece10UnitOutput := by decide +kernel

theorem node78Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece10Input) = evaluate node78Piece10Output :=
  mode_of_scaled _ _ (16/3) node78Piece10UnitInput node78Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece10_check)

def node78Piece11Input_sector0 : RawPoly ℕ := [(256/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 7])]

def node78Piece11Input : SectorVector := [(0, node78Piece11Input_sector0)]
def node78Piece11Output_sector0_chunk0 : RawPoly ℕ := [(1024/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (26112/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (99328/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (1024/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-52736/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (30720/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (8192/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11])]

def node78Piece11Output_sector0_chunk1 : RawPoly ℕ := [(16384, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (499712/21, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (32768, [1, 1, 1, 1, 1, 1, 1, 15]), (8192, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (8192, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (57344, [1, 1, 1, 1, 1, 1, 2, 14]), (16384, [1, 1, 1, 1, 1, 1, 7, 9]), (16384, [1, 1, 1, 1, 1, 2, 7, 8])]

def node78Piece11Output_sector0 : RawPoly ℕ := [node78Piece11Output_sector0_chunk0, node78Piece11Output_sector0_chunk1].flatten

def node78Piece11Output : SectorVector := [(0, node78Piece11Output_sector0)]

def node78Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 7])]

def node78Piece11UnitInput_sector0 : RawPoly ℕ := [node78Piece11UnitInput_sector0_chunk0].flatten

def node78Piece11UnitInput : SectorVector := [(0, node78Piece11UnitInput_sector0)]

def node78Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (306, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (388, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (28, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-1442, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (360, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (32, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (1344, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11])]

def node78Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1344, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (1344, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (1344, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (1952, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (384, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (192, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (2688, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (4704, [1, 1, 1, 1, 1, 1, 2, 14]), (1344, [1, 1, 1, 1, 1, 1, 7, 9]), (1344, [1, 1, 1, 1, 1, 2, 7, 8])]

def node78Piece11UnitOutput_sector0 : RawPoly ℕ := [node78Piece11UnitOutput_sector0_chunk0, node78Piece11UnitOutput_sector0_chunk1].flatten

def node78Piece11UnitOutput : SectorVector := [(0, node78Piece11UnitOutput_sector0)]

theorem node78Piece11_check : VectorCertificate (neutralBoundS JR (-2) node78Piece11UnitInput) node78Piece11UnitOutput := by decide +kernel

theorem node78Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece11Input) = evaluate node78Piece11Output :=
  mode_of_scaled _ _ (256/21) node78Piece11UnitInput node78Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece11_check)

def node78Piece12Input_sector0 : RawPoly ℕ := [(256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 6])]

def node78Piece12Input : SectorVector := [(0, node78Piece12Input_sector0)]
def node78Piece12Output_sector0_chunk0 : RawPoly ℕ := [(1024/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1024/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (8704/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (1024/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (96256/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-47104/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (48640/21, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (8192/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7])]

def node78Piece12Output_sector0_chunk1 : RawPoly ℕ := [(32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (352256/63, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (98304/7, [1, 1, 1, 1, 1, 1, 1, 15]), (8192/3, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (8192/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (16384, [1, 1, 1, 1, 1, 1, 3, 13]), (8192, [1, 1, 1, 1, 1, 1, 6, 10]), (16384/3, [1, 1, 1, 1, 1, 3, 6, 8])]

def node78Piece12Output_sector0 : RawPoly ℕ := [node78Piece12Output_sector0_chunk0, node78Piece12Output_sector0_chunk1].flatten

def node78Piece12Output : SectorVector := [(0, node78Piece12Output_sector0)]

def node78Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 3, 6])]

def node78Piece12UnitInput_sector0 : RawPoly ℕ := [node78Piece12UnitInput_sector0_chunk0].flatten

def node78Piece12UnitInput : SectorVector := [(0, node78Piece12UnitInput_sector0)]

def node78Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (306, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (376, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-552, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (432, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (570, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (32, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (1152, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7])]

def node78Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1152, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (1152, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (1152, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (1376, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (3456, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (672, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (4032, [1, 1, 1, 1, 1, 1, 3, 13]), (2016, [1, 1, 1, 1, 1, 1, 6, 10]), (1344, [1, 1, 1, 1, 1, 3, 6, 8])]

def node78Piece12UnitOutput_sector0 : RawPoly ℕ := [node78Piece12UnitOutput_sector0_chunk0, node78Piece12UnitOutput_sector0_chunk1].flatten

def node78Piece12UnitOutput : SectorVector := [(0, node78Piece12UnitOutput_sector0)]

theorem node78Piece12_check : VectorCertificate (neutralBoundS JR (-2) node78Piece12UnitInput) node78Piece12UnitOutput := by decide +kernel

theorem node78Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece12Input) = evaluate node78Piece12Output :=
  mode_of_scaled _ _ (256/63) node78Piece12UnitInput node78Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece12_check)

def node78Piece13Input_sector0 : RawPoly ℕ := [(1408/105, [1, 1, 1, 1, 1, 1, 1, 1, 4, 5])]

def node78Piece13Input : SectorVector := [(0, node78Piece13Input_sector0)]
def node78Piece13Output_sector0_chunk0 : RawPoly ℕ := [(5632/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (5632/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (22528/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (11264/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (11264/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (45056/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (121088/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (45056/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (5632/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (22528/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (580096/105, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (5632/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (45056/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (22528/105, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (5632/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (45056/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (5632/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (596992/105, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (45056/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (22528/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (45056/105, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (90112/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (360448/35, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece13Output_sector0_chunk1 : RawPoly ℕ := [(90112/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (360448/35, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (90112/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (2748416/105, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (180224/35, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (360448/7, [1, 1, 1, 1, 1, 1, 1, 15]), (45056/5, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (45056/5, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (45056, [1, 1, 1, 1, 1, 1, 4, 12]), (180224/5, [1, 1, 1, 1, 1, 1, 5, 11]), (90112/5, [1, 1, 1, 1, 1, 4, 5, 8])]

def node78Piece13Output_sector0 : RawPoly ℕ := [node78Piece13Output_sector0_chunk0, node78Piece13Output_sector0_chunk1].flatten

def node78Piece13Output : SectorVector := [(0, node78Piece13Output_sector0)]

def node78Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 4, 5])]

def node78Piece13UnitInput_sector0 : RawPoly ℕ := [node78Piece13UnitInput_sector0_chunk0].flatten

def node78Piece13UnitInput : SectorVector := [(0, node78Piece13UnitInput_sector0)]

def node78Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (258, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (412, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (16, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (424, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (480, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (32, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (960, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8])]

def node78Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (768, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (960, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]), (1952, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (384, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (3840, [1, 1, 1, 1, 1, 1, 1, 15]), (672, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (672, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (3360, [1, 1, 1, 1, 1, 1, 4, 12]), (2688, [1, 1, 1, 1, 1, 1, 5, 11]), (1344, [1, 1, 1, 1, 1, 4, 5, 8])]

def node78Piece13UnitOutput_sector0 : RawPoly ℕ := [node78Piece13UnitOutput_sector0_chunk0, node78Piece13UnitOutput_sector0_chunk1].flatten

def node78Piece13UnitOutput : SectorVector := [(0, node78Piece13UnitOutput_sector0)]

theorem node78Piece13_check : VectorCertificate (neutralBoundS JR (-2) node78Piece13UnitInput) node78Piece13UnitOutput := by decide +kernel

theorem node78Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece13Input) = evaluate node78Piece13Output :=
  mode_of_scaled _ _ (1408/105) node78Piece13UnitInput node78Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece13_check)

def node78Piece14Input_sector0 : RawPoly ℕ := [(176/315, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2])]

def node78Piece14Input : SectorVector := [(0, node78Piece14Input_sector0)]
def node78Piece14Output_sector0 : RawPoly ℕ := [(704/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (1408/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (18656/105, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (1408/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (11264/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (51392/315, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (2816/3, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (11264/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (11264/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (22528/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (704/45, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (45056/45, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (2816/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (1408/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (11264/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (1408/5, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (1408/5, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (2816, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9]), (1408/3, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8])]

def node78Piece14Output : SectorVector := [(0, node78Piece14Output_sector0)]

def node78Piece14UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2])]

def node78Piece14UnitInput_sector0 : RawPoly ℕ := [node78Piece14UnitInput_sector0_chunk0].flatten

def node78Piece14UnitInput : SectorVector := [(0, node78Piece14UnitInput_sector0)]

def node78Piece14UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (318, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (292, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (1680, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (960, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (960, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (1920, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (28, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (1792, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (1680, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (840, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (6720, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (504, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (504, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (5040, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9]), (840, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8])]

def node78Piece14UnitOutput_sector0 : RawPoly ℕ := [node78Piece14UnitOutput_sector0_chunk0].flatten

def node78Piece14UnitOutput : SectorVector := [(0, node78Piece14UnitOutput_sector0)]

theorem node78Piece14_check : VectorCertificate (neutralBoundS JR (-2) node78Piece14UnitInput) node78Piece14UnitOutput := by decide +kernel

theorem node78Piece14_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece14Input) = evaluate node78Piece14Output :=
  mode_of_scaled _ _ (176/315) node78Piece14UnitInput node78Piece14UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece14_check)

def node78Piece15Input_sector0 : RawPoly ℕ := [(928/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 6])]

def node78Piece15Input : SectorVector := [(0, node78Piece15Input_sector0)]
def node78Piece15Output_sector0_chunk0 : RawPoly ℕ := [(3712/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (7424/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (14848/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (14848/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (14848/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (98368/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (7424/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (14848/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (59392/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (29696/21, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (7424/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (48256/9, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (14848/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (7424/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (7424/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-170752/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (59392/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (59392/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (59392/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (296960/21, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (29696/21, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (29696/21, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (59392/7, [1, 1, 1, 1, 1, 1, 1, 15]), (3712/9, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6])]

def node78Piece15Output_sector0_chunk1 : RawPoly ℕ := [(14848, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (14848, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (14848, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (14848, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (170752/9, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (29696/3, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (14848/3, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (59392, [1, 1, 1, 1, 1, 1, 2, 14]), (29696/3, [1, 1, 1, 1, 1, 1, 6, 10]), (7424, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (7424, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (44544, [1, 1, 1, 1, 1, 2, 2, 13]), (29696, [1, 1, 1, 1, 1, 2, 6, 9]), (37120/3, [1, 1, 1, 1, 2, 2, 6, 8])]

def node78Piece15Output_sector0 : RawPoly ℕ := [node78Piece15Output_sector0_chunk0, node78Piece15Output_sector0_chunk1].flatten

def node78Piece15Output : SectorVector := [(0, node78Piece15Output_sector0)]

def node78Piece15UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 2, 2, 6])]

def node78Piece15UnitInput_sector0 : RawPoly ℕ := [node78Piece15UnitInput_sector0_chunk0].flatten

def node78Piece15UnitInput : SectorVector := [(0, node78Piece15UnitInput_sector0)]

def node78Piece15UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (318, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (72, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (364, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-552, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (960, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 15]), (28, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6])]

def node78Piece15UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1008, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (1288, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (336, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (4032, [1, 1, 1, 1, 1, 1, 2, 14]), (672, [1, 1, 1, 1, 1, 1, 6, 10]), (504, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (504, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (3024, [1, 1, 1, 1, 1, 2, 2, 13]), (2016, [1, 1, 1, 1, 1, 2, 6, 9]), (840, [1, 1, 1, 1, 2, 2, 6, 8])]

def node78Piece15UnitOutput_sector0 : RawPoly ℕ := [node78Piece15UnitOutput_sector0_chunk0, node78Piece15UnitOutput_sector0_chunk1].flatten

def node78Piece15UnitOutput : SectorVector := [(0, node78Piece15UnitOutput_sector0)]

theorem node78Piece15_check : VectorCertificate (neutralBoundS JR (-2) node78Piece15UnitInput) node78Piece15UnitOutput := by decide +kernel

theorem node78Piece15_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece15Input) = evaluate node78Piece15Output :=
  mode_of_scaled _ _ (928/63) node78Piece15UnitInput node78Piece15UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece15_check)

end VOA.Classification.COne.OrbC2h
