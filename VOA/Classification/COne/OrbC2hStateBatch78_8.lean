import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch78_6
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

def node78Piece128Input_sector0 : RawPoly ℕ := [(160/3, [3, 3, 3, 8])]

def node78Piece128Input : SectorVector := [(0, node78Piece128Input_sector0)]
def node78Piece128Output_sector0_chunk0 : RawPoly ℕ := [(640/3, [1, 1, 1, 2, 3, 3, 3, 8]), (5120, [1, 1, 3, 3, 3, 11]), (5760, [1, 1, 3, 3, 6, 8]), (10240, [1, 2, 3, 3, 3, 10]), (11520, [1, 2, 3, 3, 5, 8]), (10240, [1, 3, 3, 3, 3, 9]), (21440, [1, 3, 3, 3, 4, 8]), (10240, [1, 3, 3, 3, 5, 7]), (5120, [1, 3, 3, 3, 6, 6]), (92160, [1, 3, 3, 15]), (34560, [1, 3, 8, 10]), (5120, [2, 2, 3, 3, 3, 9]), (5760, [2, 2, 3, 3, 4, 8]), (48640/3, [2, 3, 3, 3, 3, 8]), (10240, [2, 3, 3, 3, 4, 7]), (10240, [2, 3, 3, 3, 5, 6]), (92160, [2, 3, 3, 14]), (34560, [2, 3, 8, 9]), (5120, [3, 3, 3, 3, 3, 7]), (10240, [3, 3, 3, 3, 4, 6]), (5120, [3, 3, 3, 3, 5, 5]), (5120, [3, 3, 3, 4, 4, 5]), (-140800, [3, 3, 3, 13]), (92160, [3, 3, 4, 12])]

def node78Piece128Output_sector0_chunk1 : RawPoly ℕ := [(92160, [3, 3, 5, 11]), (92160, [3, 3, 6, 10]), (92160, [3, 3, 7, 9]), (10560, [3, 3, 8, 8]), (34560, [3, 4, 7, 8]), (34560, [3, 5, 6, 8]), (276480, [3, 19]), (34560, [8, 14])]

def node78Piece128Output_sector0 : RawPoly ℕ := [node78Piece128Output_sector0_chunk0, node78Piece128Output_sector0_chunk1].flatten

def node78Piece128Output : SectorVector := [(0, node78Piece128Output_sector0)]

def node78Piece128UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 8])]

def node78Piece128UnitInput_sector0 : RawPoly ℕ := [node78Piece128UnitInput_sector0_chunk0].flatten

def node78Piece128UnitInput : SectorVector := [(0, node78Piece128UnitInput_sector0)]

def node78Piece128UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 3, 8]), (96, [1, 1, 3, 3, 3, 11]), (108, [1, 1, 3, 3, 6, 8]), (192, [1, 2, 3, 3, 3, 10]), (216, [1, 2, 3, 3, 5, 8]), (192, [1, 3, 3, 3, 3, 9]), (402, [1, 3, 3, 3, 4, 8]), (192, [1, 3, 3, 3, 5, 7]), (96, [1, 3, 3, 3, 6, 6]), (1728, [1, 3, 3, 15]), (648, [1, 3, 8, 10]), (96, [2, 2, 3, 3, 3, 9]), (108, [2, 2, 3, 3, 4, 8]), (304, [2, 3, 3, 3, 3, 8]), (192, [2, 3, 3, 3, 4, 7]), (192, [2, 3, 3, 3, 5, 6]), (1728, [2, 3, 3, 14]), (648, [2, 3, 8, 9]), (96, [3, 3, 3, 3, 3, 7]), (192, [3, 3, 3, 3, 4, 6]), (96, [3, 3, 3, 3, 5, 5]), (96, [3, 3, 3, 4, 4, 5]), (-2640, [3, 3, 3, 13]), (1728, [3, 3, 4, 12])]

def node78Piece128UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1728, [3, 3, 5, 11]), (1728, [3, 3, 6, 10]), (1728, [3, 3, 7, 9]), (198, [3, 3, 8, 8]), (648, [3, 4, 7, 8]), (648, [3, 5, 6, 8]), (5184, [3, 19]), (648, [8, 14])]

def node78Piece128UnitOutput_sector0 : RawPoly ℕ := [node78Piece128UnitOutput_sector0_chunk0, node78Piece128UnitOutput_sector0_chunk1].flatten

def node78Piece128UnitOutput : SectorVector := [(0, node78Piece128UnitOutput_sector0)]

theorem node78Piece128_check : VectorCertificate (neutralBoundS JR (-2) node78Piece128UnitInput) node78Piece128UnitOutput := by decide +kernel

theorem node78Piece128_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece128Input) = evaluate node78Piece128Output :=
  mode_of_scaled _ _ (160/3) node78Piece128UnitInput node78Piece128UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece128_check)

def node78Piece129Input_sector0 : RawPoly ℕ := [(1280/21, [3, 3, 4, 7])]

def node78Piece129Input : SectorVector := [(0, node78Piece129Input_sector0)]
def node78Piece129Output_sector0_chunk0 : RawPoly ℕ := [(5120/21, [1, 1, 1, 2, 3, 3, 4, 7]), (5120, [1, 1, 3, 3, 4, 10]), (20480/7, [1, 1, 3, 3, 7, 7]), (30720/7, [1, 1, 3, 4, 6, 7]), (10240, [1, 2, 3, 3, 4, 9]), (40960/7, [1, 2, 3, 3, 6, 7]), (61440/7, [1, 2, 3, 4, 5, 7]), (10240, [1, 3, 3, 3, 4, 8]), (40960/7, [1, 3, 3, 3, 5, 7]), (151040/7, [1, 3, 3, 4, 4, 7]), (10240, [1, 3, 3, 4, 5, 6]), (40960, [1, 3, 3, 15]), (61440, [1, 3, 4, 14]), (245760/7, [1, 3, 7, 11]), (92160/7, [1, 4, 7, 10]), (5120, [2, 2, 3, 3, 4, 8]), (20480/7, [2, 2, 3, 3, 5, 7]), (30720/7, [2, 2, 3, 4, 4, 7]), (435200/21, [2, 3, 3, 3, 4, 7]), (10240, [2, 3, 3, 4, 4, 6]), (5120, [2, 3, 3, 4, 5, 5]), (40960, [2, 3, 3, 14]), (61440, [2, 3, 4, 13]), (245760/7, [2, 3, 7, 10])]

def node78Piece129Output_sector0_chunk1 : RawPoly ℕ := [(92160/7, [2, 4, 7, 9]), (20480/21, [3, 3, 3, 3, 3, 7]), (5120, [3, 3, 3, 3, 4, 6]), (10240, [3, 3, 3, 4, 4, 5]), (40960, [3, 3, 3, 13]), (5120/3, [3, 3, 4, 4, 4, 4]), (-263680/3, [3, 3, 4, 12]), (40960, [3, 3, 5, 11]), (40960, [3, 3, 6, 10]), (542720/21, [3, 3, 7, 9]), (20480, [3, 3, 8, 8]), (61440, [3, 4, 4, 11]), (61440, [3, 4, 5, 10]), (61440, [3, 4, 6, 9]), (56320, [3, 4, 7, 8]), (245760/7, [3, 5, 7, 7]), (122880/7, [3, 6, 6, 7]), (245760, [3, 19]), (92160/7, [4, 4, 7, 7]), (92160/7, [4, 5, 6, 7]), (92160, [4, 18]), (368640/7, [7, 15])]

def node78Piece129Output_sector0 : RawPoly ℕ := [node78Piece129Output_sector0_chunk0, node78Piece129Output_sector0_chunk1].flatten

def node78Piece129Output : SectorVector := [(0, node78Piece129Output_sector0)]

def node78Piece129UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 4, 7])]

def node78Piece129UnitInput_sector0 : RawPoly ℕ := [node78Piece129UnitInput_sector0_chunk0].flatten

def node78Piece129UnitInput : SectorVector := [(0, node78Piece129UnitInput_sector0)]

def node78Piece129UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 7]), (84, [1, 1, 3, 3, 4, 10]), (48, [1, 1, 3, 3, 7, 7]), (72, [1, 1, 3, 4, 6, 7]), (168, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 5, 7]), (168, [1, 3, 3, 3, 4, 8]), (96, [1, 3, 3, 3, 5, 7]), (354, [1, 3, 3, 4, 4, 7]), (168, [1, 3, 3, 4, 5, 6]), (672, [1, 3, 3, 15]), (1008, [1, 3, 4, 14]), (576, [1, 3, 7, 11]), (216, [1, 4, 7, 10]), (84, [2, 2, 3, 3, 4, 8]), (48, [2, 2, 3, 3, 5, 7]), (72, [2, 2, 3, 4, 4, 7]), (340, [2, 3, 3, 3, 4, 7]), (168, [2, 3, 3, 4, 4, 6]), (84, [2, 3, 3, 4, 5, 5]), (672, [2, 3, 3, 14]), (1008, [2, 3, 4, 13]), (576, [2, 3, 7, 10])]

def node78Piece129UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [2, 4, 7, 9]), (16, [3, 3, 3, 3, 3, 7]), (84, [3, 3, 3, 3, 4, 6]), (168, [3, 3, 3, 4, 4, 5]), (672, [3, 3, 3, 13]), (28, [3, 3, 4, 4, 4, 4]), (-1442, [3, 3, 4, 12]), (672, [3, 3, 5, 11]), (672, [3, 3, 6, 10]), (424, [3, 3, 7, 9]), (336, [3, 3, 8, 8]), (1008, [3, 4, 4, 11]), (1008, [3, 4, 5, 10]), (1008, [3, 4, 6, 9]), (924, [3, 4, 7, 8]), (576, [3, 5, 7, 7]), (288, [3, 6, 6, 7]), (4032, [3, 19]), (216, [4, 4, 7, 7]), (216, [4, 5, 6, 7]), (1512, [4, 18]), (864, [7, 15])]

def node78Piece129UnitOutput_sector0 : RawPoly ℕ := [node78Piece129UnitOutput_sector0_chunk0, node78Piece129UnitOutput_sector0_chunk1].flatten

def node78Piece129UnitOutput : SectorVector := [(0, node78Piece129UnitOutput_sector0)]

theorem node78Piece129_check : VectorCertificate (neutralBoundS JR (-2) node78Piece129UnitInput) node78Piece129UnitOutput := by decide +kernel

theorem node78Piece129_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece129Input) = evaluate node78Piece129Output :=
  mode_of_scaled _ _ (1280/21) node78Piece129UnitInput node78Piece129UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece129_check)

def node78Piece130Input_sector0 : RawPoly ℕ := [(832/9, [3, 3, 5, 6])]

def node78Piece130Input : SectorVector := [(0, node78Piece130Input_sector0)]
def node78Piece130Output_sector0_chunk0 : RawPoly ℕ := [(3328/9, [1, 1, 1, 2, 3, 3, 5, 6]), (6656, [1, 1, 3, 3, 5, 9]), (16640/3, [1, 1, 3, 3, 6, 8]), (6656, [1, 1, 3, 5, 6, 6]), (13312, [1, 2, 3, 3, 5, 8]), (33280/3, [1, 2, 3, 3, 6, 7]), (13312, [1, 2, 3, 5, 5, 6]), (13312, [1, 3, 3, 3, 5, 7]), (33280/3, [1, 3, 3, 3, 6, 6]), (111488/3, [1, 3, 3, 4, 5, 6]), (6656, [1, 3, 3, 5, 5, 5]), (66560, [1, 3, 3, 15]), (79872, [1, 3, 5, 13]), (66560, [1, 3, 6, 12]), (19968, [1, 5, 6, 10]), (6656, [2, 2, 3, 3, 5, 7]), (16640/3, [2, 2, 3, 3, 6, 6]), (6656, [2, 2, 3, 4, 5, 6]), (282880/9, [2, 3, 3, 3, 5, 6]), (16640/3, [2, 3, 3, 4, 4, 6]), (13312, [2, 3, 3, 4, 5, 5]), (66560, [2, 3, 3, 14]), (79872, [2, 3, 5, 12]), (66560, [2, 3, 6, 11])]

def node78Piece130Output_sector0_chunk1 : RawPoly ℕ := [(19968, [2, 5, 6, 9]), (16640/3, [3, 3, 3, 3, 4, 6]), (6656, [3, 3, 3, 3, 5, 5]), (6656, [3, 3, 3, 4, 4, 5]), (66560, [3, 3, 3, 13]), (66560, [3, 3, 4, 12]), (-153088/3, [3, 3, 5, 11]), (16640/3, [3, 3, 6, 10]), (66560, [3, 3, 7, 9]), (33280, [3, 3, 8, 8]), (79872, [3, 4, 5, 10]), (66560, [3, 4, 6, 9]), (79872, [3, 5, 5, 9]), (256256/3, [3, 5, 6, 8]), (39936, [3, 5, 7, 7]), (66560, [3, 6, 6, 7]), (399360, [3, 19]), (19968, [4, 5, 6, 7]), (19968, [5, 5, 6, 6]), (119808, [5, 17]), (99840, [6, 16])]

def node78Piece130Output_sector0 : RawPoly ℕ := [node78Piece130Output_sector0_chunk0, node78Piece130Output_sector0_chunk1].flatten

def node78Piece130Output : SectorVector := [(0, node78Piece130Output_sector0)]

def node78Piece130UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 5, 6])]

def node78Piece130UnitInput_sector0 : RawPoly ℕ := [node78Piece130UnitInput_sector0_chunk0].flatten

def node78Piece130UnitInput : SectorVector := [(0, node78Piece130UnitInput_sector0)]

def node78Piece130UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 5, 6]), (72, [1, 1, 3, 3, 5, 9]), (60, [1, 1, 3, 3, 6, 8]), (72, [1, 1, 3, 5, 6, 6]), (144, [1, 2, 3, 3, 5, 8]), (120, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 5, 5, 6]), (144, [1, 3, 3, 3, 5, 7]), (120, [1, 3, 3, 3, 6, 6]), (402, [1, 3, 3, 4, 5, 6]), (72, [1, 3, 3, 5, 5, 5]), (720, [1, 3, 3, 15]), (864, [1, 3, 5, 13]), (720, [1, 3, 6, 12]), (216, [1, 5, 6, 10]), (72, [2, 2, 3, 3, 5, 7]), (60, [2, 2, 3, 3, 6, 6]), (72, [2, 2, 3, 4, 5, 6]), (340, [2, 3, 3, 3, 5, 6]), (60, [2, 3, 3, 4, 4, 6]), (144, [2, 3, 3, 4, 5, 5]), (720, [2, 3, 3, 14]), (864, [2, 3, 5, 12]), (720, [2, 3, 6, 11])]

def node78Piece130UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [2, 5, 6, 9]), (60, [3, 3, 3, 3, 4, 6]), (72, [3, 3, 3, 3, 5, 5]), (72, [3, 3, 3, 4, 4, 5]), (720, [3, 3, 3, 13]), (720, [3, 3, 4, 12]), (-552, [3, 3, 5, 11]), (60, [3, 3, 6, 10]), (720, [3, 3, 7, 9]), (360, [3, 3, 8, 8]), (864, [3, 4, 5, 10]), (720, [3, 4, 6, 9]), (864, [3, 5, 5, 9]), (924, [3, 5, 6, 8]), (432, [3, 5, 7, 7]), (720, [3, 6, 6, 7]), (4320, [3, 19]), (216, [4, 5, 6, 7]), (216, [5, 5, 6, 6]), (1296, [5, 17]), (1080, [6, 16])]

def node78Piece130UnitOutput_sector0 : RawPoly ℕ := [node78Piece130UnitOutput_sector0_chunk0, node78Piece130UnitOutput_sector0_chunk1].flatten

def node78Piece130UnitOutput : SectorVector := [(0, node78Piece130UnitOutput_sector0)]

theorem node78Piece130_check : VectorCertificate (neutralBoundS JR (-2) node78Piece130UnitInput) node78Piece130UnitOutput := by decide +kernel

theorem node78Piece130_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece130Input) = evaluate node78Piece130Output :=
  mode_of_scaled _ _ (832/9) node78Piece130UnitInput node78Piece130UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece130_check)

def node78Piece131Input_sector0 : RawPoly ℕ := [(-40/3, [3, 4, 4, 6])]

def node78Piece131Input : SectorVector := [(0, node78Piece131Input_sector0)]
def node78Piece131Output_sector0_chunk0 : RawPoly ℕ := [(-160/3, [1, 1, 1, 2, 3, 4, 4, 6]), (-960, [1, 1, 3, 4, 4, 9]), (-1280, [1, 1, 3, 4, 6, 7]), (-480, [1, 1, 4, 4, 6, 6]), (-1920, [1, 2, 3, 4, 4, 8]), (-2560, [1, 2, 3, 4, 6, 6]), (-960, [1, 2, 4, 4, 5, 6]), (-1920, [1, 3, 3, 4, 4, 7]), (-2560, [1, 3, 3, 4, 5, 6]), (-4080, [1, 3, 4, 4, 4, 6]), (-960, [1, 3, 4, 4, 5, 5]), (-15360, [1, 3, 4, 14]), (-5120, [1, 3, 6, 12]), (-5760, [1, 4, 4, 13]), (-7680, [1, 4, 6, 11]), (-960, [2, 2, 3, 4, 4, 7]), (-1280, [2, 2, 3, 4, 5, 6]), (-480, [2, 2, 4, 4, 4, 6]), (-15040/3, [2, 3, 3, 4, 4, 6]), (-1920, [2, 3, 4, 4, 4, 5]), (-15360, [2, 3, 4, 13]), (-5120, [2, 3, 6, 11]), (-5760, [2, 4, 4, 12]), (-7680, [2, 4, 6, 10])]

def node78Piece131Output_sector0_chunk1 : RawPoly ℕ := [(-1280/3, [3, 3, 3, 3, 4, 6]), (-960, [3, 3, 3, 4, 4, 5]), (-960, [3, 3, 4, 4, 4, 4]), (-15360, [3, 3, 4, 12]), (-5120, [3, 3, 6, 10]), (7360, [3, 4, 4, 11]), (-15360, [3, 4, 5, 10]), (-18560/3, [3, 4, 6, 9]), (-15360, [3, 4, 7, 8]), (-5120, [3, 5, 6, 8]), (-5120, [3, 6, 6, 7]), (-30720, [3, 19]), (-5760, [4, 4, 4, 10]), (-5760, [4, 4, 5, 9]), (-7600, [4, 4, 6, 8]), (-2880, [4, 4, 7, 7]), (-7680, [4, 5, 6, 7]), (-3840, [4, 6, 6, 6]), (-46080, [4, 18]), (-15360, [6, 16])]

def node78Piece131Output_sector0 : RawPoly ℕ := [node78Piece131Output_sector0_chunk0, node78Piece131Output_sector0_chunk1].flatten

def node78Piece131Output : SectorVector := [(0, node78Piece131Output_sector0)]

def node78Piece131UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 4, 4, 6])]

def node78Piece131UnitInput_sector0 : RawPoly ℕ := [node78Piece131UnitInput_sector0_chunk0].flatten

def node78Piece131UnitInput : SectorVector := [(0, node78Piece131UnitInput_sector0)]

def node78Piece131UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 4, 6]), (72, [1, 1, 3, 4, 4, 9]), (96, [1, 1, 3, 4, 6, 7]), (36, [1, 1, 4, 4, 6, 6]), (144, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 6, 6]), (72, [1, 2, 4, 4, 5, 6]), (144, [1, 3, 3, 4, 4, 7]), (192, [1, 3, 3, 4, 5, 6]), (306, [1, 3, 4, 4, 4, 6]), (72, [1, 3, 4, 4, 5, 5]), (1152, [1, 3, 4, 14]), (384, [1, 3, 6, 12]), (432, [1, 4, 4, 13]), (576, [1, 4, 6, 11]), (72, [2, 2, 3, 4, 4, 7]), (96, [2, 2, 3, 4, 5, 6]), (36, [2, 2, 4, 4, 4, 6]), (376, [2, 3, 3, 4, 4, 6]), (144, [2, 3, 4, 4, 4, 5]), (1152, [2, 3, 4, 13]), (384, [2, 3, 6, 11]), (432, [2, 4, 4, 12]), (576, [2, 4, 6, 10])]

def node78Piece131UnitOutput_sector0_chunk1 : RawPoly ℕ := [(32, [3, 3, 3, 3, 4, 6]), (72, [3, 3, 3, 4, 4, 5]), (72, [3, 3, 4, 4, 4, 4]), (1152, [3, 3, 4, 12]), (384, [3, 3, 6, 10]), (-552, [3, 4, 4, 11]), (1152, [3, 4, 5, 10]), (464, [3, 4, 6, 9]), (1152, [3, 4, 7, 8]), (384, [3, 5, 6, 8]), (384, [3, 6, 6, 7]), (2304, [3, 19]), (432, [4, 4, 4, 10]), (432, [4, 4, 5, 9]), (570, [4, 4, 6, 8]), (216, [4, 4, 7, 7]), (576, [4, 5, 6, 7]), (288, [4, 6, 6, 6]), (3456, [4, 18]), (1152, [6, 16])]

def node78Piece131UnitOutput_sector0 : RawPoly ℕ := [node78Piece131UnitOutput_sector0_chunk0, node78Piece131UnitOutput_sector0_chunk1].flatten

def node78Piece131UnitOutput : SectorVector := [(0, node78Piece131UnitOutput_sector0)]

theorem node78Piece131_check : VectorCertificate (neutralBoundS JR (-2) node78Piece131UnitInput) node78Piece131UnitOutput := by decide +kernel

theorem node78Piece131_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece131Input) = evaluate node78Piece131Output :=
  mode_of_scaled _ _ (-40/3) node78Piece131UnitInput node78Piece131UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece131_check)

def node78Piece132Input_sector0 : RawPoly ℕ := [(128/5, [3, 4, 5, 5])]

def node78Piece132Input : SectorVector := [(0, node78Piece132Input_sector0)]
def node78Piece132Output_sector0_chunk0 : RawPoly ℕ := [(512/5, [1, 1, 1, 2, 3, 4, 5, 5]), (3072, [1, 1, 3, 4, 5, 8]), (6144/5, [1, 1, 3, 5, 5, 7]), (4608/5, [1, 1, 4, 5, 5, 6]), (6144, [1, 2, 3, 4, 5, 7]), (12288/5, [1, 2, 3, 5, 5, 6]), (9216/5, [1, 2, 4, 5, 5, 5]), (6144, [1, 3, 3, 4, 5, 6]), (12288/5, [1, 3, 3, 5, 5, 5]), (45312/5, [1, 3, 4, 4, 5, 5]), (15360, [1, 3, 4, 14]), (24576, [1, 3, 5, 13]), (18432, [1, 4, 5, 12]), (36864/5, [1, 5, 5, 11]), (3072, [2, 2, 3, 4, 5, 6]), (6144/5, [2, 2, 3, 5, 5, 5]), (4608/5, [2, 2, 4, 4, 5, 5]), (48128/5, [2, 3, 3, 4, 5, 5]), (3072, [2, 3, 4, 4, 4, 5]), (15360, [2, 3, 4, 13]), (24576, [2, 3, 5, 12]), (18432, [2, 4, 5, 11]), (36864/5, [2, 5, 5, 10]), (2048/5, [3, 3, 3, 3, 5, 5])]

def node78Piece132Output_sector0_chunk1 : RawPoly ℕ := [(3072, [3, 3, 3, 4, 4, 5]), (15360, [3, 3, 4, 12]), (24576, [3, 3, 5, 11]), (15360, [3, 4, 4, 11]), (-12288, [3, 4, 5, 10]), (15360, [3, 4, 6, 9]), (15360, [3, 4, 7, 8]), (54272/5, [3, 5, 5, 9]), (24576, [3, 5, 6, 8]), (12288, [3, 5, 7, 7]), (61440, [3, 19]), (18432, [4, 4, 5, 9]), (14592, [4, 5, 5, 8]), (18432, [4, 5, 6, 7]), (46080, [4, 18]), (36864/5, [5, 5, 5, 7]), (18432/5, [5, 5, 6, 6]), (73728, [5, 17])]

def node78Piece132Output_sector0 : RawPoly ℕ := [node78Piece132Output_sector0_chunk0, node78Piece132Output_sector0_chunk1].flatten

def node78Piece132Output : SectorVector := [(0, node78Piece132Output_sector0)]

def node78Piece132UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 4, 5, 5])]

def node78Piece132UnitInput_sector0 : RawPoly ℕ := [node78Piece132UnitInput_sector0_chunk0].flatten

def node78Piece132UnitInput : SectorVector := [(0, node78Piece132UnitInput_sector0)]

def node78Piece132UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 5, 5]), (120, [1, 1, 3, 4, 5, 8]), (48, [1, 1, 3, 5, 5, 7]), (36, [1, 1, 4, 5, 5, 6]), (240, [1, 2, 3, 4, 5, 7]), (96, [1, 2, 3, 5, 5, 6]), (72, [1, 2, 4, 5, 5, 5]), (240, [1, 3, 3, 4, 5, 6]), (96, [1, 3, 3, 5, 5, 5]), (354, [1, 3, 4, 4, 5, 5]), (600, [1, 3, 4, 14]), (960, [1, 3, 5, 13]), (720, [1, 4, 5, 12]), (288, [1, 5, 5, 11]), (120, [2, 2, 3, 4, 5, 6]), (48, [2, 2, 3, 5, 5, 5]), (36, [2, 2, 4, 4, 5, 5]), (376, [2, 3, 3, 4, 5, 5]), (120, [2, 3, 4, 4, 4, 5]), (600, [2, 3, 4, 13]), (960, [2, 3, 5, 12]), (720, [2, 4, 5, 11]), (288, [2, 5, 5, 10]), (16, [3, 3, 3, 3, 5, 5])]

def node78Piece132UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [3, 3, 3, 4, 4, 5]), (600, [3, 3, 4, 12]), (960, [3, 3, 5, 11]), (600, [3, 4, 4, 11]), (-480, [3, 4, 5, 10]), (600, [3, 4, 6, 9]), (600, [3, 4, 7, 8]), (424, [3, 5, 5, 9]), (960, [3, 5, 6, 8]), (480, [3, 5, 7, 7]), (2400, [3, 19]), (720, [4, 4, 5, 9]), (570, [4, 5, 5, 8]), (720, [4, 5, 6, 7]), (1800, [4, 18]), (288, [5, 5, 5, 7]), (144, [5, 5, 6, 6]), (2880, [5, 17])]

def node78Piece132UnitOutput_sector0 : RawPoly ℕ := [node78Piece132UnitOutput_sector0_chunk0, node78Piece132UnitOutput_sector0_chunk1].flatten

def node78Piece132UnitOutput : SectorVector := [(0, node78Piece132UnitOutput_sector0)]

theorem node78Piece132_check : VectorCertificate (neutralBoundS JR (-2) node78Piece132UnitInput) node78Piece132UnitOutput := by decide +kernel

theorem node78Piece132_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece132Input) = evaluate node78Piece132Output :=
  mode_of_scaled _ _ (128/5) node78Piece132UnitInput node78Piece132UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece132_check)

def node78Piece133Input_sector0 : RawPoly ℕ := [(480/7, [3, 14])]

def node78Piece133Input : SectorVector := [(0, node78Piece133Input_sector0)]
def node78Piece133Output_sector0_chunk0 : RawPoly ℕ := [(1920/7, [1, 1, 1, 2, 3, 14]), (11520, [1, 1, 3, 17]), (17280/7, [1, 1, 6, 14]), (23040, [1, 2, 3, 16]), (34560/7, [1, 2, 5, 14]), (23040, [1, 3, 3, 15]), (192960/7, [1, 3, 4, 14]), (23040, [1, 3, 5, 13]), (23040, [1, 3, 6, 12]), (23040, [1, 3, 7, 11]), (23040, [1, 3, 8, 10]), (11520, [1, 3, 9, 9]), (69120, [1, 21]), (11520, [2, 2, 3, 15]), (17280/7, [2, 2, 4, 14]), (180480/7, [2, 3, 3, 14]), (23040, [2, 3, 4, 13]), (23040, [2, 3, 5, 12]), (23040, [2, 3, 6, 11]), (23040, [2, 3, 7, 10]), (23040, [2, 3, 8, 9]), (69120, [2, 20]), (11520, [3, 3, 3, 13]), (23040, [3, 3, 4, 12])]

def node78Piece133Output_sector0_chunk1 : RawPoly ℕ := [(23040, [3, 3, 5, 11]), (23040, [3, 3, 6, 10]), (23040, [3, 3, 7, 9]), (11520, [3, 3, 8, 8]), (11520, [3, 4, 4, 11]), (23040, [3, 4, 5, 10]), (23040, [3, 4, 6, 9]), (23040, [3, 4, 7, 8]), (11520, [3, 5, 5, 9]), (23040, [3, 5, 6, 8]), (11520, [3, 5, 7, 7]), (11520, [3, 6, 6, 7]), (-1232640, [3, 19]), (69120, [4, 18]), (69120, [5, 17]), (69120, [6, 16]), (69120, [7, 15]), (273600/7, [8, 14]), (69120, [9, 13]), (69120, [10, 12]), (34560, [11, 11])]

def node78Piece133Output_sector0 : RawPoly ℕ := [node78Piece133Output_sector0_chunk0, node78Piece133Output_sector0_chunk1].flatten

def node78Piece133Output : SectorVector := [(0, node78Piece133Output_sector0)]

def node78Piece133UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 14])]

def node78Piece133UnitInput_sector0 : RawPoly ℕ := [node78Piece133UnitInput_sector0_chunk0].flatten

def node78Piece133UnitInput : SectorVector := [(0, node78Piece133UnitInput_sector0)]

def node78Piece133UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 14]), (168, [1, 1, 3, 17]), (36, [1, 1, 6, 14]), (336, [1, 2, 3, 16]), (72, [1, 2, 5, 14]), (336, [1, 3, 3, 15]), (402, [1, 3, 4, 14]), (336, [1, 3, 5, 13]), (336, [1, 3, 6, 12]), (336, [1, 3, 7, 11]), (336, [1, 3, 8, 10]), (168, [1, 3, 9, 9]), (1008, [1, 21]), (168, [2, 2, 3, 15]), (36, [2, 2, 4, 14]), (376, [2, 3, 3, 14]), (336, [2, 3, 4, 13]), (336, [2, 3, 5, 12]), (336, [2, 3, 6, 11]), (336, [2, 3, 7, 10]), (336, [2, 3, 8, 9]), (1008, [2, 20]), (168, [3, 3, 3, 13]), (336, [3, 3, 4, 12])]

def node78Piece133UnitOutput_sector0_chunk1 : RawPoly ℕ := [(336, [3, 3, 5, 11]), (336, [3, 3, 6, 10]), (336, [3, 3, 7, 9]), (168, [3, 3, 8, 8]), (168, [3, 4, 4, 11]), (336, [3, 4, 5, 10]), (336, [3, 4, 6, 9]), (336, [3, 4, 7, 8]), (168, [3, 5, 5, 9]), (336, [3, 5, 6, 8]), (168, [3, 5, 7, 7]), (168, [3, 6, 6, 7]), (-17976, [3, 19]), (1008, [4, 18]), (1008, [5, 17]), (1008, [6, 16]), (1008, [7, 15]), (570, [8, 14]), (1008, [9, 13]), (1008, [10, 12]), (504, [11, 11])]

def node78Piece133UnitOutput_sector0 : RawPoly ℕ := [node78Piece133UnitOutput_sector0_chunk0, node78Piece133UnitOutput_sector0_chunk1].flatten

def node78Piece133UnitOutput : SectorVector := [(0, node78Piece133UnitOutput_sector0)]

theorem node78Piece133_check : VectorCertificate (neutralBoundS JR (-2) node78Piece133UnitInput) node78Piece133UnitOutput := by decide +kernel

theorem node78Piece133_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece133Input) = evaluate node78Piece133Output :=
  mode_of_scaled _ _ (480/7) node78Piece133UnitInput node78Piece133UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece133_check)

def node78Piece134Input_sector0 : RawPoly ℕ := [(-22, [4, 4, 4, 5])]

def node78Piece134Input : SectorVector := [(0, node78Piece134Input_sector0)]
def node78Piece134Output_sector0_chunk0 : RawPoly ℕ := [(-88, [1, 1, 1, 2, 4, 4, 4, 5]), (-1320, [1, 1, 4, 4, 4, 8]), (-3168, [1, 1, 4, 4, 5, 7]), (-2640, [1, 2, 4, 4, 4, 7]), (-6336, [1, 2, 4, 4, 5, 6]), (-2640, [1, 3, 4, 4, 4, 6]), (-6336, [1, 3, 4, 4, 5, 5]), (-5676, [1, 4, 4, 4, 4, 5]), (-31680, [1, 4, 4, 13]), (-25344, [1, 4, 5, 12]), (-1320, [2, 2, 4, 4, 4, 6]), (-3168, [2, 2, 4, 4, 5, 5]), (-9064, [2, 3, 4, 4, 4, 5]), (-1320, [2, 4, 4, 4, 4, 4]), (-31680, [2, 4, 4, 12]), (-25344, [2, 4, 5, 11]), (-1056, [3, 3, 3, 4, 4, 5]), (-1320, [3, 3, 4, 4, 4, 4]), (-31680, [3, 4, 4, 11]), (-25344, [3, 4, 5, 10]), (-1320, [4, 4, 4, 10]), (-2640, [4, 4, 5, 9]), (-31680, [4, 4, 6, 8]), (-15840, [4, 4, 7, 7])]

def node78Piece134Output_sector0_chunk1 : RawPoly ℕ := [(-25344, [4, 5, 5, 8]), (-25344, [4, 5, 6, 7]), (-126720, [4, 18]), (-33792, [5, 17])]

def node78Piece134Output_sector0 : RawPoly ℕ := [node78Piece134Output_sector0_chunk0, node78Piece134Output_sector0_chunk1].flatten

def node78Piece134Output : SectorVector := [(0, node78Piece134Output_sector0)]

def node78Piece134UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 4, 4, 5])]

def node78Piece134UnitInput_sector0 : RawPoly ℕ := [node78Piece134UnitInput_sector0_chunk0].flatten

def node78Piece134UnitInput : SectorVector := [(0, node78Piece134UnitInput_sector0)]

def node78Piece134UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 4, 4, 4, 5]), (60, [1, 1, 4, 4, 4, 8]), (144, [1, 1, 4, 4, 5, 7]), (120, [1, 2, 4, 4, 4, 7]), (288, [1, 2, 4, 4, 5, 6]), (120, [1, 3, 4, 4, 4, 6]), (288, [1, 3, 4, 4, 5, 5]), (258, [1, 4, 4, 4, 4, 5]), (1440, [1, 4, 4, 13]), (1152, [1, 4, 5, 12]), (60, [2, 2, 4, 4, 4, 6]), (144, [2, 2, 4, 4, 5, 5]), (412, [2, 3, 4, 4, 4, 5]), (60, [2, 4, 4, 4, 4, 4]), (1440, [2, 4, 4, 12]), (1152, [2, 4, 5, 11]), (48, [3, 3, 3, 4, 4, 5]), (60, [3, 3, 4, 4, 4, 4]), (1440, [3, 4, 4, 11]), (1152, [3, 4, 5, 10]), (60, [4, 4, 4, 10]), (120, [4, 4, 5, 9]), (1440, [4, 4, 6, 8]), (720, [4, 4, 7, 7])]

def node78Piece134UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1152, [4, 5, 5, 8]), (1152, [4, 5, 6, 7]), (5760, [4, 18]), (1536, [5, 17])]

def node78Piece134UnitOutput_sector0 : RawPoly ℕ := [node78Piece134UnitOutput_sector0_chunk0, node78Piece134UnitOutput_sector0_chunk1].flatten

def node78Piece134UnitOutput : SectorVector := [(0, node78Piece134UnitOutput_sector0)]

theorem node78Piece134_check : VectorCertificate (neutralBoundS JR (-2) node78Piece134UnitInput) node78Piece134UnitOutput := by decide +kernel

theorem node78Piece134_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece134Input) = evaluate node78Piece134Output :=
  mode_of_scaled _ _ (-22) node78Piece134UnitInput node78Piece134UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece134_check)

def node78Piece135Input_sector0 : RawPoly ℕ := [(-480/13, [4, 13])]

def node78Piece135Input : SectorVector := [(0, node78Piece135Input_sector0)]
def node78Piece135Output_sector0_chunk0 : RawPoly ℕ := [(-1920/13, [1, 1, 1, 2, 4, 13]), (-5760, [1, 1, 4, 16]), (-23040/13, [1, 1, 7, 13]), (-11520, [1, 2, 4, 15]), (-46080/13, [1, 2, 6, 13]), (-11520, [1, 3, 4, 14]), (-46080/13, [1, 3, 5, 13]), (-169920/13, [1, 4, 4, 13]), (-11520, [1, 4, 5, 12]), (-11520, [1, 4, 6, 11]), (-11520, [1, 4, 7, 10]), (-11520, [1, 4, 8, 9]), (-46080, [1, 21]), (-5760, [2, 2, 4, 14]), (-23040/13, [2, 2, 5, 13]), (-197760/13, [2, 3, 4, 13]), (-11520, [2, 4, 4, 12]), (-11520, [2, 4, 5, 11]), (-11520, [2, 4, 6, 10]), (-11520, [2, 4, 7, 9]), (-5760, [2, 4, 8, 8]), (-46080, [2, 20]), (-7680/13, [3, 3, 3, 13]), (-5760, [3, 3, 4, 12])]

def node78Piece135Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-11520, [3, 4, 7, 8]), (-46080, [3, 19]), (-5760, [4, 4, 4, 10]), (-11520, [4, 4, 5, 9]), (-11520, [4, 4, 6, 8]), (-5760, [4, 4, 7, 7]), (-5760, [4, 5, 5, 8]), (-11520, [4, 5, 6, 7]), (-1920, [4, 6, 6, 6]), (528000, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-46080, [8, 14]), (-203520/13, [9, 13]), (-46080, [10, 12]), (-23040, [11, 11])]

def node78Piece135Output_sector0 : RawPoly ℕ := [node78Piece135Output_sector0_chunk0, node78Piece135Output_sector0_chunk1].flatten

def node78Piece135Output : SectorVector := [(0, node78Piece135Output_sector0)]

def node78Piece135UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 13])]

def node78Piece135UnitInput_sector0 : RawPoly ℕ := [node78Piece135UnitInput_sector0_chunk0].flatten

def node78Piece135UnitInput : SectorVector := [(0, node78Piece135UnitInput_sector0)]

def node78Piece135UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 4, 13]), (156, [1, 1, 4, 16]), (48, [1, 1, 7, 13]), (312, [1, 2, 4, 15]), (96, [1, 2, 6, 13]), (312, [1, 3, 4, 14]), (96, [1, 3, 5, 13]), (354, [1, 4, 4, 13]), (312, [1, 4, 5, 12]), (312, [1, 4, 6, 11]), (312, [1, 4, 7, 10]), (312, [1, 4, 8, 9]), (1248, [1, 21]), (156, [2, 2, 4, 14]), (48, [2, 2, 5, 13]), (412, [2, 3, 4, 13]), (312, [2, 4, 4, 12]), (312, [2, 4, 5, 11]), (312, [2, 4, 6, 10]), (312, [2, 4, 7, 9]), (156, [2, 4, 8, 8]), (1248, [2, 20]), (16, [3, 3, 3, 13]), (156, [3, 3, 4, 12])]

def node78Piece135UnitOutput_sector0_chunk1 : RawPoly ℕ := [(312, [3, 4, 4, 11]), (312, [3, 4, 5, 10]), (312, [3, 4, 6, 9]), (312, [3, 4, 7, 8]), (1248, [3, 19]), (156, [4, 4, 4, 10]), (312, [4, 4, 5, 9]), (312, [4, 4, 6, 8]), (156, [4, 4, 7, 7]), (156, [4, 5, 5, 8]), (312, [4, 5, 6, 7]), (52, [4, 6, 6, 6]), (-14300, [4, 18]), (1248, [5, 17]), (1248, [6, 16]), (1248, [7, 15]), (1248, [8, 14]), (424, [9, 13]), (1248, [10, 12]), (624, [11, 11])]

def node78Piece135UnitOutput_sector0 : RawPoly ℕ := [node78Piece135UnitOutput_sector0_chunk0, node78Piece135UnitOutput_sector0_chunk1].flatten

def node78Piece135UnitOutput : SectorVector := [(0, node78Piece135UnitOutput_sector0)]

theorem node78Piece135_check : VectorCertificate (neutralBoundS JR (-2) node78Piece135UnitInput) node78Piece135UnitOutput := by decide +kernel

theorem node78Piece135_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece135Input) = evaluate node78Piece135Output :=
  mode_of_scaled _ _ (-480/13) node78Piece135UnitInput node78Piece135UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece135_check)

def node78Piece136Input_sector0 : RawPoly ℕ := [(8, [5, 12])]

def node78Piece136Input : SectorVector := [(0, node78Piece136Input_sector0)]
def node78Piece136Output_sector0_chunk0 : RawPoly ℕ := [(32, [1, 1, 1, 2, 5, 12]), (1152, [1, 1, 5, 15]), (480, [1, 1, 8, 12]), (2304, [1, 2, 5, 14]), (960, [1, 2, 7, 12]), (2304, [1, 3, 5, 13]), (960, [1, 3, 6, 12]), (3216, [1, 4, 5, 12]), (2304, [1, 5, 5, 11]), (2304, [1, 5, 6, 10]), (2304, [1, 5, 7, 9]), (1152, [1, 5, 8, 8]), (11520, [1, 21]), (1152, [2, 2, 5, 13]), (480, [2, 2, 6, 12]), (3296, [2, 3, 5, 12]), (480, [2, 4, 4, 12]), (2304, [2, 4, 5, 11]), (2304, [2, 5, 5, 10]), (2304, [2, 5, 6, 9]), (2304, [2, 5, 7, 8]), (11520, [2, 20]), (480, [3, 3, 4, 12]), (1152, [3, 3, 5, 11])]

def node78Piece136Output_sector0_chunk1 : RawPoly ℕ := [(2304, [3, 4, 5, 10]), (2304, [3, 5, 5, 9]), (2304, [3, 5, 6, 8]), (1152, [3, 5, 7, 7]), (11520, [3, 19]), (1152, [4, 4, 5, 9]), (2304, [4, 5, 5, 8]), (2304, [4, 5, 6, 7]), (11520, [4, 18]), (1152, [5, 5, 5, 7]), (1152, [5, 5, 6, 6]), (-88896, [5, 17]), (11520, [6, 16]), (11520, [7, 15]), (11520, [8, 14]), (11520, [9, 13]), (480, [10, 12]), (5760, [11, 11])]

def node78Piece136Output_sector0 : RawPoly ℕ := [node78Piece136Output_sector0_chunk0, node78Piece136Output_sector0_chunk1].flatten

def node78Piece136Output : SectorVector := [(0, node78Piece136Output_sector0)]

def node78Piece136UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 12])]

def node78Piece136UnitInput_sector0 : RawPoly ℕ := [node78Piece136UnitInput_sector0_chunk0].flatten

def node78Piece136UnitInput : SectorVector := [(0, node78Piece136UnitInput_sector0)]

def node78Piece136UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 5, 12]), (144, [1, 1, 5, 15]), (60, [1, 1, 8, 12]), (288, [1, 2, 5, 14]), (120, [1, 2, 7, 12]), (288, [1, 3, 5, 13]), (120, [1, 3, 6, 12]), (402, [1, 4, 5, 12]), (288, [1, 5, 5, 11]), (288, [1, 5, 6, 10]), (288, [1, 5, 7, 9]), (144, [1, 5, 8, 8]), (1440, [1, 21]), (144, [2, 2, 5, 13]), (60, [2, 2, 6, 12]), (412, [2, 3, 5, 12]), (60, [2, 4, 4, 12]), (288, [2, 4, 5, 11]), (288, [2, 5, 5, 10]), (288, [2, 5, 6, 9]), (288, [2, 5, 7, 8]), (1440, [2, 20]), (60, [3, 3, 4, 12]), (144, [3, 3, 5, 11])]

def node78Piece136UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [3, 4, 5, 10]), (288, [3, 5, 5, 9]), (288, [3, 5, 6, 8]), (144, [3, 5, 7, 7]), (1440, [3, 19]), (144, [4, 4, 5, 9]), (288, [4, 5, 5, 8]), (288, [4, 5, 6, 7]), (1440, [4, 18]), (144, [5, 5, 5, 7]), (144, [5, 5, 6, 6]), (-11112, [5, 17]), (1440, [6, 16]), (1440, [7, 15]), (1440, [8, 14]), (1440, [9, 13]), (60, [10, 12]), (720, [11, 11])]

def node78Piece136UnitOutput_sector0 : RawPoly ℕ := [node78Piece136UnitOutput_sector0_chunk0, node78Piece136UnitOutput_sector0_chunk1].flatten

def node78Piece136UnitOutput : SectorVector := [(0, node78Piece136UnitOutput_sector0)]

theorem node78Piece136_check : VectorCertificate (neutralBoundS JR (-2) node78Piece136UnitInput) node78Piece136UnitOutput := by decide +kernel

theorem node78Piece136_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece136Input) = evaluate node78Piece136Output :=
  mode_of_scaled _ _ (8) node78Piece136UnitInput node78Piece136UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece136_check)

def node78Piece137Input_sector0 : RawPoly ℕ := [(2310, [0, 1])]

def node78Piece137Input : SectorVector := [(2, node78Piece137Input_sector0)]
def node78Piece137Output_sector0 : RawPoly ℕ := [(9240, [0, 1, 1, 1, 1, 2]), (900900, [0, 1, 1, 4]), (951720, [0, 1, 2, 3]), (9240, [0, 2, 2, 2]), (757680, [0, 6]), (443520, [1, 1, 1, 3]), (443520, [1, 1, 2, 2]), (4656960, [1, 5]), (887040, [2, 4]), (443520, [3, 3])]

def node78Piece137Output : SectorVector := [(2, node78Piece137Output_sector0)]

def node78Piece137UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1])]

def node78Piece137UnitInput_sector0 : RawPoly ℕ := [node78Piece137UnitInput_sector0_chunk0].flatten

def node78Piece137UnitInput : SectorVector := [(2, node78Piece137UnitInput_sector0)]

def node78Piece137UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2]), (390, [0, 1, 1, 4]), (412, [0, 1, 2, 3]), (4, [0, 2, 2, 2]), (328, [0, 6]), (192, [1, 1, 1, 3]), (192, [1, 1, 2, 2]), (2016, [1, 5]), (384, [2, 4]), (192, [3, 3])]

def node78Piece137UnitOutput_sector0 : RawPoly ℕ := [node78Piece137UnitOutput_sector0_chunk0].flatten

def node78Piece137UnitOutput : SectorVector := [(2, node78Piece137UnitOutput_sector0)]

theorem node78Piece137_check : VectorCertificate (neutralBoundS JR (-2) node78Piece137UnitInput) node78Piece137UnitOutput := by decide +kernel

theorem node78Piece137_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece137Input) = evaluate node78Piece137Output :=
  mode_of_scaled _ _ (2310) node78Piece137UnitInput node78Piece137UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece137_check)

end VOA.Classification.COne.OrbC2h
