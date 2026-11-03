import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch81_0
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

def node81Piece32Input_sector0 : RawPoly ℕ := [(400/3, [2, 3, 3, 4])]

def node81Piece32Input : SectorVector := [(0, node81Piece32Input_sector0)]
def node81Piece32Output_sector0_chunk0 : RawPoly ℕ := [(1600/3, [1, 1, 1, 2, 3, 3, 4, 7]), (1600, [1, 1, 2, 2, 3, 3, 4, 6]), (1600, [1, 1, 2, 3, 3, 3, 4, 5]), (800, [1, 1, 2, 3, 3, 4, 4, 4]), (6400, [1, 1, 2, 3, 3, 12]), (9600, [1, 1, 2, 3, 4, 11]), (3200, [1, 1, 3, 3, 4, 10]), (1600, [1, 2, 2, 2, 3, 3, 4, 5]), (3200, [1, 2, 2, 3, 3, 3, 4, 4]), (12800, [1, 2, 2, 3, 3, 11]), (19200, [1, 2, 2, 3, 4, 10]), (1600/3, [1, 2, 3, 3, 3, 3, 3, 4]), (12800, [1, 2, 3, 3, 3, 10]), (92800/3, [1, 2, 3, 3, 4, 9]), (12800, [1, 2, 3, 3, 5, 8]), (12800, [1, 2, 3, 3, 6, 7]), (19200, [1, 2, 3, 4, 4, 8]), (19200, [1, 2, 3, 4, 5, 7]), (9600, [1, 2, 3, 4, 6, 6]), (76800, [1, 2, 3, 16]), (28800, [1, 2, 4, 15]), (6400, [1, 3, 3, 3, 4, 8]), (6400, [1, 3, 3, 4, 4, 7]), (6400, [1, 3, 3, 4, 5, 6])]

def node81Piece32Output_sector0_chunk1 : RawPoly ℕ := [(25600, [1, 3, 3, 15]), (38400, [1, 3, 4, 14]), (1600/3, [2, 2, 2, 2, 3, 3, 4, 4]), (800, [2, 2, 2, 3, 3, 3, 3, 4]), (6400, [2, 2, 2, 3, 3, 10]), (9600, [2, 2, 2, 3, 4, 9]), (12800, [2, 2, 3, 3, 3, 9]), (32400, [2, 2, 3, 3, 4, 8]), (12800, [2, 2, 3, 3, 5, 7]), (6400, [2, 2, 3, 3, 6, 6]), (19200, [2, 2, 3, 4, 4, 7]), (19200, [2, 2, 3, 4, 5, 6]), (76800, [2, 2, 3, 15]), (28800, [2, 2, 4, 14]), (6400, [2, 3, 3, 3, 3, 8]), (88000/3, [2, 3, 3, 3, 4, 7]), (12800, [2, 3, 3, 3, 5, 6]), (103600/3, [2, 3, 3, 4, 4, 6]), (20800, [2, 3, 3, 4, 5, 5]), (-100800, [2, 3, 3, 14]), (9600, [2, 3, 4, 4, 4, 5]), (-92800, [2, 3, 4, 13]), (76800, [2, 3, 5, 12]), (76800, [2, 3, 6, 11])]

def node81Piece32Output_sector0_chunk2 : RawPoly ℕ := [(76800, [2, 3, 7, 10]), (76800, [2, 3, 8, 9]), (28800, [2, 4, 4, 12]), (28800, [2, 4, 5, 11]), (28800, [2, 4, 6, 10]), (28800, [2, 4, 7, 9]), (14400, [2, 4, 8, 8]), (115200, [2, 20]), (3200, [3, 3, 3, 3, 4, 6]), (6400, [3, 3, 3, 4, 4, 5]), (25600, [3, 3, 3, 13]), (3200/3, [3, 3, 4, 4, 4, 4]), (15200/3, [3, 3, 4, 12]), (25600, [3, 3, 5, 11]), (25600, [3, 3, 6, 10]), (25600, [3, 3, 7, 9]), (12800, [3, 3, 8, 8]), (38400, [3, 4, 4, 11]), (38400, [3, 4, 5, 10]), (38400, [3, 4, 6, 9]), (38400, [3, 4, 7, 8]), (153600, [3, 19]), (57600, [4, 18])]

def node81Piece32Output_sector0 : RawPoly ℕ := [node81Piece32Output_sector0_chunk0, node81Piece32Output_sector0_chunk1, node81Piece32Output_sector0_chunk2].flatten

def node81Piece32Output : SectorVector := [(0, node81Piece32Output_sector0)]

def node81Piece32UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 4])]

def node81Piece32UnitInput_sector0 : RawPoly ℕ := [node81Piece32UnitInput_sector0_chunk0].flatten

def node81Piece32UnitInput : SectorVector := [(0, node81Piece32UnitInput_sector0)]

def node81Piece32UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 7]), (12, [1, 1, 2, 2, 3, 3, 4, 6]), (12, [1, 1, 2, 3, 3, 3, 4, 5]), (6, [1, 1, 2, 3, 3, 4, 4, 4]), (48, [1, 1, 2, 3, 3, 12]), (72, [1, 1, 2, 3, 4, 11]), (24, [1, 1, 3, 3, 4, 10]), (12, [1, 2, 2, 2, 3, 3, 4, 5]), (24, [1, 2, 2, 3, 3, 3, 4, 4]), (96, [1, 2, 2, 3, 3, 11]), (144, [1, 2, 2, 3, 4, 10]), (4, [1, 2, 3, 3, 3, 3, 3, 4]), (96, [1, 2, 3, 3, 3, 10]), (232, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 5, 8]), (96, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 4, 8]), (144, [1, 2, 3, 4, 5, 7]), (72, [1, 2, 3, 4, 6, 6]), (576, [1, 2, 3, 16]), (216, [1, 2, 4, 15]), (48, [1, 3, 3, 3, 4, 8]), (48, [1, 3, 3, 4, 4, 7]), (48, [1, 3, 3, 4, 5, 6])]

def node81Piece32UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [1, 3, 3, 15]), (288, [1, 3, 4, 14]), (4, [2, 2, 2, 2, 3, 3, 4, 4]), (6, [2, 2, 2, 3, 3, 3, 3, 4]), (48, [2, 2, 2, 3, 3, 10]), (72, [2, 2, 2, 3, 4, 9]), (96, [2, 2, 3, 3, 3, 9]), (243, [2, 2, 3, 3, 4, 8]), (96, [2, 2, 3, 3, 5, 7]), (48, [2, 2, 3, 3, 6, 6]), (144, [2, 2, 3, 4, 4, 7]), (144, [2, 2, 3, 4, 5, 6]), (576, [2, 2, 3, 15]), (216, [2, 2, 4, 14]), (48, [2, 3, 3, 3, 3, 8]), (220, [2, 3, 3, 3, 4, 7]), (96, [2, 3, 3, 3, 5, 6]), (259, [2, 3, 3, 4, 4, 6]), (156, [2, 3, 3, 4, 5, 5]), (-756, [2, 3, 3, 14]), (72, [2, 3, 4, 4, 4, 5]), (-696, [2, 3, 4, 13]), (576, [2, 3, 5, 12]), (576, [2, 3, 6, 11])]

def node81Piece32UnitOutput_sector0_chunk2 : RawPoly ℕ := [(576, [2, 3, 7, 10]), (576, [2, 3, 8, 9]), (216, [2, 4, 4, 12]), (216, [2, 4, 5, 11]), (216, [2, 4, 6, 10]), (216, [2, 4, 7, 9]), (108, [2, 4, 8, 8]), (864, [2, 20]), (24, [3, 3, 3, 3, 4, 6]), (48, [3, 3, 3, 4, 4, 5]), (192, [3, 3, 3, 13]), (8, [3, 3, 4, 4, 4, 4]), (38, [3, 3, 4, 12]), (192, [3, 3, 5, 11]), (192, [3, 3, 6, 10]), (192, [3, 3, 7, 9]), (96, [3, 3, 8, 8]), (288, [3, 4, 4, 11]), (288, [3, 4, 5, 10]), (288, [3, 4, 6, 9]), (288, [3, 4, 7, 8]), (1152, [3, 19]), (432, [4, 18])]

def node81Piece32UnitOutput_sector0 : RawPoly ℕ := [node81Piece32UnitOutput_sector0_chunk0, node81Piece32UnitOutput_sector0_chunk1, node81Piece32UnitOutput_sector0_chunk2].flatten

def node81Piece32UnitOutput : SectorVector := [(0, node81Piece32UnitOutput_sector0)]

theorem node81Piece32_check : VectorCertificate (neutralBoundS JR (-7) node81Piece32UnitInput) node81Piece32UnitOutput := by decide +kernel

theorem node81Piece32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece32Input) = evaluate node81Piece32Output :=
  mode_of_scaled _ _ (400/3) node81Piece32UnitInput node81Piece32UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece32_check)

def node81Piece33Input_sector0 : RawPoly ℕ := [(-96, [2, 10])]

def node81Piece33Input : SectorVector := [(0, node81Piece33Input_sector0)]
def node81Piece33Output_sector0_chunk0 : RawPoly ℕ := [(-384, [1, 1, 1, 2, 7, 10]), (-1152, [1, 1, 2, 2, 6, 10]), (-1152, [1, 1, 2, 3, 5, 10]), (-576, [1, 1, 2, 4, 4, 10]), (-11520, [1, 1, 2, 18]), (-2304, [1, 1, 10, 10]), (-1152, [1, 2, 2, 2, 5, 10]), (-2304, [1, 2, 2, 3, 4, 10]), (-23040, [1, 2, 2, 17]), (-384, [1, 2, 3, 3, 3, 10]), (-23040, [1, 2, 3, 16]), (-23040, [1, 2, 4, 15]), (-23040, [1, 2, 5, 14]), (-23040, [1, 2, 6, 13]), (-23040, [1, 2, 7, 12]), (-23040, [1, 2, 8, 11]), (-22272, [1, 2, 9, 10]), (-4608, [1, 3, 8, 10]), (-4608, [1, 4, 7, 10]), (-4608, [1, 5, 6, 10]), (-46080, [1, 21]), (-384, [2, 2, 2, 2, 4, 10]), (-576, [2, 2, 2, 3, 3, 10]), (-11520, [2, 2, 2, 16])]

def node81Piece33Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 2, 3, 15]), (-23040, [2, 2, 4, 14]), (-23040, [2, 2, 5, 13]), (-23040, [2, 2, 6, 12]), (-23040, [2, 2, 7, 11]), (-23328, [2, 2, 8, 10]), (-11520, [2, 2, 9, 9]), (-11520, [2, 3, 3, 14]), (-23040, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12]), (-23040, [2, 3, 6, 11]), (-28032, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-11520, [2, 4, 4, 12]), (-23040, [2, 4, 5, 11]), (-29472, [2, 4, 6, 10]), (-23040, [2, 4, 7, 9]), (-11520, [2, 4, 8, 8]), (-14976, [2, 5, 5, 10]), (-23040, [2, 5, 6, 9]), (-23040, [2, 5, 7, 8]), (-11520, [2, 6, 6, 8]), (-11520, [2, 6, 7, 7]), (1010880, [2, 20])]

def node81Piece33Output_sector0_chunk2 : RawPoly ℕ := [(-2304, [3, 3, 6, 10]), (-4608, [3, 4, 5, 10]), (-46080, [3, 19]), (-768, [4, 4, 4, 10]), (-46080, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-46080, [8, 14]), (-46080, [9, 13]), (-3648, [10, 12]), (-23040, [11, 11])]

def node81Piece33Output_sector0 : RawPoly ℕ := [node81Piece33Output_sector0_chunk0, node81Piece33Output_sector0_chunk1, node81Piece33Output_sector0_chunk2].flatten

def node81Piece33Output : SectorVector := [(0, node81Piece33Output_sector0)]

def node81Piece33UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 10])]

def node81Piece33UnitInput_sector0 : RawPoly ℕ := [node81Piece33UnitInput_sector0_chunk0].flatten

def node81Piece33UnitInput : SectorVector := [(0, node81Piece33UnitInput_sector0)]

def node81Piece33UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 7, 10]), (12, [1, 1, 2, 2, 6, 10]), (12, [1, 1, 2, 3, 5, 10]), (6, [1, 1, 2, 4, 4, 10]), (120, [1, 1, 2, 18]), (24, [1, 1, 10, 10]), (12, [1, 2, 2, 2, 5, 10]), (24, [1, 2, 2, 3, 4, 10]), (240, [1, 2, 2, 17]), (4, [1, 2, 3, 3, 3, 10]), (240, [1, 2, 3, 16]), (240, [1, 2, 4, 15]), (240, [1, 2, 5, 14]), (240, [1, 2, 6, 13]), (240, [1, 2, 7, 12]), (240, [1, 2, 8, 11]), (232, [1, 2, 9, 10]), (48, [1, 3, 8, 10]), (48, [1, 4, 7, 10]), (48, [1, 5, 6, 10]), (480, [1, 21]), (4, [2, 2, 2, 2, 4, 10]), (6, [2, 2, 2, 3, 3, 10]), (120, [2, 2, 2, 16])]

def node81Piece33UnitOutput_sector0_chunk1 : RawPoly ℕ := [(240, [2, 2, 3, 15]), (240, [2, 2, 4, 14]), (240, [2, 2, 5, 13]), (240, [2, 2, 6, 12]), (240, [2, 2, 7, 11]), (243, [2, 2, 8, 10]), (120, [2, 2, 9, 9]), (120, [2, 3, 3, 14]), (240, [2, 3, 4, 13]), (240, [2, 3, 5, 12]), (240, [2, 3, 6, 11]), (292, [2, 3, 7, 10]), (240, [2, 3, 8, 9]), (120, [2, 4, 4, 12]), (240, [2, 4, 5, 11]), (307, [2, 4, 6, 10]), (240, [2, 4, 7, 9]), (120, [2, 4, 8, 8]), (156, [2, 5, 5, 10]), (240, [2, 5, 6, 9]), (240, [2, 5, 7, 8]), (120, [2, 6, 6, 8]), (120, [2, 6, 7, 7]), (-10530, [2, 20])]

def node81Piece33UnitOutput_sector0_chunk2 : RawPoly ℕ := [(24, [3, 3, 6, 10]), (48, [3, 4, 5, 10]), (480, [3, 19]), (8, [4, 4, 4, 10]), (480, [4, 18]), (480, [5, 17]), (480, [6, 16]), (480, [7, 15]), (480, [8, 14]), (480, [9, 13]), (38, [10, 12]), (240, [11, 11])]

def node81Piece33UnitOutput_sector0 : RawPoly ℕ := [node81Piece33UnitOutput_sector0_chunk0, node81Piece33UnitOutput_sector0_chunk1, node81Piece33UnitOutput_sector0_chunk2].flatten

def node81Piece33UnitOutput : SectorVector := [(0, node81Piece33UnitOutput_sector0)]

theorem node81Piece33_check : VectorCertificate (neutralBoundS JR (-7) node81Piece33UnitInput) node81Piece33UnitOutput := by decide +kernel

theorem node81Piece33_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece33Input) = evaluate node81Piece33Output :=
  mode_of_scaled _ _ (-96) node81Piece33UnitInput node81Piece33UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece33_check)

def node81Piece34Input_sector0 : RawPoly ℕ := [(1280/27, [3, 3, 3, 3])]

def node81Piece34Input : SectorVector := [(0, node81Piece34Input_sector0)]
def node81Piece34Output_sector0_chunk0 : RawPoly ℕ := [(5120/27, [1, 1, 1, 3, 3, 3, 3, 7]), (5120/9, [1, 1, 2, 3, 3, 3, 3, 6]), (5120/9, [1, 1, 3, 3, 3, 3, 3, 5]), (2560/9, [1, 1, 3, 3, 3, 3, 4, 4]), (20480/3, [1, 1, 3, 3, 3, 11]), (5120/9, [1, 2, 2, 3, 3, 3, 3, 5]), (10240/9, [1, 2, 3, 3, 3, 3, 3, 4]), (40960/3, [1, 2, 3, 3, 3, 10]), (5120/27, [1, 3, 3, 3, 3, 3, 3, 3]), (296960/27, [1, 3, 3, 3, 3, 9]), (40960/3, [1, 3, 3, 3, 4, 8]), (40960/3, [1, 3, 3, 3, 5, 7]), (20480/3, [1, 3, 3, 3, 6, 6]), (61440, [1, 3, 3, 15]), (5120/27, [2, 2, 2, 3, 3, 3, 3, 4]), (2560/9, [2, 2, 3, 3, 3, 3, 3, 3]), (20480/3, [2, 2, 3, 3, 3, 9]), (113920/9, [2, 3, 3, 3, 3, 8]), (40960/3, [2, 3, 3, 3, 4, 7]), (40960/3, [2, 3, 3, 3, 5, 6]), (61440, [2, 3, 3, 14]), (189440/27, [3, 3, 3, 3, 3, 7]), (392960/27, [3, 3, 3, 3, 4, 6]), (66560/9, [3, 3, 3, 3, 5, 5])]

def node81Piece34Output_sector0_chunk1 : RawPoly ℕ := [(20480/3, [3, 3, 3, 4, 4, 5]), (-962560/9, [3, 3, 3, 13]), (61440, [3, 3, 4, 12]), (61440, [3, 3, 5, 11]), (61440, [3, 3, 6, 10]), (61440, [3, 3, 7, 9]), (30720, [3, 3, 8, 8]), (122880, [3, 19])]

def node81Piece34Output_sector0 : RawPoly ℕ := [node81Piece34Output_sector0_chunk0, node81Piece34Output_sector0_chunk1].flatten

def node81Piece34Output : SectorVector := [(0, node81Piece34Output_sector0)]

def node81Piece34UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 3])]

def node81Piece34UnitInput_sector0 : RawPoly ℕ := [node81Piece34UnitInput_sector0_chunk0].flatten

def node81Piece34UnitInput : SectorVector := [(0, node81Piece34UnitInput_sector0)]

def node81Piece34UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 3, 7]), (12, [1, 1, 2, 3, 3, 3, 3, 6]), (12, [1, 1, 3, 3, 3, 3, 3, 5]), (6, [1, 1, 3, 3, 3, 3, 4, 4]), (144, [1, 1, 3, 3, 3, 11]), (12, [1, 2, 2, 3, 3, 3, 3, 5]), (24, [1, 2, 3, 3, 3, 3, 3, 4]), (288, [1, 2, 3, 3, 3, 10]), (4, [1, 3, 3, 3, 3, 3, 3, 3]), (232, [1, 3, 3, 3, 3, 9]), (288, [1, 3, 3, 3, 4, 8]), (288, [1, 3, 3, 3, 5, 7]), (144, [1, 3, 3, 3, 6, 6]), (1296, [1, 3, 3, 15]), (4, [2, 2, 2, 3, 3, 3, 3, 4]), (6, [2, 2, 3, 3, 3, 3, 3, 3]), (144, [2, 2, 3, 3, 3, 9]), (267, [2, 3, 3, 3, 3, 8]), (288, [2, 3, 3, 3, 4, 7]), (288, [2, 3, 3, 3, 5, 6]), (1296, [2, 3, 3, 14]), (148, [3, 3, 3, 3, 3, 7]), (307, [3, 3, 3, 3, 4, 6]), (156, [3, 3, 3, 3, 5, 5])]

def node81Piece34UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [3, 3, 3, 4, 4, 5]), (-2256, [3, 3, 3, 13]), (1296, [3, 3, 4, 12]), (1296, [3, 3, 5, 11]), (1296, [3, 3, 6, 10]), (1296, [3, 3, 7, 9]), (648, [3, 3, 8, 8]), (2592, [3, 19])]

def node81Piece34UnitOutput_sector0 : RawPoly ℕ := [node81Piece34UnitOutput_sector0_chunk0, node81Piece34UnitOutput_sector0_chunk1].flatten

def node81Piece34UnitOutput : SectorVector := [(0, node81Piece34UnitOutput_sector0)]

theorem node81Piece34_check : VectorCertificate (neutralBoundS JR (-7) node81Piece34UnitInput) node81Piece34UnitOutput := by decide +kernel

theorem node81Piece34_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece34Input) = evaluate node81Piece34Output :=
  mode_of_scaled _ _ (1280/27) node81Piece34UnitInput node81Piece34UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece34_check)

def node81Piece35Input_sector0 : RawPoly ℕ := [(320/3, [3, 9])]

def node81Piece35Input : SectorVector := [(0, node81Piece35Input_sector0)]
def node81Piece35Output_sector0_chunk0 : RawPoly ℕ := [(1280/3, [1, 1, 1, 3, 7, 9]), (1280, [1, 1, 2, 3, 6, 9]), (1280, [1, 1, 3, 3, 5, 9]), (640, [1, 1, 3, 4, 4, 9]), (11520, [1, 1, 3, 17]), (3840, [1, 1, 9, 11]), (1280, [1, 2, 2, 3, 5, 9]), (2560, [1, 2, 3, 3, 4, 9]), (23040, [1, 2, 3, 16]), (7680, [1, 2, 9, 10]), (1280/3, [1, 3, 3, 3, 3, 9]), (23040, [1, 3, 3, 15]), (23040, [1, 3, 4, 14]), (23040, [1, 3, 5, 13]), (23040, [1, 3, 6, 12]), (23040, [1, 3, 7, 11]), (23040, [1, 3, 8, 10]), (39680/3, [1, 3, 9, 9]), (7680, [1, 4, 8, 9]), (7680, [1, 5, 7, 9]), (3840, [1, 6, 6, 9]), (69120, [1, 21]), (1280/3, [2, 2, 2, 3, 4, 9]), (640, [2, 2, 3, 3, 3, 9])]

def node81Piece35Output_sector0_chunk1 : RawPoly ℕ := [(11520, [2, 2, 3, 15]), (3840, [2, 2, 9, 9]), (23040, [2, 3, 3, 14]), (23040, [2, 3, 4, 13]), (23040, [2, 3, 5, 12]), (23040, [2, 3, 6, 11]), (23040, [2, 3, 7, 10]), (28480, [2, 3, 8, 9]), (7680, [2, 4, 7, 9]), (7680, [2, 5, 6, 9]), (69120, [2, 20]), (11520, [3, 3, 3, 13]), (23040, [3, 3, 4, 12]), (23040, [3, 3, 5, 11]), (23040, [3, 3, 6, 10]), (81920/3, [3, 3, 7, 9]), (11520, [3, 3, 8, 8]), (11520, [3, 4, 4, 11]), (23040, [3, 4, 5, 10]), (98240/3, [3, 4, 6, 9]), (23040, [3, 4, 7, 8]), (16640, [3, 5, 5, 9]), (23040, [3, 5, 6, 8]), (11520, [3, 5, 7, 7])]

def node81Piece35Output_sector0_chunk2 : RawPoly ℕ := [(11520, [3, 6, 6, 7]), (-848640, [3, 19]), (3840, [4, 4, 5, 9]), (69120, [4, 18]), (69120, [5, 17]), (69120, [6, 16]), (69120, [7, 15]), (69120, [8, 14]), (-25600, [9, 13]), (69120, [10, 12]), (34560, [11, 11])]

def node81Piece35Output_sector0 : RawPoly ℕ := [node81Piece35Output_sector0_chunk0, node81Piece35Output_sector0_chunk1, node81Piece35Output_sector0_chunk2].flatten

def node81Piece35Output : SectorVector := [(0, node81Piece35Output_sector0)]

def node81Piece35UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 9])]

def node81Piece35UnitInput_sector0 : RawPoly ℕ := [node81Piece35UnitInput_sector0_chunk0].flatten

def node81Piece35UnitInput : SectorVector := [(0, node81Piece35UnitInput_sector0)]

def node81Piece35UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 7, 9]), (12, [1, 1, 2, 3, 6, 9]), (12, [1, 1, 3, 3, 5, 9]), (6, [1, 1, 3, 4, 4, 9]), (108, [1, 1, 3, 17]), (36, [1, 1, 9, 11]), (12, [1, 2, 2, 3, 5, 9]), (24, [1, 2, 3, 3, 4, 9]), (216, [1, 2, 3, 16]), (72, [1, 2, 9, 10]), (4, [1, 3, 3, 3, 3, 9]), (216, [1, 3, 3, 15]), (216, [1, 3, 4, 14]), (216, [1, 3, 5, 13]), (216, [1, 3, 6, 12]), (216, [1, 3, 7, 11]), (216, [1, 3, 8, 10]), (124, [1, 3, 9, 9]), (72, [1, 4, 8, 9]), (72, [1, 5, 7, 9]), (36, [1, 6, 6, 9]), (648, [1, 21]), (4, [2, 2, 2, 3, 4, 9]), (6, [2, 2, 3, 3, 3, 9])]

def node81Piece35UnitOutput_sector0_chunk1 : RawPoly ℕ := [(108, [2, 2, 3, 15]), (36, [2, 2, 9, 9]), (216, [2, 3, 3, 14]), (216, [2, 3, 4, 13]), (216, [2, 3, 5, 12]), (216, [2, 3, 6, 11]), (216, [2, 3, 7, 10]), (267, [2, 3, 8, 9]), (72, [2, 4, 7, 9]), (72, [2, 5, 6, 9]), (648, [2, 20]), (108, [3, 3, 3, 13]), (216, [3, 3, 4, 12]), (216, [3, 3, 5, 11]), (216, [3, 3, 6, 10]), (256, [3, 3, 7, 9]), (108, [3, 3, 8, 8]), (108, [3, 4, 4, 11]), (216, [3, 4, 5, 10]), (307, [3, 4, 6, 9]), (216, [3, 4, 7, 8]), (156, [3, 5, 5, 9]), (216, [3, 5, 6, 8]), (108, [3, 5, 7, 7])]

def node81Piece35UnitOutput_sector0_chunk2 : RawPoly ℕ := [(108, [3, 6, 6, 7]), (-7956, [3, 19]), (36, [4, 4, 5, 9]), (648, [4, 18]), (648, [5, 17]), (648, [6, 16]), (648, [7, 15]), (648, [8, 14]), (-240, [9, 13]), (648, [10, 12]), (324, [11, 11])]

def node81Piece35UnitOutput_sector0 : RawPoly ℕ := [node81Piece35UnitOutput_sector0_chunk0, node81Piece35UnitOutput_sector0_chunk1, node81Piece35UnitOutput_sector0_chunk2].flatten

def node81Piece35UnitOutput : SectorVector := [(0, node81Piece35UnitOutput_sector0)]

theorem node81Piece35_check : VectorCertificate (neutralBoundS JR (-7) node81Piece35UnitInput) node81Piece35UnitOutput := by decide +kernel

theorem node81Piece35_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece35Input) = evaluate node81Piece35Output :=
  mode_of_scaled _ _ (320/3) node81Piece35UnitInput node81Piece35UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece35_check)

def node81Piece36Input_sector0 : RawPoly ℕ := [(-60, [4, 8])]

def node81Piece36Input : SectorVector := [(0, node81Piece36Input_sector0)]
def node81Piece36Output_sector0_chunk0 : RawPoly ℕ := [(-240, [1, 1, 1, 4, 7, 8]), (-720, [1, 1, 2, 4, 6, 8]), (-720, [1, 1, 3, 4, 5, 8]), (-360, [1, 1, 4, 4, 4, 8]), (-5760, [1, 1, 4, 16]), (-2880, [1, 1, 8, 12]), (-720, [1, 2, 2, 4, 5, 8]), (-1440, [1, 2, 3, 4, 4, 8]), (-11520, [1, 2, 4, 15]), (-5760, [1, 2, 8, 11]), (-240, [1, 3, 3, 3, 4, 8]), (-11520, [1, 3, 4, 14]), (-5760, [1, 3, 8, 10]), (-11520, [1, 4, 4, 13]), (-11520, [1, 4, 5, 12]), (-11520, [1, 4, 6, 11]), (-11520, [1, 4, 7, 10]), (-13920, [1, 4, 8, 9]), (-5760, [1, 5, 8, 8]), (-5760, [1, 6, 7, 8]), (-46080, [1, 21]), (-240, [2, 2, 2, 4, 4, 8]), (-360, [2, 2, 3, 3, 4, 8]), (-5760, [2, 2, 4, 14])]

def node81Piece36Output_sector0_chunk1 : RawPoly ℕ := [(-2880, [2, 2, 8, 10]), (-11520, [2, 3, 4, 13]), (-5760, [2, 3, 8, 9]), (-11520, [2, 4, 4, 12]), (-11520, [2, 4, 5, 11]), (-11520, [2, 4, 6, 10]), (-11520, [2, 4, 7, 9]), (-10260, [2, 4, 8, 8]), (-5760, [2, 5, 7, 8]), (-2880, [2, 6, 6, 8]), (-46080, [2, 20]), (-5760, [3, 3, 4, 12]), (-2880, [3, 3, 8, 8]), (-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-17520, [3, 4, 7, 8]), (-5760, [3, 5, 6, 8]), (-46080, [3, 19]), (-5760, [4, 4, 4, 10]), (-11520, [4, 4, 5, 9]), (-15540, [4, 4, 6, 8]), (-5760, [4, 4, 7, 7]), (-9360, [4, 5, 5, 8])]

def node81Piece36Output_sector0_chunk2 : RawPoly ℕ := [(-11520, [4, 5, 6, 7]), (-1920, [4, 6, 6, 6]), (348000, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (45360, [8, 14]), (-46080, [9, 13]), (-46080, [10, 12]), (-23040, [11, 11])]

def node81Piece36Output_sector0 : RawPoly ℕ := [node81Piece36Output_sector0_chunk0, node81Piece36Output_sector0_chunk1, node81Piece36Output_sector0_chunk2].flatten

def node81Piece36Output : SectorVector := [(0, node81Piece36Output_sector0)]

def node81Piece36UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 8])]

def node81Piece36UnitInput_sector0 : RawPoly ℕ := [node81Piece36UnitInput_sector0_chunk0].flatten

def node81Piece36UnitInput : SectorVector := [(0, node81Piece36UnitInput_sector0)]

def node81Piece36UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 7, 8]), (12, [1, 1, 2, 4, 6, 8]), (12, [1, 1, 3, 4, 5, 8]), (6, [1, 1, 4, 4, 4, 8]), (96, [1, 1, 4, 16]), (48, [1, 1, 8, 12]), (12, [1, 2, 2, 4, 5, 8]), (24, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 4, 15]), (96, [1, 2, 8, 11]), (4, [1, 3, 3, 3, 4, 8]), (192, [1, 3, 4, 14]), (96, [1, 3, 8, 10]), (192, [1, 4, 4, 13]), (192, [1, 4, 5, 12]), (192, [1, 4, 6, 11]), (192, [1, 4, 7, 10]), (232, [1, 4, 8, 9]), (96, [1, 5, 8, 8]), (96, [1, 6, 7, 8]), (768, [1, 21]), (4, [2, 2, 2, 4, 4, 8]), (6, [2, 2, 3, 3, 4, 8]), (96, [2, 2, 4, 14])]

def node81Piece36UnitOutput_sector0_chunk1 : RawPoly ℕ := [(48, [2, 2, 8, 10]), (192, [2, 3, 4, 13]), (96, [2, 3, 8, 9]), (192, [2, 4, 4, 12]), (192, [2, 4, 5, 11]), (192, [2, 4, 6, 10]), (192, [2, 4, 7, 9]), (171, [2, 4, 8, 8]), (96, [2, 5, 7, 8]), (48, [2, 6, 6, 8]), (768, [2, 20]), (96, [3, 3, 4, 12]), (48, [3, 3, 8, 8]), (192, [3, 4, 4, 11]), (192, [3, 4, 5, 10]), (192, [3, 4, 6, 9]), (292, [3, 4, 7, 8]), (96, [3, 5, 6, 8]), (768, [3, 19]), (96, [4, 4, 4, 10]), (192, [4, 4, 5, 9]), (259, [4, 4, 6, 8]), (96, [4, 4, 7, 7]), (156, [4, 5, 5, 8])]

def node81Piece36UnitOutput_sector0_chunk2 : RawPoly ℕ := [(192, [4, 5, 6, 7]), (32, [4, 6, 6, 6]), (-5800, [4, 18]), (768, [5, 17]), (768, [6, 16]), (768, [7, 15]), (-756, [8, 14]), (768, [9, 13]), (768, [10, 12]), (384, [11, 11])]

def node81Piece36UnitOutput_sector0 : RawPoly ℕ := [node81Piece36UnitOutput_sector0_chunk0, node81Piece36UnitOutput_sector0_chunk1, node81Piece36UnitOutput_sector0_chunk2].flatten

def node81Piece36UnitOutput : SectorVector := [(0, node81Piece36UnitOutput_sector0)]

theorem node81Piece36_check : VectorCertificate (neutralBoundS JR (-7) node81Piece36UnitInput) node81Piece36UnitOutput := by decide +kernel

theorem node81Piece36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece36Input) = evaluate node81Piece36Output :=
  mode_of_scaled _ _ (-60) node81Piece36UnitInput node81Piece36UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece36_check)

def node81Piece37Input_sector0 : RawPoly ℕ := [(96/7, [5, 7])]

def node81Piece37Input : SectorVector := [(0, node81Piece37Input_sector0)]
def node81Piece37Output_sector0_chunk0 : RawPoly ℕ := [(384/7, [1, 1, 1, 5, 7, 7]), (1152/7, [1, 1, 2, 5, 6, 7]), (1152/7, [1, 1, 3, 5, 5, 7]), (576/7, [1, 1, 4, 4, 5, 7]), (1152, [1, 1, 5, 15]), (5760/7, [1, 1, 7, 13]), (1152/7, [1, 2, 2, 5, 5, 7]), (2304/7, [1, 2, 3, 4, 5, 7]), (2304, [1, 2, 5, 14]), (11520/7, [1, 2, 7, 12]), (384/7, [1, 3, 3, 3, 5, 7]), (2304, [1, 3, 5, 13]), (11520/7, [1, 3, 7, 11]), (2304, [1, 4, 5, 12]), (11520/7, [1, 4, 7, 10]), (2304, [1, 5, 5, 11]), (2304, [1, 5, 6, 10]), (22272/7, [1, 5, 7, 9]), (1152, [1, 5, 8, 8]), (11520/7, [1, 6, 7, 8]), (5760/7, [1, 7, 7, 7]), (11520, [1, 21]), (384/7, [2, 2, 2, 4, 5, 7]), (576/7, [2, 2, 3, 3, 5, 7])]

def node81Piece37Output_sector0_chunk1 : RawPoly ℕ := [(1152, [2, 2, 5, 13]), (5760/7, [2, 2, 7, 11]), (2304, [2, 3, 5, 12]), (11520/7, [2, 3, 7, 10]), (2304, [2, 4, 5, 11]), (11520/7, [2, 4, 7, 9]), (2304, [2, 5, 5, 10]), (2304, [2, 5, 6, 9]), (25632/7, [2, 5, 7, 8]), (11520/7, [2, 6, 7, 7]), (11520, [2, 20]), (1152, [3, 3, 5, 11]), (5760/7, [3, 3, 7, 9]), (2304, [3, 4, 5, 10]), (11520/7, [3, 4, 7, 8]), (2304, [3, 5, 5, 9]), (2304, [3, 5, 6, 8]), (19968/7, [3, 5, 7, 7]), (5760/7, [3, 6, 6, 7]), (11520, [3, 19]), (1152, [4, 4, 5, 9]), (5760/7, [4, 4, 7, 7]), (2304, [4, 5, 5, 8]), (29472/7, [4, 5, 6, 7])]

def node81Piece37Output_sector0_chunk2 : RawPoly ℕ := [(11520, [4, 18]), (11136/7, [5, 5, 5, 7]), (1152, [5, 5, 6, 6]), (-55296, [5, 17]), (11520, [6, 16]), (-21120, [7, 15]), (11520, [8, 14]), (11520, [9, 13]), (11520, [10, 12]), (5760, [11, 11])]

def node81Piece37Output_sector0 : RawPoly ℕ := [node81Piece37Output_sector0_chunk0, node81Piece37Output_sector0_chunk1, node81Piece37Output_sector0_chunk2].flatten

def node81Piece37Output : SectorVector := [(0, node81Piece37Output_sector0)]

def node81Piece37UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 7])]

def node81Piece37UnitInput_sector0 : RawPoly ℕ := [node81Piece37UnitInput_sector0_chunk0].flatten

def node81Piece37UnitInput : SectorVector := [(0, node81Piece37UnitInput_sector0)]

def node81Piece37UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 5, 7, 7]), (12, [1, 1, 2, 5, 6, 7]), (12, [1, 1, 3, 5, 5, 7]), (6, [1, 1, 4, 4, 5, 7]), (84, [1, 1, 5, 15]), (60, [1, 1, 7, 13]), (12, [1, 2, 2, 5, 5, 7]), (24, [1, 2, 3, 4, 5, 7]), (168, [1, 2, 5, 14]), (120, [1, 2, 7, 12]), (4, [1, 3, 3, 3, 5, 7]), (168, [1, 3, 5, 13]), (120, [1, 3, 7, 11]), (168, [1, 4, 5, 12]), (120, [1, 4, 7, 10]), (168, [1, 5, 5, 11]), (168, [1, 5, 6, 10]), (232, [1, 5, 7, 9]), (84, [1, 5, 8, 8]), (120, [1, 6, 7, 8]), (60, [1, 7, 7, 7]), (840, [1, 21]), (4, [2, 2, 2, 4, 5, 7]), (6, [2, 2, 3, 3, 5, 7])]

def node81Piece37UnitOutput_sector0_chunk1 : RawPoly ℕ := [(84, [2, 2, 5, 13]), (60, [2, 2, 7, 11]), (168, [2, 3, 5, 12]), (120, [2, 3, 7, 10]), (168, [2, 4, 5, 11]), (120, [2, 4, 7, 9]), (168, [2, 5, 5, 10]), (168, [2, 5, 6, 9]), (267, [2, 5, 7, 8]), (120, [2, 6, 7, 7]), (840, [2, 20]), (84, [3, 3, 5, 11]), (60, [3, 3, 7, 9]), (168, [3, 4, 5, 10]), (120, [3, 4, 7, 8]), (168, [3, 5, 5, 9]), (168, [3, 5, 6, 8]), (208, [3, 5, 7, 7]), (60, [3, 6, 6, 7]), (840, [3, 19]), (84, [4, 4, 5, 9]), (60, [4, 4, 7, 7]), (168, [4, 5, 5, 8]), (307, [4, 5, 6, 7])]

def node81Piece37UnitOutput_sector0_chunk2 : RawPoly ℕ := [(840, [4, 18]), (116, [5, 5, 5, 7]), (84, [5, 5, 6, 6]), (-4032, [5, 17]), (840, [6, 16]), (-1540, [7, 15]), (840, [8, 14]), (840, [9, 13]), (840, [10, 12]), (420, [11, 11])]

def node81Piece37UnitOutput_sector0 : RawPoly ℕ := [node81Piece37UnitOutput_sector0_chunk0, node81Piece37UnitOutput_sector0_chunk1, node81Piece37UnitOutput_sector0_chunk2].flatten

def node81Piece37UnitOutput : SectorVector := [(0, node81Piece37UnitOutput_sector0)]

theorem node81Piece37_check : VectorCertificate (neutralBoundS JR (-7) node81Piece37UnitInput) node81Piece37UnitOutput := by decide +kernel

theorem node81Piece37_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node81Piece37Input) = evaluate node81Piece37Output :=
  mode_of_scaled _ _ (96/7) node81Piece37UnitInput node81Piece37UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node81Piece37_check)

end VOA.Classification.COne.OrbC2h
