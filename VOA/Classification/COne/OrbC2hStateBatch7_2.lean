import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch7_0
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

def node7Piece32Input_sector0 : RawPoly ℕ := [(400/3, [2, 3, 3, 4])]

def node7Piece32Input : SectorVector := [(0, node7Piece32Input_sector0)]
def node7Piece32Output_sector0_chunk0 : RawPoly ℕ := [(1600/3, [1, 1, 1, 2, 3, 3, 4, 5]), (1600, [1, 1, 2, 2, 3, 3, 4, 4]), (800, [1, 1, 2, 3, 3, 3, 3, 4]), (6400, [1, 1, 2, 3, 3, 10]), (9600, [1, 1, 2, 3, 4, 9]), (3200, [1, 1, 3, 3, 4, 8]), (1600, [1, 2, 2, 2, 3, 3, 3, 4]), (12800, [1, 2, 2, 3, 3, 9]), (19200, [1, 2, 2, 3, 4, 8]), (12800, [1, 2, 3, 3, 3, 8]), (34400, [1, 2, 3, 3, 4, 7]), (12800, [1, 2, 3, 3, 5, 6]), (19200, [1, 2, 3, 4, 4, 6]), (9600, [1, 2, 3, 4, 5, 5]), (76800, [1, 2, 3, 14]), (28800, [1, 2, 4, 13]), (6400, [1, 3, 3, 3, 4, 6]), (6400, [1, 3, 3, 4, 4, 5]), (25600, [1, 3, 3, 13]), (38400, [1, 3, 4, 12]), (400/3, [2, 2, 2, 2, 2, 3, 3, 4]), (6400, [2, 2, 2, 3, 3, 8]), (9600, [2, 2, 2, 3, 4, 7]), (12800, [2, 2, 3, 3, 3, 7])]

def node7Piece32Output_sector0_chunk1 : RawPoly ℕ := [(103600/3, [2, 2, 3, 3, 4, 6]), (6400, [2, 2, 3, 3, 5, 5]), (19200, [2, 2, 3, 4, 4, 5]), (76800, [2, 2, 3, 13]), (28800, [2, 2, 4, 12]), (6400, [2, 3, 3, 3, 3, 6]), (90400/3, [2, 3, 3, 3, 4, 5]), (47800/3, [2, 3, 3, 4, 4, 4]), (-180800/3, [2, 3, 3, 12]), (-40000, [2, 3, 4, 11]), (76800, [2, 3, 5, 10]), (76800, [2, 3, 6, 9]), (76800, [2, 3, 7, 8]), (28800, [2, 4, 4, 10]), (28800, [2, 4, 5, 9]), (28800, [2, 4, 6, 8]), (14400, [2, 4, 7, 7]), (115200, [2, 18]), (3200, [3, 3, 3, 3, 4, 4]), (25600, [3, 3, 3, 11]), (20000, [3, 3, 4, 10]), (25600, [3, 3, 5, 9]), (25600, [3, 3, 6, 8]), (12800, [3, 3, 7, 7])]

def node7Piece32Output_sector0_chunk2 : RawPoly ℕ := [(38400, [3, 4, 4, 9]), (38400, [3, 4, 5, 8]), (38400, [3, 4, 6, 7]), (153600, [3, 17]), (57600, [4, 16])]

def node7Piece32Output_sector0 : RawPoly ℕ := [node7Piece32Output_sector0_chunk0, node7Piece32Output_sector0_chunk1, node7Piece32Output_sector0_chunk2].flatten

def node7Piece32Output : SectorVector := [(0, node7Piece32Output_sector0)]

def node7Piece32UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 4])]

def node7Piece32UnitInput_sector0 : RawPoly ℕ := [node7Piece32UnitInput_sector0_chunk0].flatten

def node7Piece32UnitInput : SectorVector := [(0, node7Piece32UnitInput_sector0)]

def node7Piece32UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 5]), (12, [1, 1, 2, 2, 3, 3, 4, 4]), (6, [1, 1, 2, 3, 3, 3, 3, 4]), (48, [1, 1, 2, 3, 3, 10]), (72, [1, 1, 2, 3, 4, 9]), (24, [1, 1, 3, 3, 4, 8]), (12, [1, 2, 2, 2, 3, 3, 3, 4]), (96, [1, 2, 2, 3, 3, 9]), (144, [1, 2, 2, 3, 4, 8]), (96, [1, 2, 3, 3, 3, 8]), (258, [1, 2, 3, 3, 4, 7]), (96, [1, 2, 3, 3, 5, 6]), (144, [1, 2, 3, 4, 4, 6]), (72, [1, 2, 3, 4, 5, 5]), (576, [1, 2, 3, 14]), (216, [1, 2, 4, 13]), (48, [1, 3, 3, 3, 4, 6]), (48, [1, 3, 3, 4, 4, 5]), (192, [1, 3, 3, 13]), (288, [1, 3, 4, 12]), (1, [2, 2, 2, 2, 2, 3, 3, 4]), (48, [2, 2, 2, 3, 3, 8]), (72, [2, 2, 2, 3, 4, 7]), (96, [2, 2, 3, 3, 3, 7])]

def node7Piece32UnitOutput_sector0_chunk1 : RawPoly ℕ := [(259, [2, 2, 3, 3, 4, 6]), (48, [2, 2, 3, 3, 5, 5]), (144, [2, 2, 3, 4, 4, 5]), (576, [2, 2, 3, 13]), (216, [2, 2, 4, 12]), (48, [2, 3, 3, 3, 3, 6]), (226, [2, 3, 3, 3, 4, 5]), (239/2, [2, 3, 3, 4, 4, 4]), (-452, [2, 3, 3, 12]), (-300, [2, 3, 4, 11]), (576, [2, 3, 5, 10]), (576, [2, 3, 6, 9]), (576, [2, 3, 7, 8]), (216, [2, 4, 4, 10]), (216, [2, 4, 5, 9]), (216, [2, 4, 6, 8]), (108, [2, 4, 7, 7]), (864, [2, 18]), (24, [3, 3, 3, 3, 4, 4]), (192, [3, 3, 3, 11]), (150, [3, 3, 4, 10]), (192, [3, 3, 5, 9]), (192, [3, 3, 6, 8]), (96, [3, 3, 7, 7])]

def node7Piece32UnitOutput_sector0_chunk2 : RawPoly ℕ := [(288, [3, 4, 4, 9]), (288, [3, 4, 5, 8]), (288, [3, 4, 6, 7]), (1152, [3, 17]), (432, [4, 16])]

def node7Piece32UnitOutput_sector0 : RawPoly ℕ := [node7Piece32UnitOutput_sector0_chunk0, node7Piece32UnitOutput_sector0_chunk1, node7Piece32UnitOutput_sector0_chunk2].flatten

def node7Piece32UnitOutput : SectorVector := [(0, node7Piece32UnitOutput_sector0)]

theorem node7Piece32_check : VectorCertificate (neutralBoundS JR (-5) node7Piece32UnitInput) node7Piece32UnitOutput := by decide +kernel

theorem node7Piece32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece32Input) = evaluate node7Piece32Output :=
  mode_of_scaled _ _ (400/3) node7Piece32UnitInput node7Piece32UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece32_check)

def node7Piece33Input_sector0 : RawPoly ℕ := [(-96, [2, 10])]

def node7Piece33Input : SectorVector := [(0, node7Piece33Input_sector0)]
def node7Piece33Output_sector0_chunk0 : RawPoly ℕ := [(-384, [1, 1, 1, 2, 5, 10]), (-1152, [1, 1, 2, 2, 4, 10]), (-576, [1, 1, 2, 3, 3, 10]), (-11520, [1, 1, 2, 16]), (-2304, [1, 1, 8, 10]), (-1152, [1, 2, 2, 2, 3, 10]), (-23040, [1, 2, 2, 15]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-24768, [1, 2, 7, 10]), (-23040, [1, 2, 8, 9]), (-4608, [1, 3, 6, 10]), (-4608, [1, 4, 5, 10]), (-46080, [1, 19]), (-96, [2, 2, 2, 2, 2, 10]), (-11520, [2, 2, 2, 14]), (-23040, [2, 2, 3, 13]), (-23040, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-24864, [2, 2, 6, 10]), (-23040, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8])]

def node7Piece33Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-28608, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9]), (-23040, [2, 3, 7, 8]), (-14544, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (880320, [2, 18]), (-2304, [3, 3, 4, 10]), (-46080, [3, 17]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (-46080, [9, 11]), (8640, [10, 10])]

def node7Piece33Output_sector0 : RawPoly ℕ := [node7Piece33Output_sector0_chunk0, node7Piece33Output_sector0_chunk1].flatten

def node7Piece33Output : SectorVector := [(0, node7Piece33Output_sector0)]

def node7Piece33UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 10])]

def node7Piece33UnitInput_sector0 : RawPoly ℕ := [node7Piece33UnitInput_sector0_chunk0].flatten

def node7Piece33UnitInput : SectorVector := [(0, node7Piece33UnitInput_sector0)]

def node7Piece33UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 5, 10]), (12, [1, 1, 2, 2, 4, 10]), (6, [1, 1, 2, 3, 3, 10]), (120, [1, 1, 2, 16]), (24, [1, 1, 8, 10]), (12, [1, 2, 2, 2, 3, 10]), (240, [1, 2, 2, 15]), (240, [1, 2, 3, 14]), (240, [1, 2, 4, 13]), (240, [1, 2, 5, 12]), (240, [1, 2, 6, 11]), (258, [1, 2, 7, 10]), (240, [1, 2, 8, 9]), (48, [1, 3, 6, 10]), (48, [1, 4, 5, 10]), (480, [1, 19]), (1, [2, 2, 2, 2, 2, 10]), (120, [2, 2, 2, 14]), (240, [2, 2, 3, 13]), (240, [2, 2, 4, 12]), (240, [2, 2, 5, 11]), (259, [2, 2, 6, 10]), (240, [2, 2, 7, 9]), (120, [2, 2, 8, 8])]

def node7Piece33UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [2, 3, 3, 12]), (240, [2, 3, 4, 11]), (298, [2, 3, 5, 10]), (240, [2, 3, 6, 9]), (240, [2, 3, 7, 8]), (303/2, [2, 4, 4, 10]), (240, [2, 4, 5, 9]), (240, [2, 4, 6, 8]), (120, [2, 4, 7, 7]), (120, [2, 5, 5, 8]), (240, [2, 5, 6, 7]), (40, [2, 6, 6, 6]), (-9170, [2, 18]), (24, [3, 3, 4, 10]), (480, [3, 17]), (480, [4, 16]), (480, [5, 15]), (480, [6, 14]), (480, [7, 13]), (480, [8, 12]), (480, [9, 11]), (-90, [10, 10])]

def node7Piece33UnitOutput_sector0 : RawPoly ℕ := [node7Piece33UnitOutput_sector0_chunk0, node7Piece33UnitOutput_sector0_chunk1].flatten

def node7Piece33UnitOutput : SectorVector := [(0, node7Piece33UnitOutput_sector0)]

theorem node7Piece33_check : VectorCertificate (neutralBoundS JR (-5) node7Piece33UnitInput) node7Piece33UnitOutput := by decide +kernel

theorem node7Piece33_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece33Input) = evaluate node7Piece33Output :=
  mode_of_scaled _ _ (-96) node7Piece33UnitInput node7Piece33UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece33_check)

def node7Piece34Input_sector0 : RawPoly ℕ := [(1280/27, [3, 3, 3, 3])]

def node7Piece34Input : SectorVector := [(0, node7Piece34Input_sector0)]
def node7Piece34Output_sector0 : RawPoly ℕ := [(5120/27, [1, 1, 1, 3, 3, 3, 3, 5]), (5120/9, [1, 1, 2, 3, 3, 3, 3, 4]), (2560/9, [1, 1, 3, 3, 3, 3, 3, 3]), (20480/3, [1, 1, 3, 3, 3, 9]), (5120/9, [1, 2, 2, 3, 3, 3, 3, 3]), (40960/3, [1, 2, 3, 3, 3, 8]), (110080/9, [1, 3, 3, 3, 3, 7]), (40960/3, [1, 3, 3, 3, 4, 6]), (20480/3, [1, 3, 3, 3, 5, 5]), (61440, [1, 3, 3, 13]), (1280/27, [2, 2, 2, 2, 3, 3, 3, 3]), (20480/3, [2, 2, 3, 3, 3, 7]), (362240/27, [2, 3, 3, 3, 3, 6]), (40960/3, [2, 3, 3, 3, 4, 5]), (61440, [2, 3, 3, 12]), (197120/27, [3, 3, 3, 3, 3, 5]), (64640/9, [3, 3, 3, 3, 4, 4]), (-624640/9, [3, 3, 3, 11]), (61440, [3, 3, 4, 10]), (61440, [3, 3, 5, 9]), (61440, [3, 3, 6, 8]), (30720, [3, 3, 7, 7]), (122880, [3, 17])]

def node7Piece34Output : SectorVector := [(0, node7Piece34Output_sector0)]

def node7Piece34UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 3])]

def node7Piece34UnitInput_sector0 : RawPoly ℕ := [node7Piece34UnitInput_sector0_chunk0].flatten

def node7Piece34UnitInput : SectorVector := [(0, node7Piece34UnitInput_sector0)]

def node7Piece34UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 3, 5]), (12, [1, 1, 2, 3, 3, 3, 3, 4]), (6, [1, 1, 3, 3, 3, 3, 3, 3]), (144, [1, 1, 3, 3, 3, 9]), (12, [1, 2, 2, 3, 3, 3, 3, 3]), (288, [1, 2, 3, 3, 3, 8]), (258, [1, 3, 3, 3, 3, 7]), (288, [1, 3, 3, 3, 4, 6]), (144, [1, 3, 3, 3, 5, 5]), (1296, [1, 3, 3, 13]), (1, [2, 2, 2, 2, 3, 3, 3, 3]), (144, [2, 2, 3, 3, 3, 7]), (283, [2, 3, 3, 3, 3, 6]), (288, [2, 3, 3, 3, 4, 5]), (1296, [2, 3, 3, 12]), (154, [3, 3, 3, 3, 3, 5]), (303/2, [3, 3, 3, 3, 4, 4]), (-1464, [3, 3, 3, 11]), (1296, [3, 3, 4, 10]), (1296, [3, 3, 5, 9]), (1296, [3, 3, 6, 8]), (648, [3, 3, 7, 7]), (2592, [3, 17])]

def node7Piece34UnitOutput_sector0 : RawPoly ℕ := [node7Piece34UnitOutput_sector0_chunk0].flatten

def node7Piece34UnitOutput : SectorVector := [(0, node7Piece34UnitOutput_sector0)]

theorem node7Piece34_check : VectorCertificate (neutralBoundS JR (-5) node7Piece34UnitInput) node7Piece34UnitOutput := by decide +kernel

theorem node7Piece34_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece34Input) = evaluate node7Piece34Output :=
  mode_of_scaled _ _ (1280/27) node7Piece34UnitInput node7Piece34UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece34_check)

def node7Piece35Input_sector0 : RawPoly ℕ := [(320/3, [3, 9])]

def node7Piece35Input : SectorVector := [(0, node7Piece35Input_sector0)]
def node7Piece35Output_sector0_chunk0 : RawPoly ℕ := [(1280/3, [1, 1, 1, 3, 5, 9]), (1280, [1, 1, 2, 3, 4, 9]), (640, [1, 1, 3, 3, 3, 9]), (11520, [1, 1, 3, 15]), (3840, [1, 1, 9, 9]), (1280, [1, 2, 2, 3, 3, 9]), (23040, [1, 2, 3, 14]), (7680, [1, 2, 8, 9]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (27520, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (7680, [1, 4, 6, 9]), (3840, [1, 5, 5, 9]), (69120, [1, 19]), (320/3, [2, 2, 2, 2, 3, 9]), (11520, [2, 2, 3, 13]), (3840, [2, 2, 7, 9]), (23040, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (23040, [2, 3, 5, 10]), (90560/3, [2, 3, 6, 9])]

def node7Piece35Output_sector0_chunk1 : RawPoly ℕ := [(23040, [2, 3, 7, 8]), (7680, [2, 4, 5, 9]), (69120, [2, 18]), (11520, [3, 3, 3, 11]), (23040, [3, 3, 4, 10]), (83840/3, [3, 3, 5, 9]), (23040, [3, 3, 6, 8]), (11520, [3, 3, 7, 7]), (16160, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (23040, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-727680, [3, 17]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14]), (69120, [7, 13]), (69120, [8, 12]), (-4480, [9, 11]), (34560, [10, 10])]

def node7Piece35Output_sector0 : RawPoly ℕ := [node7Piece35Output_sector0_chunk0, node7Piece35Output_sector0_chunk1].flatten

def node7Piece35Output : SectorVector := [(0, node7Piece35Output_sector0)]

def node7Piece35UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 9])]

def node7Piece35UnitInput_sector0 : RawPoly ℕ := [node7Piece35UnitInput_sector0_chunk0].flatten

def node7Piece35UnitInput : SectorVector := [(0, node7Piece35UnitInput_sector0)]

def node7Piece35UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 5, 9]), (12, [1, 1, 2, 3, 4, 9]), (6, [1, 1, 3, 3, 3, 9]), (108, [1, 1, 3, 15]), (36, [1, 1, 9, 9]), (12, [1, 2, 2, 3, 3, 9]), (216, [1, 2, 3, 14]), (72, [1, 2, 8, 9]), (216, [1, 3, 3, 13]), (216, [1, 3, 4, 12]), (216, [1, 3, 5, 11]), (216, [1, 3, 6, 10]), (258, [1, 3, 7, 9]), (108, [1, 3, 8, 8]), (72, [1, 4, 6, 9]), (36, [1, 5, 5, 9]), (648, [1, 19]), (1, [2, 2, 2, 2, 3, 9]), (108, [2, 2, 3, 13]), (36, [2, 2, 7, 9]), (216, [2, 3, 3, 12]), (216, [2, 3, 4, 11]), (216, [2, 3, 5, 10]), (283, [2, 3, 6, 9])]

def node7Piece35UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [2, 3, 7, 8]), (72, [2, 4, 5, 9]), (648, [2, 18]), (108, [3, 3, 3, 11]), (216, [3, 3, 4, 10]), (262, [3, 3, 5, 9]), (216, [3, 3, 6, 8]), (108, [3, 3, 7, 7]), (303/2, [3, 4, 4, 9]), (216, [3, 4, 5, 8]), (216, [3, 4, 6, 7]), (108, [3, 5, 5, 7]), (108, [3, 5, 6, 6]), (-6822, [3, 17]), (648, [4, 16]), (648, [5, 15]), (648, [6, 14]), (648, [7, 13]), (648, [8, 12]), (-42, [9, 11]), (324, [10, 10])]

def node7Piece35UnitOutput_sector0 : RawPoly ℕ := [node7Piece35UnitOutput_sector0_chunk0, node7Piece35UnitOutput_sector0_chunk1].flatten

def node7Piece35UnitOutput : SectorVector := [(0, node7Piece35UnitOutput_sector0)]

theorem node7Piece35_check : VectorCertificate (neutralBoundS JR (-5) node7Piece35UnitInput) node7Piece35UnitOutput := by decide +kernel

theorem node7Piece35_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece35Input) = evaluate node7Piece35Output :=
  mode_of_scaled _ _ (320/3) node7Piece35UnitInput node7Piece35UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece35_check)

def node7Piece36Input_sector0 : RawPoly ℕ := [(-60, [4, 8])]

def node7Piece36Input : SectorVector := [(0, node7Piece36Input_sector0)]
def node7Piece36Output_sector0_chunk0 : RawPoly ℕ := [(-240, [1, 1, 1, 4, 5, 8]), (-720, [1, 1, 2, 4, 4, 8]), (-360, [1, 1, 3, 3, 4, 8]), (-5760, [1, 1, 4, 14]), (-2880, [1, 1, 8, 10]), (-720, [1, 2, 2, 3, 4, 8]), (-11520, [1, 2, 4, 13]), (-5760, [1, 2, 8, 9]), (-11520, [1, 3, 4, 12]), (-5760, [1, 3, 8, 8]), (-11520, [1, 4, 4, 11]), (-11520, [1, 4, 5, 10]), (-11520, [1, 4, 6, 9]), (-15480, [1, 4, 7, 8]), (-5760, [1, 5, 6, 8]), (-46080, [1, 19]), (-60, [2, 2, 2, 2, 4, 8]), (-5760, [2, 2, 4, 12]), (-2880, [2, 2, 8, 8]), (-11520, [2, 3, 4, 11]), (-5760, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-11520, [2, 4, 5, 9]), (-16980, [2, 4, 6, 8])]

def node7Piece36Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [2, 4, 7, 7]), (-2880, [2, 5, 5, 8]), (-46080, [2, 18]), (-5760, [3, 3, 4, 10]), (-2880, [3, 3, 6, 8]), (-11520, [3, 4, 4, 9]), (-17880, [3, 4, 5, 8]), (-11520, [3, 4, 6, 7]), (-46080, [3, 17]), (-7170, [4, 4, 4, 8]), (-11520, [4, 4, 5, 7]), (-5760, [4, 4, 6, 6]), (-5760, [4, 5, 5, 6]), (292320, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (27120, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node7Piece36Output_sector0 : RawPoly ℕ := [node7Piece36Output_sector0_chunk0, node7Piece36Output_sector0_chunk1].flatten

def node7Piece36Output : SectorVector := [(0, node7Piece36Output_sector0)]

def node7Piece36UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 8])]

def node7Piece36UnitInput_sector0 : RawPoly ℕ := [node7Piece36UnitInput_sector0_chunk0].flatten

def node7Piece36UnitInput : SectorVector := [(0, node7Piece36UnitInput_sector0)]

def node7Piece36UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 5, 8]), (12, [1, 1, 2, 4, 4, 8]), (6, [1, 1, 3, 3, 4, 8]), (96, [1, 1, 4, 14]), (48, [1, 1, 8, 10]), (12, [1, 2, 2, 3, 4, 8]), (192, [1, 2, 4, 13]), (96, [1, 2, 8, 9]), (192, [1, 3, 4, 12]), (96, [1, 3, 8, 8]), (192, [1, 4, 4, 11]), (192, [1, 4, 5, 10]), (192, [1, 4, 6, 9]), (258, [1, 4, 7, 8]), (96, [1, 5, 6, 8]), (768, [1, 19]), (1, [2, 2, 2, 2, 4, 8]), (96, [2, 2, 4, 12]), (48, [2, 2, 8, 8]), (192, [2, 3, 4, 11]), (96, [2, 3, 7, 8]), (192, [2, 4, 4, 10]), (192, [2, 4, 5, 9]), (283, [2, 4, 6, 8])]

def node7Piece36UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [2, 4, 7, 7]), (48, [2, 5, 5, 8]), (768, [2, 18]), (96, [3, 3, 4, 10]), (48, [3, 3, 6, 8]), (192, [3, 4, 4, 9]), (298, [3, 4, 5, 8]), (192, [3, 4, 6, 7]), (768, [3, 17]), (239/2, [4, 4, 4, 8]), (192, [4, 4, 5, 7]), (96, [4, 4, 6, 6]), (96, [4, 5, 5, 6]), (-4872, [4, 16]), (768, [5, 15]), (768, [6, 14]), (768, [7, 13]), (-452, [8, 12]), (768, [9, 11]), (384, [10, 10])]

def node7Piece36UnitOutput_sector0 : RawPoly ℕ := [node7Piece36UnitOutput_sector0_chunk0, node7Piece36UnitOutput_sector0_chunk1].flatten

def node7Piece36UnitOutput : SectorVector := [(0, node7Piece36UnitOutput_sector0)]

theorem node7Piece36_check : VectorCertificate (neutralBoundS JR (-5) node7Piece36UnitInput) node7Piece36UnitOutput := by decide +kernel

theorem node7Piece36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece36Input) = evaluate node7Piece36Output :=
  mode_of_scaled _ _ (-60) node7Piece36UnitInput node7Piece36UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece36_check)

def node7Piece37Input_sector0 : RawPoly ℕ := [(96/7, [5, 7])]

def node7Piece37Input : SectorVector := [(0, node7Piece37Input_sector0)]
def node7Piece37Output_sector0_chunk0 : RawPoly ℕ := [(384/7, [1, 1, 1, 5, 5, 7]), (1152/7, [1, 1, 2, 4, 5, 7]), (576/7, [1, 1, 3, 3, 5, 7]), (1152, [1, 1, 5, 13]), (5760/7, [1, 1, 7, 11]), (1152/7, [1, 2, 2, 3, 5, 7]), (2304, [1, 2, 5, 12]), (11520/7, [1, 2, 7, 10]), (2304, [1, 3, 5, 11]), (11520/7, [1, 3, 7, 9]), (2304, [1, 4, 5, 10]), (11520/7, [1, 4, 7, 8]), (2304, [1, 5, 5, 9]), (2304, [1, 5, 6, 8]), (16704/7, [1, 5, 7, 7]), (5760/7, [1, 6, 6, 7]), (11520, [1, 19]), (96/7, [2, 2, 2, 2, 5, 7]), (1152, [2, 2, 5, 11]), (5760/7, [2, 2, 7, 9]), (2304, [2, 3, 5, 10]), (11520/7, [2, 3, 7, 8]), (2304, [2, 4, 5, 9]), (11520/7, [2, 4, 7, 7])]

def node7Piece37Output_sector0_chunk1 : RawPoly ℕ := [(2304, [2, 5, 5, 8]), (27168/7, [2, 5, 6, 7]), (11520, [2, 18]), (1152, [3, 3, 5, 9]), (5760/7, [3, 3, 7, 7]), (2304, [3, 4, 5, 8]), (11520/7, [3, 4, 6, 7]), (3264, [3, 5, 5, 7]), (1152, [3, 5, 6, 6]), (11520, [3, 17]), (14544/7, [4, 4, 5, 7]), (2304, [4, 5, 5, 6]), (11520, [4, 16]), (384, [5, 5, 5, 5]), (-45120, [5, 15]), (11520, [6, 14]), (-106560/7, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node7Piece37Output_sector0 : RawPoly ℕ := [node7Piece37Output_sector0_chunk0, node7Piece37Output_sector0_chunk1].flatten

def node7Piece37Output : SectorVector := [(0, node7Piece37Output_sector0)]

def node7Piece37UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 7])]

def node7Piece37UnitInput_sector0 : RawPoly ℕ := [node7Piece37UnitInput_sector0_chunk0].flatten

def node7Piece37UnitInput : SectorVector := [(0, node7Piece37UnitInput_sector0)]

def node7Piece37UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 5, 5, 7]), (12, [1, 1, 2, 4, 5, 7]), (6, [1, 1, 3, 3, 5, 7]), (84, [1, 1, 5, 13]), (60, [1, 1, 7, 11]), (12, [1, 2, 2, 3, 5, 7]), (168, [1, 2, 5, 12]), (120, [1, 2, 7, 10]), (168, [1, 3, 5, 11]), (120, [1, 3, 7, 9]), (168, [1, 4, 5, 10]), (120, [1, 4, 7, 8]), (168, [1, 5, 5, 9]), (168, [1, 5, 6, 8]), (174, [1, 5, 7, 7]), (60, [1, 6, 6, 7]), (840, [1, 19]), (1, [2, 2, 2, 2, 5, 7]), (84, [2, 2, 5, 11]), (60, [2, 2, 7, 9]), (168, [2, 3, 5, 10]), (120, [2, 3, 7, 8]), (168, [2, 4, 5, 9]), (120, [2, 4, 7, 7])]

def node7Piece37UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [2, 5, 5, 8]), (283, [2, 5, 6, 7]), (840, [2, 18]), (84, [3, 3, 5, 9]), (60, [3, 3, 7, 7]), (168, [3, 4, 5, 8]), (120, [3, 4, 6, 7]), (238, [3, 5, 5, 7]), (84, [3, 5, 6, 6]), (840, [3, 17]), (303/2, [4, 4, 5, 7]), (168, [4, 5, 5, 6]), (840, [4, 16]), (28, [5, 5, 5, 5]), (-3290, [5, 15]), (840, [6, 14]), (-1110, [7, 13]), (840, [8, 12]), (840, [9, 11]), (420, [10, 10])]

def node7Piece37UnitOutput_sector0 : RawPoly ℕ := [node7Piece37UnitOutput_sector0_chunk0, node7Piece37UnitOutput_sector0_chunk1].flatten

def node7Piece37UnitOutput : SectorVector := [(0, node7Piece37UnitOutput_sector0)]

theorem node7Piece37_check : VectorCertificate (neutralBoundS JR (-5) node7Piece37UnitInput) node7Piece37UnitOutput := by decide +kernel

theorem node7Piece37_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node7Piece37Input) = evaluate node7Piece37Output :=
  mode_of_scaled _ _ (96/7) node7Piece37UnitInput node7Piece37UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node7Piece37_check)

end VOA.Classification.COne.OrbC2h
