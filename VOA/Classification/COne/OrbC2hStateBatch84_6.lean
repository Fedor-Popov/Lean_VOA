import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch84_4
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

def node84Piece96Input_sector0 : RawPoly ℕ := [(120, [2, 3, 3, 8])]

def node84Piece96Input : SectorVector := [(0, node84Piece96Input_sector0)]
def node84Piece96Output_sector0_chunk0 : RawPoly ℕ := [(480, [1, 1, 1, 2, 3, 3, 3, 8]), (720, [1, 1, 2, 2, 2, 3, 3, 8]), (11520, [1, 1, 2, 3, 3, 12]), (8640, [1, 1, 2, 3, 7, 8]), (2880, [1, 1, 3, 3, 6, 8]), (23040, [1, 2, 2, 3, 3, 11]), (17280, [1, 2, 2, 3, 6, 8]), (23040, [1, 2, 3, 3, 3, 10]), (23040, [1, 2, 3, 3, 4, 9]), (44640, [1, 2, 3, 3, 5, 8]), (23040, [1, 2, 3, 3, 6, 7]), (8640, [1, 2, 3, 4, 4, 8]), (138240, [1, 2, 3, 16]), (25920, [1, 2, 8, 11]), (5760, [1, 3, 3, 3, 4, 8]), (46080, [1, 3, 3, 15]), (34560, [1, 3, 8, 10]), (11520, [2, 2, 2, 3, 3, 10]), (8640, [2, 2, 2, 3, 5, 8]), (23040, [2, 2, 3, 3, 3, 9]), (43560, [2, 2, 3, 3, 4, 8]), (23040, [2, 2, 3, 3, 5, 7]), (11520, [2, 2, 3, 3, 6, 6]), (138240, [2, 2, 3, 15])]

def node84Piece96Output_sector0_chunk1 : RawPoly ℕ := [(25920, [2, 2, 8, 10]), (17760, [2, 3, 3, 3, 3, 8]), (23040, [2, 3, 3, 3, 4, 7]), (23040, [2, 3, 3, 3, 5, 6]), (11520, [2, 3, 3, 4, 4, 6]), (11520, [2, 3, 3, 4, 5, 5]), (-388800, [2, 3, 3, 14]), (138240, [2, 3, 4, 13]), (138240, [2, 3, 5, 12]), (138240, [2, 3, 6, 11]), (138240, [2, 3, 7, 10]), (74880, [2, 3, 8, 9]), (25920, [2, 4, 8, 8]), (25920, [2, 5, 7, 8]), (12960, [2, 6, 6, 8]), (207360, [2, 20]), (46080, [3, 3, 3, 13]), (46080, [3, 3, 4, 12]), (46080, [3, 3, 5, 11]), (46080, [3, 3, 6, 10]), (46080, [3, 3, 7, 9]), (29520, [3, 3, 8, 8]), (34560, [3, 4, 7, 8]), (34560, [3, 5, 6, 8])]

def node84Piece96Output_sector0_chunk2 : RawPoly ℕ := [(276480, [3, 19]), (51840, [8, 14])]

def node84Piece96Output_sector0 : RawPoly ℕ := [node84Piece96Output_sector0_chunk0, node84Piece96Output_sector0_chunk1, node84Piece96Output_sector0_chunk2].flatten

def node84Piece96Output : SectorVector := [(0, node84Piece96Output_sector0)]

def node84Piece96UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 8])]

def node84Piece96UnitInput_sector0 : RawPoly ℕ := [node84Piece96UnitInput_sector0_chunk0].flatten

def node84Piece96UnitInput : SectorVector := [(0, node84Piece96UnitInput_sector0)]

def node84Piece96UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 3, 8]), (6, [1, 1, 2, 2, 2, 3, 3, 8]), (96, [1, 1, 2, 3, 3, 12]), (72, [1, 1, 2, 3, 7, 8]), (24, [1, 1, 3, 3, 6, 8]), (192, [1, 2, 2, 3, 3, 11]), (144, [1, 2, 2, 3, 6, 8]), (192, [1, 2, 3, 3, 3, 10]), (192, [1, 2, 3, 3, 4, 9]), (372, [1, 2, 3, 3, 5, 8]), (192, [1, 2, 3, 3, 6, 7]), (72, [1, 2, 3, 4, 4, 8]), (1152, [1, 2, 3, 16]), (216, [1, 2, 8, 11]), (48, [1, 3, 3, 3, 4, 8]), (384, [1, 3, 3, 15]), (288, [1, 3, 8, 10]), (96, [2, 2, 2, 3, 3, 10]), (72, [2, 2, 2, 3, 5, 8]), (192, [2, 2, 3, 3, 3, 9]), (363, [2, 2, 3, 3, 4, 8]), (192, [2, 2, 3, 3, 5, 7]), (96, [2, 2, 3, 3, 6, 6]), (1152, [2, 2, 3, 15])]

def node84Piece96UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [2, 2, 8, 10]), (148, [2, 3, 3, 3, 3, 8]), (192, [2, 3, 3, 3, 4, 7]), (192, [2, 3, 3, 3, 5, 6]), (96, [2, 3, 3, 4, 4, 6]), (96, [2, 3, 3, 4, 5, 5]), (-3240, [2, 3, 3, 14]), (1152, [2, 3, 4, 13]), (1152, [2, 3, 5, 12]), (1152, [2, 3, 6, 11]), (1152, [2, 3, 7, 10]), (624, [2, 3, 8, 9]), (216, [2, 4, 8, 8]), (216, [2, 5, 7, 8]), (108, [2, 6, 6, 8]), (1728, [2, 20]), (384, [3, 3, 3, 13]), (384, [3, 3, 4, 12]), (384, [3, 3, 5, 11]), (384, [3, 3, 6, 10]), (384, [3, 3, 7, 9]), (246, [3, 3, 8, 8]), (288, [3, 4, 7, 8]), (288, [3, 5, 6, 8])]

def node84Piece96UnitOutput_sector0_chunk2 : RawPoly ℕ := [(2304, [3, 19]), (432, [8, 14])]

def node84Piece96UnitOutput_sector0 : RawPoly ℕ := [node84Piece96UnitOutput_sector0_chunk0, node84Piece96UnitOutput_sector0_chunk1, node84Piece96UnitOutput_sector0_chunk2].flatten

def node84Piece96UnitOutput : SectorVector := [(0, node84Piece96UnitOutput_sector0)]

theorem node84Piece96_check : neutralDirectS JR (-3) node84Piece96UnitInput = node84Piece96UnitOutput := by decide +kernel

theorem node84Piece96_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece96Input) = evaluate node84Piece96Output :=
  mode_of_scaled _ _ (120) node84Piece96UnitInput node84Piece96UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece96_check)

def node84Piece97Input_sector0 : RawPoly ℕ := [(-240/7, [2, 3, 4, 7])]

def node84Piece97Input : SectorVector := [(0, node84Piece97Input_sector0)]
def node84Piece97Output_sector0_chunk0 : RawPoly ℕ := [(-960/7, [1, 1, 1, 2, 3, 3, 4, 7]), (-1440/7, [1, 1, 2, 2, 2, 3, 4, 7]), (-2880, [1, 1, 2, 3, 4, 11]), (-11520/7, [1, 1, 2, 3, 7, 8]), (-8640/7, [1, 1, 2, 4, 7, 7]), (-5760/7, [1, 1, 3, 4, 6, 7]), (-5760, [1, 2, 2, 3, 4, 10]), (-23040/7, [1, 2, 2, 3, 7, 7]), (-17280/7, [1, 2, 2, 4, 6, 7]), (-5760, [1, 2, 3, 3, 4, 9]), (-23040/7, [1, 2, 3, 3, 6, 7]), (-5760, [1, 2, 3, 4, 4, 8]), (-89280/7, [1, 2, 3, 4, 5, 7]), (-2880, [1, 2, 3, 4, 6, 6]), (-23040, [1, 2, 3, 16]), (-8640/7, [1, 2, 4, 4, 4, 7]), (-17280, [1, 2, 4, 15]), (-69120/7, [1, 2, 7, 12]), (-11520/7, [1, 3, 3, 4, 4, 7]), (-11520, [1, 3, 4, 14]), (-46080/7, [1, 3, 7, 11]), (-34560/7, [1, 4, 7, 10]), (-2880, [2, 2, 2, 3, 4, 9]), (-11520/7, [2, 2, 2, 3, 6, 7])]

def node84Piece97Output_sector0_chunk1 : RawPoly ℕ := [(-8640/7, [2, 2, 2, 4, 5, 7]), (-5760, [2, 2, 3, 3, 4, 8]), (-23040/7, [2, 2, 3, 3, 5, 7]), (-10800, [2, 2, 3, 4, 4, 7]), (-5760, [2, 2, 3, 4, 5, 6]), (-23040, [2, 2, 3, 15]), (-17280, [2, 2, 4, 14]), (-69120/7, [2, 2, 7, 11]), (-41280/7, [2, 3, 3, 3, 4, 7]), (-5760, [2, 3, 3, 4, 4, 6]), (-2880, [2, 3, 3, 4, 5, 5]), (-23040, [2, 3, 3, 14]), (-2880, [2, 3, 4, 4, 4, 5]), (66240, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12]), (-23040, [2, 3, 6, 11]), (-48960/7, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-17280, [2, 4, 4, 12]), (-17280, [2, 4, 5, 11]), (-17280, [2, 4, 6, 10]), (-14400, [2, 4, 7, 9]), (-8640, [2, 4, 8, 8]), (-69120/7, [2, 5, 7, 8])]

def node84Piece97Output_sector0_chunk2 : RawPoly ℕ := [(-69120/7, [2, 6, 7, 7]), (-69120, [2, 20]), (-11520, [3, 3, 4, 12]), (-46080/7, [3, 3, 7, 9]), (-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-105120/7, [3, 4, 7, 8]), (-46080/7, [3, 5, 7, 7]), (-23040/7, [3, 6, 6, 7]), (-46080, [3, 19]), (-34560/7, [4, 4, 7, 7]), (-34560/7, [4, 5, 6, 7]), (-34560, [4, 18]), (-138240/7, [7, 15])]

def node84Piece97Output_sector0 : RawPoly ℕ := [node84Piece97Output_sector0_chunk0, node84Piece97Output_sector0_chunk1, node84Piece97Output_sector0_chunk2].flatten

def node84Piece97Output : SectorVector := [(0, node84Piece97Output_sector0)]

def node84Piece97UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 4, 7])]

def node84Piece97UnitInput_sector0 : RawPoly ℕ := [node84Piece97UnitInput_sector0_chunk0].flatten

def node84Piece97UnitInput : SectorVector := [(0, node84Piece97UnitInput_sector0)]

def node84Piece97UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 7]), (6, [1, 1, 2, 2, 2, 3, 4, 7]), (84, [1, 1, 2, 3, 4, 11]), (48, [1, 1, 2, 3, 7, 8]), (36, [1, 1, 2, 4, 7, 7]), (24, [1, 1, 3, 4, 6, 7]), (168, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 7, 7]), (72, [1, 2, 2, 4, 6, 7]), (168, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 6, 7]), (168, [1, 2, 3, 4, 4, 8]), (372, [1, 2, 3, 4, 5, 7]), (84, [1, 2, 3, 4, 6, 6]), (672, [1, 2, 3, 16]), (36, [1, 2, 4, 4, 4, 7]), (504, [1, 2, 4, 15]), (288, [1, 2, 7, 12]), (48, [1, 3, 3, 4, 4, 7]), (336, [1, 3, 4, 14]), (192, [1, 3, 7, 11]), (144, [1, 4, 7, 10]), (84, [2, 2, 2, 3, 4, 9]), (48, [2, 2, 2, 3, 6, 7])]

def node84Piece97UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 2, 4, 5, 7]), (168, [2, 2, 3, 3, 4, 8]), (96, [2, 2, 3, 3, 5, 7]), (315, [2, 2, 3, 4, 4, 7]), (168, [2, 2, 3, 4, 5, 6]), (672, [2, 2, 3, 15]), (504, [2, 2, 4, 14]), (288, [2, 2, 7, 11]), (172, [2, 3, 3, 3, 4, 7]), (168, [2, 3, 3, 4, 4, 6]), (84, [2, 3, 3, 4, 5, 5]), (672, [2, 3, 3, 14]), (84, [2, 3, 4, 4, 4, 5]), (-1932, [2, 3, 4, 13]), (672, [2, 3, 5, 12]), (672, [2, 3, 6, 11]), (204, [2, 3, 7, 10]), (672, [2, 3, 8, 9]), (504, [2, 4, 4, 12]), (504, [2, 4, 5, 11]), (504, [2, 4, 6, 10]), (420, [2, 4, 7, 9]), (252, [2, 4, 8, 8]), (288, [2, 5, 7, 8])]

def node84Piece97UnitOutput_sector0_chunk2 : RawPoly ℕ := [(288, [2, 6, 7, 7]), (2016, [2, 20]), (336, [3, 3, 4, 12]), (192, [3, 3, 7, 9]), (336, [3, 4, 4, 11]), (336, [3, 4, 5, 10]), (336, [3, 4, 6, 9]), (438, [3, 4, 7, 8]), (192, [3, 5, 7, 7]), (96, [3, 6, 6, 7]), (1344, [3, 19]), (144, [4, 4, 7, 7]), (144, [4, 5, 6, 7]), (1008, [4, 18]), (576, [7, 15])]

def node84Piece97UnitOutput_sector0 : RawPoly ℕ := [node84Piece97UnitOutput_sector0_chunk0, node84Piece97UnitOutput_sector0_chunk1, node84Piece97UnitOutput_sector0_chunk2].flatten

def node84Piece97UnitOutput : SectorVector := [(0, node84Piece97UnitOutput_sector0)]

theorem node84Piece97_check : neutralDirectS JR (-3) node84Piece97UnitInput = node84Piece97UnitOutput := by decide +kernel

theorem node84Piece97_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece97Input) = evaluate node84Piece97Output :=
  mode_of_scaled _ _ (-240/7) node84Piece97UnitInput node84Piece97UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece97_check)

def node84Piece98Input_sector0 : RawPoly ℕ := [(224/3, [2, 3, 5, 6])]

def node84Piece98Input : SectorVector := [(0, node84Piece98Input_sector0)]
def node84Piece98Output_sector0_chunk0 : RawPoly ℕ := [(896/3, [1, 1, 1, 2, 3, 3, 5, 6]), (448, [1, 1, 2, 2, 2, 3, 5, 6]), (5376, [1, 1, 2, 3, 5, 10]), (4480, [1, 1, 2, 3, 6, 9]), (2688, [1, 1, 2, 5, 6, 7]), (1792, [1, 1, 3, 5, 6, 6]), (10752, [1, 2, 2, 3, 5, 9]), (8960, [1, 2, 2, 3, 6, 8]), (5376, [1, 2, 2, 5, 6, 6]), (10752, [1, 2, 3, 3, 5, 8]), (8960, [1, 2, 3, 3, 6, 7]), (10752, [1, 2, 3, 4, 5, 7]), (8960, [1, 2, 3, 4, 6, 6]), (23296, [1, 2, 3, 5, 5, 6]), (53760, [1, 2, 3, 16]), (2688, [1, 2, 4, 4, 5, 6]), (32256, [1, 2, 5, 14]), (26880, [1, 2, 6, 13]), (3584, [1, 3, 3, 4, 5, 6]), (21504, [1, 3, 5, 13]), (17920, [1, 3, 6, 12]), (10752, [1, 5, 6, 10]), (5376, [2, 2, 2, 3, 5, 8]), (4480, [2, 2, 2, 3, 6, 7])]

def node84Piece98Output_sector0_chunk1 : RawPoly ℕ := [(2688, [2, 2, 2, 5, 5, 6]), (10752, [2, 2, 3, 3, 5, 7]), (8960, [2, 2, 3, 3, 6, 6]), (27104, [2, 2, 3, 4, 5, 6]), (5376, [2, 2, 3, 5, 5, 5]), (53760, [2, 2, 3, 15]), (32256, [2, 2, 5, 13]), (26880, [2, 2, 6, 12]), (38528/3, [2, 3, 3, 3, 5, 6]), (4480, [2, 3, 3, 4, 4, 6]), (10752, [2, 3, 3, 4, 5, 5]), (53760, [2, 3, 3, 14]), (1792, [2, 3, 4, 4, 4, 5]), (53760, [2, 3, 4, 13]), (-70336, [2, 3, 5, 12]), (-17920, [2, 3, 6, 11]), (53760, [2, 3, 7, 10]), (53760, [2, 3, 8, 9]), (32256, [2, 4, 5, 11]), (26880, [2, 4, 6, 10]), (32256, [2, 5, 5, 10]), (31360, [2, 5, 6, 9]), (32256, [2, 5, 7, 8]), (26880, [2, 6, 6, 8])]

def node84Piece98Output_sector0_chunk2 : RawPoly ℕ := [(13440, [2, 6, 7, 7]), (161280, [2, 20]), (21504, [3, 3, 5, 11]), (17920, [3, 3, 6, 10]), (21504, [3, 4, 5, 10]), (17920, [3, 4, 6, 9]), (21504, [3, 5, 5, 9]), (32704, [3, 5, 6, 8]), (10752, [3, 5, 7, 7]), (17920, [3, 6, 6, 7]), (107520, [3, 19]), (10752, [4, 5, 6, 7]), (10752, [5, 5, 6, 6]), (64512, [5, 17]), (53760, [6, 16])]

def node84Piece98Output_sector0 : RawPoly ℕ := [node84Piece98Output_sector0_chunk0, node84Piece98Output_sector0_chunk1, node84Piece98Output_sector0_chunk2].flatten

def node84Piece98Output : SectorVector := [(0, node84Piece98Output_sector0)]

def node84Piece98UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 5, 6])]

def node84Piece98UnitInput_sector0 : RawPoly ℕ := [node84Piece98UnitInput_sector0_chunk0].flatten

def node84Piece98UnitInput : SectorVector := [(0, node84Piece98UnitInput_sector0)]

def node84Piece98UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 5, 6]), (6, [1, 1, 2, 2, 2, 3, 5, 6]), (72, [1, 1, 2, 3, 5, 10]), (60, [1, 1, 2, 3, 6, 9]), (36, [1, 1, 2, 5, 6, 7]), (24, [1, 1, 3, 5, 6, 6]), (144, [1, 2, 2, 3, 5, 9]), (120, [1, 2, 2, 3, 6, 8]), (72, [1, 2, 2, 5, 6, 6]), (144, [1, 2, 3, 3, 5, 8]), (120, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 5, 7]), (120, [1, 2, 3, 4, 6, 6]), (312, [1, 2, 3, 5, 5, 6]), (720, [1, 2, 3, 16]), (36, [1, 2, 4, 4, 5, 6]), (432, [1, 2, 5, 14]), (360, [1, 2, 6, 13]), (48, [1, 3, 3, 4, 5, 6]), (288, [1, 3, 5, 13]), (240, [1, 3, 6, 12]), (144, [1, 5, 6, 10]), (72, [2, 2, 2, 3, 5, 8]), (60, [2, 2, 2, 3, 6, 7])]

def node84Piece98UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 2, 5, 5, 6]), (144, [2, 2, 3, 3, 5, 7]), (120, [2, 2, 3, 3, 6, 6]), (363, [2, 2, 3, 4, 5, 6]), (72, [2, 2, 3, 5, 5, 5]), (720, [2, 2, 3, 15]), (432, [2, 2, 5, 13]), (360, [2, 2, 6, 12]), (172, [2, 3, 3, 3, 5, 6]), (60, [2, 3, 3, 4, 4, 6]), (144, [2, 3, 3, 4, 5, 5]), (720, [2, 3, 3, 14]), (24, [2, 3, 4, 4, 4, 5]), (720, [2, 3, 4, 13]), (-942, [2, 3, 5, 12]), (-240, [2, 3, 6, 11]), (720, [2, 3, 7, 10]), (720, [2, 3, 8, 9]), (432, [2, 4, 5, 11]), (360, [2, 4, 6, 10]), (432, [2, 5, 5, 10]), (420, [2, 5, 6, 9]), (432, [2, 5, 7, 8]), (360, [2, 6, 6, 8])]

def node84Piece98UnitOutput_sector0_chunk2 : RawPoly ℕ := [(180, [2, 6, 7, 7]), (2160, [2, 20]), (288, [3, 3, 5, 11]), (240, [3, 3, 6, 10]), (288, [3, 4, 5, 10]), (240, [3, 4, 6, 9]), (288, [3, 5, 5, 9]), (438, [3, 5, 6, 8]), (144, [3, 5, 7, 7]), (240, [3, 6, 6, 7]), (1440, [3, 19]), (144, [4, 5, 6, 7]), (144, [5, 5, 6, 6]), (864, [5, 17]), (720, [6, 16])]

def node84Piece98UnitOutput_sector0 : RawPoly ℕ := [node84Piece98UnitOutput_sector0_chunk0, node84Piece98UnitOutput_sector0_chunk1, node84Piece98UnitOutput_sector0_chunk2].flatten

def node84Piece98UnitOutput : SectorVector := [(0, node84Piece98UnitOutput_sector0)]

theorem node84Piece98_check : neutralDirectS JR (-3) node84Piece98UnitInput = node84Piece98UnitOutput := by decide +kernel

theorem node84Piece98_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece98Input) = evaluate node84Piece98Output :=
  mode_of_scaled _ _ (224/3) node84Piece98UnitInput node84Piece98UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece98_check)

def node84Piece99Input_sector0 : RawPoly ℕ := [(-120, [2, 4, 4, 6])]

def node84Piece99Input : SectorVector := [(0, node84Piece99Input_sector0)]
def node84Piece99Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 2, 3, 4, 4, 6]), (-720, [1, 1, 2, 2, 2, 4, 4, 6]), (-8640, [1, 1, 2, 4, 4, 10]), (-11520, [1, 1, 2, 4, 6, 8]), (-2880, [1, 1, 4, 4, 6, 6]), (-17280, [1, 2, 2, 4, 4, 9]), (-23040, [1, 2, 2, 4, 6, 7]), (-17280, [1, 2, 3, 4, 4, 8]), (-23040, [1, 2, 3, 4, 6, 6]), (-17280, [1, 2, 4, 4, 4, 7]), (-44640, [1, 2, 4, 4, 5, 6]), (-138240, [1, 2, 4, 15]), (-46080, [1, 2, 6, 13]), (-5760, [1, 3, 4, 4, 4, 6]), (-34560, [1, 4, 4, 13]), (-46080, [1, 4, 6, 11]), (-8640, [2, 2, 2, 4, 4, 8]), (-11520, [2, 2, 2, 4, 6, 6]), (-17280, [2, 2, 3, 4, 4, 7]), (-23040, [2, 2, 3, 4, 5, 6]), (-32040, [2, 2, 4, 4, 4, 6]), (-8640, [2, 2, 4, 4, 5, 5]), (-138240, [2, 2, 4, 14]), (-46080, [2, 2, 6, 12])]

def node84Piece99Output_sector0_chunk1 : RawPoly ℕ := [(-23520, [2, 3, 3, 4, 4, 6]), (-17280, [2, 3, 4, 4, 4, 5]), (-138240, [2, 3, 4, 13]), (-46080, [2, 3, 6, 11]), (-2880, [2, 4, 4, 4, 4, 4]), (113040, [2, 4, 4, 12]), (-138240, [2, 4, 5, 11]), (-2880, [2, 4, 6, 10]), (-138240, [2, 4, 7, 9]), (-69120, [2, 4, 8, 8]), (-46080, [2, 5, 6, 9]), (-46080, [2, 6, 6, 8]), (-23040, [2, 6, 7, 7]), (-276480, [2, 20]), (-34560, [3, 4, 4, 11]), (-46080, [3, 4, 6, 9]), (-34560, [4, 4, 4, 10]), (-34560, [4, 4, 5, 9]), (-52560, [4, 4, 6, 8]), (-17280, [4, 4, 7, 7]), (-46080, [4, 5, 6, 7]), (-23040, [4, 6, 6, 6]), (-276480, [4, 18]), (-92160, [6, 16])]

def node84Piece99Output_sector0 : RawPoly ℕ := [node84Piece99Output_sector0_chunk0, node84Piece99Output_sector0_chunk1].flatten

def node84Piece99Output : SectorVector := [(0, node84Piece99Output_sector0)]

def node84Piece99UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 4, 6])]

def node84Piece99UnitInput_sector0 : RawPoly ℕ := [node84Piece99UnitInput_sector0_chunk0].flatten

def node84Piece99UnitInput : SectorVector := [(0, node84Piece99UnitInput_sector0)]

def node84Piece99UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 4, 6]), (6, [1, 1, 2, 2, 2, 4, 4, 6]), (72, [1, 1, 2, 4, 4, 10]), (96, [1, 1, 2, 4, 6, 8]), (24, [1, 1, 4, 4, 6, 6]), (144, [1, 2, 2, 4, 4, 9]), (192, [1, 2, 2, 4, 6, 7]), (144, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 6, 6]), (144, [1, 2, 4, 4, 4, 7]), (372, [1, 2, 4, 4, 5, 6]), (1152, [1, 2, 4, 15]), (384, [1, 2, 6, 13]), (48, [1, 3, 4, 4, 4, 6]), (288, [1, 4, 4, 13]), (384, [1, 4, 6, 11]), (72, [2, 2, 2, 4, 4, 8]), (96, [2, 2, 2, 4, 6, 6]), (144, [2, 2, 3, 4, 4, 7]), (192, [2, 2, 3, 4, 5, 6]), (267, [2, 2, 4, 4, 4, 6]), (72, [2, 2, 4, 4, 5, 5]), (1152, [2, 2, 4, 14]), (384, [2, 2, 6, 12])]

def node84Piece99UnitOutput_sector0_chunk1 : RawPoly ℕ := [(196, [2, 3, 3, 4, 4, 6]), (144, [2, 3, 4, 4, 4, 5]), (1152, [2, 3, 4, 13]), (384, [2, 3, 6, 11]), (24, [2, 4, 4, 4, 4, 4]), (-942, [2, 4, 4, 12]), (1152, [2, 4, 5, 11]), (24, [2, 4, 6, 10]), (1152, [2, 4, 7, 9]), (576, [2, 4, 8, 8]), (384, [2, 5, 6, 9]), (384, [2, 6, 6, 8]), (192, [2, 6, 7, 7]), (2304, [2, 20]), (288, [3, 4, 4, 11]), (384, [3, 4, 6, 9]), (288, [4, 4, 4, 10]), (288, [4, 4, 5, 9]), (438, [4, 4, 6, 8]), (144, [4, 4, 7, 7]), (384, [4, 5, 6, 7]), (192, [4, 6, 6, 6]), (2304, [4, 18]), (768, [6, 16])]

def node84Piece99UnitOutput_sector0 : RawPoly ℕ := [node84Piece99UnitOutput_sector0_chunk0, node84Piece99UnitOutput_sector0_chunk1].flatten

def node84Piece99UnitOutput : SectorVector := [(0, node84Piece99UnitOutput_sector0)]

theorem node84Piece99_check : neutralDirectS JR (-3) node84Piece99UnitInput = node84Piece99UnitOutput := by decide +kernel

theorem node84Piece99_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece99Input) = evaluate node84Piece99Output :=
  mode_of_scaled _ _ (-120) node84Piece99UnitInput node84Piece99UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece99_check)

def node84Piece100Input_sector0 : RawPoly ℕ := [(-288/5, [2, 4, 5, 5])]

def node84Piece100Input : SectorVector := [(0, node84Piece100Input_sector0)]
def node84Piece100Output_sector0_chunk0 : RawPoly ℕ := [(-1152/5, [1, 1, 1, 2, 3, 4, 5, 5]), (-1728/5, [1, 1, 2, 2, 2, 4, 5, 5]), (-6912, [1, 1, 2, 4, 5, 9]), (-13824/5, [1, 1, 2, 5, 5, 8]), (-6912/5, [1, 1, 4, 5, 5, 6]), (-13824, [1, 2, 2, 4, 5, 8]), (-27648/5, [1, 2, 2, 5, 5, 7]), (-13824, [1, 2, 3, 4, 5, 7]), (-27648/5, [1, 2, 3, 5, 5, 6]), (-13824, [1, 2, 4, 4, 5, 6]), (-72576/5, [1, 2, 4, 5, 5, 5]), (-34560, [1, 2, 4, 15]), (-55296, [1, 2, 5, 14]), (-13824/5, [1, 3, 4, 4, 5, 5]), (-27648, [1, 4, 5, 12]), (-55296/5, [1, 5, 5, 11]), (-6912, [2, 2, 2, 4, 5, 7]), (-13824/5, [2, 2, 2, 5, 5, 6]), (-13824, [2, 2, 3, 4, 5, 6]), (-27648/5, [2, 2, 3, 5, 5, 5]), (-18144, [2, 2, 4, 4, 5, 5]), (-34560, [2, 2, 4, 14]), (-55296, [2, 2, 5, 13]), (-56448/5, [2, 3, 3, 4, 5, 5])]

def node84Piece100Output_sector0_chunk1 : RawPoly ℕ := [(-6912, [2, 3, 4, 4, 4, 5]), (-34560, [2, 3, 4, 13]), (-55296, [2, 3, 5, 12]), (-34560, [2, 4, 4, 12]), (62208, [2, 4, 5, 11]), (-34560, [2, 4, 6, 10]), (-34560, [2, 4, 7, 9]), (-17280, [2, 4, 8, 8]), (-58752/5, [2, 5, 5, 10]), (-55296, [2, 5, 6, 9]), (-55296, [2, 5, 7, 8]), (-138240, [2, 20]), (-27648, [3, 4, 5, 10]), (-55296/5, [3, 5, 5, 9]), (-27648, [4, 4, 5, 9]), (-126144/5, [4, 5, 5, 8]), (-27648, [4, 5, 6, 7]), (-69120, [4, 18]), (-55296/5, [5, 5, 5, 7]), (-27648/5, [5, 5, 6, 6]), (-110592, [5, 17])]

def node84Piece100Output_sector0 : RawPoly ℕ := [node84Piece100Output_sector0_chunk0, node84Piece100Output_sector0_chunk1].flatten

def node84Piece100Output : SectorVector := [(0, node84Piece100Output_sector0)]

def node84Piece100UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 5, 5])]

def node84Piece100UnitInput_sector0 : RawPoly ℕ := [node84Piece100UnitInput_sector0_chunk0].flatten

def node84Piece100UnitInput : SectorVector := [(0, node84Piece100UnitInput_sector0)]

def node84Piece100UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 5, 5]), (6, [1, 1, 2, 2, 2, 4, 5, 5]), (120, [1, 1, 2, 4, 5, 9]), (48, [1, 1, 2, 5, 5, 8]), (24, [1, 1, 4, 5, 5, 6]), (240, [1, 2, 2, 4, 5, 8]), (96, [1, 2, 2, 5, 5, 7]), (240, [1, 2, 3, 4, 5, 7]), (96, [1, 2, 3, 5, 5, 6]), (240, [1, 2, 4, 4, 5, 6]), (252, [1, 2, 4, 5, 5, 5]), (600, [1, 2, 4, 15]), (960, [1, 2, 5, 14]), (48, [1, 3, 4, 4, 5, 5]), (480, [1, 4, 5, 12]), (192, [1, 5, 5, 11]), (120, [2, 2, 2, 4, 5, 7]), (48, [2, 2, 2, 5, 5, 6]), (240, [2, 2, 3, 4, 5, 6]), (96, [2, 2, 3, 5, 5, 5]), (315, [2, 2, 4, 4, 5, 5]), (600, [2, 2, 4, 14]), (960, [2, 2, 5, 13]), (196, [2, 3, 3, 4, 5, 5])]

def node84Piece100UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [2, 3, 4, 4, 4, 5]), (600, [2, 3, 4, 13]), (960, [2, 3, 5, 12]), (600, [2, 4, 4, 12]), (-1080, [2, 4, 5, 11]), (600, [2, 4, 6, 10]), (600, [2, 4, 7, 9]), (300, [2, 4, 8, 8]), (204, [2, 5, 5, 10]), (960, [2, 5, 6, 9]), (960, [2, 5, 7, 8]), (2400, [2, 20]), (480, [3, 4, 5, 10]), (192, [3, 5, 5, 9]), (480, [4, 4, 5, 9]), (438, [4, 5, 5, 8]), (480, [4, 5, 6, 7]), (1200, [4, 18]), (192, [5, 5, 5, 7]), (96, [5, 5, 6, 6]), (1920, [5, 17])]

def node84Piece100UnitOutput_sector0 : RawPoly ℕ := [node84Piece100UnitOutput_sector0_chunk0, node84Piece100UnitOutput_sector0_chunk1].flatten

def node84Piece100UnitOutput : SectorVector := [(0, node84Piece100UnitOutput_sector0)]

theorem node84Piece100_check : neutralDirectS JR (-3) node84Piece100UnitInput = node84Piece100UnitOutput := by decide +kernel

theorem node84Piece100_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece100Input) = evaluate node84Piece100Output :=
  mode_of_scaled _ _ (-288/5) node84Piece100UnitInput node84Piece100UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece100_check)

def node84Piece101Input_sector0 : RawPoly ℕ := [(-480/7, [2, 14])]

def node84Piece101Input : SectorVector := [(0, node84Piece101Input_sector0)]
def node84Piece101Output_sector0_chunk0 : RawPoly ℕ := [(-1920/7, [1, 1, 1, 2, 3, 14]), (-2880/7, [1, 1, 2, 2, 2, 14]), (-11520, [1, 1, 2, 18]), (-11520/7, [1, 1, 6, 14]), (-23040, [1, 2, 2, 17]), (-23040, [1, 2, 3, 16]), (-23040, [1, 2, 4, 15]), (-178560/7, [1, 2, 5, 14]), (-23040, [1, 2, 6, 13]), (-23040, [1, 2, 7, 12]), (-23040, [1, 2, 8, 11]), (-23040, [1, 2, 9, 10]), (-23040/7, [1, 3, 4, 14]), (-46080, [1, 21]), (-11520, [2, 2, 2, 16]), (-23040, [2, 2, 3, 15]), (-174240/7, [2, 2, 4, 14]), (-23040, [2, 2, 5, 13]), (-23040, [2, 2, 6, 12]), (-23040, [2, 2, 7, 11]), (-23040, [2, 2, 8, 10]), (-11520, [2, 2, 9, 9]), (-13440, [2, 3, 3, 14]), (-23040, [2, 3, 4, 13])]

def node84Piece101Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 3, 5, 12]), (-23040, [2, 3, 6, 11]), (-23040, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-11520, [2, 4, 4, 12]), (-23040, [2, 4, 5, 11]), (-23040, [2, 4, 6, 10]), (-23040, [2, 4, 7, 9]), (-11520, [2, 4, 8, 8]), (-11520, [2, 5, 5, 10]), (-23040, [2, 5, 6, 9]), (-23040, [2, 5, 7, 8]), (-11520, [2, 6, 6, 8]), (-11520, [2, 6, 7, 7]), (1333440, [2, 20]), (-46080, [3, 19]), (-46080, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-210240/7, [8, 14]), (-46080, [9, 13]), (-46080, [10, 12]), (-23040, [11, 11])]

def node84Piece101Output_sector0 : RawPoly ℕ := [node84Piece101Output_sector0_chunk0, node84Piece101Output_sector0_chunk1].flatten

def node84Piece101Output : SectorVector := [(0, node84Piece101Output_sector0)]

def node84Piece101UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 14])]

def node84Piece101UnitInput_sector0 : RawPoly ℕ := [node84Piece101UnitInput_sector0_chunk0].flatten

def node84Piece101UnitInput : SectorVector := [(0, node84Piece101UnitInput_sector0)]

def node84Piece101UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 14]), (6, [1, 1, 2, 2, 2, 14]), (168, [1, 1, 2, 18]), (24, [1, 1, 6, 14]), (336, [1, 2, 2, 17]), (336, [1, 2, 3, 16]), (336, [1, 2, 4, 15]), (372, [1, 2, 5, 14]), (336, [1, 2, 6, 13]), (336, [1, 2, 7, 12]), (336, [1, 2, 8, 11]), (336, [1, 2, 9, 10]), (48, [1, 3, 4, 14]), (672, [1, 21]), (168, [2, 2, 2, 16]), (336, [2, 2, 3, 15]), (363, [2, 2, 4, 14]), (336, [2, 2, 5, 13]), (336, [2, 2, 6, 12]), (336, [2, 2, 7, 11]), (336, [2, 2, 8, 10]), (168, [2, 2, 9, 9]), (196, [2, 3, 3, 14]), (336, [2, 3, 4, 13])]

def node84Piece101UnitOutput_sector0_chunk1 : RawPoly ℕ := [(336, [2, 3, 5, 12]), (336, [2, 3, 6, 11]), (336, [2, 3, 7, 10]), (336, [2, 3, 8, 9]), (168, [2, 4, 4, 12]), (336, [2, 4, 5, 11]), (336, [2, 4, 6, 10]), (336, [2, 4, 7, 9]), (168, [2, 4, 8, 8]), (168, [2, 5, 5, 10]), (336, [2, 5, 6, 9]), (336, [2, 5, 7, 8]), (168, [2, 6, 6, 8]), (168, [2, 6, 7, 7]), (-19446, [2, 20]), (672, [3, 19]), (672, [4, 18]), (672, [5, 17]), (672, [6, 16]), (672, [7, 15]), (438, [8, 14]), (672, [9, 13]), (672, [10, 12]), (336, [11, 11])]

def node84Piece101UnitOutput_sector0 : RawPoly ℕ := [node84Piece101UnitOutput_sector0_chunk0, node84Piece101UnitOutput_sector0_chunk1].flatten

def node84Piece101UnitOutput : SectorVector := [(0, node84Piece101UnitOutput_sector0)]

theorem node84Piece101_check : neutralDirectS JR (-3) node84Piece101UnitInput = node84Piece101UnitOutput := by decide +kernel

theorem node84Piece101_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece101Input) = evaluate node84Piece101Output :=
  mode_of_scaled _ _ (-480/7) node84Piece101UnitInput node84Piece101UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece101_check)

def node84Piece102Input_sector0 : RawPoly ℕ := [(1280/21, [3, 3, 3, 7])]

def node84Piece102Input : SectorVector := [(0, node84Piece102Input_sector0)]
def node84Piece102Output_sector0_chunk0 : RawPoly ℕ := [(5120/21, [1, 1, 1, 3, 3, 3, 3, 7]), (2560/7, [1, 1, 2, 2, 3, 3, 3, 7]), (5120, [1, 1, 3, 3, 3, 11]), (46080/7, [1, 1, 3, 3, 7, 7]), (10240, [1, 2, 3, 3, 3, 10]), (92160/7, [1, 2, 3, 3, 6, 7]), (10240, [1, 3, 3, 3, 3, 9]), (10240, [1, 3, 3, 3, 4, 8]), (158720/7, [1, 3, 3, 3, 5, 7]), (5120, [1, 3, 3, 3, 6, 6]), (46080/7, [1, 3, 3, 4, 4, 7]), (92160, [1, 3, 3, 15]), (276480/7, [1, 3, 7, 11]), (5120, [2, 2, 3, 3, 3, 9]), (46080/7, [2, 2, 3, 3, 5, 7]), (10240, [2, 3, 3, 3, 3, 8]), (165120/7, [2, 3, 3, 3, 4, 7]), (10240, [2, 3, 3, 3, 5, 6]), (92160, [2, 3, 3, 14]), (276480/7, [2, 3, 7, 10]), (158720/21, [3, 3, 3, 3, 3, 7]), (10240, [3, 3, 3, 3, 4, 6]), (5120, [3, 3, 3, 3, 5, 5]), (5120, [3, 3, 3, 4, 4, 5])]

def node84Piece102Output_sector0_chunk1 : RawPoly ℕ := [(-117760, [3, 3, 3, 13]), (92160, [3, 3, 4, 12]), (92160, [3, 3, 5, 11]), (92160, [3, 3, 6, 10]), (261120/7, [3, 3, 7, 9]), (46080, [3, 3, 8, 8]), (276480/7, [3, 4, 7, 8]), (276480/7, [3, 5, 7, 7]), (138240/7, [3, 6, 6, 7]), (276480, [3, 19]), (276480/7, [7, 15])]

def node84Piece102Output_sector0 : RawPoly ℕ := [node84Piece102Output_sector0_chunk0, node84Piece102Output_sector0_chunk1].flatten

def node84Piece102Output : SectorVector := [(0, node84Piece102Output_sector0)]

def node84Piece102UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 7])]

def node84Piece102UnitInput_sector0 : RawPoly ℕ := [node84Piece102UnitInput_sector0_chunk0].flatten

def node84Piece102UnitInput : SectorVector := [(0, node84Piece102UnitInput_sector0)]

def node84Piece102UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 3, 7]), (6, [1, 1, 2, 2, 3, 3, 3, 7]), (84, [1, 1, 3, 3, 3, 11]), (108, [1, 1, 3, 3, 7, 7]), (168, [1, 2, 3, 3, 3, 10]), (216, [1, 2, 3, 3, 6, 7]), (168, [1, 3, 3, 3, 3, 9]), (168, [1, 3, 3, 3, 4, 8]), (372, [1, 3, 3, 3, 5, 7]), (84, [1, 3, 3, 3, 6, 6]), (108, [1, 3, 3, 4, 4, 7]), (1512, [1, 3, 3, 15]), (648, [1, 3, 7, 11]), (84, [2, 2, 3, 3, 3, 9]), (108, [2, 2, 3, 3, 5, 7]), (168, [2, 3, 3, 3, 3, 8]), (387, [2, 3, 3, 3, 4, 7]), (168, [2, 3, 3, 3, 5, 6]), (1512, [2, 3, 3, 14]), (648, [2, 3, 7, 10]), (124, [3, 3, 3, 3, 3, 7]), (168, [3, 3, 3, 3, 4, 6]), (84, [3, 3, 3, 3, 5, 5]), (84, [3, 3, 3, 4, 4, 5])]

def node84Piece102UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-1932, [3, 3, 3, 13]), (1512, [3, 3, 4, 12]), (1512, [3, 3, 5, 11]), (1512, [3, 3, 6, 10]), (612, [3, 3, 7, 9]), (756, [3, 3, 8, 8]), (648, [3, 4, 7, 8]), (648, [3, 5, 7, 7]), (324, [3, 6, 6, 7]), (4536, [3, 19]), (648, [7, 15])]

def node84Piece102UnitOutput_sector0 : RawPoly ℕ := [node84Piece102UnitOutput_sector0_chunk0, node84Piece102UnitOutput_sector0_chunk1].flatten

def node84Piece102UnitOutput : SectorVector := [(0, node84Piece102UnitOutput_sector0)]

theorem node84Piece102_check : neutralDirectS JR (-3) node84Piece102UnitInput = node84Piece102UnitOutput := by decide +kernel

theorem node84Piece102_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece102Input) = evaluate node84Piece102Output :=
  mode_of_scaled _ _ (1280/21) node84Piece102UnitInput node84Piece102UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece102_check)

def node84Piece103Input_sector0 : RawPoly ℕ := [(640/9, [3, 3, 4, 6])]

def node84Piece103Input : SectorVector := [(0, node84Piece103Input_sector0)]
def node84Piece103Output_sector0_chunk0 : RawPoly ℕ := [(2560/9, [1, 1, 1, 3, 3, 3, 4, 6]), (1280/3, [1, 1, 2, 2, 3, 3, 4, 6]), (5120, [1, 1, 3, 3, 4, 10]), (10240/3, [1, 1, 3, 3, 6, 8]), (5120, [1, 1, 3, 4, 6, 7]), (10240, [1, 2, 3, 3, 4, 9]), (20480/3, [1, 2, 3, 3, 6, 7]), (10240, [1, 2, 3, 4, 6, 6]), (10240, [1, 3, 3, 3, 4, 8]), (20480/3, [1, 3, 3, 3, 6, 6]), (10240, [1, 3, 3, 4, 4, 7]), (79360/3, [1, 3, 3, 4, 5, 6]), (40960, [1, 3, 3, 15]), (5120, [1, 3, 4, 4, 4, 6]), (61440, [1, 3, 4, 14]), (40960, [1, 3, 6, 12]), (15360, [1, 4, 6, 11]), (5120, [2, 2, 3, 3, 4, 8]), (10240/3, [2, 2, 3, 3, 6, 6]), (5120, [2, 2, 3, 4, 5, 6]), (10240, [2, 3, 3, 3, 4, 7]), (20480/3, [2, 3, 3, 3, 5, 6]), (72320/3, [2, 3, 3, 4, 4, 6]), (5120, [2, 3, 3, 4, 5, 5])]

def node84Piece103Output_sector0_chunk1 : RawPoly ℕ := [(40960, [2, 3, 3, 14]), (61440, [2, 3, 4, 13]), (40960, [2, 3, 6, 11]), (15360, [2, 4, 6, 10]), (94720/9, [3, 3, 3, 3, 4, 6]), (10240, [3, 3, 3, 4, 4, 5]), (40960, [3, 3, 3, 13]), (5120/3, [3, 3, 4, 4, 4, 4]), (-200960/3, [3, 3, 4, 12]), (40960, [3, 3, 5, 11]), (43520/3, [3, 3, 6, 10]), (40960, [3, 3, 7, 9]), (20480, [3, 3, 8, 8]), (61440, [3, 4, 4, 11]), (61440, [3, 4, 5, 10]), (133120/3, [3, 4, 6, 9]), (61440, [3, 4, 7, 8]), (40960, [3, 5, 6, 8]), (40960, [3, 6, 6, 7]), (245760, [3, 19]), (15360, [4, 4, 6, 8]), (15360, [4, 5, 6, 7]), (7680, [4, 6, 6, 6]), (92160, [4, 18])]

def node84Piece103Output_sector0_chunk2 : RawPoly ℕ := [(61440, [6, 16])]

def node84Piece103Output_sector0 : RawPoly ℕ := [node84Piece103Output_sector0_chunk0, node84Piece103Output_sector0_chunk1, node84Piece103Output_sector0_chunk2].flatten

def node84Piece103Output : SectorVector := [(0, node84Piece103Output_sector0)]

def node84Piece103UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 4, 6])]

def node84Piece103UnitInput_sector0 : RawPoly ℕ := [node84Piece103UnitInput_sector0_chunk0].flatten

def node84Piece103UnitInput : SectorVector := [(0, node84Piece103UnitInput_sector0)]

def node84Piece103UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 4, 6]), (6, [1, 1, 2, 2, 3, 3, 4, 6]), (72, [1, 1, 3, 3, 4, 10]), (48, [1, 1, 3, 3, 6, 8]), (72, [1, 1, 3, 4, 6, 7]), (144, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 6, 6]), (144, [1, 3, 3, 3, 4, 8]), (96, [1, 3, 3, 3, 6, 6]), (144, [1, 3, 3, 4, 4, 7]), (372, [1, 3, 3, 4, 5, 6]), (576, [1, 3, 3, 15]), (72, [1, 3, 4, 4, 4, 6]), (864, [1, 3, 4, 14]), (576, [1, 3, 6, 12]), (216, [1, 4, 6, 11]), (72, [2, 2, 3, 3, 4, 8]), (48, [2, 2, 3, 3, 6, 6]), (72, [2, 2, 3, 4, 5, 6]), (144, [2, 3, 3, 3, 4, 7]), (96, [2, 3, 3, 3, 5, 6]), (339, [2, 3, 3, 4, 4, 6]), (72, [2, 3, 3, 4, 5, 5])]

def node84Piece103UnitOutput_sector0_chunk1 : RawPoly ℕ := [(576, [2, 3, 3, 14]), (864, [2, 3, 4, 13]), (576, [2, 3, 6, 11]), (216, [2, 4, 6, 10]), (148, [3, 3, 3, 3, 4, 6]), (144, [3, 3, 3, 4, 4, 5]), (576, [3, 3, 3, 13]), (24, [3, 3, 4, 4, 4, 4]), (-942, [3, 3, 4, 12]), (576, [3, 3, 5, 11]), (204, [3, 3, 6, 10]), (576, [3, 3, 7, 9]), (288, [3, 3, 8, 8]), (864, [3, 4, 4, 11]), (864, [3, 4, 5, 10]), (624, [3, 4, 6, 9]), (864, [3, 4, 7, 8]), (576, [3, 5, 6, 8]), (576, [3, 6, 6, 7]), (3456, [3, 19]), (216, [4, 4, 6, 8]), (216, [4, 5, 6, 7]), (108, [4, 6, 6, 6]), (1296, [4, 18])]

def node84Piece103UnitOutput_sector0_chunk2 : RawPoly ℕ := [(864, [6, 16])]

def node84Piece103UnitOutput_sector0 : RawPoly ℕ := [node84Piece103UnitOutput_sector0_chunk0, node84Piece103UnitOutput_sector0_chunk1, node84Piece103UnitOutput_sector0_chunk2].flatten

def node84Piece103UnitOutput : SectorVector := [(0, node84Piece103UnitOutput_sector0)]

theorem node84Piece103_check : neutralDirectS JR (-3) node84Piece103UnitInput = node84Piece103UnitOutput := by decide +kernel

theorem node84Piece103_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece103Input) = evaluate node84Piece103Output :=
  mode_of_scaled _ _ (640/9) node84Piece103UnitInput node84Piece103UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece103_check)

def node84Piece104Input_sector0 : RawPoly ℕ := [(896/15, [3, 3, 5, 5])]

def node84Piece104Input : SectorVector := [(0, node84Piece104Input_sector0)]
def node84Piece104Output_sector0_chunk0 : RawPoly ℕ := [(3584/15, [1, 1, 1, 3, 3, 3, 5, 5]), (1792/5, [1, 1, 2, 2, 3, 3, 5, 5]), (7168, [1, 1, 3, 3, 5, 9]), (21504/5, [1, 1, 3, 5, 5, 7]), (14336, [1, 2, 3, 3, 5, 8]), (43008/5, [1, 2, 3, 5, 5, 6]), (14336, [1, 3, 3, 3, 5, 7]), (14336, [1, 3, 3, 4, 5, 6]), (75264/5, [1, 3, 3, 5, 5, 5]), (35840, [1, 3, 3, 15]), (21504/5, [1, 3, 4, 4, 5, 5]), (86016, [1, 3, 5, 13]), (64512/5, [1, 5, 5, 11]), (7168, [2, 2, 3, 3, 5, 7]), (21504/5, [2, 2, 3, 5, 5, 5]), (14336, [2, 3, 3, 3, 5, 6]), (115584/5, [2, 3, 3, 4, 5, 5]), (35840, [2, 3, 3, 14]), (86016, [2, 3, 5, 12]), (64512/5, [2, 5, 5, 10]), (132608/15, [3, 3, 3, 3, 5, 5]), (7168, [3, 3, 3, 4, 4, 5]), (35840, [3, 3, 3, 13]), (35840, [3, 3, 4, 12])]

def node84Piece104Output_sector0_chunk1 : RawPoly ℕ := [(-64512, [3, 3, 5, 11]), (35840, [3, 3, 6, 10]), (35840, [3, 3, 7, 9]), (17920, [3, 3, 8, 8]), (86016, [3, 4, 5, 10]), (186368/5, [3, 5, 5, 9]), (86016, [3, 5, 6, 8]), (43008, [3, 5, 7, 7]), (215040, [3, 19]), (64512/5, [4, 5, 5, 8]), (64512/5, [5, 5, 5, 7]), (32256/5, [5, 5, 6, 6]), (129024, [5, 17])]

def node84Piece104Output_sector0 : RawPoly ℕ := [node84Piece104Output_sector0_chunk0, node84Piece104Output_sector0_chunk1].flatten

def node84Piece104Output : SectorVector := [(0, node84Piece104Output_sector0)]

def node84Piece104UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 5, 5])]

def node84Piece104UnitInput_sector0 : RawPoly ℕ := [node84Piece104UnitInput_sector0_chunk0].flatten

def node84Piece104UnitInput : SectorVector := [(0, node84Piece104UnitInput_sector0)]

def node84Piece104UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 5, 5]), (6, [1, 1, 2, 2, 3, 3, 5, 5]), (120, [1, 1, 3, 3, 5, 9]), (72, [1, 1, 3, 5, 5, 7]), (240, [1, 2, 3, 3, 5, 8]), (144, [1, 2, 3, 5, 5, 6]), (240, [1, 3, 3, 3, 5, 7]), (240, [1, 3, 3, 4, 5, 6]), (252, [1, 3, 3, 5, 5, 5]), (600, [1, 3, 3, 15]), (72, [1, 3, 4, 4, 5, 5]), (1440, [1, 3, 5, 13]), (216, [1, 5, 5, 11]), (120, [2, 2, 3, 3, 5, 7]), (72, [2, 2, 3, 5, 5, 5]), (240, [2, 3, 3, 3, 5, 6]), (387, [2, 3, 3, 4, 5, 5]), (600, [2, 3, 3, 14]), (1440, [2, 3, 5, 12]), (216, [2, 5, 5, 10]), (148, [3, 3, 3, 3, 5, 5]), (120, [3, 3, 3, 4, 4, 5]), (600, [3, 3, 3, 13]), (600, [3, 3, 4, 12])]

def node84Piece104UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-1080, [3, 3, 5, 11]), (600, [3, 3, 6, 10]), (600, [3, 3, 7, 9]), (300, [3, 3, 8, 8]), (1440, [3, 4, 5, 10]), (624, [3, 5, 5, 9]), (1440, [3, 5, 6, 8]), (720, [3, 5, 7, 7]), (3600, [3, 19]), (216, [4, 5, 5, 8]), (216, [5, 5, 5, 7]), (108, [5, 5, 6, 6]), (2160, [5, 17])]

def node84Piece104UnitOutput_sector0 : RawPoly ℕ := [node84Piece104UnitOutput_sector0_chunk0, node84Piece104UnitOutput_sector0_chunk1].flatten

def node84Piece104UnitOutput : SectorVector := [(0, node84Piece104UnitOutput_sector0)]

theorem node84Piece104_check : neutralDirectS JR (-3) node84Piece104UnitInput = node84Piece104UnitOutput := by decide +kernel

theorem node84Piece104_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece104Input) = evaluate node84Piece104Output :=
  mode_of_scaled _ _ (896/15) node84Piece104UnitInput node84Piece104UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece104_check)

def node84Piece105Input_sector0 : RawPoly ℕ := [(-8, [3, 4, 4, 5])]

def node84Piece105Input : SectorVector := [(0, node84Piece105Input_sector0)]
def node84Piece105Output_sector0_chunk0 : RawPoly ℕ := [(-32, [1, 1, 1, 3, 3, 4, 4, 5]), (-48, [1, 1, 2, 2, 3, 4, 4, 5]), (-480, [1, 1, 3, 4, 4, 9]), (-768, [1, 1, 3, 4, 5, 8]), (-288, [1, 1, 4, 4, 5, 7]), (-960, [1, 2, 3, 4, 4, 8]), (-1536, [1, 2, 3, 4, 5, 7]), (-576, [1, 2, 4, 4, 5, 6]), (-960, [1, 3, 3, 4, 4, 7]), (-1536, [1, 3, 3, 4, 5, 6]), (-960, [1, 3, 4, 4, 4, 6]), (-2496, [1, 3, 4, 4, 5, 5]), (-7680, [1, 3, 4, 14]), (-3072, [1, 3, 5, 13]), (-288, [1, 4, 4, 4, 4, 5]), (-2880, [1, 4, 4, 13]), (-4608, [1, 4, 5, 12]), (-480, [2, 2, 3, 4, 4, 7]), (-768, [2, 2, 3, 4, 5, 6]), (-288, [2, 2, 4, 4, 5, 5]), (-960, [2, 3, 3, 4, 4, 6]), (-1536, [2, 3, 3, 4, 5, 5]), (-2328, [2, 3, 4, 4, 4, 5]), (-7680, [2, 3, 4, 13])]

def node84Piece105Output_sector0_chunk1 : RawPoly ℕ := [(-3072, [2, 3, 5, 12]), (-2880, [2, 4, 4, 12]), (-4608, [2, 4, 5, 11]), (-1376, [3, 3, 3, 4, 4, 5]), (-480, [3, 3, 4, 4, 4, 4]), (-7680, [3, 3, 4, 12]), (-3072, [3, 3, 5, 11]), (1920, [3, 4, 4, 11]), (-192, [3, 4, 5, 10]), (-7680, [3, 4, 6, 9]), (-7680, [3, 4, 7, 8]), (-3072, [3, 5, 5, 9]), (-3072, [3, 5, 6, 8]), (-1536, [3, 5, 7, 7]), (-15360, [3, 19]), (-2880, [4, 4, 4, 10]), (-3360, [4, 4, 5, 9]), (-2880, [4, 4, 6, 8]), (-1440, [4, 4, 7, 7]), (-4608, [4, 5, 5, 8]), (-4608, [4, 5, 6, 7]), (-23040, [4, 18]), (-9216, [5, 17])]

def node84Piece105Output_sector0 : RawPoly ℕ := [node84Piece105Output_sector0_chunk0, node84Piece105Output_sector0_chunk1].flatten

def node84Piece105Output : SectorVector := [(0, node84Piece105Output_sector0)]

def node84Piece105UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 4, 4, 5])]

def node84Piece105UnitInput_sector0 : RawPoly ℕ := [node84Piece105UnitInput_sector0_chunk0].flatten

def node84Piece105UnitInput : SectorVector := [(0, node84Piece105UnitInput_sector0)]

def node84Piece105UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 4, 4, 5]), (6, [1, 1, 2, 2, 3, 4, 4, 5]), (60, [1, 1, 3, 4, 4, 9]), (96, [1, 1, 3, 4, 5, 8]), (36, [1, 1, 4, 4, 5, 7]), (120, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (72, [1, 2, 4, 4, 5, 6]), (120, [1, 3, 3, 4, 4, 7]), (192, [1, 3, 3, 4, 5, 6]), (120, [1, 3, 4, 4, 4, 6]), (312, [1, 3, 4, 4, 5, 5]), (960, [1, 3, 4, 14]), (384, [1, 3, 5, 13]), (36, [1, 4, 4, 4, 4, 5]), (360, [1, 4, 4, 13]), (576, [1, 4, 5, 12]), (60, [2, 2, 3, 4, 4, 7]), (96, [2, 2, 3, 4, 5, 6]), (36, [2, 2, 4, 4, 5, 5]), (120, [2, 3, 3, 4, 4, 6]), (192, [2, 3, 3, 4, 5, 5]), (291, [2, 3, 4, 4, 4, 5]), (960, [2, 3, 4, 13])]

def node84Piece105UnitOutput_sector0_chunk1 : RawPoly ℕ := [(384, [2, 3, 5, 12]), (360, [2, 4, 4, 12]), (576, [2, 4, 5, 11]), (172, [3, 3, 3, 4, 4, 5]), (60, [3, 3, 4, 4, 4, 4]), (960, [3, 3, 4, 12]), (384, [3, 3, 5, 11]), (-240, [3, 4, 4, 11]), (24, [3, 4, 5, 10]), (960, [3, 4, 6, 9]), (960, [3, 4, 7, 8]), (384, [3, 5, 5, 9]), (384, [3, 5, 6, 8]), (192, [3, 5, 7, 7]), (1920, [3, 19]), (360, [4, 4, 4, 10]), (420, [4, 4, 5, 9]), (360, [4, 4, 6, 8]), (180, [4, 4, 7, 7]), (576, [4, 5, 5, 8]), (576, [4, 5, 6, 7]), (2880, [4, 18]), (1152, [5, 17])]

def node84Piece105UnitOutput_sector0 : RawPoly ℕ := [node84Piece105UnitOutput_sector0_chunk0, node84Piece105UnitOutput_sector0_chunk1].flatten

def node84Piece105UnitOutput : SectorVector := [(0, node84Piece105UnitOutput_sector0)]

theorem node84Piece105_check : neutralDirectS JR (-3) node84Piece105UnitInput = node84Piece105UnitOutput := by decide +kernel

theorem node84Piece105_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece105Input) = evaluate node84Piece105Output :=
  mode_of_scaled _ _ (-8) node84Piece105UnitInput node84Piece105UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece105_check)

def node84Piece106Input_sector0 : RawPoly ℕ := [(960/13, [3, 13])]

def node84Piece106Input : SectorVector := [(0, node84Piece106Input_sector0)]
def node84Piece106Output_sector0_chunk0 : RawPoly ℕ := [(3840/13, [1, 1, 1, 3, 3, 13]), (5760/13, [1, 1, 2, 2, 3, 13]), (11520, [1, 1, 3, 17]), (34560/13, [1, 1, 7, 13]), (23040, [1, 2, 3, 16]), (69120/13, [1, 2, 6, 13]), (23040, [1, 3, 3, 15]), (23040, [1, 3, 4, 14]), (357120/13, [1, 3, 5, 13]), (23040, [1, 3, 6, 12]), (23040, [1, 3, 7, 11]), (23040, [1, 3, 8, 10]), (11520, [1, 3, 9, 9]), (34560/13, [1, 4, 4, 13]), (69120, [1, 21]), (11520, [2, 2, 3, 15]), (34560/13, [2, 2, 5, 13]), (23040, [2, 3, 3, 14]), (371520/13, [2, 3, 4, 13]), (23040, [2, 3, 5, 12]), (23040, [2, 3, 6, 11]), (23040, [2, 3, 7, 10]), (23040, [2, 3, 8, 9]), (69120, [2, 20])]

def node84Piece106Output_sector0_chunk1 : RawPoly ℕ := [(165120/13, [3, 3, 3, 13]), (23040, [3, 3, 4, 12]), (23040, [3, 3, 5, 11]), (23040, [3, 3, 6, 10]), (23040, [3, 3, 7, 9]), (11520, [3, 3, 8, 8]), (11520, [3, 4, 4, 11]), (23040, [3, 4, 5, 10]), (23040, [3, 4, 6, 9]), (23040, [3, 4, 7, 8]), (11520, [3, 5, 5, 9]), (23040, [3, 5, 6, 8]), (11520, [3, 5, 7, 7]), (11520, [3, 6, 6, 7]), (-1152000, [3, 19]), (69120, [4, 18]), (69120, [5, 17]), (69120, [6, 16]), (69120, [7, 15]), (69120, [8, 14]), (403200/13, [9, 13]), (69120, [10, 12]), (34560, [11, 11])]

def node84Piece106Output_sector0 : RawPoly ℕ := [node84Piece106Output_sector0_chunk0, node84Piece106Output_sector0_chunk1].flatten

def node84Piece106Output : SectorVector := [(0, node84Piece106Output_sector0)]

def node84Piece106UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 13])]

def node84Piece106UnitInput_sector0 : RawPoly ℕ := [node84Piece106UnitInput_sector0_chunk0].flatten

def node84Piece106UnitInput : SectorVector := [(0, node84Piece106UnitInput_sector0)]

def node84Piece106UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 13]), (6, [1, 1, 2, 2, 3, 13]), (156, [1, 1, 3, 17]), (36, [1, 1, 7, 13]), (312, [1, 2, 3, 16]), (72, [1, 2, 6, 13]), (312, [1, 3, 3, 15]), (312, [1, 3, 4, 14]), (372, [1, 3, 5, 13]), (312, [1, 3, 6, 12]), (312, [1, 3, 7, 11]), (312, [1, 3, 8, 10]), (156, [1, 3, 9, 9]), (36, [1, 4, 4, 13]), (936, [1, 21]), (156, [2, 2, 3, 15]), (36, [2, 2, 5, 13]), (312, [2, 3, 3, 14]), (387, [2, 3, 4, 13]), (312, [2, 3, 5, 12]), (312, [2, 3, 6, 11]), (312, [2, 3, 7, 10]), (312, [2, 3, 8, 9]), (936, [2, 20])]

def node84Piece106UnitOutput_sector0_chunk1 : RawPoly ℕ := [(172, [3, 3, 3, 13]), (312, [3, 3, 4, 12]), (312, [3, 3, 5, 11]), (312, [3, 3, 6, 10]), (312, [3, 3, 7, 9]), (156, [3, 3, 8, 8]), (156, [3, 4, 4, 11]), (312, [3, 4, 5, 10]), (312, [3, 4, 6, 9]), (312, [3, 4, 7, 8]), (156, [3, 5, 5, 9]), (312, [3, 5, 6, 8]), (156, [3, 5, 7, 7]), (156, [3, 6, 6, 7]), (-15600, [3, 19]), (936, [4, 18]), (936, [5, 17]), (936, [6, 16]), (936, [7, 15]), (936, [8, 14]), (420, [9, 13]), (936, [10, 12]), (468, [11, 11])]

def node84Piece106UnitOutput_sector0 : RawPoly ℕ := [node84Piece106UnitOutput_sector0_chunk0, node84Piece106UnitOutput_sector0_chunk1].flatten

def node84Piece106UnitOutput : SectorVector := [(0, node84Piece106UnitOutput_sector0)]

theorem node84Piece106_check : neutralDirectS JR (-3) node84Piece106UnitInput = node84Piece106UnitOutput := by decide +kernel

theorem node84Piece106_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece106Input) = evaluate node84Piece106Output :=
  mode_of_scaled _ _ (960/13) node84Piece106UnitInput node84Piece106UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece106_check)

def node84Piece107Input_sector0 : RawPoly ℕ := [(-10, [4, 4, 4, 4])]

def node84Piece107Input : SectorVector := [(0, node84Piece107Input_sector0)]
def node84Piece107Output_sector0 : RawPoly ℕ := [(-40, [1, 1, 1, 3, 4, 4, 4, 4]), (-60, [1, 1, 2, 2, 4, 4, 4, 4]), (-1920, [1, 1, 4, 4, 4, 8]), (-3840, [1, 2, 4, 4, 4, 7]), (-3840, [1, 3, 4, 4, 4, 6]), (-3720, [1, 4, 4, 4, 4, 5]), (-23040, [1, 4, 4, 13]), (-1920, [2, 2, 4, 4, 4, 6]), (-3840, [2, 3, 4, 4, 4, 5]), (-1950, [2, 4, 4, 4, 4, 4]), (-23040, [2, 4, 4, 12]), (-1960, [3, 3, 4, 4, 4, 4]), (-23040, [3, 4, 4, 11]), (14880, [4, 4, 4, 10]), (-23040, [4, 4, 5, 9]), (-23040, [4, 4, 6, 8]), (-11520, [4, 4, 7, 7]), (-61440, [4, 18])]

def node84Piece107Output : SectorVector := [(0, node84Piece107Output_sector0)]

def node84Piece107UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 4, 4, 4])]

def node84Piece107UnitInput_sector0 : RawPoly ℕ := [node84Piece107UnitInput_sector0_chunk0].flatten

def node84Piece107UnitInput : SectorVector := [(0, node84Piece107UnitInput_sector0)]

def node84Piece107UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 4, 4, 4]), (6, [1, 1, 2, 2, 4, 4, 4, 4]), (192, [1, 1, 4, 4, 4, 8]), (384, [1, 2, 4, 4, 4, 7]), (384, [1, 3, 4, 4, 4, 6]), (372, [1, 4, 4, 4, 4, 5]), (2304, [1, 4, 4, 13]), (192, [2, 2, 4, 4, 4, 6]), (384, [2, 3, 4, 4, 4, 5]), (195, [2, 4, 4, 4, 4, 4]), (2304, [2, 4, 4, 12]), (196, [3, 3, 4, 4, 4, 4]), (2304, [3, 4, 4, 11]), (-1488, [4, 4, 4, 10]), (2304, [4, 4, 5, 9]), (2304, [4, 4, 6, 8]), (1152, [4, 4, 7, 7]), (6144, [4, 18])]

def node84Piece107UnitOutput_sector0 : RawPoly ℕ := [node84Piece107UnitOutput_sector0_chunk0].flatten

def node84Piece107UnitOutput : SectorVector := [(0, node84Piece107UnitOutput_sector0)]

theorem node84Piece107_check : neutralDirectS JR (-3) node84Piece107UnitInput = node84Piece107UnitOutput := by decide +kernel

theorem node84Piece107_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece107Input) = evaluate node84Piece107Output :=
  mode_of_scaled _ _ (-10) node84Piece107UnitInput node84Piece107UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece107_check)

def node84Piece108Input_sector0 : RawPoly ℕ := [(-40, [4, 12])]

def node84Piece108Input : SectorVector := [(0, node84Piece108Input_sector0)]
def node84Piece108Output_sector0_chunk0 : RawPoly ℕ := [(-160, [1, 1, 1, 3, 4, 12]), (-240, [1, 1, 2, 2, 4, 12]), (-5760, [1, 1, 4, 16]), (-1920, [1, 1, 8, 12]), (-11520, [1, 2, 4, 15]), (-3840, [1, 2, 7, 12]), (-11520, [1, 3, 4, 14]), (-3840, [1, 3, 6, 12]), (-11520, [1, 4, 4, 13]), (-14880, [1, 4, 5, 12]), (-11520, [1, 4, 6, 11]), (-11520, [1, 4, 7, 10]), (-11520, [1, 4, 8, 9]), (-46080, [1, 21]), (-5760, [2, 2, 4, 14]), (-1920, [2, 2, 6, 12]), (-11520, [2, 3, 4, 13]), (-3840, [2, 3, 5, 12]), (-13560, [2, 4, 4, 12]), (-11520, [2, 4, 5, 11]), (-11520, [2, 4, 6, 10]), (-11520, [2, 4, 7, 9]), (-5760, [2, 4, 8, 8]), (-46080, [2, 20])]

def node84Piece108Output_sector0_chunk1 : RawPoly ℕ := [(-7840, [3, 3, 4, 12]), (-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-11520, [3, 4, 7, 8]), (-46080, [3, 19]), (-5760, [4, 4, 4, 10]), (-11520, [4, 4, 5, 9]), (-11520, [4, 4, 6, 8]), (-5760, [4, 4, 7, 7]), (-5760, [4, 5, 5, 8]), (-11520, [4, 5, 6, 7]), (-1920, [4, 6, 6, 6]), (490080, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-46080, [8, 14]), (-46080, [9, 13]), (-8160, [10, 12]), (-23040, [11, 11])]

def node84Piece108Output_sector0 : RawPoly ℕ := [node84Piece108Output_sector0_chunk0, node84Piece108Output_sector0_chunk1].flatten

def node84Piece108Output : SectorVector := [(0, node84Piece108Output_sector0)]

def node84Piece108UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 12])]

def node84Piece108UnitInput_sector0 : RawPoly ℕ := [node84Piece108UnitInput_sector0_chunk0].flatten

def node84Piece108UnitInput : SectorVector := [(0, node84Piece108UnitInput_sector0)]

def node84Piece108UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 12]), (6, [1, 1, 2, 2, 4, 12]), (144, [1, 1, 4, 16]), (48, [1, 1, 8, 12]), (288, [1, 2, 4, 15]), (96, [1, 2, 7, 12]), (288, [1, 3, 4, 14]), (96, [1, 3, 6, 12]), (288, [1, 4, 4, 13]), (372, [1, 4, 5, 12]), (288, [1, 4, 6, 11]), (288, [1, 4, 7, 10]), (288, [1, 4, 8, 9]), (1152, [1, 21]), (144, [2, 2, 4, 14]), (48, [2, 2, 6, 12]), (288, [2, 3, 4, 13]), (96, [2, 3, 5, 12]), (339, [2, 4, 4, 12]), (288, [2, 4, 5, 11]), (288, [2, 4, 6, 10]), (288, [2, 4, 7, 9]), (144, [2, 4, 8, 8]), (1152, [2, 20])]

def node84Piece108UnitOutput_sector0_chunk1 : RawPoly ℕ := [(196, [3, 3, 4, 12]), (288, [3, 4, 4, 11]), (288, [3, 4, 5, 10]), (288, [3, 4, 6, 9]), (288, [3, 4, 7, 8]), (1152, [3, 19]), (144, [4, 4, 4, 10]), (288, [4, 4, 5, 9]), (288, [4, 4, 6, 8]), (144, [4, 4, 7, 7]), (144, [4, 5, 5, 8]), (288, [4, 5, 6, 7]), (48, [4, 6, 6, 6]), (-12252, [4, 18]), (1152, [5, 17]), (1152, [6, 16]), (1152, [7, 15]), (1152, [8, 14]), (1152, [9, 13]), (204, [10, 12]), (576, [11, 11])]

def node84Piece108UnitOutput_sector0 : RawPoly ℕ := [node84Piece108UnitOutput_sector0_chunk0, node84Piece108UnitOutput_sector0_chunk1].flatten

def node84Piece108UnitOutput : SectorVector := [(0, node84Piece108UnitOutput_sector0)]

theorem node84Piece108_check : neutralDirectS JR (-3) node84Piece108UnitInput = node84Piece108UnitOutput := by decide +kernel

theorem node84Piece108_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece108Input) = evaluate node84Piece108Output :=
  mode_of_scaled _ _ (-40) node84Piece108UnitInput node84Piece108UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece108_check)

def node84Piece109Input_sector0 : RawPoly ℕ := [(96/11, [5, 11])]

def node84Piece109Input : SectorVector := [(0, node84Piece109Input_sector0)]
def node84Piece109Output_sector0_chunk0 : RawPoly ℕ := [(384/11, [1, 1, 1, 3, 5, 11]), (576/11, [1, 1, 2, 2, 5, 11]), (1152, [1, 1, 5, 15]), (5760/11, [1, 1, 9, 11]), (2304, [1, 2, 5, 14]), (11520/11, [1, 2, 8, 11]), (2304, [1, 3, 5, 13]), (11520/11, [1, 3, 7, 11]), (2304, [1, 4, 5, 12]), (11520/11, [1, 4, 6, 11]), (29952/11, [1, 5, 5, 11]), (2304, [1, 5, 6, 10]), (2304, [1, 5, 7, 9]), (1152, [1, 5, 8, 8]), (11520, [1, 21]), (1152, [2, 2, 5, 13]), (5760/11, [2, 2, 7, 11]), (2304, [2, 3, 5, 12]), (11520/11, [2, 3, 6, 11]), (37152/11, [2, 4, 5, 11]), (2304, [2, 5, 5, 10]), (2304, [2, 5, 6, 9]), (2304, [2, 5, 7, 8]), (11520, [2, 20])]

def node84Piece109Output_sector0_chunk1 : RawPoly ℕ := [(18816/11, [3, 3, 5, 11]), (5760/11, [3, 4, 4, 11]), (2304, [3, 4, 5, 10]), (2304, [3, 5, 5, 9]), (2304, [3, 5, 6, 8]), (1152, [3, 5, 7, 7]), (11520, [3, 19]), (1152, [4, 4, 5, 9]), (2304, [4, 5, 5, 8]), (2304, [4, 5, 6, 7]), (11520, [4, 18]), (1152, [5, 5, 5, 7]), (1152, [5, 5, 6, 6]), (-81792, [5, 17]), (11520, [6, 16]), (11520, [7, 15]), (11520, [8, 14]), (11520, [9, 13]), (11520, [10, 12]), (-86400/11, [11, 11])]

def node84Piece109Output_sector0 : RawPoly ℕ := [node84Piece109Output_sector0_chunk0, node84Piece109Output_sector0_chunk1].flatten

def node84Piece109Output : SectorVector := [(0, node84Piece109Output_sector0)]

def node84Piece109UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 11])]

def node84Piece109UnitInput_sector0 : RawPoly ℕ := [node84Piece109UnitInput_sector0_chunk0].flatten

def node84Piece109UnitInput : SectorVector := [(0, node84Piece109UnitInput_sector0)]

def node84Piece109UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 5, 11]), (6, [1, 1, 2, 2, 5, 11]), (132, [1, 1, 5, 15]), (60, [1, 1, 9, 11]), (264, [1, 2, 5, 14]), (120, [1, 2, 8, 11]), (264, [1, 3, 5, 13]), (120, [1, 3, 7, 11]), (264, [1, 4, 5, 12]), (120, [1, 4, 6, 11]), (312, [1, 5, 5, 11]), (264, [1, 5, 6, 10]), (264, [1, 5, 7, 9]), (132, [1, 5, 8, 8]), (1320, [1, 21]), (132, [2, 2, 5, 13]), (60, [2, 2, 7, 11]), (264, [2, 3, 5, 12]), (120, [2, 3, 6, 11]), (387, [2, 4, 5, 11]), (264, [2, 5, 5, 10]), (264, [2, 5, 6, 9]), (264, [2, 5, 7, 8]), (1320, [2, 20])]

def node84Piece109UnitOutput_sector0_chunk1 : RawPoly ℕ := [(196, [3, 3, 5, 11]), (60, [3, 4, 4, 11]), (264, [3, 4, 5, 10]), (264, [3, 5, 5, 9]), (264, [3, 5, 6, 8]), (132, [3, 5, 7, 7]), (1320, [3, 19]), (132, [4, 4, 5, 9]), (264, [4, 5, 5, 8]), (264, [4, 5, 6, 7]), (1320, [4, 18]), (132, [5, 5, 5, 7]), (132, [5, 5, 6, 6]), (-9372, [5, 17]), (1320, [6, 16]), (1320, [7, 15]), (1320, [8, 14]), (1320, [9, 13]), (1320, [10, 12]), (-900, [11, 11])]

def node84Piece109UnitOutput_sector0 : RawPoly ℕ := [node84Piece109UnitOutput_sector0_chunk0, node84Piece109UnitOutput_sector0_chunk1].flatten

def node84Piece109UnitOutput : SectorVector := [(0, node84Piece109UnitOutput_sector0)]

theorem node84Piece109_check : neutralDirectS JR (-3) node84Piece109UnitInput = node84Piece109UnitOutput := by decide +kernel

theorem node84Piece109_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece109Input) = evaluate node84Piece109Output :=
  mode_of_scaled _ _ (96/11) node84Piece109UnitInput node84Piece109UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece109_check)

def node84Piece110Input_sector0 : RawPoly ℕ := [(3360, [])]

def node84Piece110Input : SectorVector := [(2, node84Piece110Input_sector0)]
def node84Piece110Output_sector0 : RawPoly ℕ := [(80640, [0, 1, 1, 4]), (161280, [0, 1, 2, 3]), (26880, [0, 2, 2, 2]), (611520, [0, 6]), (13440, [1, 1, 1, 3]), (20160, [1, 1, 2, 2]), (1249920, [1, 5]), (1300320, [2, 4]), (658560, [3, 3])]

def node84Piece110Output : SectorVector := [(2, node84Piece110Output_sector0)]

def node84Piece110UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [])]

def node84Piece110UnitInput_sector0 : RawPoly ℕ := [node84Piece110UnitInput_sector0_chunk0].flatten

def node84Piece110UnitInput : SectorVector := [(2, node84Piece110UnitInput_sector0)]

def node84Piece110UnitOutput_sector0_chunk0 : RawPoly ℕ := [(24, [0, 1, 1, 4]), (48, [0, 1, 2, 3]), (8, [0, 2, 2, 2]), (182, [0, 6]), (4, [1, 1, 1, 3]), (6, [1, 1, 2, 2]), (372, [1, 5]), (387, [2, 4]), (196, [3, 3])]

def node84Piece110UnitOutput_sector0 : RawPoly ℕ := [node84Piece110UnitOutput_sector0_chunk0].flatten

def node84Piece110UnitOutput : SectorVector := [(2, node84Piece110UnitOutput_sector0)]

theorem node84Piece110_check : neutralDirectS JR (-3) node84Piece110UnitInput = node84Piece110UnitOutput := by decide +kernel

theorem node84Piece110_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece110Input) = evaluate node84Piece110Output :=
  mode_of_scaled _ _ (3360) node84Piece110UnitInput node84Piece110UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece110_check)

end VOA.Classification.COne.OrbC2h
