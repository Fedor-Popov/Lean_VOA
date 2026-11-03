import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch84_3
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

def node84Piece80Input_sector0 : RawPoly ℕ := [(800/9, [1, 3, 6, 6])]

def node84Piece80Input : SectorVector := [(0, node84Piece80Input_sector0)]
def node84Piece80Output_sector0_chunk0 : RawPoly ℕ := [(3200/9, [1, 1, 1, 1, 3, 3, 6, 6]), (1600/3, [1, 1, 1, 2, 2, 3, 6, 6]), (12800, [1, 1, 1, 3, 6, 10]), (3200, [1, 1, 1, 6, 6, 7]), (25600, [1, 1, 2, 3, 6, 9]), (6400, [1, 1, 2, 6, 6, 6]), (25600, [1, 1, 3, 3, 6, 8]), (25600, [1, 1, 3, 4, 6, 7]), (32000, [1, 1, 3, 5, 6, 6]), (76800, [1, 1, 3, 17]), (3200, [1, 1, 4, 4, 6, 6]), (76800, [1, 1, 6, 14]), (12800, [1, 2, 2, 3, 6, 8]), (3200, [1, 2, 2, 5, 6, 6]), (25600, [1, 2, 3, 3, 6, 7]), (34400, [1, 2, 3, 4, 6, 6]), (12800, [1, 2, 3, 5, 5, 6]), (76800, [1, 2, 3, 16]), (76800, [1, 2, 6, 13]), (137600/9, [1, 3, 3, 3, 6, 6]), (25600, [1, 3, 3, 4, 5, 6]), (76800, [1, 3, 3, 15]), (12800/3, [1, 3, 4, 4, 4, 6]), (76800, [1, 3, 4, 14])]

def node84Piece80Output_sector0_chunk1 : RawPoly ℕ := [(76800, [1, 3, 5, 13]), (-732800/3, [1, 3, 6, 12]), (76800, [1, 3, 7, 11]), (76800, [1, 3, 8, 10]), (38400, [1, 3, 9, 9]), (76800, [1, 4, 6, 11]), (76800, [1, 5, 6, 10]), (112000/3, [1, 6, 6, 9]), (76800, [1, 6, 7, 8]), (230400, [1, 21]), (3200/3, [2, 2, 3, 3, 6, 6]), (25600, [2, 3, 6, 11]), (6400, [2, 6, 6, 8]), (25600, [3, 3, 6, 10]), (25600, [3, 4, 6, 9]), (25600, [3, 5, 6, 8]), (25600, [3, 6, 6, 7]), (76800, [3, 19]), (6400, [4, 6, 6, 6]), (3200, [5, 5, 6, 6]), (76800, [6, 16])]

def node84Piece80Output_sector0 : RawPoly ℕ := [node84Piece80Output_sector0_chunk0, node84Piece80Output_sector0_chunk1].flatten

def node84Piece80Output : SectorVector := [(0, node84Piece80Output_sector0)]

def node84Piece80UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 6, 6])]

def node84Piece80UnitInput_sector0 : RawPoly ℕ := [node84Piece80UnitInput_sector0_chunk0].flatten

def node84Piece80UnitInput : SectorVector := [(0, node84Piece80UnitInput_sector0)]

def node84Piece80UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 3, 6, 6]), (6, [1, 1, 1, 2, 2, 3, 6, 6]), (144, [1, 1, 1, 3, 6, 10]), (36, [1, 1, 1, 6, 6, 7]), (288, [1, 1, 2, 3, 6, 9]), (72, [1, 1, 2, 6, 6, 6]), (288, [1, 1, 3, 3, 6, 8]), (288, [1, 1, 3, 4, 6, 7]), (360, [1, 1, 3, 5, 6, 6]), (864, [1, 1, 3, 17]), (36, [1, 1, 4, 4, 6, 6]), (864, [1, 1, 6, 14]), (144, [1, 2, 2, 3, 6, 8]), (36, [1, 2, 2, 5, 6, 6]), (288, [1, 2, 3, 3, 6, 7]), (387, [1, 2, 3, 4, 6, 6]), (144, [1, 2, 3, 5, 5, 6]), (864, [1, 2, 3, 16]), (864, [1, 2, 6, 13]), (172, [1, 3, 3, 3, 6, 6]), (288, [1, 3, 3, 4, 5, 6]), (864, [1, 3, 3, 15]), (48, [1, 3, 4, 4, 4, 6]), (864, [1, 3, 4, 14])]

def node84Piece80UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 3, 5, 13]), (-2748, [1, 3, 6, 12]), (864, [1, 3, 7, 11]), (864, [1, 3, 8, 10]), (432, [1, 3, 9, 9]), (864, [1, 4, 6, 11]), (864, [1, 5, 6, 10]), (420, [1, 6, 6, 9]), (864, [1, 6, 7, 8]), (2592, [1, 21]), (12, [2, 2, 3, 3, 6, 6]), (288, [2, 3, 6, 11]), (72, [2, 6, 6, 8]), (288, [3, 3, 6, 10]), (288, [3, 4, 6, 9]), (288, [3, 5, 6, 8]), (288, [3, 6, 6, 7]), (864, [3, 19]), (72, [4, 6, 6, 6]), (36, [5, 5, 6, 6]), (864, [6, 16])]

def node84Piece80UnitOutput_sector0 : RawPoly ℕ := [node84Piece80UnitOutput_sector0_chunk0, node84Piece80UnitOutput_sector0_chunk1].flatten

def node84Piece80UnitOutput : SectorVector := [(0, node84Piece80UnitOutput_sector0)]

theorem node84Piece80_check : neutralDirectS JR (-3) node84Piece80UnitInput = node84Piece80UnitOutput := by decide +kernel

theorem node84Piece80_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece80Input) = evaluate node84Piece80Output :=
  mode_of_scaled _ _ (800/9) node84Piece80UnitInput node84Piece80UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece80_check)

def node84Piece81Input_sector0 : RawPoly ℕ := [(-720/7, [1, 4, 4, 7])]

def node84Piece81Input : SectorVector := [(0, node84Piece81Input_sector0)]
def node84Piece81Output_sector0_chunk0 : RawPoly ℕ := [(-2880/7, [1, 1, 1, 1, 3, 4, 4, 7]), (-4320/7, [1, 1, 1, 2, 2, 4, 4, 7]), (-8640, [1, 1, 1, 4, 4, 11]), (-69120/7, [1, 1, 1, 4, 7, 8]), (-17280, [1, 1, 2, 4, 4, 10]), (-138240/7, [1, 1, 2, 4, 7, 7]), (-17280, [1, 1, 3, 4, 4, 9]), (-138240/7, [1, 1, 3, 4, 6, 7]), (-17280, [1, 1, 4, 4, 4, 8]), (-259200/7, [1, 1, 4, 4, 5, 7]), (-8640, [1, 1, 4, 4, 6, 6]), (-138240, [1, 1, 4, 16]), (-276480/7, [1, 1, 7, 13]), (-8640, [1, 2, 2, 4, 4, 9]), (-69120/7, [1, 2, 2, 4, 6, 7]), (-17280, [1, 2, 3, 4, 4, 8]), (-138240/7, [1, 2, 3, 4, 5, 7]), (-209520/7, [1, 2, 4, 4, 4, 7]), (-17280, [1, 2, 4, 4, 5, 6]), (-138240, [1, 2, 4, 15]), (-276480/7, [1, 2, 7, 12]), (-20160, [1, 3, 3, 4, 4, 7]), (-17280, [1, 3, 4, 4, 4, 6]), (-8640, [1, 3, 4, 4, 5, 5])]

def node84Piece81Output_sector0_chunk1 : RawPoly ℕ := [(-138240, [1, 3, 4, 14]), (-276480/7, [1, 3, 7, 11]), (-8640, [1, 4, 4, 4, 4, 5]), (198720, [1, 4, 4, 13]), (-138240, [1, 4, 5, 12]), (-138240, [1, 4, 6, 11]), (-17280/7, [1, 4, 7, 10]), (-138240, [1, 4, 8, 9]), (-276480/7, [1, 5, 7, 9]), (-276480/7, [1, 6, 7, 8]), (-138240/7, [1, 7, 7, 7]), (-276480, [1, 21]), (-8640/7, [2, 2, 3, 4, 4, 7]), (-17280, [2, 4, 4, 12]), (-138240/7, [2, 4, 7, 9]), (-17280, [3, 4, 4, 11]), (-138240/7, [3, 4, 7, 8]), (-17280, [4, 4, 4, 10]), (-17280, [4, 4, 5, 9]), (-17280, [4, 4, 6, 8]), (-146880/7, [4, 4, 7, 7]), (-138240/7, [4, 5, 6, 7]), (-138240, [4, 18]), (-276480/7, [7, 15])]

def node84Piece81Output_sector0 : RawPoly ℕ := [node84Piece81Output_sector0_chunk0, node84Piece81Output_sector0_chunk1].flatten

def node84Piece81Output : SectorVector := [(0, node84Piece81Output_sector0)]

def node84Piece81UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 4, 7])]

def node84Piece81UnitInput_sector0 : RawPoly ℕ := [node84Piece81UnitInput_sector0_chunk0].flatten

def node84Piece81UnitInput : SectorVector := [(0, node84Piece81UnitInput_sector0)]

def node84Piece81UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 4, 4, 7]), (6, [1, 1, 1, 2, 2, 4, 4, 7]), (84, [1, 1, 1, 4, 4, 11]), (96, [1, 1, 1, 4, 7, 8]), (168, [1, 1, 2, 4, 4, 10]), (192, [1, 1, 2, 4, 7, 7]), (168, [1, 1, 3, 4, 4, 9]), (192, [1, 1, 3, 4, 6, 7]), (168, [1, 1, 4, 4, 4, 8]), (360, [1, 1, 4, 4, 5, 7]), (84, [1, 1, 4, 4, 6, 6]), (1344, [1, 1, 4, 16]), (384, [1, 1, 7, 13]), (84, [1, 2, 2, 4, 4, 9]), (96, [1, 2, 2, 4, 6, 7]), (168, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (291, [1, 2, 4, 4, 4, 7]), (168, [1, 2, 4, 4, 5, 6]), (1344, [1, 2, 4, 15]), (384, [1, 2, 7, 12]), (196, [1, 3, 3, 4, 4, 7]), (168, [1, 3, 4, 4, 4, 6]), (84, [1, 3, 4, 4, 5, 5])]

def node84Piece81UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1344, [1, 3, 4, 14]), (384, [1, 3, 7, 11]), (84, [1, 4, 4, 4, 4, 5]), (-1932, [1, 4, 4, 13]), (1344, [1, 4, 5, 12]), (1344, [1, 4, 6, 11]), (24, [1, 4, 7, 10]), (1344, [1, 4, 8, 9]), (384, [1, 5, 7, 9]), (384, [1, 6, 7, 8]), (192, [1, 7, 7, 7]), (2688, [1, 21]), (12, [2, 2, 3, 4, 4, 7]), (168, [2, 4, 4, 12]), (192, [2, 4, 7, 9]), (168, [3, 4, 4, 11]), (192, [3, 4, 7, 8]), (168, [4, 4, 4, 10]), (168, [4, 4, 5, 9]), (168, [4, 4, 6, 8]), (204, [4, 4, 7, 7]), (192, [4, 5, 6, 7]), (1344, [4, 18]), (384, [7, 15])]

def node84Piece81UnitOutput_sector0 : RawPoly ℕ := [node84Piece81UnitOutput_sector0_chunk0, node84Piece81UnitOutput_sector0_chunk1].flatten

def node84Piece81UnitOutput : SectorVector := [(0, node84Piece81UnitOutput_sector0)]

theorem node84Piece81_check : neutralDirectS JR (-3) node84Piece81UnitInput = node84Piece81UnitOutput := by decide +kernel

theorem node84Piece81_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece81Input) = evaluate node84Piece81Output :=
  mode_of_scaled _ _ (-720/7) node84Piece81UnitInput node84Piece81UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece81_check)

def node84Piece82Input_sector0 : RawPoly ℕ := [(-48, [1, 4, 5, 6])]

def node84Piece82Input : SectorVector := [(0, node84Piece82Input_sector0)]
def node84Piece82Output_sector0_chunk0 : RawPoly ℕ := [(-192, [1, 1, 1, 1, 3, 4, 5, 6]), (-288, [1, 1, 1, 2, 2, 4, 5, 6]), (-3456, [1, 1, 1, 4, 5, 10]), (-2880, [1, 1, 1, 4, 6, 9]), (-2304, [1, 1, 1, 5, 6, 8]), (-6912, [1, 1, 2, 4, 5, 9]), (-5760, [1, 1, 2, 4, 6, 8]), (-4608, [1, 1, 2, 5, 6, 7]), (-6912, [1, 1, 3, 4, 5, 8]), (-5760, [1, 1, 3, 4, 6, 7]), (-4608, [1, 1, 3, 5, 6, 6]), (-6912, [1, 1, 4, 4, 5, 7]), (-5760, [1, 1, 4, 4, 6, 6]), (-14400, [1, 1, 4, 5, 5, 6]), (-34560, [1, 1, 4, 16]), (-27648, [1, 1, 5, 15]), (-23040, [1, 1, 6, 14]), (-3456, [1, 2, 2, 4, 5, 8]), (-2880, [1, 2, 2, 4, 6, 7]), (-2304, [1, 2, 2, 5, 6, 6]), (-6912, [1, 2, 3, 4, 5, 7]), (-5760, [1, 2, 3, 4, 6, 6]), (-4608, [1, 2, 3, 5, 5, 6]), (-16272, [1, 2, 4, 4, 5, 6])]

def node84Piece82Output_sector0_chunk1 : RawPoly ℕ := [(-3456, [1, 2, 4, 5, 5, 5]), (-34560, [1, 2, 4, 15]), (-27648, [1, 2, 5, 14]), (-23040, [1, 2, 6, 13]), (-9408, [1, 3, 3, 4, 5, 6]), (-2880, [1, 3, 4, 4, 4, 6]), (-6912, [1, 3, 4, 4, 5, 5]), (-34560, [1, 3, 4, 14]), (-27648, [1, 3, 5, 13]), (-23040, [1, 3, 6, 12]), (-1152, [1, 4, 4, 4, 4, 5]), (-34560, [1, 4, 4, 13]), (45216, [1, 4, 5, 12]), (11520, [1, 4, 6, 11]), (-34560, [1, 4, 7, 10]), (-34560, [1, 4, 8, 9]), (-27648, [1, 5, 5, 11]), (-9792, [1, 5, 6, 10]), (-27648, [1, 5, 7, 9]), (-13824, [1, 5, 8, 8]), (-23040, [1, 6, 6, 9]), (-23040, [1, 6, 7, 8]), (-138240, [1, 21]), (-576, [2, 2, 3, 4, 5, 6])]

def node84Piece82Output_sector0_chunk2 : RawPoly ℕ := [(-6912, [2, 4, 5, 11]), (-5760, [2, 4, 6, 10]), (-4608, [2, 5, 6, 9]), (-6912, [3, 4, 5, 10]), (-5760, [3, 4, 6, 9]), (-4608, [3, 5, 6, 8]), (-6912, [4, 4, 5, 9]), (-5760, [4, 4, 6, 8]), (-6912, [4, 5, 5, 8]), (-13824, [4, 5, 6, 7]), (-2880, [4, 6, 6, 6]), (-34560, [4, 18]), (-4608, [5, 5, 6, 6]), (-27648, [5, 17]), (-23040, [6, 16])]

def node84Piece82Output_sector0 : RawPoly ℕ := [node84Piece82Output_sector0_chunk0, node84Piece82Output_sector0_chunk1, node84Piece82Output_sector0_chunk2].flatten

def node84Piece82Output : SectorVector := [(0, node84Piece82Output_sector0)]

def node84Piece82UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 5, 6])]

def node84Piece82UnitInput_sector0 : RawPoly ℕ := [node84Piece82UnitInput_sector0_chunk0].flatten

def node84Piece82UnitInput : SectorVector := [(0, node84Piece82UnitInput_sector0)]

def node84Piece82UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 4, 5, 6]), (6, [1, 1, 1, 2, 2, 4, 5, 6]), (72, [1, 1, 1, 4, 5, 10]), (60, [1, 1, 1, 4, 6, 9]), (48, [1, 1, 1, 5, 6, 8]), (144, [1, 1, 2, 4, 5, 9]), (120, [1, 1, 2, 4, 6, 8]), (96, [1, 1, 2, 5, 6, 7]), (144, [1, 1, 3, 4, 5, 8]), (120, [1, 1, 3, 4, 6, 7]), (96, [1, 1, 3, 5, 6, 6]), (144, [1, 1, 4, 4, 5, 7]), (120, [1, 1, 4, 4, 6, 6]), (300, [1, 1, 4, 5, 5, 6]), (720, [1, 1, 4, 16]), (576, [1, 1, 5, 15]), (480, [1, 1, 6, 14]), (72, [1, 2, 2, 4, 5, 8]), (60, [1, 2, 2, 4, 6, 7]), (48, [1, 2, 2, 5, 6, 6]), (144, [1, 2, 3, 4, 5, 7]), (120, [1, 2, 3, 4, 6, 6]), (96, [1, 2, 3, 5, 5, 6]), (339, [1, 2, 4, 4, 5, 6])]

def node84Piece82UnitOutput_sector0_chunk1 : RawPoly ℕ := [(72, [1, 2, 4, 5, 5, 5]), (720, [1, 2, 4, 15]), (576, [1, 2, 5, 14]), (480, [1, 2, 6, 13]), (196, [1, 3, 3, 4, 5, 6]), (60, [1, 3, 4, 4, 4, 6]), (144, [1, 3, 4, 4, 5, 5]), (720, [1, 3, 4, 14]), (576, [1, 3, 5, 13]), (480, [1, 3, 6, 12]), (24, [1, 4, 4, 4, 4, 5]), (720, [1, 4, 4, 13]), (-942, [1, 4, 5, 12]), (-240, [1, 4, 6, 11]), (720, [1, 4, 7, 10]), (720, [1, 4, 8, 9]), (576, [1, 5, 5, 11]), (204, [1, 5, 6, 10]), (576, [1, 5, 7, 9]), (288, [1, 5, 8, 8]), (480, [1, 6, 6, 9]), (480, [1, 6, 7, 8]), (2880, [1, 21]), (12, [2, 2, 3, 4, 5, 6])]

def node84Piece82UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [2, 4, 5, 11]), (120, [2, 4, 6, 10]), (96, [2, 5, 6, 9]), (144, [3, 4, 5, 10]), (120, [3, 4, 6, 9]), (96, [3, 5, 6, 8]), (144, [4, 4, 5, 9]), (120, [4, 4, 6, 8]), (144, [4, 5, 5, 8]), (288, [4, 5, 6, 7]), (60, [4, 6, 6, 6]), (720, [4, 18]), (96, [5, 5, 6, 6]), (576, [5, 17]), (480, [6, 16])]

def node84Piece82UnitOutput_sector0 : RawPoly ℕ := [node84Piece82UnitOutput_sector0_chunk0, node84Piece82UnitOutput_sector0_chunk1, node84Piece82UnitOutput_sector0_chunk2].flatten

def node84Piece82UnitOutput : SectorVector := [(0, node84Piece82UnitOutput_sector0)]

theorem node84Piece82_check : neutralDirectS JR (-3) node84Piece82UnitInput = node84Piece82UnitOutput := by decide +kernel

theorem node84Piece82_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece82Input) = evaluate node84Piece82Output :=
  mode_of_scaled _ _ (-48) node84Piece82UnitInput node84Piece82UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece82_check)

def node84Piece83Input_sector0 : RawPoly ℕ := [(512/25, [1, 5, 5, 5])]

def node84Piece83Input : SectorVector := [(0, node84Piece83Input_sector0)]
def node84Piece83Output_sector0_chunk0 : RawPoly ℕ := [(2048/25, [1, 1, 1, 1, 3, 5, 5, 5]), (3072/25, [1, 1, 1, 2, 2, 5, 5, 5]), (18432/5, [1, 1, 1, 5, 5, 9]), (36864/5, [1, 1, 2, 5, 5, 8]), (36864/5, [1, 1, 3, 5, 5, 7]), (36864/5, [1, 1, 4, 5, 5, 6]), (18432/5, [1, 1, 5, 5, 5, 5]), (36864, [1, 1, 5, 15]), (18432/5, [1, 2, 2, 5, 5, 7]), (36864/5, [1, 2, 3, 5, 5, 6]), (198144/25, [1, 2, 4, 5, 5, 5]), (36864, [1, 2, 5, 14]), (100352/25, [1, 3, 3, 5, 5, 5]), (18432/5, [1, 3, 4, 4, 5, 5]), (36864, [1, 3, 5, 13]), (36864, [1, 4, 5, 12]), (-258048/5, [1, 5, 5, 11]), (36864, [1, 5, 6, 10]), (36864, [1, 5, 7, 9]), (18432, [1, 5, 8, 8]), (61440, [1, 21]), (6144/25, [2, 2, 3, 5, 5, 5]), (36864/5, [2, 5, 5, 10]), (36864/5, [3, 5, 5, 9])]

def node84Piece83Output_sector0_chunk1 : RawPoly ℕ := [(36864/5, [4, 5, 5, 8]), (147456/25, [5, 5, 5, 7]), (18432/5, [5, 5, 6, 6]), (36864, [5, 17])]

def node84Piece83Output_sector0 : RawPoly ℕ := [node84Piece83Output_sector0_chunk0, node84Piece83Output_sector0_chunk1].flatten

def node84Piece83Output : SectorVector := [(0, node84Piece83Output_sector0)]

def node84Piece83UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 5, 5, 5])]

def node84Piece83UnitInput_sector0 : RawPoly ℕ := [node84Piece83UnitInput_sector0_chunk0].flatten

def node84Piece83UnitInput : SectorVector := [(0, node84Piece83UnitInput_sector0)]

def node84Piece83UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 5, 5, 5]), (6, [1, 1, 1, 2, 2, 5, 5, 5]), (180, [1, 1, 1, 5, 5, 9]), (360, [1, 1, 2, 5, 5, 8]), (360, [1, 1, 3, 5, 5, 7]), (360, [1, 1, 4, 5, 5, 6]), (180, [1, 1, 5, 5, 5, 5]), (1800, [1, 1, 5, 15]), (180, [1, 2, 2, 5, 5, 7]), (360, [1, 2, 3, 5, 5, 6]), (387, [1, 2, 4, 5, 5, 5]), (1800, [1, 2, 5, 14]), (196, [1, 3, 3, 5, 5, 5]), (180, [1, 3, 4, 4, 5, 5]), (1800, [1, 3, 5, 13]), (1800, [1, 4, 5, 12]), (-2520, [1, 5, 5, 11]), (1800, [1, 5, 6, 10]), (1800, [1, 5, 7, 9]), (900, [1, 5, 8, 8]), (3000, [1, 21]), (12, [2, 2, 3, 5, 5, 5]), (360, [2, 5, 5, 10]), (360, [3, 5, 5, 9])]

def node84Piece83UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [4, 5, 5, 8]), (288, [5, 5, 5, 7]), (180, [5, 5, 6, 6]), (1800, [5, 17])]

def node84Piece83UnitOutput_sector0 : RawPoly ℕ := [node84Piece83UnitOutput_sector0_chunk0, node84Piece83UnitOutput_sector0_chunk1].flatten

def node84Piece83UnitOutput : SectorVector := [(0, node84Piece83UnitOutput_sector0)]

theorem node84Piece83_check : neutralDirectS JR (-3) node84Piece83UnitInput = node84Piece83UnitOutput := by decide +kernel

theorem node84Piece83_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece83Input) = evaluate node84Piece83Output :=
  mode_of_scaled _ _ (512/25) node84Piece83UnitInput node84Piece83UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece83_check)

def node84Piece84Input_sector0 : RawPoly ℕ := [(32, [1, 15])]

def node84Piece84Input : SectorVector := [(0, node84Piece84Input_sector0)]
def node84Piece84Output_sector0_chunk0 : RawPoly ℕ := [(128, [1, 1, 1, 1, 3, 15]), (192, [1, 1, 1, 2, 2, 15]), (5760, [1, 1, 1, 19]), (11520, [1, 1, 2, 18]), (11520, [1, 1, 3, 17]), (11520, [1, 1, 4, 16]), (11520, [1, 1, 5, 15]), (11520, [1, 1, 6, 14]), (11520, [1, 1, 7, 13]), (11520, [1, 1, 8, 12]), (11520, [1, 1, 9, 11]), (5760, [1, 1, 10, 10]), (5760, [1, 2, 2, 17]), (11520, [1, 2, 3, 16]), (12384, [1, 2, 4, 15]), (11520, [1, 2, 5, 14]), (11520, [1, 2, 6, 13]), (11520, [1, 2, 7, 12]), (11520, [1, 2, 8, 11]), (11520, [1, 2, 9, 10]), (6272, [1, 3, 3, 15]), (11520, [1, 3, 4, 14]), (11520, [1, 3, 5, 13]), (11520, [1, 3, 6, 12])]

def node84Piece84Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 3, 7, 11]), (11520, [1, 3, 8, 10]), (5760, [1, 3, 9, 9]), (5760, [1, 4, 4, 13]), (11520, [1, 4, 5, 12]), (11520, [1, 4, 6, 11]), (11520, [1, 4, 7, 10]), (11520, [1, 4, 8, 9]), (5760, [1, 5, 5, 11]), (11520, [1, 5, 6, 10]), (11520, [1, 5, 7, 9]), (5760, [1, 5, 8, 8]), (5760, [1, 6, 6, 9]), (11520, [1, 6, 7, 8]), (1920, [1, 7, 7, 7]), (-762240, [1, 21]), (384, [2, 2, 3, 15]), (11520, [2, 20]), (11520, [3, 19]), (11520, [4, 18]), (11520, [5, 17]), (11520, [6, 16]), (9216, [7, 15]), (11520, [8, 14])]

def node84Piece84Output_sector0_chunk2 : RawPoly ℕ := [(11520, [9, 13]), (11520, [10, 12]), (5760, [11, 11])]

def node84Piece84Output_sector0 : RawPoly ℕ := [node84Piece84Output_sector0_chunk0, node84Piece84Output_sector0_chunk1, node84Piece84Output_sector0_chunk2].flatten

def node84Piece84Output : SectorVector := [(0, node84Piece84Output_sector0)]

def node84Piece84UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 15])]

def node84Piece84UnitInput_sector0 : RawPoly ℕ := [node84Piece84UnitInput_sector0_chunk0].flatten

def node84Piece84UnitInput : SectorVector := [(0, node84Piece84UnitInput_sector0)]

def node84Piece84UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 15]), (6, [1, 1, 1, 2, 2, 15]), (180, [1, 1, 1, 19]), (360, [1, 1, 2, 18]), (360, [1, 1, 3, 17]), (360, [1, 1, 4, 16]), (360, [1, 1, 5, 15]), (360, [1, 1, 6, 14]), (360, [1, 1, 7, 13]), (360, [1, 1, 8, 12]), (360, [1, 1, 9, 11]), (180, [1, 1, 10, 10]), (180, [1, 2, 2, 17]), (360, [1, 2, 3, 16]), (387, [1, 2, 4, 15]), (360, [1, 2, 5, 14]), (360, [1, 2, 6, 13]), (360, [1, 2, 7, 12]), (360, [1, 2, 8, 11]), (360, [1, 2, 9, 10]), (196, [1, 3, 3, 15]), (360, [1, 3, 4, 14]), (360, [1, 3, 5, 13]), (360, [1, 3, 6, 12])]

def node84Piece84UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [1, 3, 7, 11]), (360, [1, 3, 8, 10]), (180, [1, 3, 9, 9]), (180, [1, 4, 4, 13]), (360, [1, 4, 5, 12]), (360, [1, 4, 6, 11]), (360, [1, 4, 7, 10]), (360, [1, 4, 8, 9]), (180, [1, 5, 5, 11]), (360, [1, 5, 6, 10]), (360, [1, 5, 7, 9]), (180, [1, 5, 8, 8]), (180, [1, 6, 6, 9]), (360, [1, 6, 7, 8]), (60, [1, 7, 7, 7]), (-23820, [1, 21]), (12, [2, 2, 3, 15]), (360, [2, 20]), (360, [3, 19]), (360, [4, 18]), (360, [5, 17]), (360, [6, 16]), (288, [7, 15]), (360, [8, 14])]

def node84Piece84UnitOutput_sector0_chunk2 : RawPoly ℕ := [(360, [9, 13]), (360, [10, 12]), (180, [11, 11])]

def node84Piece84UnitOutput_sector0 : RawPoly ℕ := [node84Piece84UnitOutput_sector0_chunk0, node84Piece84UnitOutput_sector0_chunk1, node84Piece84UnitOutput_sector0_chunk2].flatten

def node84Piece84UnitOutput : SectorVector := [(0, node84Piece84UnitOutput_sector0)]

theorem node84Piece84_check : neutralDirectS JR (-3) node84Piece84UnitInput = node84Piece84UnitOutput := by decide +kernel

theorem node84Piece84_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece84Input) = evaluate node84Piece84Output :=
  mode_of_scaled _ _ (32) node84Piece84UnitInput node84Piece84UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece84_check)

def node84Piece85Input_sector0 : RawPoly ℕ := [(-44/21, [2, 2, 2, 2, 2, 2, 2, 2])]

def node84Piece85Input : SectorVector := [(0, node84Piece85Input_sector0)]
def node84Piece85Output_sector0 : RawPoly ℕ := [(-176/21, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-88/7, [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]), (-2816/7, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-5456/7, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (-5632/7, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-5632, [1, 2, 2, 2, 2, 2, 2, 9]), (-2860/7, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (-1232/3, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (-11968/7, [2, 2, 2, 2, 2, 2, 2, 8]), (-5632, [2, 2, 2, 2, 2, 2, 3, 7]), (-5632, [2, 2, 2, 2, 2, 2, 4, 6]), (-2816, [2, 2, 2, 2, 2, 2, 5, 5]), (-22528, [2, 2, 2, 2, 2, 12])]

def node84Piece85Output : SectorVector := [(0, node84Piece85Output_sector0)]

def node84Piece85UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 2, 2, 2])]

def node84Piece85UnitInput_sector0 : RawPoly ℕ := [node84Piece85UnitInput_sector0_chunk0].flatten

def node84Piece85UnitInput : SectorVector := [(0, node84Piece85UnitInput_sector0)]

def node84Piece85UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]), (192, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (372, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (384, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (2688, [1, 2, 2, 2, 2, 2, 2, 9]), (195, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (196, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (816, [2, 2, 2, 2, 2, 2, 2, 8]), (2688, [2, 2, 2, 2, 2, 2, 3, 7]), (2688, [2, 2, 2, 2, 2, 2, 4, 6]), (1344, [2, 2, 2, 2, 2, 2, 5, 5]), (10752, [2, 2, 2, 2, 2, 12])]

def node84Piece85UnitOutput_sector0 : RawPoly ℕ := [node84Piece85UnitOutput_sector0_chunk0].flatten

def node84Piece85UnitOutput : SectorVector := [(0, node84Piece85UnitOutput_sector0)]

theorem node84Piece85_check : neutralDirectS JR (-3) node84Piece85UnitInput = node84Piece85UnitOutput := by decide +kernel

theorem node84Piece85_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece85Input) = evaluate node84Piece85Output :=
  mode_of_scaled _ _ (-44/21) node84Piece85UnitInput node84Piece85UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece85_check)

def node84Piece86Input_sector0 : RawPoly ℕ := [(-160/3, [2, 2, 2, 2, 2, 6])]

def node84Piece86Input : SectorVector := [(0, node84Piece86Input_sector0)]
def node84Piece86Output_sector0_chunk0 : RawPoly ℕ := [(-640/3, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-320, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-3840, [1, 1, 2, 2, 2, 2, 2, 10]), (-6400, [1, 1, 2, 2, 2, 2, 6, 6]), (-7680, [1, 2, 2, 2, 2, 2, 2, 9]), (-7680, [1, 2, 2, 2, 2, 2, 3, 8]), (-7680, [1, 2, 2, 2, 2, 2, 4, 7]), (-19840, [1, 2, 2, 2, 2, 2, 5, 6]), (-12800, [1, 2, 2, 2, 2, 3, 4, 6]), (-76800, [1, 2, 2, 2, 2, 13]), (-51200, [1, 2, 2, 2, 6, 9]), (-3840, [2, 2, 2, 2, 2, 2, 2, 8]), (-7680, [2, 2, 2, 2, 2, 2, 3, 7]), (-14240, [2, 2, 2, 2, 2, 2, 4, 6]), (-3840, [2, 2, 2, 2, 2, 2, 5, 5]), (-31360/3, [2, 2, 2, 2, 2, 3, 3, 6]), (-7680, [2, 2, 2, 2, 2, 3, 4, 5]), (-1280, [2, 2, 2, 2, 2, 4, 4, 4]), (50240, [2, 2, 2, 2, 2, 12]), (-76800, [2, 2, 2, 2, 3, 11]), (-76800, [2, 2, 2, 2, 4, 10]), (-76800, [2, 2, 2, 2, 5, 9]), (-65600, [2, 2, 2, 2, 6, 8]), (-38400, [2, 2, 2, 2, 7, 7])]

def node84Piece86Output_sector0_chunk1 : RawPoly ℕ := [(-51200, [2, 2, 2, 3, 6, 7]), (-51200, [2, 2, 2, 4, 6, 6]), (-25600, [2, 2, 2, 5, 5, 6]), (-307200, [2, 2, 2, 16]), (-102400, [2, 2, 6, 12])]

def node84Piece86Output_sector0 : RawPoly ℕ := [node84Piece86Output_sector0_chunk0, node84Piece86Output_sector0_chunk1].flatten

def node84Piece86Output : SectorVector := [(0, node84Piece86Output_sector0)]

def node84Piece86UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 6])]

def node84Piece86UnitInput_sector0 : RawPoly ℕ := [node84Piece86UnitInput_sector0_chunk0].flatten

def node84Piece86UnitInput : SectorVector := [(0, node84Piece86UnitInput_sector0)]

def node84Piece86UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (72, [1, 1, 2, 2, 2, 2, 2, 10]), (120, [1, 1, 2, 2, 2, 2, 6, 6]), (144, [1, 2, 2, 2, 2, 2, 2, 9]), (144, [1, 2, 2, 2, 2, 2, 3, 8]), (144, [1, 2, 2, 2, 2, 2, 4, 7]), (372, [1, 2, 2, 2, 2, 2, 5, 6]), (240, [1, 2, 2, 2, 2, 3, 4, 6]), (1440, [1, 2, 2, 2, 2, 13]), (960, [1, 2, 2, 2, 6, 9]), (72, [2, 2, 2, 2, 2, 2, 2, 8]), (144, [2, 2, 2, 2, 2, 2, 3, 7]), (267, [2, 2, 2, 2, 2, 2, 4, 6]), (72, [2, 2, 2, 2, 2, 2, 5, 5]), (196, [2, 2, 2, 2, 2, 3, 3, 6]), (144, [2, 2, 2, 2, 2, 3, 4, 5]), (24, [2, 2, 2, 2, 2, 4, 4, 4]), (-942, [2, 2, 2, 2, 2, 12]), (1440, [2, 2, 2, 2, 3, 11]), (1440, [2, 2, 2, 2, 4, 10]), (1440, [2, 2, 2, 2, 5, 9]), (1230, [2, 2, 2, 2, 6, 8]), (720, [2, 2, 2, 2, 7, 7])]

def node84Piece86UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [2, 2, 2, 3, 6, 7]), (960, [2, 2, 2, 4, 6, 6]), (480, [2, 2, 2, 5, 5, 6]), (5760, [2, 2, 2, 16]), (1920, [2, 2, 6, 12])]

def node84Piece86UnitOutput_sector0 : RawPoly ℕ := [node84Piece86UnitOutput_sector0_chunk0, node84Piece86UnitOutput_sector0_chunk1].flatten

def node84Piece86UnitOutput : SectorVector := [(0, node84Piece86UnitOutput_sector0)]

theorem node84Piece86_check : neutralDirectS JR (-3) node84Piece86UnitInput = node84Piece86UnitOutput := by decide +kernel

theorem node84Piece86_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece86Input) = evaluate node84Piece86Output :=
  mode_of_scaled _ _ (-160/3) node84Piece86UnitInput node84Piece86UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece86_check)

def node84Piece87Input_sector0 : RawPoly ℕ := [(-304/3, [2, 2, 2, 2, 3, 5])]

def node84Piece87Input : SectorVector := [(0, node84Piece87Input_sector0)]
def node84Piece87Output_sector0_chunk0 : RawPoly ℕ := [(-1216/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (-608, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-6080, [1, 1, 2, 2, 2, 2, 3, 9]), (-3648, [1, 1, 2, 2, 2, 2, 5, 7]), (-9728, [1, 1, 2, 2, 2, 3, 5, 6]), (-12160, [1, 2, 2, 2, 2, 2, 3, 8]), (-7296, [1, 2, 2, 2, 2, 2, 5, 6]), (-12160, [1, 2, 2, 2, 2, 3, 3, 7]), (-12160, [1, 2, 2, 2, 2, 3, 4, 6]), (-31616, [1, 2, 2, 2, 2, 3, 5, 5]), (-3648, [1, 2, 2, 2, 2, 4, 4, 5]), (-36480, [1, 2, 2, 2, 2, 13]), (-19456, [1, 2, 2, 2, 3, 3, 4, 5]), (-97280, [1, 2, 2, 2, 3, 12]), (-58368, [1, 2, 2, 2, 5, 10]), (-58368, [1, 2, 2, 3, 5, 9]), (-6080, [2, 2, 2, 2, 2, 2, 3, 7]), (-3648, [2, 2, 2, 2, 2, 2, 5, 5]), (-12160, [2, 2, 2, 2, 2, 3, 3, 6]), (-29488, [2, 2, 2, 2, 2, 3, 4, 5]), (-36480, [2, 2, 2, 2, 2, 12]), (-52288/3, [2, 2, 2, 2, 3, 3, 3, 5]), (-6080, [2, 2, 2, 2, 3, 3, 4, 4]), (24320, [2, 2, 2, 2, 3, 11])]

def node84Piece87Output_sector0_chunk1 : RawPoly ℕ := [(-36480, [2, 2, 2, 2, 4, 10]), (-42560, [2, 2, 2, 2, 5, 9]), (-36480, [2, 2, 2, 2, 6, 8]), (-18240, [2, 2, 2, 2, 7, 7]), (-97280, [2, 2, 2, 3, 3, 10]), (-97280, [2, 2, 2, 3, 4, 9]), (-119168, [2, 2, 2, 3, 5, 8]), (-97280, [2, 2, 2, 3, 6, 7]), (-58368, [2, 2, 2, 4, 5, 7]), (-58368, [2, 2, 2, 5, 5, 6]), (-291840, [2, 2, 2, 16]), (-58368, [2, 2, 3, 3, 5, 7]), (-58368, [2, 2, 3, 4, 5, 6]), (-29184, [2, 2, 3, 5, 5, 5]), (-291840, [2, 2, 3, 15]), (-175104, [2, 2, 5, 13]), (-77824, [2, 3, 5, 12])]

def node84Piece87Output_sector0 : RawPoly ℕ := [node84Piece87Output_sector0_chunk0, node84Piece87Output_sector0_chunk1].flatten

def node84Piece87Output : SectorVector := [(0, node84Piece87Output_sector0)]

def node84Piece87UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 3, 5])]

def node84Piece87UnitInput_sector0 : RawPoly ℕ := [node84Piece87UnitInput_sector0_chunk0].flatten

def node84Piece87UnitInput : SectorVector := [(0, node84Piece87UnitInput_sector0)]

def node84Piece87UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (60, [1, 1, 2, 2, 2, 2, 3, 9]), (36, [1, 1, 2, 2, 2, 2, 5, 7]), (96, [1, 1, 2, 2, 2, 3, 5, 6]), (120, [1, 2, 2, 2, 2, 2, 3, 8]), (72, [1, 2, 2, 2, 2, 2, 5, 6]), (120, [1, 2, 2, 2, 2, 3, 3, 7]), (120, [1, 2, 2, 2, 2, 3, 4, 6]), (312, [1, 2, 2, 2, 2, 3, 5, 5]), (36, [1, 2, 2, 2, 2, 4, 4, 5]), (360, [1, 2, 2, 2, 2, 13]), (192, [1, 2, 2, 2, 3, 3, 4, 5]), (960, [1, 2, 2, 2, 3, 12]), (576, [1, 2, 2, 2, 5, 10]), (576, [1, 2, 2, 3, 5, 9]), (60, [2, 2, 2, 2, 2, 2, 3, 7]), (36, [2, 2, 2, 2, 2, 2, 5, 5]), (120, [2, 2, 2, 2, 2, 3, 3, 6]), (291, [2, 2, 2, 2, 2, 3, 4, 5]), (360, [2, 2, 2, 2, 2, 12]), (172, [2, 2, 2, 2, 3, 3, 3, 5]), (60, [2, 2, 2, 2, 3, 3, 4, 4]), (-240, [2, 2, 2, 2, 3, 11])]

def node84Piece87UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [2, 2, 2, 2, 4, 10]), (420, [2, 2, 2, 2, 5, 9]), (360, [2, 2, 2, 2, 6, 8]), (180, [2, 2, 2, 2, 7, 7]), (960, [2, 2, 2, 3, 3, 10]), (960, [2, 2, 2, 3, 4, 9]), (1176, [2, 2, 2, 3, 5, 8]), (960, [2, 2, 2, 3, 6, 7]), (576, [2, 2, 2, 4, 5, 7]), (576, [2, 2, 2, 5, 5, 6]), (2880, [2, 2, 2, 16]), (576, [2, 2, 3, 3, 5, 7]), (576, [2, 2, 3, 4, 5, 6]), (288, [2, 2, 3, 5, 5, 5]), (2880, [2, 2, 3, 15]), (1728, [2, 2, 5, 13]), (768, [2, 3, 5, 12])]

def node84Piece87UnitOutput_sector0 : RawPoly ℕ := [node84Piece87UnitOutput_sector0_chunk0, node84Piece87UnitOutput_sector0_chunk1].flatten

def node84Piece87UnitOutput : SectorVector := [(0, node84Piece87UnitOutput_sector0)]

theorem node84Piece87_check : neutralDirectS JR (-3) node84Piece87UnitInput = node84Piece87UnitOutput := by decide +kernel

theorem node84Piece87_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece87Input) = evaluate node84Piece87Output :=
  mode_of_scaled _ _ (-304/3) node84Piece87UnitInput node84Piece87UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece87_check)

def node84Piece88Input_sector0 : RawPoly ℕ := [(-90, [2, 2, 2, 2, 4, 4])]

def node84Piece88Input : SectorVector := [(0, node84Piece88Input_sector0)]
def node84Piece88Output_sector0_chunk0 : RawPoly ℕ := [(-360, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (-540, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (-8640, [1, 1, 2, 2, 2, 2, 4, 8]), (-8640, [1, 1, 2, 2, 2, 4, 4, 6]), (-17280, [1, 2, 2, 2, 2, 2, 4, 7]), (-17280, [1, 2, 2, 2, 2, 3, 4, 6]), (-33480, [1, 2, 2, 2, 2, 4, 4, 5]), (-34560, [1, 2, 2, 2, 2, 13]), (-17280, [1, 2, 2, 2, 3, 4, 4, 4]), (-138240, [1, 2, 2, 2, 4, 11]), (-51840, [1, 2, 2, 4, 4, 9]), (-8640, [2, 2, 2, 2, 2, 2, 4, 6]), (-17280, [2, 2, 2, 2, 2, 3, 4, 5]), (-17550, [2, 2, 2, 2, 2, 4, 4, 4]), (-34560, [2, 2, 2, 2, 2, 12]), (-17640, [2, 2, 2, 2, 3, 3, 4, 4]), (-34560, [2, 2, 2, 2, 3, 11]), (-2160, [2, 2, 2, 2, 4, 10]), (-34560, [2, 2, 2, 2, 5, 9]), (-34560, [2, 2, 2, 2, 6, 8]), (-17280, [2, 2, 2, 2, 7, 7]), (-138240, [2, 2, 2, 3, 4, 9]), (-105840, [2, 2, 2, 4, 4, 8]), (-138240, [2, 2, 2, 4, 5, 7])]

def node84Piece88Output_sector0_chunk1 : RawPoly ℕ := [(-69120, [2, 2, 2, 4, 6, 6]), (-276480, [2, 2, 2, 16]), (-51840, [2, 2, 3, 4, 4, 7]), (-51840, [2, 2, 4, 4, 4, 6]), (-25920, [2, 2, 4, 4, 5, 5]), (-414720, [2, 2, 4, 14]), (-69120, [2, 4, 4, 12])]

def node84Piece88Output_sector0 : RawPoly ℕ := [node84Piece88Output_sector0_chunk0, node84Piece88Output_sector0_chunk1].flatten

def node84Piece88Output : SectorVector := [(0, node84Piece88Output_sector0)]

def node84Piece88UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 4, 4])]

def node84Piece88UnitInput_sector0 : RawPoly ℕ := [node84Piece88UnitInput_sector0_chunk0].flatten

def node84Piece88UnitInput : SectorVector := [(0, node84Piece88UnitInput_sector0)]

def node84Piece88UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (96, [1, 1, 2, 2, 2, 2, 4, 8]), (96, [1, 1, 2, 2, 2, 4, 4, 6]), (192, [1, 2, 2, 2, 2, 2, 4, 7]), (192, [1, 2, 2, 2, 2, 3, 4, 6]), (372, [1, 2, 2, 2, 2, 4, 4, 5]), (384, [1, 2, 2, 2, 2, 13]), (192, [1, 2, 2, 2, 3, 4, 4, 4]), (1536, [1, 2, 2, 2, 4, 11]), (576, [1, 2, 2, 4, 4, 9]), (96, [2, 2, 2, 2, 2, 2, 4, 6]), (192, [2, 2, 2, 2, 2, 3, 4, 5]), (195, [2, 2, 2, 2, 2, 4, 4, 4]), (384, [2, 2, 2, 2, 2, 12]), (196, [2, 2, 2, 2, 3, 3, 4, 4]), (384, [2, 2, 2, 2, 3, 11]), (24, [2, 2, 2, 2, 4, 10]), (384, [2, 2, 2, 2, 5, 9]), (384, [2, 2, 2, 2, 6, 8]), (192, [2, 2, 2, 2, 7, 7]), (1536, [2, 2, 2, 3, 4, 9]), (1176, [2, 2, 2, 4, 4, 8]), (1536, [2, 2, 2, 4, 5, 7])]

def node84Piece88UnitOutput_sector0_chunk1 : RawPoly ℕ := [(768, [2, 2, 2, 4, 6, 6]), (3072, [2, 2, 2, 16]), (576, [2, 2, 3, 4, 4, 7]), (576, [2, 2, 4, 4, 4, 6]), (288, [2, 2, 4, 4, 5, 5]), (4608, [2, 2, 4, 14]), (768, [2, 4, 4, 12])]

def node84Piece88UnitOutput_sector0 : RawPoly ℕ := [node84Piece88UnitOutput_sector0_chunk0, node84Piece88UnitOutput_sector0_chunk1].flatten

def node84Piece88UnitOutput : SectorVector := [(0, node84Piece88UnitOutput_sector0)]

theorem node84Piece88_check : neutralDirectS JR (-3) node84Piece88UnitInput = node84Piece88UnitOutput := by decide +kernel

theorem node84Piece88_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece88Input) = evaluate node84Piece88Output :=
  mode_of_scaled _ _ (-90) node84Piece88UnitInput node84Piece88UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece88_check)

def node84Piece89Input_sector0 : RawPoly ℕ := [(-560/9, [2, 2, 2, 3, 3, 4])]

def node84Piece89Input : SectorVector := [(0, node84Piece89Input_sector0)]
def node84Piece89Output_sector0_chunk0 : RawPoly ℕ := [(-2240/9, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (-1120/3, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-8960/3, [1, 1, 2, 2, 2, 3, 3, 8]), (-4480, [1, 1, 2, 2, 2, 3, 4, 7]), (-4480, [1, 1, 2, 2, 3, 3, 4, 6]), (-17920/3, [1, 2, 2, 2, 2, 3, 3, 7]), (-8960, [1, 2, 2, 2, 2, 3, 4, 6]), (-17920/3, [1, 2, 2, 2, 3, 3, 3, 6]), (-69440/3, [1, 2, 2, 2, 3, 3, 4, 5]), (-4480, [1, 2, 2, 2, 3, 4, 4, 4]), (-35840, [1, 2, 2, 2, 3, 12]), (-13440, [1, 2, 2, 2, 4, 11]), (-8960, [1, 2, 2, 3, 3, 3, 4, 4]), (-35840, [1, 2, 2, 3, 3, 11]), (-53760, [1, 2, 2, 3, 4, 10]), (-17920, [1, 2, 3, 3, 4, 9]), (-8960/3, [2, 2, 2, 2, 2, 3, 3, 6]), (-4480, [2, 2, 2, 2, 2, 3, 4, 5]), (-17920/3, [2, 2, 2, 2, 3, 3, 3, 5]), (-49840/3, [2, 2, 2, 2, 3, 3, 4, 4]), (-35840, [2, 2, 2, 2, 3, 11]), (-13440, [2, 2, 2, 2, 4, 10]), (-82880/9, [2, 2, 2, 3, 3, 3, 3, 4]), (-38080/3, [2, 2, 2, 3, 3, 10])]

def node84Piece89Output_sector0_chunk1 : RawPoly ℕ := [(-116480/3, [2, 2, 2, 3, 4, 9]), (-35840, [2, 2, 2, 3, 5, 8]), (-35840, [2, 2, 2, 3, 6, 7]), (-13440, [2, 2, 2, 4, 4, 8]), (-13440, [2, 2, 2, 4, 5, 7]), (-6720, [2, 2, 2, 4, 6, 6]), (-53760, [2, 2, 2, 16]), (-35840, [2, 2, 3, 3, 3, 9]), (-63840, [2, 2, 3, 3, 4, 8]), (-35840, [2, 2, 3, 3, 5, 7]), (-17920, [2, 2, 3, 3, 6, 6]), (-53760, [2, 2, 3, 4, 4, 7]), (-53760, [2, 2, 3, 4, 5, 6]), (-215040, [2, 2, 3, 15]), (-80640, [2, 2, 4, 14]), (-17920, [2, 3, 3, 3, 4, 7]), (-17920, [2, 3, 3, 4, 4, 6]), (-8960, [2, 3, 3, 4, 5, 5]), (-71680, [2, 3, 3, 14]), (-107520, [2, 3, 4, 13]), (-35840/3, [3, 3, 4, 12])]

def node84Piece89Output_sector0 : RawPoly ℕ := [node84Piece89Output_sector0_chunk0, node84Piece89Output_sector0_chunk1].flatten

def node84Piece89Output : SectorVector := [(0, node84Piece89Output_sector0)]

def node84Piece89UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 3, 3, 4])]

def node84Piece89UnitInput_sector0 : RawPoly ℕ := [node84Piece89UnitInput_sector0_chunk0].flatten

def node84Piece89UnitInput : SectorVector := [(0, node84Piece89UnitInput_sector0)]

def node84Piece89UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (6, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (48, [1, 1, 2, 2, 2, 3, 3, 8]), (72, [1, 1, 2, 2, 2, 3, 4, 7]), (72, [1, 1, 2, 2, 3, 3, 4, 6]), (96, [1, 2, 2, 2, 2, 3, 3, 7]), (144, [1, 2, 2, 2, 2, 3, 4, 6]), (96, [1, 2, 2, 2, 3, 3, 3, 6]), (372, [1, 2, 2, 2, 3, 3, 4, 5]), (72, [1, 2, 2, 2, 3, 4, 4, 4]), (576, [1, 2, 2, 2, 3, 12]), (216, [1, 2, 2, 2, 4, 11]), (144, [1, 2, 2, 3, 3, 3, 4, 4]), (576, [1, 2, 2, 3, 3, 11]), (864, [1, 2, 2, 3, 4, 10]), (288, [1, 2, 3, 3, 4, 9]), (48, [2, 2, 2, 2, 2, 3, 3, 6]), (72, [2, 2, 2, 2, 2, 3, 4, 5]), (96, [2, 2, 2, 2, 3, 3, 3, 5]), (267, [2, 2, 2, 2, 3, 3, 4, 4]), (576, [2, 2, 2, 2, 3, 11]), (216, [2, 2, 2, 2, 4, 10]), (148, [2, 2, 2, 3, 3, 3, 3, 4]), (204, [2, 2, 2, 3, 3, 10])]

def node84Piece89UnitOutput_sector0_chunk1 : RawPoly ℕ := [(624, [2, 2, 2, 3, 4, 9]), (576, [2, 2, 2, 3, 5, 8]), (576, [2, 2, 2, 3, 6, 7]), (216, [2, 2, 2, 4, 4, 8]), (216, [2, 2, 2, 4, 5, 7]), (108, [2, 2, 2, 4, 6, 6]), (864, [2, 2, 2, 16]), (576, [2, 2, 3, 3, 3, 9]), (1026, [2, 2, 3, 3, 4, 8]), (576, [2, 2, 3, 3, 5, 7]), (288, [2, 2, 3, 3, 6, 6]), (864, [2, 2, 3, 4, 4, 7]), (864, [2, 2, 3, 4, 5, 6]), (3456, [2, 2, 3, 15]), (1296, [2, 2, 4, 14]), (288, [2, 3, 3, 3, 4, 7]), (288, [2, 3, 3, 4, 4, 6]), (144, [2, 3, 3, 4, 5, 5]), (1152, [2, 3, 3, 14]), (1728, [2, 3, 4, 13]), (192, [3, 3, 4, 12])]

def node84Piece89UnitOutput_sector0 : RawPoly ℕ := [node84Piece89UnitOutput_sector0_chunk0, node84Piece89UnitOutput_sector0_chunk1].flatten

def node84Piece89UnitOutput : SectorVector := [(0, node84Piece89UnitOutput_sector0)]

theorem node84Piece89_check : neutralDirectS JR (-3) node84Piece89UnitInput = node84Piece89UnitOutput := by decide +kernel

theorem node84Piece89_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece89Input) = evaluate node84Piece89Output :=
  mode_of_scaled _ _ (-560/9) node84Piece89UnitInput node84Piece89UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece89_check)

def node84Piece90Input_sector0 : RawPoly ℕ := [(-144, [2, 2, 2, 10])]

def node84Piece90Input : SectorVector := [(0, node84Piece90Input_sector0)]
def node84Piece90Output_sector0_chunk0 : RawPoly ℕ := [(-576, [1, 1, 1, 2, 2, 2, 3, 10]), (-864, [1, 1, 2, 2, 2, 2, 2, 10]), (-17280, [1, 1, 2, 2, 2, 14]), (-10368, [1, 1, 2, 2, 6, 10]), (-34560, [1, 2, 2, 2, 2, 13]), (-34560, [1, 2, 2, 2, 3, 12]), (-34560, [1, 2, 2, 2, 4, 11]), (-53568, [1, 2, 2, 2, 5, 10]), (-34560, [1, 2, 2, 2, 6, 9]), (-34560, [1, 2, 2, 2, 7, 8]), (-20736, [1, 2, 2, 3, 4, 10]), (-207360, [1, 2, 2, 17]), (-41472, [1, 2, 9, 10]), (-17280, [2, 2, 2, 2, 2, 12]), (-34560, [2, 2, 2, 2, 3, 11]), (-45360, [2, 2, 2, 2, 4, 10]), (-34560, [2, 2, 2, 2, 5, 9]), (-34560, [2, 2, 2, 2, 6, 8]), (-17280, [2, 2, 2, 2, 7, 7]), (-28224, [2, 2, 2, 3, 3, 10]), (-34560, [2, 2, 2, 3, 4, 9]), (-34560, [2, 2, 2, 3, 5, 8]), (-34560, [2, 2, 2, 3, 6, 7]), (-17280, [2, 2, 2, 4, 4, 8])]

def node84Piece90Output_sector0_chunk1 : RawPoly ℕ := [(-34560, [2, 2, 2, 4, 5, 7]), (-17280, [2, 2, 2, 4, 6, 6]), (-17280, [2, 2, 2, 5, 5, 6]), (997920, [2, 2, 2, 16]), (-207360, [2, 2, 3, 15]), (-207360, [2, 2, 4, 14]), (-207360, [2, 2, 5, 13]), (-207360, [2, 2, 6, 12]), (-207360, [2, 2, 7, 11]), (-147744, [2, 2, 8, 10]), (-103680, [2, 2, 9, 9]), (-41472, [2, 3, 7, 10]), (-41472, [2, 4, 6, 10]), (-20736, [2, 5, 5, 10]), (-414720, [2, 20]), (-27648, [10, 12])]

def node84Piece90Output_sector0 : RawPoly ℕ := [node84Piece90Output_sector0_chunk0, node84Piece90Output_sector0_chunk1].flatten

def node84Piece90Output : SectorVector := [(0, node84Piece90Output_sector0)]

def node84Piece90UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 10])]

def node84Piece90UnitInput_sector0 : RawPoly ℕ := [node84Piece90UnitInput_sector0_chunk0].flatten

def node84Piece90UnitInput : SectorVector := [(0, node84Piece90UnitInput_sector0)]

def node84Piece90UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 3, 10]), (6, [1, 1, 2, 2, 2, 2, 2, 10]), (120, [1, 1, 2, 2, 2, 14]), (72, [1, 1, 2, 2, 6, 10]), (240, [1, 2, 2, 2, 2, 13]), (240, [1, 2, 2, 2, 3, 12]), (240, [1, 2, 2, 2, 4, 11]), (372, [1, 2, 2, 2, 5, 10]), (240, [1, 2, 2, 2, 6, 9]), (240, [1, 2, 2, 2, 7, 8]), (144, [1, 2, 2, 3, 4, 10]), (1440, [1, 2, 2, 17]), (288, [1, 2, 9, 10]), (120, [2, 2, 2, 2, 2, 12]), (240, [2, 2, 2, 2, 3, 11]), (315, [2, 2, 2, 2, 4, 10]), (240, [2, 2, 2, 2, 5, 9]), (240, [2, 2, 2, 2, 6, 8]), (120, [2, 2, 2, 2, 7, 7]), (196, [2, 2, 2, 3, 3, 10]), (240, [2, 2, 2, 3, 4, 9]), (240, [2, 2, 2, 3, 5, 8]), (240, [2, 2, 2, 3, 6, 7]), (120, [2, 2, 2, 4, 4, 8])]

def node84Piece90UnitOutput_sector0_chunk1 : RawPoly ℕ := [(240, [2, 2, 2, 4, 5, 7]), (120, [2, 2, 2, 4, 6, 6]), (120, [2, 2, 2, 5, 5, 6]), (-6930, [2, 2, 2, 16]), (1440, [2, 2, 3, 15]), (1440, [2, 2, 4, 14]), (1440, [2, 2, 5, 13]), (1440, [2, 2, 6, 12]), (1440, [2, 2, 7, 11]), (1026, [2, 2, 8, 10]), (720, [2, 2, 9, 9]), (288, [2, 3, 7, 10]), (288, [2, 4, 6, 10]), (144, [2, 5, 5, 10]), (2880, [2, 20]), (192, [10, 12])]

def node84Piece90UnitOutput_sector0 : RawPoly ℕ := [node84Piece90UnitOutput_sector0_chunk0, node84Piece90UnitOutput_sector0_chunk1].flatten

def node84Piece90UnitOutput : SectorVector := [(0, node84Piece90UnitOutput_sector0)]

theorem node84Piece90_check : neutralDirectS JR (-3) node84Piece90UnitInput = node84Piece90UnitOutput := by decide +kernel

theorem node84Piece90_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece90Input) = evaluate node84Piece90Output :=
  mode_of_scaled _ _ (-144) node84Piece90UnitInput node84Piece90UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece90_check)

def node84Piece91Input_sector0 : RawPoly ℕ := [(320/9, [2, 2, 3, 3, 3, 3])]

def node84Piece91Input : SectorVector := [(0, node84Piece91Input_sector0)]
def node84Piece91Output_sector0_chunk0 : RawPoly ℕ := [(1280/9, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (640/3, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (5120, [1, 1, 2, 2, 3, 3, 3, 7]), (5120/3, [1, 1, 2, 3, 3, 3, 3, 6]), (10240, [1, 2, 2, 2, 3, 3, 3, 6]), (39680/3, [1, 2, 2, 3, 3, 3, 3, 5]), (5120, [1, 2, 2, 3, 3, 3, 4, 4]), (46080, [1, 2, 2, 3, 3, 11]), (10240/3, [1, 2, 3, 3, 3, 3, 3, 4]), (40960, [1, 2, 3, 3, 3, 10]), (10240/3, [1, 3, 3, 3, 3, 9]), (5120, [2, 2, 2, 2, 3, 3, 3, 5]), (36160/3, [2, 2, 2, 3, 3, 3, 3, 4]), (46080, [2, 2, 2, 3, 3, 10]), (32000/9, [2, 2, 3, 3, 3, 3, 3, 3]), (40960/3, [2, 2, 3, 3, 3, 9]), (46080, [2, 2, 3, 3, 4, 8]), (46080, [2, 2, 3, 3, 5, 7]), (23040, [2, 2, 3, 3, 6, 6]), (92160, [2, 2, 3, 15]), (83200/3, [2, 3, 3, 3, 3, 8]), (40960, [2, 3, 3, 3, 4, 7]), (40960, [2, 3, 3, 3, 5, 6]), (184320, [2, 3, 3, 14])]

def node84Piece91Output_sector0_chunk1 : RawPoly ℕ := [(10240/3, [3, 3, 3, 3, 3, 7]), (10240/3, [3, 3, 3, 3, 4, 6]), (5120/3, [3, 3, 3, 3, 5, 5]), (40960, [3, 3, 3, 13])]

def node84Piece91Output_sector0 : RawPoly ℕ := [node84Piece91Output_sector0_chunk0, node84Piece91Output_sector0_chunk1].flatten

def node84Piece91Output : SectorVector := [(0, node84Piece91Output_sector0)]

def node84Piece91UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 3, 3, 3])]

def node84Piece91UnitInput_sector0 : RawPoly ℕ := [node84Piece91UnitInput_sector0_chunk0].flatten

def node84Piece91UnitInput : SectorVector := [(0, node84Piece91UnitInput_sector0)]

def node84Piece91UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (6, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (144, [1, 1, 2, 2, 3, 3, 3, 7]), (48, [1, 1, 2, 3, 3, 3, 3, 6]), (288, [1, 2, 2, 2, 3, 3, 3, 6]), (372, [1, 2, 2, 3, 3, 3, 3, 5]), (144, [1, 2, 2, 3, 3, 3, 4, 4]), (1296, [1, 2, 2, 3, 3, 11]), (96, [1, 2, 3, 3, 3, 3, 3, 4]), (1152, [1, 2, 3, 3, 3, 10]), (96, [1, 3, 3, 3, 3, 9]), (144, [2, 2, 2, 2, 3, 3, 3, 5]), (339, [2, 2, 2, 3, 3, 3, 3, 4]), (1296, [2, 2, 2, 3, 3, 10]), (100, [2, 2, 3, 3, 3, 3, 3, 3]), (384, [2, 2, 3, 3, 3, 9]), (1296, [2, 2, 3, 3, 4, 8]), (1296, [2, 2, 3, 3, 5, 7]), (648, [2, 2, 3, 3, 6, 6]), (2592, [2, 2, 3, 15]), (780, [2, 3, 3, 3, 3, 8]), (1152, [2, 3, 3, 3, 4, 7]), (1152, [2, 3, 3, 3, 5, 6]), (5184, [2, 3, 3, 14])]

def node84Piece91UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [3, 3, 3, 3, 3, 7]), (96, [3, 3, 3, 3, 4, 6]), (48, [3, 3, 3, 3, 5, 5]), (1152, [3, 3, 3, 13])]

def node84Piece91UnitOutput_sector0 : RawPoly ℕ := [node84Piece91UnitOutput_sector0_chunk0, node84Piece91UnitOutput_sector0_chunk1].flatten

def node84Piece91UnitOutput : SectorVector := [(0, node84Piece91UnitOutput_sector0)]

theorem node84Piece91_check : neutralDirectS JR (-3) node84Piece91UnitInput = node84Piece91UnitOutput := by decide +kernel

theorem node84Piece91_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece91Input) = evaluate node84Piece91Output :=
  mode_of_scaled _ _ (320/9) node84Piece91UnitInput node84Piece91UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece91_check)

def node84Piece92Input_sector0 : RawPoly ℕ := [(-160/3, [2, 2, 3, 9])]

def node84Piece92Input : SectorVector := [(0, node84Piece92Input_sector0)]
def node84Piece92Output_sector0_chunk0 : RawPoly ℕ := [(-640/3, [1, 1, 1, 2, 2, 3, 3, 9]), (-320, [1, 1, 2, 2, 2, 2, 3, 9]), (-5760, [1, 1, 2, 2, 3, 13]), (-1920, [1, 1, 2, 2, 7, 9]), (-2560, [1, 1, 2, 3, 6, 9]), (-11520, [1, 2, 2, 2, 3, 12]), (-3840, [1, 2, 2, 2, 6, 9]), (-11520, [1, 2, 2, 3, 3, 11]), (-11520, [1, 2, 2, 3, 4, 10]), (-19840, [1, 2, 2, 3, 5, 9]), (-11520, [1, 2, 2, 3, 6, 8]), (-5760, [1, 2, 2, 3, 7, 7]), (-1920, [1, 2, 2, 4, 4, 9]), (-34560, [1, 2, 2, 17]), (-5120, [1, 2, 3, 3, 4, 9]), (-46080, [1, 2, 3, 16]), (-15360, [1, 2, 9, 10]), (-5120, [1, 3, 9, 9]), (-5760, [2, 2, 2, 2, 3, 11]), (-1920, [2, 2, 2, 2, 5, 9]), (-11520, [2, 2, 2, 3, 3, 10]), (-18080, [2, 2, 2, 3, 4, 9]), (-11520, [2, 2, 2, 3, 5, 8]), (-11520, [2, 2, 2, 3, 6, 7])]

def node84Piece92Output_sector0_chunk1 : RawPoly ℕ := [(-34560, [2, 2, 2, 16]), (-27520/3, [2, 2, 3, 3, 3, 9]), (-11520, [2, 2, 3, 3, 4, 8]), (-11520, [2, 2, 3, 3, 5, 7]), (-5760, [2, 2, 3, 3, 6, 6]), (-5760, [2, 2, 3, 4, 4, 7]), (-11520, [2, 2, 3, 4, 5, 6]), (-1920, [2, 2, 3, 5, 5, 5]), (261120, [2, 2, 3, 15]), (-34560, [2, 2, 4, 14]), (-34560, [2, 2, 5, 13]), (-34560, [2, 2, 6, 12]), (-34560, [2, 2, 7, 11]), (-34560, [2, 2, 8, 10]), (-5120, [2, 2, 9, 9]), (-46080, [2, 3, 3, 14]), (-46080, [2, 3, 4, 13]), (-46080, [2, 3, 5, 12]), (-46080, [2, 3, 6, 11]), (-46080, [2, 3, 7, 10]), (-41600, [2, 3, 8, 9]), (-15360, [2, 4, 7, 9]), (-15360, [2, 5, 6, 9]), (-138240, [2, 20])]

def node84Piece92Output_sector0_chunk2 : RawPoly ℕ := [(-5120, [3, 3, 7, 9]), (-5120, [3, 4, 6, 9]), (-2560, [3, 5, 5, 9]), (-46080, [3, 19]), (-15360, [9, 13])]

def node84Piece92Output_sector0 : RawPoly ℕ := [node84Piece92Output_sector0_chunk0, node84Piece92Output_sector0_chunk1, node84Piece92Output_sector0_chunk2].flatten

def node84Piece92Output : SectorVector := [(0, node84Piece92Output_sector0)]

def node84Piece92UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 9])]

def node84Piece92UnitInput_sector0 : RawPoly ℕ := [node84Piece92UnitInput_sector0_chunk0].flatten

def node84Piece92UnitInput : SectorVector := [(0, node84Piece92UnitInput_sector0)]

def node84Piece92UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 3, 9]), (6, [1, 1, 2, 2, 2, 2, 3, 9]), (108, [1, 1, 2, 2, 3, 13]), (36, [1, 1, 2, 2, 7, 9]), (48, [1, 1, 2, 3, 6, 9]), (216, [1, 2, 2, 2, 3, 12]), (72, [1, 2, 2, 2, 6, 9]), (216, [1, 2, 2, 3, 3, 11]), (216, [1, 2, 2, 3, 4, 10]), (372, [1, 2, 2, 3, 5, 9]), (216, [1, 2, 2, 3, 6, 8]), (108, [1, 2, 2, 3, 7, 7]), (36, [1, 2, 2, 4, 4, 9]), (648, [1, 2, 2, 17]), (96, [1, 2, 3, 3, 4, 9]), (864, [1, 2, 3, 16]), (288, [1, 2, 9, 10]), (96, [1, 3, 9, 9]), (108, [2, 2, 2, 2, 3, 11]), (36, [2, 2, 2, 2, 5, 9]), (216, [2, 2, 2, 3, 3, 10]), (339, [2, 2, 2, 3, 4, 9]), (216, [2, 2, 2, 3, 5, 8]), (216, [2, 2, 2, 3, 6, 7])]

def node84Piece92UnitOutput_sector0_chunk1 : RawPoly ℕ := [(648, [2, 2, 2, 16]), (172, [2, 2, 3, 3, 3, 9]), (216, [2, 2, 3, 3, 4, 8]), (216, [2, 2, 3, 3, 5, 7]), (108, [2, 2, 3, 3, 6, 6]), (108, [2, 2, 3, 4, 4, 7]), (216, [2, 2, 3, 4, 5, 6]), (36, [2, 2, 3, 5, 5, 5]), (-4896, [2, 2, 3, 15]), (648, [2, 2, 4, 14]), (648, [2, 2, 5, 13]), (648, [2, 2, 6, 12]), (648, [2, 2, 7, 11]), (648, [2, 2, 8, 10]), (96, [2, 2, 9, 9]), (864, [2, 3, 3, 14]), (864, [2, 3, 4, 13]), (864, [2, 3, 5, 12]), (864, [2, 3, 6, 11]), (864, [2, 3, 7, 10]), (780, [2, 3, 8, 9]), (288, [2, 4, 7, 9]), (288, [2, 5, 6, 9]), (2592, [2, 20])]

def node84Piece92UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [3, 3, 7, 9]), (96, [3, 4, 6, 9]), (48, [3, 5, 5, 9]), (864, [3, 19]), (288, [9, 13])]

def node84Piece92UnitOutput_sector0 : RawPoly ℕ := [node84Piece92UnitOutput_sector0_chunk0, node84Piece92UnitOutput_sector0_chunk1, node84Piece92UnitOutput_sector0_chunk2].flatten

def node84Piece92UnitOutput : SectorVector := [(0, node84Piece92UnitOutput_sector0)]

theorem node84Piece92_check : neutralDirectS JR (-3) node84Piece92UnitInput = node84Piece92UnitOutput := by decide +kernel

theorem node84Piece92_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece92Input) = evaluate node84Piece92Output :=
  mode_of_scaled _ _ (-160/3) node84Piece92UnitInput node84Piece92UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece92_check)

def node84Piece93Input_sector0 : RawPoly ℕ := [(-210, [2, 2, 4, 8])]

def node84Piece93Input : SectorVector := [(0, node84Piece93Input_sector0)]
def node84Piece93Output_sector0_chunk0 : RawPoly ℕ := [(-840, [1, 1, 1, 2, 2, 3, 4, 8]), (-1260, [1, 1, 2, 2, 2, 2, 4, 8]), (-20160, [1, 1, 2, 2, 4, 12]), (-10080, [1, 1, 2, 2, 8, 8]), (-10080, [1, 1, 2, 4, 6, 8]), (-40320, [1, 2, 2, 2, 4, 11]), (-20160, [1, 2, 2, 2, 7, 8]), (-40320, [1, 2, 2, 3, 4, 10]), (-20160, [1, 2, 2, 3, 6, 8]), (-40320, [1, 2, 2, 4, 4, 9]), (-78120, [1, 2, 2, 4, 5, 8]), (-40320, [1, 2, 2, 4, 6, 7]), (-161280, [1, 2, 2, 17]), (-20160, [1, 2, 3, 4, 4, 8]), (-161280, [1, 2, 4, 15]), (-80640, [1, 2, 8, 11]), (-20160, [1, 4, 8, 9]), (-20160, [2, 2, 2, 2, 4, 10]), (-10080, [2, 2, 2, 2, 6, 8]), (-40320, [2, 2, 2, 3, 4, 9]), (-20160, [2, 2, 2, 3, 5, 8]), (-61110, [2, 2, 2, 4, 4, 8]), (-40320, [2, 2, 2, 4, 5, 7]), (-20160, [2, 2, 2, 4, 6, 6])]

def node84Piece93Output_sector0_chunk1 : RawPoly ℕ := [(-161280, [2, 2, 2, 16]), (-41160, [2, 2, 3, 3, 4, 8]), (-40320, [2, 2, 3, 4, 4, 7]), (-40320, [2, 2, 3, 4, 5, 6]), (-161280, [2, 2, 3, 15]), (-20160, [2, 2, 4, 4, 4, 6]), (-20160, [2, 2, 4, 4, 5, 5]), (680400, [2, 2, 4, 14]), (-161280, [2, 2, 5, 13]), (-161280, [2, 2, 6, 12]), (-161280, [2, 2, 7, 11]), (-42840, [2, 2, 8, 10]), (-80640, [2, 2, 9, 9]), (-161280, [2, 3, 4, 13]), (-80640, [2, 3, 8, 9]), (-161280, [2, 4, 4, 12]), (-161280, [2, 4, 5, 11]), (-161280, [2, 4, 6, 10]), (-161280, [2, 4, 7, 9]), (-83160, [2, 4, 8, 8]), (-80640, [2, 5, 7, 8]), (-40320, [2, 6, 6, 8]), (-645120, [2, 20]), (-20160, [3, 4, 7, 8])]

def node84Piece93Output_sector0_chunk2 : RawPoly ℕ := [(-20160, [4, 4, 6, 8]), (-10080, [4, 5, 5, 8]), (-161280, [4, 18]), (-80640, [8, 14])]

def node84Piece93Output_sector0 : RawPoly ℕ := [node84Piece93Output_sector0_chunk0, node84Piece93Output_sector0_chunk1, node84Piece93Output_sector0_chunk2].flatten

def node84Piece93Output : SectorVector := [(0, node84Piece93Output_sector0)]

def node84Piece93UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 4, 8])]

def node84Piece93UnitInput_sector0 : RawPoly ℕ := [node84Piece93UnitInput_sector0_chunk0].flatten

def node84Piece93UnitInput : SectorVector := [(0, node84Piece93UnitInput_sector0)]

def node84Piece93UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 4, 8]), (6, [1, 1, 2, 2, 2, 2, 4, 8]), (96, [1, 1, 2, 2, 4, 12]), (48, [1, 1, 2, 2, 8, 8]), (48, [1, 1, 2, 4, 6, 8]), (192, [1, 2, 2, 2, 4, 11]), (96, [1, 2, 2, 2, 7, 8]), (192, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 6, 8]), (192, [1, 2, 2, 4, 4, 9]), (372, [1, 2, 2, 4, 5, 8]), (192, [1, 2, 2, 4, 6, 7]), (768, [1, 2, 2, 17]), (96, [1, 2, 3, 4, 4, 8]), (768, [1, 2, 4, 15]), (384, [1, 2, 8, 11]), (96, [1, 4, 8, 9]), (96, [2, 2, 2, 2, 4, 10]), (48, [2, 2, 2, 2, 6, 8]), (192, [2, 2, 2, 3, 4, 9]), (96, [2, 2, 2, 3, 5, 8]), (291, [2, 2, 2, 4, 4, 8]), (192, [2, 2, 2, 4, 5, 7]), (96, [2, 2, 2, 4, 6, 6])]

def node84Piece93UnitOutput_sector0_chunk1 : RawPoly ℕ := [(768, [2, 2, 2, 16]), (196, [2, 2, 3, 3, 4, 8]), (192, [2, 2, 3, 4, 4, 7]), (192, [2, 2, 3, 4, 5, 6]), (768, [2, 2, 3, 15]), (96, [2, 2, 4, 4, 4, 6]), (96, [2, 2, 4, 4, 5, 5]), (-3240, [2, 2, 4, 14]), (768, [2, 2, 5, 13]), (768, [2, 2, 6, 12]), (768, [2, 2, 7, 11]), (204, [2, 2, 8, 10]), (384, [2, 2, 9, 9]), (768, [2, 3, 4, 13]), (384, [2, 3, 8, 9]), (768, [2, 4, 4, 12]), (768, [2, 4, 5, 11]), (768, [2, 4, 6, 10]), (768, [2, 4, 7, 9]), (396, [2, 4, 8, 8]), (384, [2, 5, 7, 8]), (192, [2, 6, 6, 8]), (3072, [2, 20]), (96, [3, 4, 7, 8])]

def node84Piece93UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [4, 4, 6, 8]), (48, [4, 5, 5, 8]), (768, [4, 18]), (384, [8, 14])]

def node84Piece93UnitOutput_sector0 : RawPoly ℕ := [node84Piece93UnitOutput_sector0_chunk0, node84Piece93UnitOutput_sector0_chunk1, node84Piece93UnitOutput_sector0_chunk2].flatten

def node84Piece93UnitOutput : SectorVector := [(0, node84Piece93UnitOutput_sector0)]

theorem node84Piece93_check : neutralDirectS JR (-3) node84Piece93UnitInput = node84Piece93UnitOutput := by decide +kernel

theorem node84Piece93_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece93Input) = evaluate node84Piece93Output :=
  mode_of_scaled _ _ (-210) node84Piece93UnitInput node84Piece93UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece93_check)

def node84Piece94Input_sector0 : RawPoly ℕ := [(-864/7, [2, 2, 5, 7])]

def node84Piece94Input : SectorVector := [(0, node84Piece94Input_sector0)]
def node84Piece94Output_sector0_chunk0 : RawPoly ℕ := [(-3456/7, [1, 1, 1, 2, 2, 3, 5, 7]), (-5184/7, [1, 1, 2, 2, 2, 2, 5, 7]), (-10368, [1, 1, 2, 2, 5, 11]), (-51840/7, [1, 1, 2, 2, 7, 9]), (-41472/7, [1, 1, 2, 5, 6, 7]), (-20736, [1, 2, 2, 2, 5, 10]), (-103680/7, [1, 2, 2, 2, 7, 8]), (-20736, [1, 2, 2, 3, 5, 9]), (-103680/7, [1, 2, 2, 3, 7, 7]), (-20736, [1, 2, 2, 4, 5, 8]), (-103680/7, [1, 2, 2, 4, 6, 7]), (-269568/7, [1, 2, 2, 5, 5, 7]), (-10368, [1, 2, 2, 5, 6, 6]), (-103680, [1, 2, 2, 17]), (-82944/7, [1, 2, 3, 4, 5, 7]), (-82944, [1, 2, 5, 14]), (-414720/7, [1, 2, 7, 12]), (-82944/7, [1, 5, 7, 9]), (-10368, [2, 2, 2, 2, 5, 9]), (-51840/7, [2, 2, 2, 2, 7, 7]), (-20736, [2, 2, 2, 3, 5, 8]), (-103680/7, [2, 2, 2, 3, 6, 7]), (-292896/7, [2, 2, 2, 4, 5, 7]), (-20736, [2, 2, 2, 5, 5, 6])]

def node84Piece94Output_sector0_chunk1 : RawPoly ℕ := [(-103680, [2, 2, 2, 16]), (-24192, [2, 2, 3, 3, 5, 7]), (-51840/7, [2, 2, 3, 4, 4, 7]), (-20736, [2, 2, 3, 4, 5, 6]), (-10368, [2, 2, 3, 5, 5, 5]), (-103680, [2, 2, 3, 15]), (-10368, [2, 2, 4, 4, 5, 5]), (-103680, [2, 2, 4, 14]), (238464, [2, 2, 5, 13]), (-103680, [2, 2, 6, 12]), (207360/7, [2, 2, 7, 11]), (-103680, [2, 2, 8, 10]), (-51840, [2, 2, 9, 9]), (-82944, [2, 3, 5, 12]), (-414720/7, [2, 3, 7, 10]), (-82944, [2, 4, 5, 11]), (-414720/7, [2, 4, 7, 9]), (-82944, [2, 5, 5, 10]), (-82944, [2, 5, 6, 9]), (-673920/7, [2, 5, 7, 8]), (-414720/7, [2, 6, 7, 7]), (-414720, [2, 20]), (-82944/7, [3, 5, 7, 7]), (-82944/7, [4, 5, 6, 7])]

def node84Piece94Output_sector0_chunk2 : RawPoly ℕ := [(-41472/7, [5, 5, 5, 7]), (-82944, [5, 17]), (-414720/7, [7, 15])]

def node84Piece94Output_sector0 : RawPoly ℕ := [node84Piece94Output_sector0_chunk0, node84Piece94Output_sector0_chunk1, node84Piece94Output_sector0_chunk2].flatten

def node84Piece94Output : SectorVector := [(0, node84Piece94Output_sector0)]

def node84Piece94UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 5, 7])]

def node84Piece94UnitInput_sector0 : RawPoly ℕ := [node84Piece94UnitInput_sector0_chunk0].flatten

def node84Piece94UnitInput : SectorVector := [(0, node84Piece94UnitInput_sector0)]

def node84Piece94UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 5, 7]), (6, [1, 1, 2, 2, 2, 2, 5, 7]), (84, [1, 1, 2, 2, 5, 11]), (60, [1, 1, 2, 2, 7, 9]), (48, [1, 1, 2, 5, 6, 7]), (168, [1, 2, 2, 2, 5, 10]), (120, [1, 2, 2, 2, 7, 8]), (168, [1, 2, 2, 3, 5, 9]), (120, [1, 2, 2, 3, 7, 7]), (168, [1, 2, 2, 4, 5, 8]), (120, [1, 2, 2, 4, 6, 7]), (312, [1, 2, 2, 5, 5, 7]), (84, [1, 2, 2, 5, 6, 6]), (840, [1, 2, 2, 17]), (96, [1, 2, 3, 4, 5, 7]), (672, [1, 2, 5, 14]), (480, [1, 2, 7, 12]), (96, [1, 5, 7, 9]), (84, [2, 2, 2, 2, 5, 9]), (60, [2, 2, 2, 2, 7, 7]), (168, [2, 2, 2, 3, 5, 8]), (120, [2, 2, 2, 3, 6, 7]), (339, [2, 2, 2, 4, 5, 7]), (168, [2, 2, 2, 5, 5, 6])]

def node84Piece94UnitOutput_sector0_chunk1 : RawPoly ℕ := [(840, [2, 2, 2, 16]), (196, [2, 2, 3, 3, 5, 7]), (60, [2, 2, 3, 4, 4, 7]), (168, [2, 2, 3, 4, 5, 6]), (84, [2, 2, 3, 5, 5, 5]), (840, [2, 2, 3, 15]), (84, [2, 2, 4, 4, 5, 5]), (840, [2, 2, 4, 14]), (-1932, [2, 2, 5, 13]), (840, [2, 2, 6, 12]), (-240, [2, 2, 7, 11]), (840, [2, 2, 8, 10]), (420, [2, 2, 9, 9]), (672, [2, 3, 5, 12]), (480, [2, 3, 7, 10]), (672, [2, 4, 5, 11]), (480, [2, 4, 7, 9]), (672, [2, 5, 5, 10]), (672, [2, 5, 6, 9]), (780, [2, 5, 7, 8]), (480, [2, 6, 7, 7]), (3360, [2, 20]), (96, [3, 5, 7, 7]), (96, [4, 5, 6, 7])]

def node84Piece94UnitOutput_sector0_chunk2 : RawPoly ℕ := [(48, [5, 5, 5, 7]), (672, [5, 17]), (480, [7, 15])]

def node84Piece94UnitOutput_sector0 : RawPoly ℕ := [node84Piece94UnitOutput_sector0_chunk0, node84Piece94UnitOutput_sector0_chunk1, node84Piece94UnitOutput_sector0_chunk2].flatten

def node84Piece94UnitOutput : SectorVector := [(0, node84Piece94UnitOutput_sector0)]

theorem node84Piece94_check : neutralDirectS JR (-3) node84Piece94UnitInput = node84Piece94UnitOutput := by decide +kernel

theorem node84Piece94_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece94Input) = evaluate node84Piece94Output :=
  mode_of_scaled _ _ (-864/7) node84Piece94UnitInput node84Piece94UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece94_check)

def node84Piece95Input_sector0 : RawPoly ℕ := [(-200/3, [2, 2, 6, 6])]

def node84Piece95Input : SectorVector := [(0, node84Piece95Input_sector0)]
def node84Piece95Output_sector0_chunk0 : RawPoly ℕ := [(-800/3, [1, 1, 1, 2, 2, 3, 6, 6]), (-400, [1, 1, 2, 2, 2, 2, 6, 6]), (-9600, [1, 1, 2, 2, 6, 10]), (-3200, [1, 1, 2, 6, 6, 6]), (-19200, [1, 2, 2, 2, 6, 9]), (-19200, [1, 2, 2, 3, 6, 8]), (-19200, [1, 2, 2, 4, 6, 7]), (-24800, [1, 2, 2, 5, 6, 6]), (-57600, [1, 2, 2, 17]), (-6400, [1, 2, 3, 4, 6, 6]), (-76800, [1, 2, 6, 13]), (-6400, [1, 6, 6, 9]), (-9600, [2, 2, 2, 2, 6, 8]), (-19200, [2, 2, 2, 3, 6, 7]), (-22600, [2, 2, 2, 4, 6, 6]), (-9600, [2, 2, 2, 5, 5, 6]), (-57600, [2, 2, 2, 16]), (-39200/3, [2, 2, 3, 3, 6, 6]), (-19200, [2, 2, 3, 4, 5, 6]), (-57600, [2, 2, 3, 15]), (-3200, [2, 2, 4, 4, 4, 6]), (-57600, [2, 2, 4, 14]), (-57600, [2, 2, 5, 13]), (183200, [2, 2, 6, 12])]

def node84Piece95Output_sector0_chunk1 : RawPoly ℕ := [(-57600, [2, 2, 7, 11]), (-57600, [2, 2, 8, 10]), (-28800, [2, 2, 9, 9]), (-76800, [2, 3, 6, 11]), (-76800, [2, 4, 6, 10]), (-76800, [2, 5, 6, 9]), (-52000, [2, 6, 6, 8]), (-38400, [2, 6, 7, 7]), (-230400, [2, 20]), (-6400, [3, 6, 6, 7]), (-6400, [4, 6, 6, 6]), (-3200, [5, 5, 6, 6]), (-76800, [6, 16])]

def node84Piece95Output_sector0 : RawPoly ℕ := [node84Piece95Output_sector0_chunk0, node84Piece95Output_sector0_chunk1].flatten

def node84Piece95Output : SectorVector := [(0, node84Piece95Output_sector0)]

def node84Piece95UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 6, 6])]

def node84Piece95UnitInput_sector0 : RawPoly ℕ := [node84Piece95UnitInput_sector0_chunk0].flatten

def node84Piece95UnitInput : SectorVector := [(0, node84Piece95UnitInput_sector0)]

def node84Piece95UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 6, 6]), (6, [1, 1, 2, 2, 2, 2, 6, 6]), (144, [1, 1, 2, 2, 6, 10]), (48, [1, 1, 2, 6, 6, 6]), (288, [1, 2, 2, 2, 6, 9]), (288, [1, 2, 2, 3, 6, 8]), (288, [1, 2, 2, 4, 6, 7]), (372, [1, 2, 2, 5, 6, 6]), (864, [1, 2, 2, 17]), (96, [1, 2, 3, 4, 6, 6]), (1152, [1, 2, 6, 13]), (96, [1, 6, 6, 9]), (144, [2, 2, 2, 2, 6, 8]), (288, [2, 2, 2, 3, 6, 7]), (339, [2, 2, 2, 4, 6, 6]), (144, [2, 2, 2, 5, 5, 6]), (864, [2, 2, 2, 16]), (196, [2, 2, 3, 3, 6, 6]), (288, [2, 2, 3, 4, 5, 6]), (864, [2, 2, 3, 15]), (48, [2, 2, 4, 4, 4, 6]), (864, [2, 2, 4, 14]), (864, [2, 2, 5, 13]), (-2748, [2, 2, 6, 12])]

def node84Piece95UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [2, 2, 7, 11]), (864, [2, 2, 8, 10]), (432, [2, 2, 9, 9]), (1152, [2, 3, 6, 11]), (1152, [2, 4, 6, 10]), (1152, [2, 5, 6, 9]), (780, [2, 6, 6, 8]), (576, [2, 6, 7, 7]), (3456, [2, 20]), (96, [3, 6, 6, 7]), (96, [4, 6, 6, 6]), (48, [5, 5, 6, 6]), (1152, [6, 16])]

def node84Piece95UnitOutput_sector0 : RawPoly ℕ := [node84Piece95UnitOutput_sector0_chunk0, node84Piece95UnitOutput_sector0_chunk1].flatten

def node84Piece95UnitOutput : SectorVector := [(0, node84Piece95UnitOutput_sector0)]

theorem node84Piece95_check : neutralDirectS JR (-3) node84Piece95UnitInput = node84Piece95UnitOutput := by decide +kernel

theorem node84Piece95_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node84Piece95Input) = evaluate node84Piece95Output :=
  mode_of_scaled _ _ (-200/3) node84Piece95UnitInput node84Piece95UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node84Piece95_check)

end VOA.Classification.COne.OrbC2h
