import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch78_4
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

def node78Piece96Input_sector0 : RawPoly ℕ := [(128/3, [1, 2, 5, 9])]

def node78Piece96Input : SectorVector := [(0, node78Piece96Input_sector0)]
def node78Piece96Output_sector0_chunk0 : RawPoly ℕ := [(512/3, [1, 1, 1, 1, 2, 2, 5, 9]), (4608, [1, 1, 1, 2, 5, 12]), (2560, [1, 1, 1, 2, 8, 9]), (1024, [1, 1, 1, 5, 5, 9]), (9216, [1, 1, 2, 2, 5, 11]), (5120, [1, 1, 2, 2, 7, 9]), (9216, [1, 1, 2, 3, 5, 10]), (5120, [1, 1, 2, 3, 6, 9]), (16640, [1, 1, 2, 4, 5, 9]), (9216, [1, 1, 2, 5, 5, 8]), (9216, [1, 1, 2, 5, 6, 7]), (46080, [1, 1, 2, 18]), (1024, [1, 1, 3, 3, 5, 9]), (18432, [1, 1, 5, 15]), (10240, [1, 1, 9, 11]), (4608, [1, 2, 2, 2, 5, 10]), (2560, [1, 2, 2, 2, 6, 9]), (49664/3, [1, 2, 2, 3, 5, 9]), (2560, [1, 2, 2, 4, 4, 9]), (9216, [1, 2, 2, 4, 5, 8]), (9216, [1, 2, 2, 5, 5, 7]), (4608, [1, 2, 2, 5, 6, 6]), (46080, [1, 2, 2, 17]), (2560, [1, 2, 3, 3, 4, 9])]

def node78Piece96Output_sector0_chunk1 : RawPoly ℕ := [(4608, [1, 2, 3, 3, 5, 8]), (9216, [1, 2, 3, 4, 5, 7]), (9216, [1, 2, 3, 5, 5, 6]), (46080, [1, 2, 3, 16]), (4608, [1, 2, 4, 4, 5, 6]), (4608, [1, 2, 4, 5, 5, 5]), (46080, [1, 2, 4, 15]), (-178176, [1, 2, 5, 14]), (46080, [1, 2, 6, 13]), (46080, [1, 2, 7, 12]), (46080, [1, 2, 8, 11]), (2560, [1, 2, 9, 10]), (18432, [1, 3, 5, 13]), (10240, [1, 3, 9, 9]), (18432, [1, 4, 5, 12]), (10240, [1, 4, 8, 9]), (18432, [1, 5, 5, 11]), (18432, [1, 5, 6, 10]), (22528, [1, 5, 7, 9]), (9216, [1, 5, 8, 8]), (5120, [1, 6, 6, 9]), (92160, [1, 21]), (512/3, [2, 2, 2, 2, 5, 9]), (9216, [2, 2, 5, 13])]

def node78Piece96Output_sector0_chunk2 : RawPoly ℕ := [(5120, [2, 2, 9, 9]), (9216, [2, 3, 5, 12]), (5120, [2, 3, 8, 9]), (9216, [2, 4, 5, 11]), (5120, [2, 4, 7, 9]), (9216, [2, 5, 5, 10]), (41984/3, [2, 5, 6, 9]), (9216, [2, 5, 7, 8]), (46080, [2, 20]), (2048, [3, 5, 5, 9]), (1024, [4, 4, 5, 9]), (18432, [5, 17]), (10240, [9, 13])]

def node78Piece96Output_sector0 : RawPoly ℕ := [node78Piece96Output_sector0_chunk0, node78Piece96Output_sector0_chunk1, node78Piece96Output_sector0_chunk2].flatten

def node78Piece96Output : SectorVector := [(0, node78Piece96Output_sector0)]

def node78Piece96UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 5, 9])]

def node78Piece96UnitInput_sector0 : RawPoly ℕ := [node78Piece96UnitInput_sector0_chunk0].flatten

def node78Piece96UnitInput : SectorVector := [(0, node78Piece96UnitInput_sector0)]

def node78Piece96UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 5, 9]), (108, [1, 1, 1, 2, 5, 12]), (60, [1, 1, 1, 2, 8, 9]), (24, [1, 1, 1, 5, 5, 9]), (216, [1, 1, 2, 2, 5, 11]), (120, [1, 1, 2, 2, 7, 9]), (216, [1, 1, 2, 3, 5, 10]), (120, [1, 1, 2, 3, 6, 9]), (390, [1, 1, 2, 4, 5, 9]), (216, [1, 1, 2, 5, 5, 8]), (216, [1, 1, 2, 5, 6, 7]), (1080, [1, 1, 2, 18]), (24, [1, 1, 3, 3, 5, 9]), (432, [1, 1, 5, 15]), (240, [1, 1, 9, 11]), (108, [1, 2, 2, 2, 5, 10]), (60, [1, 2, 2, 2, 6, 9]), (388, [1, 2, 2, 3, 5, 9]), (60, [1, 2, 2, 4, 4, 9]), (216, [1, 2, 2, 4, 5, 8]), (216, [1, 2, 2, 5, 5, 7]), (108, [1, 2, 2, 5, 6, 6]), (1080, [1, 2, 2, 17]), (60, [1, 2, 3, 3, 4, 9])]

def node78Piece96UnitOutput_sector0_chunk1 : RawPoly ℕ := [(108, [1, 2, 3, 3, 5, 8]), (216, [1, 2, 3, 4, 5, 7]), (216, [1, 2, 3, 5, 5, 6]), (1080, [1, 2, 3, 16]), (108, [1, 2, 4, 4, 5, 6]), (108, [1, 2, 4, 5, 5, 5]), (1080, [1, 2, 4, 15]), (-4176, [1, 2, 5, 14]), (1080, [1, 2, 6, 13]), (1080, [1, 2, 7, 12]), (1080, [1, 2, 8, 11]), (60, [1, 2, 9, 10]), (432, [1, 3, 5, 13]), (240, [1, 3, 9, 9]), (432, [1, 4, 5, 12]), (240, [1, 4, 8, 9]), (432, [1, 5, 5, 11]), (432, [1, 5, 6, 10]), (528, [1, 5, 7, 9]), (216, [1, 5, 8, 8]), (120, [1, 6, 6, 9]), (2160, [1, 21]), (4, [2, 2, 2, 2, 5, 9]), (216, [2, 2, 5, 13])]

def node78Piece96UnitOutput_sector0_chunk2 : RawPoly ℕ := [(120, [2, 2, 9, 9]), (216, [2, 3, 5, 12]), (120, [2, 3, 8, 9]), (216, [2, 4, 5, 11]), (120, [2, 4, 7, 9]), (216, [2, 5, 5, 10]), (328, [2, 5, 6, 9]), (216, [2, 5, 7, 8]), (1080, [2, 20]), (48, [3, 5, 5, 9]), (24, [4, 4, 5, 9]), (432, [5, 17]), (240, [9, 13])]

def node78Piece96UnitOutput_sector0 : RawPoly ℕ := [node78Piece96UnitOutput_sector0_chunk0, node78Piece96UnitOutput_sector0_chunk1, node78Piece96UnitOutput_sector0_chunk2].flatten

def node78Piece96UnitOutput : SectorVector := [(0, node78Piece96UnitOutput_sector0)]

theorem node78Piece96_check : VectorCertificate (neutralBoundS JR (-2) node78Piece96UnitInput) node78Piece96UnitOutput := by decide +kernel

theorem node78Piece96_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece96Input) = evaluate node78Piece96Output :=
  mode_of_scaled _ _ (128/3) node78Piece96UnitInput node78Piece96UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece96_check)

def node78Piece97Input_sector0 : RawPoly ℕ := [(160/3, [1, 3, 3, 3, 3, 4])]

def node78Piece97Input : SectorVector := [(0, node78Piece97Input_sector0)]
def node78Piece97Output_sector0_chunk0 : RawPoly ℕ := [(640/3, [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]), (2560, [1, 1, 1, 3, 3, 3, 3, 7]), (7680, [1, 1, 1, 3, 3, 3, 4, 6]), (5120, [1, 1, 2, 3, 3, 3, 3, 6]), (15360, [1, 1, 2, 3, 3, 3, 4, 5]), (5120, [1, 1, 3, 3, 3, 3, 3, 5]), (18240, [1, 1, 3, 3, 3, 3, 4, 4]), (61440, [1, 1, 3, 3, 3, 11]), (69120, [1, 1, 3, 3, 4, 10]), (2560, [1, 2, 2, 3, 3, 3, 3, 5]), (7680, [1, 2, 2, 3, 3, 3, 4, 4]), (42880/3, [1, 2, 3, 3, 3, 3, 3, 4]), (61440, [1, 2, 3, 3, 3, 10]), (69120, [1, 2, 3, 3, 4, 9]), (2560/3, [1, 3, 3, 3, 3, 3, 3, 3]), (67840/3, [1, 3, 3, 3, 3, 9]), (52480, [1, 3, 3, 3, 4, 8]), (61440, [1, 3, 3, 3, 5, 7]), (30720, [1, 3, 3, 3, 6, 6]), (69120, [1, 3, 3, 4, 4, 7]), (69120, [1, 3, 3, 4, 5, 6]), (276480, [1, 3, 3, 15]), (138240, [1, 3, 4, 14]), (640/3, [2, 2, 2, 3, 3, 3, 3, 4])]

def node78Piece97Output_sector0_chunk1 : RawPoly ℕ := [(5120, [2, 3, 3, 3, 3, 8]), (15360, [2, 3, 3, 3, 4, 7]), (5120, [3, 3, 3, 3, 3, 7]), (52480/3, [3, 3, 3, 3, 4, 6]), (2560, [3, 3, 3, 3, 5, 5]), (15360, [3, 3, 3, 4, 4, 5]), (61440, [3, 3, 3, 13]), (69120, [3, 3, 4, 12])]

def node78Piece97Output_sector0 : RawPoly ℕ := [node78Piece97Output_sector0_chunk0, node78Piece97Output_sector0_chunk1].flatten

def node78Piece97Output : SectorVector := [(0, node78Piece97Output_sector0)]

def node78Piece97UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 3, 3, 3, 4])]

def node78Piece97UnitInput_sector0 : RawPoly ℕ := [node78Piece97UnitInput_sector0_chunk0].flatten

def node78Piece97UnitInput : SectorVector := [(0, node78Piece97UnitInput_sector0)]

def node78Piece97UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]), (48, [1, 1, 1, 3, 3, 3, 3, 7]), (144, [1, 1, 1, 3, 3, 3, 4, 6]), (96, [1, 1, 2, 3, 3, 3, 3, 6]), (288, [1, 1, 2, 3, 3, 3, 4, 5]), (96, [1, 1, 3, 3, 3, 3, 3, 5]), (342, [1, 1, 3, 3, 3, 3, 4, 4]), (1152, [1, 1, 3, 3, 3, 11]), (1296, [1, 1, 3, 3, 4, 10]), (48, [1, 2, 2, 3, 3, 3, 3, 5]), (144, [1, 2, 2, 3, 3, 3, 4, 4]), (268, [1, 2, 3, 3, 3, 3, 3, 4]), (1152, [1, 2, 3, 3, 3, 10]), (1296, [1, 2, 3, 3, 4, 9]), (16, [1, 3, 3, 3, 3, 3, 3, 3]), (424, [1, 3, 3, 3, 3, 9]), (984, [1, 3, 3, 3, 4, 8]), (1152, [1, 3, 3, 3, 5, 7]), (576, [1, 3, 3, 3, 6, 6]), (1296, [1, 3, 3, 4, 4, 7]), (1296, [1, 3, 3, 4, 5, 6]), (5184, [1, 3, 3, 15]), (2592, [1, 3, 4, 14]), (4, [2, 2, 2, 3, 3, 3, 3, 4])]

def node78Piece97UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [2, 3, 3, 3, 3, 8]), (288, [2, 3, 3, 3, 4, 7]), (96, [3, 3, 3, 3, 3, 7]), (328, [3, 3, 3, 3, 4, 6]), (48, [3, 3, 3, 3, 5, 5]), (288, [3, 3, 3, 4, 4, 5]), (1152, [3, 3, 3, 13]), (1296, [3, 3, 4, 12])]

def node78Piece97UnitOutput_sector0 : RawPoly ℕ := [node78Piece97UnitOutput_sector0_chunk0, node78Piece97UnitOutput_sector0_chunk1].flatten

def node78Piece97UnitOutput : SectorVector := [(0, node78Piece97UnitOutput_sector0)]

theorem node78Piece97_check : VectorCertificate (neutralBoundS JR (-2) node78Piece97UnitInput) node78Piece97UnitOutput := by decide +kernel

theorem node78Piece97_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece97Input) = evaluate node78Piece97Output :=
  mode_of_scaled _ _ (160/3) node78Piece97UnitInput node78Piece97UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece97_check)

def node78Piece98Input_sector0 : RawPoly ℕ := [(192, [1, 3, 3, 10])]

def node78Piece98Input : SectorVector := [(0, node78Piece98Input_sector0)]
def node78Piece98Output_sector0_chunk0 : RawPoly ℕ := [(768, [1, 1, 1, 1, 2, 3, 3, 10]), (23040, [1, 1, 1, 3, 3, 13]), (13824, [1, 1, 1, 3, 6, 10]), (46080, [1, 1, 2, 3, 3, 12]), (27648, [1, 1, 2, 3, 5, 10]), (46080, [1, 1, 3, 3, 3, 11]), (74880, [1, 1, 3, 3, 4, 10]), (46080, [1, 1, 3, 3, 5, 9]), (46080, [1, 1, 3, 3, 6, 8]), (23040, [1, 1, 3, 3, 7, 7]), (276480, [1, 1, 3, 17]), (41472, [1, 1, 10, 10]), (23040, [1, 2, 2, 3, 3, 11]), (13824, [1, 2, 2, 3, 4, 10]), (65280, [1, 2, 3, 3, 3, 10]), (46080, [1, 2, 3, 3, 4, 9]), (46080, [1, 2, 3, 3, 5, 8]), (46080, [1, 2, 3, 3, 6, 7]), (276480, [1, 2, 3, 16]), (41472, [1, 2, 9, 10]), (23040, [1, 3, 3, 3, 3, 9]), (46080, [1, 3, 3, 3, 4, 8]), (46080, [1, 3, 3, 3, 5, 7]), (23040, [1, 3, 3, 3, 6, 6])]

def node78Piece98Output_sector0_chunk1 : RawPoly ℕ := [(23040, [1, 3, 3, 4, 4, 7]), (46080, [1, 3, 3, 4, 5, 6]), (7680, [1, 3, 3, 5, 5, 5]), (-1167360, [1, 3, 3, 15]), (276480, [1, 3, 4, 14]), (276480, [1, 3, 5, 13]), (276480, [1, 3, 6, 12]), (276480, [1, 3, 7, 11]), (177408, [1, 3, 8, 10]), (138240, [1, 3, 9, 9]), (41472, [1, 4, 7, 10]), (41472, [1, 5, 6, 10]), (414720, [1, 21]), (768, [2, 2, 2, 3, 3, 10]), (46080, [2, 3, 3, 14]), (27648, [2, 3, 7, 10]), (46080, [3, 3, 3, 13]), (46080, [3, 3, 4, 12]), (46080, [3, 3, 5, 11]), (62976, [3, 3, 6, 10]), (46080, [3, 3, 7, 9]), (23040, [3, 3, 8, 8]), (27648, [3, 4, 5, 10]), (276480, [3, 19])]

def node78Piece98Output_sector0_chunk2 : RawPoly ℕ := [(41472, [10, 12])]

def node78Piece98Output_sector0 : RawPoly ℕ := [node78Piece98Output_sector0_chunk0, node78Piece98Output_sector0_chunk1, node78Piece98Output_sector0_chunk2].flatten

def node78Piece98Output : SectorVector := [(0, node78Piece98Output_sector0)]

def node78Piece98UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 3, 10])]

def node78Piece98UnitInput_sector0 : RawPoly ℕ := [node78Piece98UnitInput_sector0_chunk0].flatten

def node78Piece98UnitInput : SectorVector := [(0, node78Piece98UnitInput_sector0)]

def node78Piece98UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 3, 10]), (120, [1, 1, 1, 3, 3, 13]), (72, [1, 1, 1, 3, 6, 10]), (240, [1, 1, 2, 3, 3, 12]), (144, [1, 1, 2, 3, 5, 10]), (240, [1, 1, 3, 3, 3, 11]), (390, [1, 1, 3, 3, 4, 10]), (240, [1, 1, 3, 3, 5, 9]), (240, [1, 1, 3, 3, 6, 8]), (120, [1, 1, 3, 3, 7, 7]), (1440, [1, 1, 3, 17]), (216, [1, 1, 10, 10]), (120, [1, 2, 2, 3, 3, 11]), (72, [1, 2, 2, 3, 4, 10]), (340, [1, 2, 3, 3, 3, 10]), (240, [1, 2, 3, 3, 4, 9]), (240, [1, 2, 3, 3, 5, 8]), (240, [1, 2, 3, 3, 6, 7]), (1440, [1, 2, 3, 16]), (216, [1, 2, 9, 10]), (120, [1, 3, 3, 3, 3, 9]), (240, [1, 3, 3, 3, 4, 8]), (240, [1, 3, 3, 3, 5, 7]), (120, [1, 3, 3, 3, 6, 6])]

def node78Piece98UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 3, 3, 4, 4, 7]), (240, [1, 3, 3, 4, 5, 6]), (40, [1, 3, 3, 5, 5, 5]), (-6080, [1, 3, 3, 15]), (1440, [1, 3, 4, 14]), (1440, [1, 3, 5, 13]), (1440, [1, 3, 6, 12]), (1440, [1, 3, 7, 11]), (924, [1, 3, 8, 10]), (720, [1, 3, 9, 9]), (216, [1, 4, 7, 10]), (216, [1, 5, 6, 10]), (2160, [1, 21]), (4, [2, 2, 2, 3, 3, 10]), (240, [2, 3, 3, 14]), (144, [2, 3, 7, 10]), (240, [3, 3, 3, 13]), (240, [3, 3, 4, 12]), (240, [3, 3, 5, 11]), (328, [3, 3, 6, 10]), (240, [3, 3, 7, 9]), (120, [3, 3, 8, 8]), (144, [3, 4, 5, 10]), (1440, [3, 19])]

def node78Piece98UnitOutput_sector0_chunk2 : RawPoly ℕ := [(216, [10, 12])]

def node78Piece98UnitOutput_sector0 : RawPoly ℕ := [node78Piece98UnitOutput_sector0_chunk0, node78Piece98UnitOutput_sector0_chunk1, node78Piece98UnitOutput_sector0_chunk2].flatten

def node78Piece98UnitOutput : SectorVector := [(0, node78Piece98UnitOutput_sector0)]

theorem node78Piece98_check : VectorCertificate (neutralBoundS JR (-2) node78Piece98UnitInput) node78Piece98UnitOutput := by decide +kernel

theorem node78Piece98_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece98Input) = evaluate node78Piece98Output :=
  mode_of_scaled _ _ (192) node78Piece98UnitInput node78Piece98UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece98_check)

def node78Piece99Input_sector0 : RawPoly ℕ := [(160/3, [1, 3, 4, 9])]

def node78Piece99Input : SectorVector := [(0, node78Piece99Input_sector0)]
def node78Piece99Output_sector0_chunk0 : RawPoly ℕ := [(640/3, [1, 1, 1, 1, 2, 3, 4, 9]), (5760, [1, 1, 1, 3, 4, 12]), (2560, [1, 1, 1, 3, 7, 9]), (1920, [1, 1, 1, 4, 6, 9]), (11520, [1, 1, 2, 3, 4, 11]), (5120, [1, 1, 2, 3, 6, 9]), (3840, [1, 1, 2, 4, 5, 9]), (11520, [1, 1, 3, 3, 4, 10]), (5120, [1, 1, 3, 3, 5, 9]), (18240, [1, 1, 3, 4, 4, 9]), (11520, [1, 1, 3, 4, 5, 8]), (11520, [1, 1, 3, 4, 6, 7]), (46080, [1, 1, 3, 17]), (34560, [1, 1, 4, 16]), (15360, [1, 1, 9, 11]), (5760, [1, 2, 2, 3, 4, 10]), (2560, [1, 2, 2, 3, 5, 9]), (1920, [1, 2, 2, 4, 4, 9]), (60160/3, [1, 2, 3, 3, 4, 9]), (11520, [1, 2, 3, 4, 4, 8]), (11520, [1, 2, 3, 4, 5, 7]), (5760, [1, 2, 3, 4, 6, 6]), (46080, [1, 2, 3, 16]), (34560, [1, 2, 4, 15])]

def node78Piece99Output_sector0_chunk1 : RawPoly ℕ := [(15360, [1, 2, 9, 10]), (2560/3, [1, 3, 3, 3, 3, 9]), (5760, [1, 3, 3, 3, 4, 8]), (11520, [1, 3, 3, 4, 4, 7]), (11520, [1, 3, 3, 4, 5, 6]), (46080, [1, 3, 3, 15]), (5760, [1, 3, 4, 4, 4, 6]), (5760, [1, 3, 4, 4, 5, 5]), (-222720, [1, 3, 4, 14]), (46080, [1, 3, 5, 13]), (46080, [1, 3, 6, 12]), (46080, [1, 3, 7, 11]), (46080, [1, 3, 8, 10]), (-1280/3, [1, 3, 9, 9]), (34560, [1, 4, 4, 13]), (34560, [1, 4, 5, 12]), (34560, [1, 4, 6, 11]), (34560, [1, 4, 7, 10]), (30400, [1, 4, 8, 9]), (15360, [1, 5, 7, 9]), (7680, [1, 6, 6, 9]), (138240, [1, 21]), (640/3, [2, 2, 2, 3, 4, 9]), (11520, [2, 3, 4, 13])]

def node78Piece99Output_sector0_chunk2 : RawPoly ℕ := [(5120, [2, 3, 8, 9]), (3840, [2, 4, 7, 9]), (11520, [3, 3, 4, 12]), (5120, [3, 3, 7, 9]), (11520, [3, 4, 4, 11]), (11520, [3, 4, 5, 10]), (52480/3, [3, 4, 6, 9]), (11520, [3, 4, 7, 8]), (2560, [3, 5, 5, 9]), (46080, [3, 19]), (3840, [4, 4, 5, 9]), (34560, [4, 18]), (15360, [9, 13])]

def node78Piece99Output_sector0 : RawPoly ℕ := [node78Piece99Output_sector0_chunk0, node78Piece99Output_sector0_chunk1, node78Piece99Output_sector0_chunk2].flatten

def node78Piece99Output : SectorVector := [(0, node78Piece99Output_sector0)]

def node78Piece99UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 4, 9])]

def node78Piece99UnitInput_sector0 : RawPoly ℕ := [node78Piece99UnitInput_sector0_chunk0].flatten

def node78Piece99UnitInput : SectorVector := [(0, node78Piece99UnitInput_sector0)]

def node78Piece99UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 4, 9]), (108, [1, 1, 1, 3, 4, 12]), (48, [1, 1, 1, 3, 7, 9]), (36, [1, 1, 1, 4, 6, 9]), (216, [1, 1, 2, 3, 4, 11]), (96, [1, 1, 2, 3, 6, 9]), (72, [1, 1, 2, 4, 5, 9]), (216, [1, 1, 3, 3, 4, 10]), (96, [1, 1, 3, 3, 5, 9]), (342, [1, 1, 3, 4, 4, 9]), (216, [1, 1, 3, 4, 5, 8]), (216, [1, 1, 3, 4, 6, 7]), (864, [1, 1, 3, 17]), (648, [1, 1, 4, 16]), (288, [1, 1, 9, 11]), (108, [1, 2, 2, 3, 4, 10]), (48, [1, 2, 2, 3, 5, 9]), (36, [1, 2, 2, 4, 4, 9]), (376, [1, 2, 3, 3, 4, 9]), (216, [1, 2, 3, 4, 4, 8]), (216, [1, 2, 3, 4, 5, 7]), (108, [1, 2, 3, 4, 6, 6]), (864, [1, 2, 3, 16]), (648, [1, 2, 4, 15])]

def node78Piece99UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [1, 2, 9, 10]), (16, [1, 3, 3, 3, 3, 9]), (108, [1, 3, 3, 3, 4, 8]), (216, [1, 3, 3, 4, 4, 7]), (216, [1, 3, 3, 4, 5, 6]), (864, [1, 3, 3, 15]), (108, [1, 3, 4, 4, 4, 6]), (108, [1, 3, 4, 4, 5, 5]), (-4176, [1, 3, 4, 14]), (864, [1, 3, 5, 13]), (864, [1, 3, 6, 12]), (864, [1, 3, 7, 11]), (864, [1, 3, 8, 10]), (-8, [1, 3, 9, 9]), (648, [1, 4, 4, 13]), (648, [1, 4, 5, 12]), (648, [1, 4, 6, 11]), (648, [1, 4, 7, 10]), (570, [1, 4, 8, 9]), (288, [1, 5, 7, 9]), (144, [1, 6, 6, 9]), (2592, [1, 21]), (4, [2, 2, 2, 3, 4, 9]), (216, [2, 3, 4, 13])]

def node78Piece99UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [2, 3, 8, 9]), (72, [2, 4, 7, 9]), (216, [3, 3, 4, 12]), (96, [3, 3, 7, 9]), (216, [3, 4, 4, 11]), (216, [3, 4, 5, 10]), (328, [3, 4, 6, 9]), (216, [3, 4, 7, 8]), (48, [3, 5, 5, 9]), (864, [3, 19]), (72, [4, 4, 5, 9]), (648, [4, 18]), (288, [9, 13])]

def node78Piece99UnitOutput_sector0 : RawPoly ℕ := [node78Piece99UnitOutput_sector0_chunk0, node78Piece99UnitOutput_sector0_chunk1, node78Piece99UnitOutput_sector0_chunk2].flatten

def node78Piece99UnitOutput : SectorVector := [(0, node78Piece99UnitOutput_sector0)]

theorem node78Piece99_check : VectorCertificate (neutralBoundS JR (-2) node78Piece99UnitInput) node78Piece99UnitOutput := by decide +kernel

theorem node78Piece99_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece99Input) = evaluate node78Piece99Output :=
  mode_of_scaled _ _ (160/3) node78Piece99UnitInput node78Piece99UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece99_check)

def node78Piece100Input_sector0 : RawPoly ℕ := [(192, [1, 3, 5, 8])]

def node78Piece100Input : SectorVector := [(0, node78Piece100Input_sector0)]
def node78Piece100Output_sector0_chunk0 : RawPoly ℕ := [(768, [1, 1, 1, 1, 2, 3, 5, 8]), (18432, [1, 1, 1, 3, 5, 11]), (11520, [1, 1, 1, 3, 8, 8]), (6912, [1, 1, 1, 5, 6, 8]), (36864, [1, 1, 2, 3, 5, 10]), (23040, [1, 1, 2, 3, 7, 8]), (13824, [1, 1, 2, 5, 5, 8]), (36864, [1, 1, 3, 3, 5, 9]), (23040, [1, 1, 3, 3, 6, 8]), (74880, [1, 1, 3, 4, 5, 8]), (36864, [1, 1, 3, 5, 5, 7]), (18432, [1, 1, 3, 5, 6, 6]), (184320, [1, 1, 3, 17]), (110592, [1, 1, 5, 15]), (69120, [1, 1, 8, 12]), (18432, [1, 2, 2, 3, 5, 9]), (11520, [1, 2, 2, 3, 6, 8]), (6912, [1, 2, 2, 4, 5, 8]), (72192, [1, 2, 3, 3, 5, 8]), (11520, [1, 2, 3, 4, 4, 8]), (36864, [1, 2, 3, 4, 5, 7]), (36864, [1, 2, 3, 5, 5, 6]), (184320, [1, 2, 3, 16]), (110592, [1, 2, 5, 14])]

def node78Piece100Output_sector0_chunk1 : RawPoly ℕ := [(69120, [1, 2, 8, 11]), (11520, [1, 3, 3, 3, 4, 8]), (18432, [1, 3, 3, 3, 5, 7]), (36864, [1, 3, 3, 4, 5, 6]), (18432, [1, 3, 3, 5, 5, 5]), (184320, [1, 3, 3, 15]), (18432, [1, 3, 4, 4, 5, 5]), (184320, [1, 3, 4, 14]), (-506880, [1, 3, 5, 13]), (184320, [1, 3, 6, 12]), (184320, [1, 3, 7, 11]), (11520, [1, 3, 8, 10]), (92160, [1, 3, 9, 9]), (110592, [1, 4, 5, 12]), (69120, [1, 4, 8, 9]), (110592, [1, 5, 5, 11]), (110592, [1, 5, 6, 10]), (110592, [1, 5, 7, 9]), (54144, [1, 5, 8, 8]), (69120, [1, 6, 7, 8]), (552960, [1, 21]), (768, [2, 2, 2, 3, 5, 8]), (36864, [2, 3, 5, 12]), (23040, [2, 3, 8, 9])]

def node78Piece100Output_sector0_chunk2 : RawPoly ℕ := [(13824, [2, 5, 7, 8]), (36864, [3, 3, 5, 11]), (23040, [3, 3, 8, 8]), (36864, [3, 4, 5, 10]), (23040, [3, 4, 7, 8]), (36864, [3, 5, 5, 9]), (62976, [3, 5, 6, 8]), (18432, [3, 5, 7, 7]), (184320, [3, 19]), (13824, [4, 5, 5, 8]), (110592, [5, 17]), (69120, [8, 14])]

def node78Piece100Output_sector0 : RawPoly ℕ := [node78Piece100Output_sector0_chunk0, node78Piece100Output_sector0_chunk1, node78Piece100Output_sector0_chunk2].flatten

def node78Piece100Output : SectorVector := [(0, node78Piece100Output_sector0)]

def node78Piece100UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 5, 8])]

def node78Piece100UnitInput_sector0 : RawPoly ℕ := [node78Piece100UnitInput_sector0_chunk0].flatten

def node78Piece100UnitInput : SectorVector := [(0, node78Piece100UnitInput_sector0)]

def node78Piece100UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 5, 8]), (96, [1, 1, 1, 3, 5, 11]), (60, [1, 1, 1, 3, 8, 8]), (36, [1, 1, 1, 5, 6, 8]), (192, [1, 1, 2, 3, 5, 10]), (120, [1, 1, 2, 3, 7, 8]), (72, [1, 1, 2, 5, 5, 8]), (192, [1, 1, 3, 3, 5, 9]), (120, [1, 1, 3, 3, 6, 8]), (390, [1, 1, 3, 4, 5, 8]), (192, [1, 1, 3, 5, 5, 7]), (96, [1, 1, 3, 5, 6, 6]), (960, [1, 1, 3, 17]), (576, [1, 1, 5, 15]), (360, [1, 1, 8, 12]), (96, [1, 2, 2, 3, 5, 9]), (60, [1, 2, 2, 3, 6, 8]), (36, [1, 2, 2, 4, 5, 8]), (376, [1, 2, 3, 3, 5, 8]), (60, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (192, [1, 2, 3, 5, 5, 6]), (960, [1, 2, 3, 16]), (576, [1, 2, 5, 14])]

def node78Piece100UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [1, 2, 8, 11]), (60, [1, 3, 3, 3, 4, 8]), (96, [1, 3, 3, 3, 5, 7]), (192, [1, 3, 3, 4, 5, 6]), (96, [1, 3, 3, 5, 5, 5]), (960, [1, 3, 3, 15]), (96, [1, 3, 4, 4, 5, 5]), (960, [1, 3, 4, 14]), (-2640, [1, 3, 5, 13]), (960, [1, 3, 6, 12]), (960, [1, 3, 7, 11]), (60, [1, 3, 8, 10]), (480, [1, 3, 9, 9]), (576, [1, 4, 5, 12]), (360, [1, 4, 8, 9]), (576, [1, 5, 5, 11]), (576, [1, 5, 6, 10]), (576, [1, 5, 7, 9]), (282, [1, 5, 8, 8]), (360, [1, 6, 7, 8]), (2880, [1, 21]), (4, [2, 2, 2, 3, 5, 8]), (192, [2, 3, 5, 12]), (120, [2, 3, 8, 9])]

def node78Piece100UnitOutput_sector0_chunk2 : RawPoly ℕ := [(72, [2, 5, 7, 8]), (192, [3, 3, 5, 11]), (120, [3, 3, 8, 8]), (192, [3, 4, 5, 10]), (120, [3, 4, 7, 8]), (192, [3, 5, 5, 9]), (328, [3, 5, 6, 8]), (96, [3, 5, 7, 7]), (960, [3, 19]), (72, [4, 5, 5, 8]), (576, [5, 17]), (360, [8, 14])]

def node78Piece100UnitOutput_sector0 : RawPoly ℕ := [node78Piece100UnitOutput_sector0_chunk0, node78Piece100UnitOutput_sector0_chunk1, node78Piece100UnitOutput_sector0_chunk2].flatten

def node78Piece100UnitOutput : SectorVector := [(0, node78Piece100UnitOutput_sector0)]

theorem node78Piece100_check : VectorCertificate (neutralBoundS JR (-2) node78Piece100UnitInput) node78Piece100UnitOutput := by decide +kernel

theorem node78Piece100_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece100Input) = evaluate node78Piece100Output :=
  mode_of_scaled _ _ (192) node78Piece100UnitInput node78Piece100UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece100_check)

def node78Piece101Input_sector0 : RawPoly ℕ := [(3200/21, [1, 3, 6, 7])]

def node78Piece101Input : SectorVector := [(0, node78Piece101Input_sector0)]
def node78Piece101Output_sector0_chunk0 : RawPoly ℕ := [(12800/21, [1, 1, 1, 1, 2, 3, 6, 7]), (12800, [1, 1, 1, 3, 6, 10]), (76800/7, [1, 1, 1, 3, 7, 9]), (38400/7, [1, 1, 1, 6, 6, 7]), (25600, [1, 1, 2, 3, 6, 9]), (153600/7, [1, 1, 2, 3, 7, 8]), (76800/7, [1, 1, 2, 5, 6, 7]), (25600, [1, 1, 3, 3, 6, 8]), (153600/7, [1, 1, 3, 3, 7, 7]), (416000/7, [1, 1, 3, 4, 6, 7]), (76800/7, [1, 1, 3, 5, 5, 7]), (25600, [1, 1, 3, 5, 6, 6]), (153600, [1, 1, 3, 17]), (76800, [1, 1, 6, 14]), (460800/7, [1, 1, 7, 13]), (12800, [1, 2, 2, 3, 6, 8]), (76800/7, [1, 2, 2, 3, 7, 7]), (38400/7, [1, 2, 2, 4, 6, 7]), (1203200/21, [1, 2, 3, 3, 6, 7]), (153600/7, [1, 2, 3, 4, 5, 7]), (25600, [1, 2, 3, 4, 6, 6]), (12800, [1, 2, 3, 5, 5, 6]), (153600, [1, 2, 3, 16]), (76800, [1, 2, 6, 13])]

def node78Piece101Output_sector0_chunk1 : RawPoly ℕ := [(460800/7, [1, 2, 7, 12]), (76800/7, [1, 3, 3, 3, 5, 7]), (12800, [1, 3, 3, 3, 6, 6]), (76800/7, [1, 3, 3, 4, 4, 7]), (25600, [1, 3, 3, 4, 5, 6]), (153600, [1, 3, 3, 15]), (12800/3, [1, 3, 4, 4, 4, 6]), (153600, [1, 3, 4, 14]), (153600, [1, 3, 5, 13]), (-659200/3, [1, 3, 6, 12]), (-588800/7, [1, 3, 7, 11]), (153600, [1, 3, 8, 10]), (76800, [1, 3, 9, 9]), (76800, [1, 4, 6, 11]), (460800/7, [1, 4, 7, 10]), (76800, [1, 5, 6, 10]), (460800/7, [1, 5, 7, 9]), (76800, [1, 6, 6, 9]), (608000/7, [1, 6, 7, 8]), (230400/7, [1, 7, 7, 7]), (460800, [1, 21]), (12800/21, [2, 2, 2, 3, 6, 7]), (25600, [2, 3, 6, 11]), (153600/7, [2, 3, 7, 10])]

def node78Piece101Output_sector0_chunk2 : RawPoly ℕ := [(76800/7, [2, 6, 7, 7]), (25600, [3, 3, 6, 10]), (153600/7, [3, 3, 7, 9]), (25600, [3, 4, 6, 9]), (153600/7, [3, 4, 7, 8]), (25600, [3, 5, 6, 8]), (153600/7, [3, 5, 7, 7]), (819200/21, [3, 6, 6, 7]), (153600, [3, 19]), (76800/7, [4, 5, 6, 7]), (76800, [6, 16]), (460800/7, [7, 15])]

def node78Piece101Output_sector0 : RawPoly ℕ := [node78Piece101Output_sector0_chunk0, node78Piece101Output_sector0_chunk1, node78Piece101Output_sector0_chunk2].flatten

def node78Piece101Output : SectorVector := [(0, node78Piece101Output_sector0)]

def node78Piece101UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 6, 7])]

def node78Piece101UnitInput_sector0 : RawPoly ℕ := [node78Piece101UnitInput_sector0_chunk0].flatten

def node78Piece101UnitInput : SectorVector := [(0, node78Piece101UnitInput_sector0)]

def node78Piece101UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 6, 7]), (84, [1, 1, 1, 3, 6, 10]), (72, [1, 1, 1, 3, 7, 9]), (36, [1, 1, 1, 6, 6, 7]), (168, [1, 1, 2, 3, 6, 9]), (144, [1, 1, 2, 3, 7, 8]), (72, [1, 1, 2, 5, 6, 7]), (168, [1, 1, 3, 3, 6, 8]), (144, [1, 1, 3, 3, 7, 7]), (390, [1, 1, 3, 4, 6, 7]), (72, [1, 1, 3, 5, 5, 7]), (168, [1, 1, 3, 5, 6, 6]), (1008, [1, 1, 3, 17]), (504, [1, 1, 6, 14]), (432, [1, 1, 7, 13]), (84, [1, 2, 2, 3, 6, 8]), (72, [1, 2, 2, 3, 7, 7]), (36, [1, 2, 2, 4, 6, 7]), (376, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 5, 7]), (168, [1, 2, 3, 4, 6, 6]), (84, [1, 2, 3, 5, 5, 6]), (1008, [1, 2, 3, 16]), (504, [1, 2, 6, 13])]

def node78Piece101UnitOutput_sector0_chunk1 : RawPoly ℕ := [(432, [1, 2, 7, 12]), (72, [1, 3, 3, 3, 5, 7]), (84, [1, 3, 3, 3, 6, 6]), (72, [1, 3, 3, 4, 4, 7]), (168, [1, 3, 3, 4, 5, 6]), (1008, [1, 3, 3, 15]), (28, [1, 3, 4, 4, 4, 6]), (1008, [1, 3, 4, 14]), (1008, [1, 3, 5, 13]), (-1442, [1, 3, 6, 12]), (-552, [1, 3, 7, 11]), (1008, [1, 3, 8, 10]), (504, [1, 3, 9, 9]), (504, [1, 4, 6, 11]), (432, [1, 4, 7, 10]), (504, [1, 5, 6, 10]), (432, [1, 5, 7, 9]), (504, [1, 6, 6, 9]), (570, [1, 6, 7, 8]), (216, [1, 7, 7, 7]), (3024, [1, 21]), (4, [2, 2, 2, 3, 6, 7]), (168, [2, 3, 6, 11]), (144, [2, 3, 7, 10])]

def node78Piece101UnitOutput_sector0_chunk2 : RawPoly ℕ := [(72, [2, 6, 7, 7]), (168, [3, 3, 6, 10]), (144, [3, 3, 7, 9]), (168, [3, 4, 6, 9]), (144, [3, 4, 7, 8]), (168, [3, 5, 6, 8]), (144, [3, 5, 7, 7]), (256, [3, 6, 6, 7]), (1008, [3, 19]), (72, [4, 5, 6, 7]), (504, [6, 16]), (432, [7, 15])]

def node78Piece101UnitOutput_sector0 : RawPoly ℕ := [node78Piece101UnitOutput_sector0_chunk0, node78Piece101UnitOutput_sector0_chunk1, node78Piece101UnitOutput_sector0_chunk2].flatten

def node78Piece101UnitOutput : SectorVector := [(0, node78Piece101UnitOutput_sector0)]

theorem node78Piece101_check : VectorCertificate (neutralBoundS JR (-2) node78Piece101UnitInput) node78Piece101UnitOutput := by decide +kernel

theorem node78Piece101_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece101Input) = evaluate node78Piece101Output :=
  mode_of_scaled _ _ (3200/21) node78Piece101UnitInput node78Piece101UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece101_check)

def node78Piece102Input_sector0 : RawPoly ℕ := [(-90, [1, 4, 4, 8])]

def node78Piece102Input : SectorVector := [(0, node78Piece102Input_sector0)]
def node78Piece102Output_sector0_chunk0 : RawPoly ℕ := [(-360, [1, 1, 1, 1, 2, 4, 4, 8]), (-8640, [1, 1, 1, 4, 4, 11]), (-8640, [1, 1, 1, 4, 7, 8]), (-17280, [1, 1, 2, 4, 4, 10]), (-17280, [1, 1, 2, 4, 6, 8]), (-17280, [1, 1, 3, 4, 4, 9]), (-17280, [1, 1, 3, 4, 5, 8]), (-26460, [1, 1, 4, 4, 4, 8]), (-17280, [1, 1, 4, 4, 5, 7]), (-8640, [1, 1, 4, 4, 6, 6]), (-138240, [1, 1, 4, 16]), (-34560, [1, 1, 8, 12]), (-8640, [1, 2, 2, 4, 4, 9]), (-8640, [1, 2, 2, 4, 5, 8]), (-37080, [1, 2, 3, 4, 4, 8]), (-17280, [1, 2, 4, 4, 4, 7]), (-17280, [1, 2, 4, 4, 5, 6]), (-138240, [1, 2, 4, 15]), (-34560, [1, 2, 8, 11]), (-2880, [1, 3, 3, 3, 4, 8]), (-8640, [1, 3, 3, 4, 4, 7]), (-17280, [1, 3, 4, 4, 4, 6]), (-8640, [1, 3, 4, 4, 5, 5]), (-138240, [1, 3, 4, 14])]

def node78Piece102Output_sector0_chunk1 : RawPoly ℕ := [(-34560, [1, 3, 8, 10]), (-8640, [1, 4, 4, 4, 4, 5]), (237600, [1, 4, 4, 13]), (-138240, [1, 4, 5, 12]), (-138240, [1, 4, 6, 11]), (-138240, [1, 4, 7, 10]), (-41760, [1, 4, 8, 9]), (-34560, [1, 5, 8, 8]), (-34560, [1, 6, 7, 8]), (-276480, [1, 21]), (-360, [2, 2, 2, 4, 4, 8]), (-17280, [2, 4, 4, 12]), (-17280, [2, 4, 8, 8]), (-17280, [3, 4, 4, 11]), (-17280, [3, 4, 7, 8]), (-17280, [4, 4, 4, 10]), (-17280, [4, 4, 5, 9]), (-29520, [4, 4, 6, 8]), (-8640, [4, 4, 7, 7]), (-8640, [4, 5, 5, 8]), (-138240, [4, 18]), (-34560, [8, 14])]

def node78Piece102Output_sector0 : RawPoly ℕ := [node78Piece102Output_sector0_chunk0, node78Piece102Output_sector0_chunk1].flatten

def node78Piece102Output : SectorVector := [(0, node78Piece102Output_sector0)]

def node78Piece102UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 4, 8])]

def node78Piece102UnitInput_sector0 : RawPoly ℕ := [node78Piece102UnitInput_sector0_chunk0].flatten

def node78Piece102UnitInput : SectorVector := [(0, node78Piece102UnitInput_sector0)]

def node78Piece102UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 4, 4, 8]), (96, [1, 1, 1, 4, 4, 11]), (96, [1, 1, 1, 4, 7, 8]), (192, [1, 1, 2, 4, 4, 10]), (192, [1, 1, 2, 4, 6, 8]), (192, [1, 1, 3, 4, 4, 9]), (192, [1, 1, 3, 4, 5, 8]), (294, [1, 1, 4, 4, 4, 8]), (192, [1, 1, 4, 4, 5, 7]), (96, [1, 1, 4, 4, 6, 6]), (1536, [1, 1, 4, 16]), (384, [1, 1, 8, 12]), (96, [1, 2, 2, 4, 4, 9]), (96, [1, 2, 2, 4, 5, 8]), (412, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 4, 4, 4, 7]), (192, [1, 2, 4, 4, 5, 6]), (1536, [1, 2, 4, 15]), (384, [1, 2, 8, 11]), (32, [1, 3, 3, 3, 4, 8]), (96, [1, 3, 3, 4, 4, 7]), (192, [1, 3, 4, 4, 4, 6]), (96, [1, 3, 4, 4, 5, 5]), (1536, [1, 3, 4, 14])]

def node78Piece102UnitOutput_sector0_chunk1 : RawPoly ℕ := [(384, [1, 3, 8, 10]), (96, [1, 4, 4, 4, 4, 5]), (-2640, [1, 4, 4, 13]), (1536, [1, 4, 5, 12]), (1536, [1, 4, 6, 11]), (1536, [1, 4, 7, 10]), (464, [1, 4, 8, 9]), (384, [1, 5, 8, 8]), (384, [1, 6, 7, 8]), (3072, [1, 21]), (4, [2, 2, 2, 4, 4, 8]), (192, [2, 4, 4, 12]), (192, [2, 4, 8, 8]), (192, [3, 4, 4, 11]), (192, [3, 4, 7, 8]), (192, [4, 4, 4, 10]), (192, [4, 4, 5, 9]), (328, [4, 4, 6, 8]), (96, [4, 4, 7, 7]), (96, [4, 5, 5, 8]), (1536, [4, 18]), (384, [8, 14])]

def node78Piece102UnitOutput_sector0 : RawPoly ℕ := [node78Piece102UnitOutput_sector0_chunk0, node78Piece102UnitOutput_sector0_chunk1].flatten

def node78Piece102UnitOutput : SectorVector := [(0, node78Piece102UnitOutput_sector0)]

theorem node78Piece102_check : VectorCertificate (neutralBoundS JR (-2) node78Piece102UnitInput) node78Piece102UnitOutput := by decide +kernel

theorem node78Piece102_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece102Input) = evaluate node78Piece102Output :=
  mode_of_scaled _ _ (-90) node78Piece102UnitInput node78Piece102UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece102_check)

def node78Piece103Input_sector0 : RawPoly ℕ := [(-288/7, [1, 4, 5, 7])]

def node78Piece103Input : SectorVector := [(0, node78Piece103Input_sector0)]
def node78Piece103Output_sector0_chunk0 : RawPoly ℕ := [(-1152/7, [1, 1, 1, 1, 2, 4, 5, 7]), (-3456, [1, 1, 1, 4, 5, 10]), (-17280/7, [1, 1, 1, 4, 7, 8]), (-13824/7, [1, 1, 1, 5, 7, 7]), (-6912, [1, 1, 2, 4, 5, 9]), (-34560/7, [1, 1, 2, 4, 7, 7]), (-27648/7, [1, 1, 2, 5, 6, 7]), (-6912, [1, 1, 3, 4, 5, 8]), (-34560/7, [1, 1, 3, 4, 6, 7]), (-27648/7, [1, 1, 3, 5, 5, 7]), (-98496/7, [1, 1, 4, 4, 5, 7]), (-6912, [1, 1, 4, 5, 5, 6]), (-34560, [1, 1, 4, 16]), (-27648, [1, 1, 5, 15]), (-138240/7, [1, 1, 7, 13]), (-3456, [1, 2, 2, 4, 5, 8]), (-17280/7, [1, 2, 2, 4, 6, 7]), (-13824/7, [1, 2, 2, 5, 5, 7]), (-118656/7, [1, 2, 3, 4, 5, 7]), (-17280/7, [1, 2, 4, 4, 4, 7]), (-6912, [1, 2, 4, 4, 5, 6]), (-3456, [1, 2, 4, 5, 5, 5]), (-34560, [1, 2, 4, 15]), (-27648, [1, 2, 5, 14])]

def node78Piece103Output_sector0_chunk1 : RawPoly ℕ := [(-138240/7, [1, 2, 7, 12]), (-4608/7, [1, 3, 3, 3, 5, 7]), (-17280/7, [1, 3, 3, 4, 4, 7]), (-3456, [1, 3, 3, 4, 5, 6]), (-6912, [1, 3, 4, 4, 5, 5]), (-34560, [1, 3, 4, 14]), (-27648, [1, 3, 5, 13]), (-138240/7, [1, 3, 7, 11]), (-1152, [1, 4, 4, 4, 4, 5]), (-34560, [1, 4, 4, 13]), (59328, [1, 4, 5, 12]), (-34560, [1, 4, 6, 11]), (-17280/7, [1, 4, 7, 10]), (-34560, [1, 4, 8, 9]), (-27648, [1, 5, 5, 11]), (-27648, [1, 5, 6, 10]), (-122112/7, [1, 5, 7, 9]), (-13824, [1, 5, 8, 8]), (-138240/7, [1, 6, 7, 8]), (-69120/7, [1, 7, 7, 7]), (-138240, [1, 21]), (-1152/7, [2, 2, 2, 4, 5, 7]), (-6912, [2, 4, 5, 11]), (-34560/7, [2, 4, 7, 9])]

def node78Piece103Output_sector0_chunk2 : RawPoly ℕ := [(-27648/7, [2, 5, 7, 8]), (-6912, [3, 4, 5, 10]), (-34560/7, [3, 4, 7, 8]), (-27648/7, [3, 5, 7, 7]), (-6912, [4, 4, 5, 9]), (-34560/7, [4, 4, 7, 7]), (-6912, [4, 5, 5, 8]), (-94464/7, [4, 5, 6, 7]), (-34560, [4, 18]), (-13824/7, [5, 5, 5, 7]), (-27648, [5, 17]), (-138240/7, [7, 15])]

def node78Piece103Output_sector0 : RawPoly ℕ := [node78Piece103Output_sector0_chunk0, node78Piece103Output_sector0_chunk1, node78Piece103Output_sector0_chunk2].flatten

def node78Piece103Output : SectorVector := [(0, node78Piece103Output_sector0)]

def node78Piece103UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 5, 7])]

def node78Piece103UnitInput_sector0 : RawPoly ℕ := [node78Piece103UnitInput_sector0_chunk0].flatten

def node78Piece103UnitInput : SectorVector := [(0, node78Piece103UnitInput_sector0)]

def node78Piece103UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 4, 5, 7]), (84, [1, 1, 1, 4, 5, 10]), (60, [1, 1, 1, 4, 7, 8]), (48, [1, 1, 1, 5, 7, 7]), (168, [1, 1, 2, 4, 5, 9]), (120, [1, 1, 2, 4, 7, 7]), (96, [1, 1, 2, 5, 6, 7]), (168, [1, 1, 3, 4, 5, 8]), (120, [1, 1, 3, 4, 6, 7]), (96, [1, 1, 3, 5, 5, 7]), (342, [1, 1, 4, 4, 5, 7]), (168, [1, 1, 4, 5, 5, 6]), (840, [1, 1, 4, 16]), (672, [1, 1, 5, 15]), (480, [1, 1, 7, 13]), (84, [1, 2, 2, 4, 5, 8]), (60, [1, 2, 2, 4, 6, 7]), (48, [1, 2, 2, 5, 5, 7]), (412, [1, 2, 3, 4, 5, 7]), (60, [1, 2, 4, 4, 4, 7]), (168, [1, 2, 4, 4, 5, 6]), (84, [1, 2, 4, 5, 5, 5]), (840, [1, 2, 4, 15]), (672, [1, 2, 5, 14])]

def node78Piece103UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [1, 2, 7, 12]), (16, [1, 3, 3, 3, 5, 7]), (60, [1, 3, 3, 4, 4, 7]), (84, [1, 3, 3, 4, 5, 6]), (168, [1, 3, 4, 4, 5, 5]), (840, [1, 3, 4, 14]), (672, [1, 3, 5, 13]), (480, [1, 3, 7, 11]), (28, [1, 4, 4, 4, 4, 5]), (840, [1, 4, 4, 13]), (-1442, [1, 4, 5, 12]), (840, [1, 4, 6, 11]), (60, [1, 4, 7, 10]), (840, [1, 4, 8, 9]), (672, [1, 5, 5, 11]), (672, [1, 5, 6, 10]), (424, [1, 5, 7, 9]), (336, [1, 5, 8, 8]), (480, [1, 6, 7, 8]), (240, [1, 7, 7, 7]), (3360, [1, 21]), (4, [2, 2, 2, 4, 5, 7]), (168, [2, 4, 5, 11]), (120, [2, 4, 7, 9])]

def node78Piece103UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [2, 5, 7, 8]), (168, [3, 4, 5, 10]), (120, [3, 4, 7, 8]), (96, [3, 5, 7, 7]), (168, [4, 4, 5, 9]), (120, [4, 4, 7, 7]), (168, [4, 5, 5, 8]), (328, [4, 5, 6, 7]), (840, [4, 18]), (48, [5, 5, 5, 7]), (672, [5, 17]), (480, [7, 15])]

def node78Piece103UnitOutput_sector0 : RawPoly ℕ := [node78Piece103UnitOutput_sector0_chunk0, node78Piece103UnitOutput_sector0_chunk1, node78Piece103UnitOutput_sector0_chunk2].flatten

def node78Piece103UnitOutput : SectorVector := [(0, node78Piece103UnitOutput_sector0)]

theorem node78Piece103_check : VectorCertificate (neutralBoundS JR (-2) node78Piece103UnitInput) node78Piece103UnitOutput := by decide +kernel

theorem node78Piece103_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece103Input) = evaluate node78Piece103Output :=
  mode_of_scaled _ _ (-288/7) node78Piece103UnitInput node78Piece103UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece103_check)

def node78Piece104Input_sector0 : RawPoly ℕ := [(-100/3, [1, 4, 6, 6])]

def node78Piece104Input : SectorVector := [(0, node78Piece104Input_sector0)]
def node78Piece104Output_sector0_chunk0 : RawPoly ℕ := [(-400/3, [1, 1, 1, 1, 2, 4, 6, 6]), (-4800, [1, 1, 1, 4, 6, 9]), (-1600, [1, 1, 1, 6, 6, 7]), (-9600, [1, 1, 2, 4, 6, 8]), (-3200, [1, 1, 2, 6, 6, 6]), (-9600, [1, 1, 3, 4, 6, 7]), (-3200, [1, 1, 3, 5, 6, 6]), (-11400, [1, 1, 4, 4, 6, 6]), (-4800, [1, 1, 4, 5, 5, 6]), (-28800, [1, 1, 4, 16]), (-38400, [1, 1, 6, 14]), (-4800, [1, 2, 2, 4, 6, 7]), (-1600, [1, 2, 2, 5, 6, 6]), (-41200/3, [1, 2, 3, 4, 6, 6]), (-9600, [1, 2, 4, 4, 5, 6]), (-28800, [1, 2, 4, 15]), (-38400, [1, 2, 6, 13]), (-1600/3, [1, 3, 3, 3, 6, 6]), (-4800, [1, 3, 3, 4, 5, 6]), (-4800, [1, 3, 4, 4, 4, 6]), (-28800, [1, 3, 4, 14]), (-38400, [1, 3, 6, 12]), (-28800, [1, 4, 4, 13]), (-28800, [1, 4, 5, 12])]

def node78Piece104Output_sector0_chunk1 : RawPoly ℕ := [(65600, [1, 4, 6, 11]), (-28800, [1, 4, 7, 10]), (-28800, [1, 4, 8, 9]), (-38400, [1, 5, 6, 10]), (-42400/3, [1, 6, 6, 9]), (-38400, [1, 6, 7, 8]), (-115200, [1, 21]), (-400/3, [2, 2, 2, 4, 6, 6]), (-9600, [2, 4, 6, 10]), (-3200, [2, 6, 6, 8]), (-9600, [3, 4, 6, 9]), (-3200, [3, 6, 6, 7]), (-9600, [4, 4, 6, 8]), (-9600, [4, 5, 6, 7]), (-18400/3, [4, 6, 6, 6]), (-28800, [4, 18]), (-1600, [5, 5, 6, 6]), (-38400, [6, 16])]

def node78Piece104Output_sector0 : RawPoly ℕ := [node78Piece104Output_sector0_chunk0, node78Piece104Output_sector0_chunk1].flatten

def node78Piece104Output : SectorVector := [(0, node78Piece104Output_sector0)]

def node78Piece104UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 6, 6])]

def node78Piece104UnitInput_sector0 : RawPoly ℕ := [node78Piece104UnitInput_sector0_chunk0].flatten

def node78Piece104UnitInput : SectorVector := [(0, node78Piece104UnitInput_sector0)]

def node78Piece104UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 4, 6, 6]), (144, [1, 1, 1, 4, 6, 9]), (48, [1, 1, 1, 6, 6, 7]), (288, [1, 1, 2, 4, 6, 8]), (96, [1, 1, 2, 6, 6, 6]), (288, [1, 1, 3, 4, 6, 7]), (96, [1, 1, 3, 5, 6, 6]), (342, [1, 1, 4, 4, 6, 6]), (144, [1, 1, 4, 5, 5, 6]), (864, [1, 1, 4, 16]), (1152, [1, 1, 6, 14]), (144, [1, 2, 2, 4, 6, 7]), (48, [1, 2, 2, 5, 6, 6]), (412, [1, 2, 3, 4, 6, 6]), (288, [1, 2, 4, 4, 5, 6]), (864, [1, 2, 4, 15]), (1152, [1, 2, 6, 13]), (16, [1, 3, 3, 3, 6, 6]), (144, [1, 3, 3, 4, 5, 6]), (144, [1, 3, 4, 4, 4, 6]), (864, [1, 3, 4, 14]), (1152, [1, 3, 6, 12]), (864, [1, 4, 4, 13]), (864, [1, 4, 5, 12])]

def node78Piece104UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-1968, [1, 4, 6, 11]), (864, [1, 4, 7, 10]), (864, [1, 4, 8, 9]), (1152, [1, 5, 6, 10]), (424, [1, 6, 6, 9]), (1152, [1, 6, 7, 8]), (3456, [1, 21]), (4, [2, 2, 2, 4, 6, 6]), (288, [2, 4, 6, 10]), (96, [2, 6, 6, 8]), (288, [3, 4, 6, 9]), (96, [3, 6, 6, 7]), (288, [4, 4, 6, 8]), (288, [4, 5, 6, 7]), (184, [4, 6, 6, 6]), (864, [4, 18]), (48, [5, 5, 6, 6]), (1152, [6, 16])]

def node78Piece104UnitOutput_sector0 : RawPoly ℕ := [node78Piece104UnitOutput_sector0_chunk0, node78Piece104UnitOutput_sector0_chunk1].flatten

def node78Piece104UnitOutput : SectorVector := [(0, node78Piece104UnitOutput_sector0)]

theorem node78Piece104_check : VectorCertificate (neutralBoundS JR (-2) node78Piece104UnitInput) node78Piece104UnitOutput := by decide +kernel

theorem node78Piece104_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece104Input) = evaluate node78Piece104Output :=
  mode_of_scaled _ _ (-100/3) node78Piece104UnitInput node78Piece104UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece104_check)

def node78Piece105Input_sector0 : RawPoly ℕ := [(192/5, [1, 5, 5, 6])]

def node78Piece105Input : SectorVector := [(0, node78Piece105Input_sector0)]
def node78Piece105Output_sector0_chunk0 : RawPoly ℕ := [(768/5, [1, 1, 1, 1, 2, 5, 5, 6]), (13824/5, [1, 1, 1, 5, 5, 9]), (4608, [1, 1, 1, 5, 6, 8]), (27648/5, [1, 1, 2, 5, 5, 8]), (9216, [1, 1, 2, 5, 6, 7]), (27648/5, [1, 1, 3, 5, 5, 7]), (9216, [1, 1, 3, 5, 6, 6]), (14976, [1, 1, 4, 5, 5, 6]), (13824/5, [1, 1, 5, 5, 5, 5]), (55296, [1, 1, 5, 15]), (23040, [1, 1, 6, 14]), (13824/5, [1, 2, 2, 5, 5, 7]), (4608, [1, 2, 2, 5, 6, 6]), (79104/5, [1, 2, 3, 5, 5, 6]), (4608, [1, 2, 4, 4, 5, 6]), (27648/5, [1, 2, 4, 5, 5, 5]), (55296, [1, 2, 5, 14]), (23040, [1, 2, 6, 13]), (4608, [1, 3, 3, 4, 5, 6]), (13824/5, [1, 3, 3, 5, 5, 5]), (13824/5, [1, 3, 4, 4, 5, 5]), (55296, [1, 3, 5, 13]), (23040, [1, 3, 6, 12]), (55296, [1, 4, 5, 12])]

def node78Piece105Output_sector0_chunk1 : RawPoly ℕ := [(23040, [1, 4, 6, 11]), (-105984/5, [1, 5, 5, 11]), (-18432, [1, 5, 6, 10]), (55296, [1, 5, 7, 9]), (27648, [1, 5, 8, 8]), (23040, [1, 6, 6, 9]), (23040, [1, 6, 7, 8]), (138240, [1, 21]), (768/5, [2, 2, 2, 5, 5, 6]), (27648/5, [2, 5, 5, 10]), (9216, [2, 5, 6, 9]), (27648/5, [3, 5, 5, 9]), (9216, [3, 5, 6, 8]), (27648/5, [4, 5, 5, 8]), (9216, [4, 5, 6, 7]), (27648/5, [5, 5, 5, 7]), (49152/5, [5, 5, 6, 6]), (55296, [5, 17]), (23040, [6, 16])]

def node78Piece105Output_sector0 : RawPoly ℕ := [node78Piece105Output_sector0_chunk0, node78Piece105Output_sector0_chunk1].flatten

def node78Piece105Output : SectorVector := [(0, node78Piece105Output_sector0)]

def node78Piece105UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 5, 5, 6])]

def node78Piece105UnitInput_sector0 : RawPoly ℕ := [node78Piece105UnitInput_sector0_chunk0].flatten

def node78Piece105UnitInput : SectorVector := [(0, node78Piece105UnitInput_sector0)]

def node78Piece105UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 5, 5, 6]), (72, [1, 1, 1, 5, 5, 9]), (120, [1, 1, 1, 5, 6, 8]), (144, [1, 1, 2, 5, 5, 8]), (240, [1, 1, 2, 5, 6, 7]), (144, [1, 1, 3, 5, 5, 7]), (240, [1, 1, 3, 5, 6, 6]), (390, [1, 1, 4, 5, 5, 6]), (72, [1, 1, 5, 5, 5, 5]), (1440, [1, 1, 5, 15]), (600, [1, 1, 6, 14]), (72, [1, 2, 2, 5, 5, 7]), (120, [1, 2, 2, 5, 6, 6]), (412, [1, 2, 3, 5, 5, 6]), (120, [1, 2, 4, 4, 5, 6]), (144, [1, 2, 4, 5, 5, 5]), (1440, [1, 2, 5, 14]), (600, [1, 2, 6, 13]), (120, [1, 3, 3, 4, 5, 6]), (72, [1, 3, 3, 5, 5, 5]), (72, [1, 3, 4, 4, 5, 5]), (1440, [1, 3, 5, 13]), (600, [1, 3, 6, 12]), (1440, [1, 4, 5, 12])]

def node78Piece105UnitOutput_sector0_chunk1 : RawPoly ℕ := [(600, [1, 4, 6, 11]), (-552, [1, 5, 5, 11]), (-480, [1, 5, 6, 10]), (1440, [1, 5, 7, 9]), (720, [1, 5, 8, 8]), (600, [1, 6, 6, 9]), (600, [1, 6, 7, 8]), (3600, [1, 21]), (4, [2, 2, 2, 5, 5, 6]), (144, [2, 5, 5, 10]), (240, [2, 5, 6, 9]), (144, [3, 5, 5, 9]), (240, [3, 5, 6, 8]), (144, [4, 5, 5, 8]), (240, [4, 5, 6, 7]), (144, [5, 5, 5, 7]), (256, [5, 5, 6, 6]), (1440, [5, 17]), (600, [6, 16])]

def node78Piece105UnitOutput_sector0 : RawPoly ℕ := [node78Piece105UnitOutput_sector0_chunk0, node78Piece105UnitOutput_sector0_chunk1].flatten

def node78Piece105UnitOutput : SectorVector := [(0, node78Piece105UnitOutput_sector0)]

theorem node78Piece105_check : VectorCertificate (neutralBoundS JR (-2) node78Piece105UnitInput) node78Piece105UnitOutput := by decide +kernel

theorem node78Piece105_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece105Input) = evaluate node78Piece105Output :=
  mode_of_scaled _ _ (192/5) node78Piece105UnitInput node78Piece105UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece105_check)

def node78Piece106Input_sector0 : RawPoly ℕ := [(30, [1, 16])]

def node78Piece106Input : SectorVector := [(0, node78Piece106Input_sector0)]
def node78Piece106Output_sector0_chunk0 : RawPoly ℕ := [(120, [1, 1, 1, 1, 2, 16]), (5760, [1, 1, 1, 19]), (11520, [1, 1, 2, 18]), (11520, [1, 1, 3, 17]), (11700, [1, 1, 4, 16]), (11520, [1, 1, 5, 15]), (11520, [1, 1, 6, 14]), (11520, [1, 1, 7, 13]), (11520, [1, 1, 8, 12]), (11520, [1, 1, 9, 11]), (5760, [1, 1, 10, 10]), (5760, [1, 2, 2, 17]), (12360, [1, 2, 3, 16]), (11520, [1, 2, 4, 15]), (11520, [1, 2, 5, 14]), (11520, [1, 2, 6, 13]), (11520, [1, 2, 7, 12]), (11520, [1, 2, 8, 11]), (11520, [1, 2, 9, 10]), (5760, [1, 3, 3, 15]), (11520, [1, 3, 4, 14]), (11520, [1, 3, 5, 13]), (11520, [1, 3, 6, 12]), (11520, [1, 3, 7, 11])]

def node78Piece106Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 3, 8, 10]), (5760, [1, 3, 9, 9]), (5760, [1, 4, 4, 13]), (11520, [1, 4, 5, 12]), (11520, [1, 4, 6, 11]), (11520, [1, 4, 7, 10]), (11520, [1, 4, 8, 9]), (5760, [1, 5, 5, 11]), (11520, [1, 5, 6, 10]), (11520, [1, 5, 7, 9]), (5760, [1, 5, 8, 8]), (5760, [1, 6, 6, 9]), (11520, [1, 6, 7, 8]), (1920, [1, 7, 7, 7]), (-807360, [1, 21]), (120, [2, 2, 2, 16]), (11520, [2, 20]), (11520, [3, 19]), (11520, [4, 18]), (11520, [5, 17]), (9840, [6, 16]), (11520, [7, 15]), (11520, [8, 14]), (11520, [9, 13])]

def node78Piece106Output_sector0_chunk2 : RawPoly ℕ := [(11520, [10, 12]), (5760, [11, 11])]

def node78Piece106Output_sector0 : RawPoly ℕ := [node78Piece106Output_sector0_chunk0, node78Piece106Output_sector0_chunk1, node78Piece106Output_sector0_chunk2].flatten

def node78Piece106Output : SectorVector := [(0, node78Piece106Output_sector0)]

def node78Piece106UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 16])]

def node78Piece106UnitInput_sector0 : RawPoly ℕ := [node78Piece106UnitInput_sector0_chunk0].flatten

def node78Piece106UnitInput : SectorVector := [(0, node78Piece106UnitInput_sector0)]

def node78Piece106UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 16]), (192, [1, 1, 1, 19]), (384, [1, 1, 2, 18]), (384, [1, 1, 3, 17]), (390, [1, 1, 4, 16]), (384, [1, 1, 5, 15]), (384, [1, 1, 6, 14]), (384, [1, 1, 7, 13]), (384, [1, 1, 8, 12]), (384, [1, 1, 9, 11]), (192, [1, 1, 10, 10]), (192, [1, 2, 2, 17]), (412, [1, 2, 3, 16]), (384, [1, 2, 4, 15]), (384, [1, 2, 5, 14]), (384, [1, 2, 6, 13]), (384, [1, 2, 7, 12]), (384, [1, 2, 8, 11]), (384, [1, 2, 9, 10]), (192, [1, 3, 3, 15]), (384, [1, 3, 4, 14]), (384, [1, 3, 5, 13]), (384, [1, 3, 6, 12]), (384, [1, 3, 7, 11])]

def node78Piece106UnitOutput_sector0_chunk1 : RawPoly ℕ := [(384, [1, 3, 8, 10]), (192, [1, 3, 9, 9]), (192, [1, 4, 4, 13]), (384, [1, 4, 5, 12]), (384, [1, 4, 6, 11]), (384, [1, 4, 7, 10]), (384, [1, 4, 8, 9]), (192, [1, 5, 5, 11]), (384, [1, 5, 6, 10]), (384, [1, 5, 7, 9]), (192, [1, 5, 8, 8]), (192, [1, 6, 6, 9]), (384, [1, 6, 7, 8]), (64, [1, 7, 7, 7]), (-26912, [1, 21]), (4, [2, 2, 2, 16]), (384, [2, 20]), (384, [3, 19]), (384, [4, 18]), (384, [5, 17]), (328, [6, 16]), (384, [7, 15]), (384, [8, 14]), (384, [9, 13])]

def node78Piece106UnitOutput_sector0_chunk2 : RawPoly ℕ := [(384, [10, 12]), (192, [11, 11])]

def node78Piece106UnitOutput_sector0 : RawPoly ℕ := [node78Piece106UnitOutput_sector0_chunk0, node78Piece106UnitOutput_sector0_chunk1, node78Piece106UnitOutput_sector0_chunk2].flatten

def node78Piece106UnitOutput : SectorVector := [(0, node78Piece106UnitOutput_sector0)]

theorem node78Piece106_check : VectorCertificate (neutralBoundS JR (-2) node78Piece106UnitInput) node78Piece106UnitOutput := by decide +kernel

theorem node78Piece106_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece106Input) = evaluate node78Piece106Output :=
  mode_of_scaled _ _ (30) node78Piece106UnitInput node78Piece106UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece106_check)

def node78Piece107Input_sector0 : RawPoly ℕ := [(-484/63, [2, 2, 2, 2, 2, 2, 2, 3])]

def node78Piece107Input : SectorVector := [(0, node78Piece107Input_sector0)]
def node78Piece107Output_sector0 : RawPoly ℕ := [(-1936/63, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-1936/7, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-3872/3, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-3872/7, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (-64856/21, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-3872/3, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-7744, [1, 2, 2, 2, 2, 2, 2, 9]), (-15488, [1, 2, 2, 2, 2, 2, 3, 8]), (-1936/7, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (-100672/63, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (-91960/21, [2, 2, 2, 2, 2, 2, 2, 8]), (-38720/3, [2, 2, 2, 2, 2, 2, 3, 7]), (-7744, [2, 2, 2, 2, 2, 2, 4, 6]), (-3872, [2, 2, 2, 2, 2, 2, 5, 5]), (-15488, [2, 2, 2, 2, 2, 3, 3, 6]), (-15488, [2, 2, 2, 2, 2, 3, 4, 5]), (-46464, [2, 2, 2, 2, 2, 12]), (-154880/3, [2, 2, 2, 2, 3, 11])]

def node78Piece107Output : SectorVector := [(0, node78Piece107Output_sector0)]

def node78Piece107UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 2, 2, 3])]

def node78Piece107UnitInput_sector0 : RawPoly ℕ := [node78Piece107UnitInput_sector0_chunk0].flatten

def node78Piece107UnitInput : SectorVector := [(0, node78Piece107UnitInput_sector0)]

def node78Piece107UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (36, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (168, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (72, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (402, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (168, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (1008, [1, 2, 2, 2, 2, 2, 2, 9]), (2016, [1, 2, 2, 2, 2, 2, 3, 8]), (36, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (208, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (570, [2, 2, 2, 2, 2, 2, 2, 8]), (1680, [2, 2, 2, 2, 2, 2, 3, 7]), (1008, [2, 2, 2, 2, 2, 2, 4, 6]), (504, [2, 2, 2, 2, 2, 2, 5, 5]), (2016, [2, 2, 2, 2, 2, 3, 3, 6]), (2016, [2, 2, 2, 2, 2, 3, 4, 5]), (6048, [2, 2, 2, 2, 2, 12]), (6720, [2, 2, 2, 2, 3, 11])]

def node78Piece107UnitOutput_sector0 : RawPoly ℕ := [node78Piece107UnitOutput_sector0_chunk0].flatten

def node78Piece107UnitOutput : SectorVector := [(0, node78Piece107UnitOutput_sector0)]

theorem node78Piece107_check : VectorCertificate (neutralBoundS JR (-2) node78Piece107UnitInput) node78Piece107UnitOutput := by decide +kernel

theorem node78Piece107_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece107Input) = evaluate node78Piece107Output :=
  mode_of_scaled _ _ (-484/63) node78Piece107UnitInput node78Piece107UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece107_check)

def node78Piece108Input_sector0 : RawPoly ℕ := [(-320/7, [2, 2, 2, 2, 2, 7])]

def node78Piece108Input : SectorVector := [(0, node78Piece108Input_sector0)]
def node78Piece108Output_sector0_chunk0 : RawPoly ℕ := [(-1280/7, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (-3840, [1, 1, 2, 2, 2, 2, 2, 10]), (-38400/7, [1, 1, 2, 2, 2, 2, 5, 7]), (-7680, [1, 2, 2, 2, 2, 2, 2, 9]), (-7680, [1, 2, 2, 2, 2, 2, 3, 8]), (-128640/7, [1, 2, 2, 2, 2, 2, 4, 7]), (-7680, [1, 2, 2, 2, 2, 2, 5, 6]), (-38400/7, [1, 2, 2, 2, 2, 3, 3, 7]), (-76800, [1, 2, 2, 2, 2, 13]), (-307200/7, [1, 2, 2, 2, 7, 8]), (-3840, [2, 2, 2, 2, 2, 2, 2, 8]), (-93440/7, [2, 2, 2, 2, 2, 2, 3, 7]), (-7680, [2, 2, 2, 2, 2, 2, 4, 6]), (-3840, [2, 2, 2, 2, 2, 2, 5, 5]), (-3840, [2, 2, 2, 2, 2, 3, 3, 6]), (-7680, [2, 2, 2, 2, 2, 3, 4, 5]), (-1280, [2, 2, 2, 2, 2, 4, 4, 4]), (65920, [2, 2, 2, 2, 2, 12]), (-76800, [2, 2, 2, 2, 3, 11]), (-76800, [2, 2, 2, 2, 4, 10]), (-76800, [2, 2, 2, 2, 5, 9]), (-76800, [2, 2, 2, 2, 6, 8]), (-38400, [2, 2, 2, 2, 7, 7]), (-307200/7, [2, 2, 2, 3, 6, 7])]

def node78Piece108Output_sector0_chunk1 : RawPoly ℕ := [(-307200/7, [2, 2, 2, 4, 5, 7]), (-307200, [2, 2, 2, 16]), (-614400/7, [2, 2, 7, 11])]

def node78Piece108Output_sector0 : RawPoly ℕ := [node78Piece108Output_sector0_chunk0, node78Piece108Output_sector0_chunk1].flatten

def node78Piece108Output : SectorVector := [(0, node78Piece108Output_sector0)]

def node78Piece108UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 7])]

def node78Piece108UnitInput_sector0 : RawPoly ℕ := [node78Piece108UnitInput_sector0_chunk0].flatten

def node78Piece108UnitInput : SectorVector := [(0, node78Piece108UnitInput_sector0)]

def node78Piece108UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (84, [1, 1, 2, 2, 2, 2, 2, 10]), (120, [1, 1, 2, 2, 2, 2, 5, 7]), (168, [1, 2, 2, 2, 2, 2, 2, 9]), (168, [1, 2, 2, 2, 2, 2, 3, 8]), (402, [1, 2, 2, 2, 2, 2, 4, 7]), (168, [1, 2, 2, 2, 2, 2, 5, 6]), (120, [1, 2, 2, 2, 2, 3, 3, 7]), (1680, [1, 2, 2, 2, 2, 13]), (960, [1, 2, 2, 2, 7, 8]), (84, [2, 2, 2, 2, 2, 2, 2, 8]), (292, [2, 2, 2, 2, 2, 2, 3, 7]), (168, [2, 2, 2, 2, 2, 2, 4, 6]), (84, [2, 2, 2, 2, 2, 2, 5, 5]), (84, [2, 2, 2, 2, 2, 3, 3, 6]), (168, [2, 2, 2, 2, 2, 3, 4, 5]), (28, [2, 2, 2, 2, 2, 4, 4, 4]), (-1442, [2, 2, 2, 2, 2, 12]), (1680, [2, 2, 2, 2, 3, 11]), (1680, [2, 2, 2, 2, 4, 10]), (1680, [2, 2, 2, 2, 5, 9]), (1680, [2, 2, 2, 2, 6, 8]), (840, [2, 2, 2, 2, 7, 7]), (960, [2, 2, 2, 3, 6, 7])]

def node78Piece108UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [2, 2, 2, 4, 5, 7]), (6720, [2, 2, 2, 16]), (1920, [2, 2, 7, 11])]

def node78Piece108UnitOutput_sector0 : RawPoly ℕ := [node78Piece108UnitOutput_sector0_chunk0, node78Piece108UnitOutput_sector0_chunk1].flatten

def node78Piece108UnitOutput : SectorVector := [(0, node78Piece108UnitOutput_sector0)]

theorem node78Piece108_check : VectorCertificate (neutralBoundS JR (-2) node78Piece108UnitInput) node78Piece108UnitOutput := by decide +kernel

theorem node78Piece108_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece108Input) = evaluate node78Piece108Output :=
  mode_of_scaled _ _ (-320/7) node78Piece108UnitInput node78Piece108UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece108_check)

def node78Piece109Input_sector0 : RawPoly ℕ := [(-800/9, [2, 2, 2, 2, 3, 6])]

def node78Piece109Input : SectorVector := [(0, node78Piece109Input_sector0)]
def node78Piece109Output_sector0_chunk0 : RawPoly ℕ := [(-3200/9, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-6400, [1, 1, 2, 2, 2, 2, 3, 9]), (-3200, [1, 1, 2, 2, 2, 2, 6, 6]), (-25600/3, [1, 1, 2, 2, 2, 3, 5, 6]), (-12800, [1, 2, 2, 2, 2, 2, 3, 8]), (-6400, [1, 2, 2, 2, 2, 2, 5, 6]), (-12800, [1, 2, 2, 2, 2, 3, 3, 7]), (-107200/3, [1, 2, 2, 2, 2, 3, 4, 6]), (-6400, [1, 2, 2, 2, 2, 3, 5, 5]), (-38400, [1, 2, 2, 2, 2, 13]), (-25600/3, [1, 2, 2, 2, 3, 3, 3, 6]), (-102400, [1, 2, 2, 2, 3, 12]), (-51200, [1, 2, 2, 2, 6, 9]), (-51200, [1, 2, 2, 3, 6, 8]), (-6400, [2, 2, 2, 2, 2, 2, 3, 7]), (-3200, [2, 2, 2, 2, 2, 2, 4, 6]), (-224000/9, [2, 2, 2, 2, 2, 3, 3, 6]), (-12800, [2, 2, 2, 2, 2, 3, 4, 5]), (-38400, [2, 2, 2, 2, 2, 12]), (-6400, [2, 2, 2, 2, 3, 3, 3, 5]), (-6400, [2, 2, 2, 2, 3, 3, 4, 4]), (147200/3, [2, 2, 2, 2, 3, 11]), (-38400, [2, 2, 2, 2, 4, 10]), (-38400, [2, 2, 2, 2, 5, 9])]

def node78Piece109Output_sector0_chunk1 : RawPoly ℕ := [(-152000/3, [2, 2, 2, 2, 6, 8]), (-19200, [2, 2, 2, 2, 7, 7]), (-102400, [2, 2, 2, 3, 3, 10]), (-102400, [2, 2, 2, 3, 4, 9]), (-102400, [2, 2, 2, 3, 5, 8]), (-409600/3, [2, 2, 2, 3, 6, 7]), (-51200, [2, 2, 2, 4, 6, 6]), (-25600, [2, 2, 2, 5, 5, 6]), (-307200, [2, 2, 2, 16]), (-51200, [2, 2, 3, 3, 6, 6]), (-51200, [2, 2, 3, 4, 5, 6]), (-307200, [2, 2, 3, 15]), (-153600, [2, 2, 6, 12]), (-204800/3, [2, 3, 6, 11])]

def node78Piece109Output_sector0 : RawPoly ℕ := [node78Piece109Output_sector0_chunk0, node78Piece109Output_sector0_chunk1].flatten

def node78Piece109Output : SectorVector := [(0, node78Piece109Output_sector0)]

def node78Piece109UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 3, 6])]

def node78Piece109UnitInput_sector0 : RawPoly ℕ := [node78Piece109UnitInput_sector0_chunk0].flatten

def node78Piece109UnitInput : SectorVector := [(0, node78Piece109UnitInput_sector0)]

def node78Piece109UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (72, [1, 1, 2, 2, 2, 2, 3, 9]), (36, [1, 1, 2, 2, 2, 2, 6, 6]), (96, [1, 1, 2, 2, 2, 3, 5, 6]), (144, [1, 2, 2, 2, 2, 2, 3, 8]), (72, [1, 2, 2, 2, 2, 2, 5, 6]), (144, [1, 2, 2, 2, 2, 3, 3, 7]), (402, [1, 2, 2, 2, 2, 3, 4, 6]), (72, [1, 2, 2, 2, 2, 3, 5, 5]), (432, [1, 2, 2, 2, 2, 13]), (96, [1, 2, 2, 2, 3, 3, 3, 6]), (1152, [1, 2, 2, 2, 3, 12]), (576, [1, 2, 2, 2, 6, 9]), (576, [1, 2, 2, 3, 6, 8]), (72, [2, 2, 2, 2, 2, 2, 3, 7]), (36, [2, 2, 2, 2, 2, 2, 4, 6]), (280, [2, 2, 2, 2, 2, 3, 3, 6]), (144, [2, 2, 2, 2, 2, 3, 4, 5]), (432, [2, 2, 2, 2, 2, 12]), (72, [2, 2, 2, 2, 3, 3, 3, 5]), (72, [2, 2, 2, 2, 3, 3, 4, 4]), (-552, [2, 2, 2, 2, 3, 11]), (432, [2, 2, 2, 2, 4, 10]), (432, [2, 2, 2, 2, 5, 9])]

def node78Piece109UnitOutput_sector0_chunk1 : RawPoly ℕ := [(570, [2, 2, 2, 2, 6, 8]), (216, [2, 2, 2, 2, 7, 7]), (1152, [2, 2, 2, 3, 3, 10]), (1152, [2, 2, 2, 3, 4, 9]), (1152, [2, 2, 2, 3, 5, 8]), (1536, [2, 2, 2, 3, 6, 7]), (576, [2, 2, 2, 4, 6, 6]), (288, [2, 2, 2, 5, 5, 6]), (3456, [2, 2, 2, 16]), (576, [2, 2, 3, 3, 6, 6]), (576, [2, 2, 3, 4, 5, 6]), (3456, [2, 2, 3, 15]), (1728, [2, 2, 6, 12]), (768, [2, 3, 6, 11])]

def node78Piece109UnitOutput_sector0 : RawPoly ℕ := [node78Piece109UnitOutput_sector0_chunk0, node78Piece109UnitOutput_sector0_chunk1].flatten

def node78Piece109UnitOutput : SectorVector := [(0, node78Piece109UnitOutput_sector0)]

theorem node78Piece109_check : VectorCertificate (neutralBoundS JR (-2) node78Piece109UnitInput) node78Piece109UnitOutput := by decide +kernel

theorem node78Piece109_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece109Input) = evaluate node78Piece109Output :=
  mode_of_scaled _ _ (-800/9) node78Piece109UnitInput node78Piece109UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece109_check)

def node78Piece110Input_sector0 : RawPoly ℕ := [(-124, [2, 2, 2, 2, 4, 5])]

def node78Piece110Input : SectorVector := [(0, node78Piece110Input_sector0)]
def node78Piece110Output_sector0_chunk0 : RawPoly ℕ := [(-496, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (-7440, [1, 1, 2, 2, 2, 2, 4, 8]), (-5952, [1, 1, 2, 2, 2, 2, 5, 7]), (-11904, [1, 1, 2, 2, 2, 4, 5, 5]), (-14880, [1, 2, 2, 2, 2, 2, 4, 7]), (-11904, [1, 2, 2, 2, 2, 2, 5, 6]), (-14880, [1, 2, 2, 2, 2, 3, 4, 6]), (-11904, [1, 2, 2, 2, 2, 3, 5, 5]), (-43896, [1, 2, 2, 2, 2, 4, 4, 5]), (-59520, [1, 2, 2, 2, 2, 13]), (-11904, [1, 2, 2, 2, 3, 3, 4, 5]), (-119040, [1, 2, 2, 2, 4, 11]), (-95232, [1, 2, 2, 2, 5, 10]), (-71424, [1, 2, 2, 4, 5, 8]), (-7440, [2, 2, 2, 2, 2, 2, 4, 6]), (-5952, [2, 2, 2, 2, 2, 2, 5, 5]), (-39184, [2, 2, 2, 2, 2, 3, 4, 5]), (-7440, [2, 2, 2, 2, 2, 4, 4, 4]), (-59520, [2, 2, 2, 2, 2, 12]), (-1984, [2, 2, 2, 2, 3, 3, 3, 5]), (-7440, [2, 2, 2, 2, 3, 3, 4, 4]), (-59520, [2, 2, 2, 2, 3, 11]), (-7440, [2, 2, 2, 2, 4, 10]), (-52576, [2, 2, 2, 2, 5, 9])]

def node78Piece110Output_sector0_chunk1 : RawPoly ℕ := [(-59520, [2, 2, 2, 2, 6, 8]), (-29760, [2, 2, 2, 2, 7, 7]), (-119040, [2, 2, 2, 3, 4, 9]), (-95232, [2, 2, 2, 3, 5, 8]), (-119040, [2, 2, 2, 4, 4, 8]), (-190464, [2, 2, 2, 4, 5, 7]), (-59520, [2, 2, 2, 4, 6, 6]), (-95232, [2, 2, 2, 5, 5, 6]), (-476160, [2, 2, 2, 16]), (-71424, [2, 2, 3, 4, 5, 6]), (-71424, [2, 2, 4, 4, 5, 5]), (-357120, [2, 2, 4, 14]), (-285696, [2, 2, 5, 13]), (-95232, [2, 4, 5, 11])]

def node78Piece110Output_sector0 : RawPoly ℕ := [node78Piece110Output_sector0_chunk0, node78Piece110Output_sector0_chunk1].flatten

def node78Piece110Output : SectorVector := [(0, node78Piece110Output_sector0)]

def node78Piece110UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 4, 5])]

def node78Piece110UnitInput_sector0 : RawPoly ℕ := [node78Piece110UnitInput_sector0_chunk0].flatten

def node78Piece110UnitInput : SectorVector := [(0, node78Piece110UnitInput_sector0)]

def node78Piece110UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (60, [1, 1, 2, 2, 2, 2, 4, 8]), (48, [1, 1, 2, 2, 2, 2, 5, 7]), (96, [1, 1, 2, 2, 2, 4, 5, 5]), (120, [1, 2, 2, 2, 2, 2, 4, 7]), (96, [1, 2, 2, 2, 2, 2, 5, 6]), (120, [1, 2, 2, 2, 2, 3, 4, 6]), (96, [1, 2, 2, 2, 2, 3, 5, 5]), (354, [1, 2, 2, 2, 2, 4, 4, 5]), (480, [1, 2, 2, 2, 2, 13]), (96, [1, 2, 2, 2, 3, 3, 4, 5]), (960, [1, 2, 2, 2, 4, 11]), (768, [1, 2, 2, 2, 5, 10]), (576, [1, 2, 2, 4, 5, 8]), (60, [2, 2, 2, 2, 2, 2, 4, 6]), (48, [2, 2, 2, 2, 2, 2, 5, 5]), (316, [2, 2, 2, 2, 2, 3, 4, 5]), (60, [2, 2, 2, 2, 2, 4, 4, 4]), (480, [2, 2, 2, 2, 2, 12]), (16, [2, 2, 2, 2, 3, 3, 3, 5]), (60, [2, 2, 2, 2, 3, 3, 4, 4]), (480, [2, 2, 2, 2, 3, 11]), (60, [2, 2, 2, 2, 4, 10]), (424, [2, 2, 2, 2, 5, 9])]

def node78Piece110UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [2, 2, 2, 2, 6, 8]), (240, [2, 2, 2, 2, 7, 7]), (960, [2, 2, 2, 3, 4, 9]), (768, [2, 2, 2, 3, 5, 8]), (960, [2, 2, 2, 4, 4, 8]), (1536, [2, 2, 2, 4, 5, 7]), (480, [2, 2, 2, 4, 6, 6]), (768, [2, 2, 2, 5, 5, 6]), (3840, [2, 2, 2, 16]), (576, [2, 2, 3, 4, 5, 6]), (576, [2, 2, 4, 4, 5, 5]), (2880, [2, 2, 4, 14]), (2304, [2, 2, 5, 13]), (768, [2, 4, 5, 11])]

def node78Piece110UnitOutput_sector0 : RawPoly ℕ := [node78Piece110UnitOutput_sector0_chunk0, node78Piece110UnitOutput_sector0_chunk1].flatten

def node78Piece110UnitOutput : SectorVector := [(0, node78Piece110UnitOutput_sector0)]

theorem node78Piece110_check : VectorCertificate (neutralBoundS JR (-2) node78Piece110UnitInput) node78Piece110UnitOutput := by decide +kernel

theorem node78Piece110_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece110Input) = evaluate node78Piece110Output :=
  mode_of_scaled _ _ (-124) node78Piece110UnitInput node78Piece110UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece110_check)

def node78Piece111Input_sector0 : RawPoly ℕ := [(-128/9, [2, 2, 2, 3, 3, 5])]

def node78Piece111Input : SectorVector := [(0, node78Piece111Input_sector0)]
def node78Piece111Output_sector0_chunk0 : RawPoly ℕ := [(-512/9, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (-2560/3, [1, 1, 2, 2, 2, 3, 3, 8]), (-1024, [1, 1, 2, 2, 2, 3, 5, 6]), (-1024, [1, 1, 2, 2, 3, 3, 5, 5]), (-5120/3, [1, 2, 2, 2, 2, 3, 3, 7]), (-2048, [1, 2, 2, 2, 2, 3, 5, 5]), (-5120/3, [1, 2, 2, 2, 3, 3, 3, 6]), (-17152/3, [1, 2, 2, 2, 3, 3, 4, 5]), (-10240, [1, 2, 2, 2, 3, 12]), (-3072, [1, 2, 2, 2, 5, 10]), (-1024, [1, 2, 2, 3, 3, 3, 3, 5]), (-10240, [1, 2, 2, 3, 3, 11]), (-12288, [1, 2, 2, 3, 5, 9]), (-4096, [1, 2, 3, 3, 5, 8]), (-2560/3, [2, 2, 2, 2, 2, 3, 3, 6]), (-1024, [2, 2, 2, 2, 2, 3, 4, 5]), (-34304/9, [2, 2, 2, 2, 3, 3, 3, 5]), (-2560/3, [2, 2, 2, 2, 3, 3, 4, 4]), (-10240, [2, 2, 2, 2, 3, 11]), (-3072, [2, 2, 2, 2, 5, 9]), (-2560/3, [2, 2, 2, 3, 3, 3, 3, 4]), (-2560/3, [2, 2, 2, 3, 3, 10]), (-10240, [2, 2, 2, 3, 4, 9]), (-39424/3, [2, 2, 2, 3, 5, 8])]

def node78Piece111Output_sector0_chunk1 : RawPoly ℕ := [(-10240, [2, 2, 2, 3, 6, 7]), (-3072, [2, 2, 2, 4, 5, 7]), (-3072, [2, 2, 2, 5, 5, 6]), (-15360, [2, 2, 2, 16]), (-10240, [2, 2, 3, 3, 3, 9]), (-10240, [2, 2, 3, 3, 4, 8]), (-18432, [2, 2, 3, 3, 5, 7]), (-5120, [2, 2, 3, 3, 6, 6]), (-12288, [2, 2, 3, 4, 5, 6]), (-6144, [2, 2, 3, 5, 5, 5]), (-61440, [2, 2, 3, 15]), (-18432, [2, 2, 5, 13]), (-4096, [2, 3, 3, 3, 5, 6]), (-4096, [2, 3, 3, 4, 5, 5]), (-20480, [2, 3, 3, 14]), (-24576, [2, 3, 5, 12]), (-8192/3, [3, 3, 5, 11])]

def node78Piece111Output_sector0 : RawPoly ℕ := [node78Piece111Output_sector0_chunk0, node78Piece111Output_sector0_chunk1].flatten

def node78Piece111Output : SectorVector := [(0, node78Piece111Output_sector0)]

def node78Piece111UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 3, 3, 5])]

def node78Piece111UnitInput_sector0 : RawPoly ℕ := [node78Piece111UnitInput_sector0_chunk0].flatten

def node78Piece111UnitInput : SectorVector := [(0, node78Piece111UnitInput_sector0)]

def node78Piece111UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (60, [1, 1, 2, 2, 2, 3, 3, 8]), (72, [1, 1, 2, 2, 2, 3, 5, 6]), (72, [1, 1, 2, 2, 3, 3, 5, 5]), (120, [1, 2, 2, 2, 2, 3, 3, 7]), (144, [1, 2, 2, 2, 2, 3, 5, 5]), (120, [1, 2, 2, 2, 3, 3, 3, 6]), (402, [1, 2, 2, 2, 3, 3, 4, 5]), (720, [1, 2, 2, 2, 3, 12]), (216, [1, 2, 2, 2, 5, 10]), (72, [1, 2, 2, 3, 3, 3, 3, 5]), (720, [1, 2, 2, 3, 3, 11]), (864, [1, 2, 2, 3, 5, 9]), (288, [1, 2, 3, 3, 5, 8]), (60, [2, 2, 2, 2, 2, 3, 3, 6]), (72, [2, 2, 2, 2, 2, 3, 4, 5]), (268, [2, 2, 2, 2, 3, 3, 3, 5]), (60, [2, 2, 2, 2, 3, 3, 4, 4]), (720, [2, 2, 2, 2, 3, 11]), (216, [2, 2, 2, 2, 5, 9]), (60, [2, 2, 2, 3, 3, 3, 3, 4]), (60, [2, 2, 2, 3, 3, 10]), (720, [2, 2, 2, 3, 4, 9]), (924, [2, 2, 2, 3, 5, 8])]

def node78Piece111UnitOutput_sector0_chunk1 : RawPoly ℕ := [(720, [2, 2, 2, 3, 6, 7]), (216, [2, 2, 2, 4, 5, 7]), (216, [2, 2, 2, 5, 5, 6]), (1080, [2, 2, 2, 16]), (720, [2, 2, 3, 3, 3, 9]), (720, [2, 2, 3, 3, 4, 8]), (1296, [2, 2, 3, 3, 5, 7]), (360, [2, 2, 3, 3, 6, 6]), (864, [2, 2, 3, 4, 5, 6]), (432, [2, 2, 3, 5, 5, 5]), (4320, [2, 2, 3, 15]), (1296, [2, 2, 5, 13]), (288, [2, 3, 3, 3, 5, 6]), (288, [2, 3, 3, 4, 5, 5]), (1440, [2, 3, 3, 14]), (1728, [2, 3, 5, 12]), (192, [3, 3, 5, 11])]

def node78Piece111UnitOutput_sector0 : RawPoly ℕ := [node78Piece111UnitOutput_sector0_chunk0, node78Piece111UnitOutput_sector0_chunk1].flatten

def node78Piece111UnitOutput : SectorVector := [(0, node78Piece111UnitOutput_sector0)]

theorem node78Piece111_check : VectorCertificate (neutralBoundS JR (-2) node78Piece111UnitInput) node78Piece111UnitOutput := by decide +kernel

theorem node78Piece111_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece111Input) = evaluate node78Piece111Output :=
  mode_of_scaled _ _ (-128/9) node78Piece111UnitInput node78Piece111UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece111_check)

end VOA.Classification.COne.OrbC2h
