import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch78_3
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

def node78Piece80Input_sector0 : RawPoly ℕ := [(-1440/11, [1, 1, 4, 11])]

def node78Piece80Input : SectorVector := [(0, node78Piece80Input_sector0)]
def node78Piece80Output_sector0_chunk0 : RawPoly ℕ := [(-5760/11, [1, 1, 1, 1, 1, 2, 4, 11]), (-17280, [1, 1, 1, 1, 4, 14]), (-69120/11, [1, 1, 1, 1, 7, 11]), (-34560, [1, 1, 1, 2, 4, 13]), (-138240/11, [1, 1, 1, 2, 6, 11]), (-34560, [1, 1, 1, 3, 4, 12]), (-138240/11, [1, 1, 1, 3, 5, 11]), (-43200, [1, 1, 1, 4, 4, 11]), (-34560, [1, 1, 1, 4, 5, 10]), (-34560, [1, 1, 1, 4, 6, 9]), (-34560, [1, 1, 1, 4, 7, 8]), (-138240, [1, 1, 1, 19]), (-17280, [1, 1, 2, 2, 4, 12]), (-69120/11, [1, 1, 2, 2, 5, 11]), (-593280/11, [1, 1, 2, 3, 4, 11]), (-34560, [1, 1, 2, 4, 4, 10]), (-34560, [1, 1, 2, 4, 5, 9]), (-34560, [1, 1, 2, 4, 6, 8]), (-17280, [1, 1, 2, 4, 7, 7]), (-138240, [1, 1, 2, 18]), (-23040/11, [1, 1, 3, 3, 3, 11]), (-17280, [1, 1, 3, 3, 4, 10]), (-34560, [1, 1, 3, 4, 4, 9]), (-34560, [1, 1, 3, 4, 5, 8])]

def node78Piece80Output_sector0_chunk1 : RawPoly ℕ := [(-34560, [1, 1, 3, 4, 6, 7]), (-138240, [1, 1, 3, 17]), (-17280, [1, 1, 4, 4, 4, 8]), (-34560, [1, 1, 4, 4, 5, 7]), (-17280, [1, 1, 4, 4, 6, 6]), (-17280, [1, 1, 4, 5, 5, 6]), (1097280, [1, 1, 4, 16]), (-138240, [1, 1, 5, 15]), (-138240, [1, 1, 6, 14]), (-138240, [1, 1, 7, 13]), (-138240, [1, 1, 8, 12]), (-610560/11, [1, 1, 9, 11]), (-69120, [1, 1, 10, 10]), (-11520/11, [1, 2, 2, 2, 4, 11]), (-69120, [1, 2, 4, 15]), (-276480/11, [1, 2, 8, 11]), (-69120, [1, 3, 4, 14]), (-276480/11, [1, 3, 7, 11]), (-69120, [1, 4, 4, 13]), (-69120, [1, 4, 5, 12]), (-910080/11, [1, 4, 6, 11]), (-69120, [1, 4, 7, 10]), (-69120, [1, 4, 8, 9]), (-138240/11, [1, 5, 5, 11])]

def node78Piece80Output_sector0_chunk2 : RawPoly ℕ := [(-276480, [1, 21]), (-34560/11, [2, 4, 5, 11]), (-34560/11, [3, 4, 4, 11]), (-34560, [4, 18]), (-138240/11, [11, 11])]

def node78Piece80Output_sector0 : RawPoly ℕ := [node78Piece80Output_sector0_chunk0, node78Piece80Output_sector0_chunk1, node78Piece80Output_sector0_chunk2].flatten

def node78Piece80Output : SectorVector := [(0, node78Piece80Output_sector0)]

def node78Piece80UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 4, 11])]

def node78Piece80UnitInput_sector0 : RawPoly ℕ := [node78Piece80UnitInput_sector0_chunk0].flatten

def node78Piece80UnitInput : SectorVector := [(0, node78Piece80UnitInput_sector0)]

def node78Piece80UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 2, 4, 11]), (132, [1, 1, 1, 1, 4, 14]), (48, [1, 1, 1, 1, 7, 11]), (264, [1, 1, 1, 2, 4, 13]), (96, [1, 1, 1, 2, 6, 11]), (264, [1, 1, 1, 3, 4, 12]), (96, [1, 1, 1, 3, 5, 11]), (330, [1, 1, 1, 4, 4, 11]), (264, [1, 1, 1, 4, 5, 10]), (264, [1, 1, 1, 4, 6, 9]), (264, [1, 1, 1, 4, 7, 8]), (1056, [1, 1, 1, 19]), (132, [1, 1, 2, 2, 4, 12]), (48, [1, 1, 2, 2, 5, 11]), (412, [1, 1, 2, 3, 4, 11]), (264, [1, 1, 2, 4, 4, 10]), (264, [1, 1, 2, 4, 5, 9]), (264, [1, 1, 2, 4, 6, 8]), (132, [1, 1, 2, 4, 7, 7]), (1056, [1, 1, 2, 18]), (16, [1, 1, 3, 3, 3, 11]), (132, [1, 1, 3, 3, 4, 10]), (264, [1, 1, 3, 4, 4, 9]), (264, [1, 1, 3, 4, 5, 8])]

def node78Piece80UnitOutput_sector0_chunk1 : RawPoly ℕ := [(264, [1, 1, 3, 4, 6, 7]), (1056, [1, 1, 3, 17]), (132, [1, 1, 4, 4, 4, 8]), (264, [1, 1, 4, 4, 5, 7]), (132, [1, 1, 4, 4, 6, 6]), (132, [1, 1, 4, 5, 5, 6]), (-8382, [1, 1, 4, 16]), (1056, [1, 1, 5, 15]), (1056, [1, 1, 6, 14]), (1056, [1, 1, 7, 13]), (1056, [1, 1, 8, 12]), (424, [1, 1, 9, 11]), (528, [1, 1, 10, 10]), (8, [1, 2, 2, 2, 4, 11]), (528, [1, 2, 4, 15]), (192, [1, 2, 8, 11]), (528, [1, 3, 4, 14]), (192, [1, 3, 7, 11]), (528, [1, 4, 4, 13]), (528, [1, 4, 5, 12]), (632, [1, 4, 6, 11]), (528, [1, 4, 7, 10]), (528, [1, 4, 8, 9]), (96, [1, 5, 5, 11])]

def node78Piece80UnitOutput_sector0_chunk2 : RawPoly ℕ := [(2112, [1, 21]), (24, [2, 4, 5, 11]), (24, [3, 4, 4, 11]), (264, [4, 18]), (96, [11, 11])]

def node78Piece80UnitOutput_sector0 : RawPoly ℕ := [node78Piece80UnitOutput_sector0_chunk0, node78Piece80UnitOutput_sector0_chunk1, node78Piece80UnitOutput_sector0_chunk2].flatten

def node78Piece80UnitOutput : SectorVector := [(0, node78Piece80UnitOutput_sector0)]

theorem node78Piece80_check : VectorCertificate (neutralBoundS JR (-2) node78Piece80UnitInput) node78Piece80UnitOutput := by decide +kernel

theorem node78Piece80_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece80Input) = evaluate node78Piece80Output :=
  mode_of_scaled _ _ (-1440/11) node78Piece80UnitInput node78Piece80UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece80_check)

def node78Piece81Input_sector0 : RawPoly ℕ := [(192/5, [1, 1, 5, 10])]

def node78Piece81Input : SectorVector := [(0, node78Piece81Input_sector0)]
def node78Piece81Output_sector0_chunk0 : RawPoly ℕ := [(768/5, [1, 1, 1, 1, 1, 2, 5, 10]), (4608, [1, 1, 1, 1, 5, 13]), (2304, [1, 1, 1, 1, 8, 10]), (9216, [1, 1, 1, 2, 5, 12]), (4608, [1, 1, 1, 2, 7, 10]), (9216, [1, 1, 1, 3, 5, 11]), (4608, [1, 1, 1, 3, 6, 10]), (72576/5, [1, 1, 1, 4, 5, 10]), (9216, [1, 1, 1, 5, 5, 9]), (9216, [1, 1, 1, 5, 6, 8]), (4608, [1, 1, 1, 5, 7, 7]), (46080, [1, 1, 1, 19]), (4608, [1, 1, 2, 2, 5, 11]), (2304, [1, 1, 2, 2, 6, 10]), (79104/5, [1, 1, 2, 3, 5, 10]), (2304, [1, 1, 2, 4, 4, 10]), (9216, [1, 1, 2, 4, 5, 9]), (9216, [1, 1, 2, 5, 5, 8]), (9216, [1, 1, 2, 5, 6, 7]), (46080, [1, 1, 2, 18]), (2304, [1, 1, 3, 3, 4, 10]), (4608, [1, 1, 3, 3, 5, 9]), (9216, [1, 1, 3, 4, 5, 8]), (9216, [1, 1, 3, 5, 5, 7])]

def node78Piece81Output_sector0_chunk1 : RawPoly ℕ := [(4608, [1, 1, 3, 5, 6, 6]), (46080, [1, 1, 3, 17]), (4608, [1, 1, 4, 4, 5, 7]), (9216, [1, 1, 4, 5, 5, 6]), (46080, [1, 1, 4, 16]), (1536, [1, 1, 5, 5, 5, 5]), (-233472, [1, 1, 5, 15]), (46080, [1, 1, 6, 14]), (46080, [1, 1, 7, 13]), (46080, [1, 1, 8, 12]), (46080, [1, 1, 9, 11]), (-20736, [1, 1, 10, 10]), (1536/5, [1, 2, 2, 2, 5, 10]), (18432, [1, 2, 5, 14]), (9216, [1, 2, 9, 10]), (18432, [1, 3, 5, 13]), (9216, [1, 3, 8, 10]), (18432, [1, 4, 5, 12]), (9216, [1, 4, 7, 10]), (18432, [1, 5, 5, 11]), (121344/5, [1, 5, 6, 10]), (18432, [1, 5, 7, 9]), (9216, [1, 5, 8, 8]), (92160, [1, 21])]

def node78Piece81Output_sector0_chunk2 : RawPoly ℕ := [(4608/5, [2, 5, 5, 10]), (4608/5, [3, 4, 5, 10]), (9216, [5, 17]), (4608, [10, 12])]

def node78Piece81Output_sector0 : RawPoly ℕ := [node78Piece81Output_sector0_chunk0, node78Piece81Output_sector0_chunk1, node78Piece81Output_sector0_chunk2].flatten

def node78Piece81Output : SectorVector := [(0, node78Piece81Output_sector0)]

def node78Piece81UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 5, 10])]

def node78Piece81UnitInput_sector0 : RawPoly ℕ := [node78Piece81UnitInput_sector0_chunk0].flatten

def node78Piece81UnitInput : SectorVector := [(0, node78Piece81UnitInput_sector0)]

def node78Piece81UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 2, 5, 10]), (120, [1, 1, 1, 1, 5, 13]), (60, [1, 1, 1, 1, 8, 10]), (240, [1, 1, 1, 2, 5, 12]), (120, [1, 1, 1, 2, 7, 10]), (240, [1, 1, 1, 3, 5, 11]), (120, [1, 1, 1, 3, 6, 10]), (378, [1, 1, 1, 4, 5, 10]), (240, [1, 1, 1, 5, 5, 9]), (240, [1, 1, 1, 5, 6, 8]), (120, [1, 1, 1, 5, 7, 7]), (1200, [1, 1, 1, 19]), (120, [1, 1, 2, 2, 5, 11]), (60, [1, 1, 2, 2, 6, 10]), (412, [1, 1, 2, 3, 5, 10]), (60, [1, 1, 2, 4, 4, 10]), (240, [1, 1, 2, 4, 5, 9]), (240, [1, 1, 2, 5, 5, 8]), (240, [1, 1, 2, 5, 6, 7]), (1200, [1, 1, 2, 18]), (60, [1, 1, 3, 3, 4, 10]), (120, [1, 1, 3, 3, 5, 9]), (240, [1, 1, 3, 4, 5, 8]), (240, [1, 1, 3, 5, 5, 7])]

def node78Piece81UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 1, 3, 5, 6, 6]), (1200, [1, 1, 3, 17]), (120, [1, 1, 4, 4, 5, 7]), (240, [1, 1, 4, 5, 5, 6]), (1200, [1, 1, 4, 16]), (40, [1, 1, 5, 5, 5, 5]), (-6080, [1, 1, 5, 15]), (1200, [1, 1, 6, 14]), (1200, [1, 1, 7, 13]), (1200, [1, 1, 8, 12]), (1200, [1, 1, 9, 11]), (-540, [1, 1, 10, 10]), (8, [1, 2, 2, 2, 5, 10]), (480, [1, 2, 5, 14]), (240, [1, 2, 9, 10]), (480, [1, 3, 5, 13]), (240, [1, 3, 8, 10]), (480, [1, 4, 5, 12]), (240, [1, 4, 7, 10]), (480, [1, 5, 5, 11]), (632, [1, 5, 6, 10]), (480, [1, 5, 7, 9]), (240, [1, 5, 8, 8]), (2400, [1, 21])]

def node78Piece81UnitOutput_sector0_chunk2 : RawPoly ℕ := [(24, [2, 5, 5, 10]), (24, [3, 4, 5, 10]), (240, [5, 17]), (120, [10, 12])]

def node78Piece81UnitOutput_sector0 : RawPoly ℕ := [node78Piece81UnitOutput_sector0_chunk0, node78Piece81UnitOutput_sector0_chunk1, node78Piece81UnitOutput_sector0_chunk2].flatten

def node78Piece81UnitOutput : SectorVector := [(0, node78Piece81UnitOutput_sector0)]

theorem node78Piece81_check : VectorCertificate (neutralBoundS JR (-2) node78Piece81UnitInput) node78Piece81UnitOutput := by decide +kernel

theorem node78Piece81_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece81Input) = evaluate node78Piece81Output :=
  mode_of_scaled _ _ (192/5) node78Piece81UnitInput node78Piece81UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece81_check)

def node78Piece82Input_sector0 : RawPoly ℕ := [(-139/3, [1, 2, 2, 2, 2, 2, 2, 4])]

def node78Piece82Input : SectorVector := [(0, node78Piece82Input_sector0)]
def node78Piece82Output_sector0_chunk0 : RawPoly ℕ := [(-556/3, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-2224, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (-6672, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (-4448, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-4448, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-15846, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (-6672, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-53376, [1, 1, 2, 2, 2, 2, 2, 10]), (-66720, [1, 1, 2, 2, 2, 2, 4, 8]), (-2224, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (-37252/3, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-2224/3, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-58936/3, [1, 2, 2, 2, 2, 2, 2, 9]), (-53376, [1, 2, 2, 2, 2, 2, 3, 8]), (-80064, [1, 2, 2, 2, 2, 2, 4, 7]), (-53376, [1, 2, 2, 2, 2, 2, 5, 6]), (-66720, [1, 2, 2, 2, 2, 3, 4, 6]), (-66720, [1, 2, 2, 2, 2, 4, 4, 5]), (-266880, [1, 2, 2, 2, 2, 13]), (-177920, [1, 2, 2, 2, 4, 11]), (-556/3, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (-4448, [2, 2, 2, 2, 2, 2, 2, 8]), (-4448, [2, 2, 2, 2, 2, 2, 3, 7]), (-45592/3, [2, 2, 2, 2, 2, 2, 4, 6])]

def node78Piece82Output_sector0_chunk1 : RawPoly ℕ := [(-2224, [2, 2, 2, 2, 2, 2, 5, 5]), (-13344, [2, 2, 2, 2, 2, 3, 4, 5]), (-6672, [2, 2, 2, 2, 2, 4, 4, 4]), (-53376, [2, 2, 2, 2, 2, 12]), (-66720, [2, 2, 2, 2, 4, 10])]

def node78Piece82Output_sector0 : RawPoly ℕ := [node78Piece82Output_sector0_chunk0, node78Piece82Output_sector0_chunk1].flatten

def node78Piece82Output : SectorVector := [(0, node78Piece82Output_sector0)]

def node78Piece82UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 2, 2, 4])]

def node78Piece82UnitInput_sector0 : RawPoly ℕ := [node78Piece82UnitInput_sector0_chunk0].flatten

def node78Piece82UnitInput : SectorVector := [(0, node78Piece82UnitInput_sector0)]

def node78Piece82UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (48, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (144, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (96, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (96, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (342, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (144, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (1152, [1, 1, 2, 2, 2, 2, 2, 10]), (1440, [1, 1, 2, 2, 2, 2, 4, 8]), (48, [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]), (268, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (16, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (424, [1, 2, 2, 2, 2, 2, 2, 9]), (1152, [1, 2, 2, 2, 2, 2, 3, 8]), (1728, [1, 2, 2, 2, 2, 2, 4, 7]), (1152, [1, 2, 2, 2, 2, 2, 5, 6]), (1440, [1, 2, 2, 2, 2, 3, 4, 6]), (1440, [1, 2, 2, 2, 2, 4, 4, 5]), (5760, [1, 2, 2, 2, 2, 13]), (3840, [1, 2, 2, 2, 4, 11]), (4, [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]), (96, [2, 2, 2, 2, 2, 2, 2, 8]), (96, [2, 2, 2, 2, 2, 2, 3, 7]), (328, [2, 2, 2, 2, 2, 2, 4, 6])]

def node78Piece82UnitOutput_sector0_chunk1 : RawPoly ℕ := [(48, [2, 2, 2, 2, 2, 2, 5, 5]), (288, [2, 2, 2, 2, 2, 3, 4, 5]), (144, [2, 2, 2, 2, 2, 4, 4, 4]), (1152, [2, 2, 2, 2, 2, 12]), (1440, [2, 2, 2, 2, 4, 10])]

def node78Piece82UnitOutput_sector0 : RawPoly ℕ := [node78Piece82UnitOutput_sector0_chunk0, node78Piece82UnitOutput_sector0_chunk1].flatten

def node78Piece82UnitOutput : SectorVector := [(0, node78Piece82UnitOutput_sector0)]

theorem node78Piece82_check : VectorCertificate (neutralBoundS JR (-2) node78Piece82UnitInput) node78Piece82UnitOutput := by decide +kernel

theorem node78Piece82_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece82Input) = evaluate node78Piece82Output :=
  mode_of_scaled _ _ (-139/3) node78Piece82UnitInput node78Piece82UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece82_check)

def node78Piece83Input_sector0 : RawPoly ℕ := [(-272/9, [1, 2, 2, 2, 2, 2, 3, 3])]

def node78Piece83Input : SectorVector := [(0, node78Piece83Input_sector0)]
def node78Piece83Output_sector0_chunk0 : RawPoly ℕ := [(-1088/9, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-2176, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-10880/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (-4352, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-35360/3, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-6528, [1, 1, 2, 2, 2, 2, 2, 10]), (-10880/3, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (-43520, [1, 1, 2, 2, 2, 2, 3, 9]), (-87040/3, [1, 1, 2, 2, 2, 3, 3, 8]), (-2176, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-59840/9, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-6528, [1, 2, 2, 2, 2, 2, 2, 9]), (-83776/3, [1, 2, 2, 2, 2, 2, 3, 8]), (-6528, [1, 2, 2, 2, 2, 2, 4, 7]), (-6528, [1, 2, 2, 2, 2, 2, 5, 6]), (-152320/3, [1, 2, 2, 2, 2, 3, 3, 7]), (-43520, [1, 2, 2, 2, 2, 3, 4, 6]), (-21760, [1, 2, 2, 2, 2, 3, 5, 5]), (-65280, [1, 2, 2, 2, 2, 13]), (-87040/3, [1, 2, 2, 2, 3, 3, 3, 6]), (-87040/3, [1, 2, 2, 2, 3, 3, 4, 5]), (-174080, [1, 2, 2, 2, 3, 12]), (-174080/3, [1, 2, 2, 3, 3, 11]), (-1088/9, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3])]

def node78Piece83Output_sector0_chunk1 : RawPoly ℕ := [(-4352, [2, 2, 2, 2, 2, 2, 3, 7]), (-89216/9, [2, 2, 2, 2, 2, 3, 3, 6]), (-4352, [2, 2, 2, 2, 2, 3, 4, 5]), (-6528, [2, 2, 2, 2, 2, 12]), (-21760/3, [2, 2, 2, 2, 3, 3, 3, 5]), (-10880/3, [2, 2, 2, 2, 3, 3, 4, 4]), (-43520, [2, 2, 2, 2, 3, 11]), (-87040/3, [2, 2, 2, 3, 3, 10])]

def node78Piece83Output_sector0 : RawPoly ℕ := [node78Piece83Output_sector0_chunk0, node78Piece83Output_sector0_chunk1].flatten

def node78Piece83Output : SectorVector := [(0, node78Piece83Output_sector0)]

def node78Piece83UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 2, 3, 3])]

def node78Piece83UnitInput_sector0 : RawPoly ℕ := [node78Piece83UnitInput_sector0_chunk0].flatten

def node78Piece83UnitInput : SectorVector := [(0, node78Piece83UnitInput_sector0)]

def node78Piece83UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (72, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (120, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (144, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (390, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (216, [1, 1, 2, 2, 2, 2, 2, 10]), (120, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (1440, [1, 1, 2, 2, 2, 2, 3, 9]), (960, [1, 1, 2, 2, 2, 3, 3, 8]), (72, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (220, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (216, [1, 2, 2, 2, 2, 2, 2, 9]), (924, [1, 2, 2, 2, 2, 2, 3, 8]), (216, [1, 2, 2, 2, 2, 2, 4, 7]), (216, [1, 2, 2, 2, 2, 2, 5, 6]), (1680, [1, 2, 2, 2, 2, 3, 3, 7]), (1440, [1, 2, 2, 2, 2, 3, 4, 6]), (720, [1, 2, 2, 2, 2, 3, 5, 5]), (2160, [1, 2, 2, 2, 2, 13]), (960, [1, 2, 2, 2, 3, 3, 3, 6]), (960, [1, 2, 2, 2, 3, 3, 4, 5]), (5760, [1, 2, 2, 2, 3, 12]), (1920, [1, 2, 2, 3, 3, 11]), (4, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3])]

def node78Piece83UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [2, 2, 2, 2, 2, 2, 3, 7]), (328, [2, 2, 2, 2, 2, 3, 3, 6]), (144, [2, 2, 2, 2, 2, 3, 4, 5]), (216, [2, 2, 2, 2, 2, 12]), (240, [2, 2, 2, 2, 3, 3, 3, 5]), (120, [2, 2, 2, 2, 3, 3, 4, 4]), (1440, [2, 2, 2, 2, 3, 11]), (960, [2, 2, 2, 3, 3, 10])]

def node78Piece83UnitOutput_sector0 : RawPoly ℕ := [node78Piece83UnitOutput_sector0_chunk0, node78Piece83UnitOutput_sector0_chunk1].flatten

def node78Piece83UnitOutput : SectorVector := [(0, node78Piece83UnitOutput_sector0)]

theorem node78Piece83_check : VectorCertificate (neutralBoundS JR (-2) node78Piece83UnitInput) node78Piece83UnitOutput := by decide +kernel

theorem node78Piece83_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece83Input) = evaluate node78Piece83Output :=
  mode_of_scaled _ _ (-272/9) node78Piece83UnitInput node78Piece83UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece83_check)

def node78Piece84Input_sector0 : RawPoly ℕ := [(-135, [1, 2, 2, 2, 2, 8])]

def node78Piece84Input : SectorVector := [(0, node78Piece84Input_sector0)]
def node78Piece84Output_sector0_chunk0 : RawPoly ℕ := [(-540, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8]), (-12960, [1, 1, 1, 2, 2, 2, 2, 11]), (-12960, [1, 1, 1, 2, 2, 2, 5, 8]), (-25920, [1, 1, 2, 2, 2, 2, 2, 10]), (-25920, [1, 1, 2, 2, 2, 2, 3, 9]), (-52650, [1, 1, 2, 2, 2, 2, 4, 8]), (-25920, [1, 1, 2, 2, 2, 2, 5, 7]), (-12960, [1, 1, 2, 2, 2, 2, 6, 6]), (-12960, [1, 1, 2, 2, 2, 3, 3, 8]), (-207360, [1, 1, 2, 2, 2, 14]), (-77760, [1, 1, 2, 2, 8, 8]), (-12960, [1, 2, 2, 2, 2, 2, 2, 9]), (-42660, [1, 2, 2, 2, 2, 2, 3, 8]), (-25920, [1, 2, 2, 2, 2, 2, 4, 7]), (-25920, [1, 2, 2, 2, 2, 2, 5, 6]), (-12960, [1, 2, 2, 2, 2, 3, 3, 7]), (-25920, [1, 2, 2, 2, 2, 3, 4, 6]), (-12960, [1, 2, 2, 2, 2, 3, 5, 5]), (-12960, [1, 2, 2, 2, 2, 4, 4, 5]), (356400, [1, 2, 2, 2, 2, 13]), (-207360, [1, 2, 2, 2, 3, 12]), (-207360, [1, 2, 2, 2, 4, 11]), (-207360, [1, 2, 2, 2, 5, 10]), (-207360, [1, 2, 2, 2, 6, 9])]

def node78Piece84Output_sector0_chunk1 : RawPoly ℕ := [(-207360, [1, 2, 2, 2, 7, 8]), (-77760, [1, 2, 2, 3, 6, 8]), (-77760, [1, 2, 2, 4, 5, 8]), (-622080, [1, 2, 2, 17]), (-103680, [1, 2, 8, 11]), (-540, [2, 2, 2, 2, 2, 2, 2, 8]), (-25920, [2, 2, 2, 2, 2, 12]), (-25920, [2, 2, 2, 2, 3, 11]), (-25920, [2, 2, 2, 2, 4, 10]), (-25920, [2, 2, 2, 2, 5, 9]), (-44280, [2, 2, 2, 2, 6, 8]), (-12960, [2, 2, 2, 2, 7, 7]), (-25920, [2, 2, 2, 3, 5, 8]), (-12960, [2, 2, 2, 4, 4, 8]), (-207360, [2, 2, 2, 16]), (-77760, [2, 2, 8, 10])]

def node78Piece84Output_sector0 : RawPoly ℕ := [node78Piece84Output_sector0_chunk0, node78Piece84Output_sector0_chunk1].flatten

def node78Piece84Output : SectorVector := [(0, node78Piece84Output_sector0)]

def node78Piece84UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 8])]

def node78Piece84UnitInput_sector0 : RawPoly ℕ := [node78Piece84UnitInput_sector0_chunk0].flatten

def node78Piece84UnitInput : SectorVector := [(0, node78Piece84UnitInput_sector0)]

def node78Piece84UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8]), (96, [1, 1, 1, 2, 2, 2, 2, 11]), (96, [1, 1, 1, 2, 2, 2, 5, 8]), (192, [1, 1, 2, 2, 2, 2, 2, 10]), (192, [1, 1, 2, 2, 2, 2, 3, 9]), (390, [1, 1, 2, 2, 2, 2, 4, 8]), (192, [1, 1, 2, 2, 2, 2, 5, 7]), (96, [1, 1, 2, 2, 2, 2, 6, 6]), (96, [1, 1, 2, 2, 2, 3, 3, 8]), (1536, [1, 1, 2, 2, 2, 14]), (576, [1, 1, 2, 2, 8, 8]), (96, [1, 2, 2, 2, 2, 2, 2, 9]), (316, [1, 2, 2, 2, 2, 2, 3, 8]), (192, [1, 2, 2, 2, 2, 2, 4, 7]), (192, [1, 2, 2, 2, 2, 2, 5, 6]), (96, [1, 2, 2, 2, 2, 3, 3, 7]), (192, [1, 2, 2, 2, 2, 3, 4, 6]), (96, [1, 2, 2, 2, 2, 3, 5, 5]), (96, [1, 2, 2, 2, 2, 4, 4, 5]), (-2640, [1, 2, 2, 2, 2, 13]), (1536, [1, 2, 2, 2, 3, 12]), (1536, [1, 2, 2, 2, 4, 11]), (1536, [1, 2, 2, 2, 5, 10]), (1536, [1, 2, 2, 2, 6, 9])]

def node78Piece84UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1536, [1, 2, 2, 2, 7, 8]), (576, [1, 2, 2, 3, 6, 8]), (576, [1, 2, 2, 4, 5, 8]), (4608, [1, 2, 2, 17]), (768, [1, 2, 8, 11]), (4, [2, 2, 2, 2, 2, 2, 2, 8]), (192, [2, 2, 2, 2, 2, 12]), (192, [2, 2, 2, 2, 3, 11]), (192, [2, 2, 2, 2, 4, 10]), (192, [2, 2, 2, 2, 5, 9]), (328, [2, 2, 2, 2, 6, 8]), (96, [2, 2, 2, 2, 7, 7]), (192, [2, 2, 2, 3, 5, 8]), (96, [2, 2, 2, 4, 4, 8]), (1536, [2, 2, 2, 16]), (576, [2, 2, 8, 10])]

def node78Piece84UnitOutput_sector0 : RawPoly ℕ := [node78Piece84UnitOutput_sector0_chunk0, node78Piece84UnitOutput_sector0_chunk1].flatten

def node78Piece84UnitOutput : SectorVector := [(0, node78Piece84UnitOutput_sector0)]

theorem node78Piece84_check : VectorCertificate (neutralBoundS JR (-2) node78Piece84UnitInput) node78Piece84UnitOutput := by decide +kernel

theorem node78Piece84_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece84Input) = evaluate node78Piece84Output :=
  mode_of_scaled _ _ (-135) node78Piece84UnitInput node78Piece84UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece84_check)

def node78Piece85Input_sector0 : RawPoly ℕ := [(-160/3, [1, 2, 2, 2, 3, 7])]

def node78Piece85Input : SectorVector := [(0, node78Piece85Input_sector0)]
def node78Piece85Output_sector0_chunk0 : RawPoly ℕ := [(-640/3, [1, 1, 1, 1, 2, 2, 2, 2, 3, 7]), (-4480, [1, 1, 1, 2, 2, 2, 3, 10]), (-1920, [1, 1, 1, 2, 2, 2, 6, 7]), (-3840, [1, 1, 1, 2, 2, 3, 5, 7]), (-8960, [1, 1, 2, 2, 2, 2, 3, 9]), (-3840, [1, 1, 2, 2, 2, 2, 5, 7]), (-8960, [1, 1, 2, 2, 2, 3, 3, 8]), (-20800, [1, 1, 2, 2, 2, 3, 4, 7]), (-8960, [1, 1, 2, 2, 2, 3, 5, 6]), (-26880, [1, 1, 2, 2, 2, 14]), (-3840, [1, 1, 2, 2, 3, 3, 3, 7]), (-53760, [1, 1, 2, 2, 3, 13]), (-23040, [1, 1, 2, 2, 7, 9]), (-15360, [1, 1, 2, 3, 7, 8]), (-4480, [1, 2, 2, 2, 2, 2, 3, 8]), (-1920, [1, 2, 2, 2, 2, 2, 4, 7]), (-48640/3, [1, 2, 2, 2, 2, 3, 3, 7]), (-8960, [1, 2, 2, 2, 2, 3, 4, 6]), (-4480, [1, 2, 2, 2, 2, 3, 5, 5]), (-26880, [1, 2, 2, 2, 2, 13]), (-4480, [1, 2, 2, 2, 3, 3, 3, 6]), (-8960, [1, 2, 2, 2, 3, 3, 4, 5]), (-4480/3, [1, 2, 2, 2, 3, 4, 4, 4]), (230720/3, [1, 2, 2, 2, 3, 12])]

def node78Piece85Output_sector0_chunk1 : RawPoly ℕ := [(-26880, [1, 2, 2, 2, 4, 11]), (-26880, [1, 2, 2, 2, 5, 10]), (-26880, [1, 2, 2, 2, 6, 9]), (-30400, [1, 2, 2, 2, 7, 8]), (-53760, [1, 2, 2, 3, 3, 11]), (-53760, [1, 2, 2, 3, 4, 10]), (-53760, [1, 2, 2, 3, 5, 9]), (-53760, [1, 2, 2, 3, 6, 8]), (-42240, [1, 2, 2, 3, 7, 7]), (-23040, [1, 2, 2, 4, 6, 7]), (-11520, [1, 2, 2, 5, 5, 7]), (-161280, [1, 2, 2, 17]), (-15360, [1, 2, 3, 3, 6, 7]), (-15360, [1, 2, 3, 4, 5, 7]), (-107520, [1, 2, 3, 16]), (-46080, [1, 2, 7, 12]), (-10240, [1, 3, 7, 11]), (-640/3, [2, 2, 2, 2, 2, 2, 3, 7]), (-8960, [2, 2, 2, 2, 3, 11]), (-3840, [2, 2, 2, 2, 7, 7]), (-8960, [2, 2, 2, 3, 3, 10]), (-8960, [2, 2, 2, 3, 4, 9]), (-8960, [2, 2, 2, 3, 5, 8]), (-52480/3, [2, 2, 2, 3, 6, 7])]

def node78Piece85Output_sector0_chunk2 : RawPoly ℕ := [(-3840, [2, 2, 2, 4, 5, 7]), (-26880, [2, 2, 2, 16]), (-7680, [2, 2, 3, 3, 5, 7]), (-3840, [2, 2, 3, 4, 4, 7]), (-53760, [2, 2, 3, 15]), (-23040, [2, 2, 7, 11]), (-15360, [2, 3, 7, 10])]

def node78Piece85Output_sector0 : RawPoly ℕ := [node78Piece85Output_sector0_chunk0, node78Piece85Output_sector0_chunk1, node78Piece85Output_sector0_chunk2].flatten

def node78Piece85Output : SectorVector := [(0, node78Piece85Output_sector0)]

def node78Piece85UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 3, 7])]

def node78Piece85UnitInput_sector0 : RawPoly ℕ := [node78Piece85UnitInput_sector0_chunk0].flatten

def node78Piece85UnitInput : SectorVector := [(0, node78Piece85UnitInput_sector0)]

def node78Piece85UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 3, 7]), (84, [1, 1, 1, 2, 2, 2, 3, 10]), (36, [1, 1, 1, 2, 2, 2, 6, 7]), (72, [1, 1, 1, 2, 2, 3, 5, 7]), (168, [1, 1, 2, 2, 2, 2, 3, 9]), (72, [1, 1, 2, 2, 2, 2, 5, 7]), (168, [1, 1, 2, 2, 2, 3, 3, 8]), (390, [1, 1, 2, 2, 2, 3, 4, 7]), (168, [1, 1, 2, 2, 2, 3, 5, 6]), (504, [1, 1, 2, 2, 2, 14]), (72, [1, 1, 2, 2, 3, 3, 3, 7]), (1008, [1, 1, 2, 2, 3, 13]), (432, [1, 1, 2, 2, 7, 9]), (288, [1, 1, 2, 3, 7, 8]), (84, [1, 2, 2, 2, 2, 2, 3, 8]), (36, [1, 2, 2, 2, 2, 2, 4, 7]), (304, [1, 2, 2, 2, 2, 3, 3, 7]), (168, [1, 2, 2, 2, 2, 3, 4, 6]), (84, [1, 2, 2, 2, 2, 3, 5, 5]), (504, [1, 2, 2, 2, 2, 13]), (84, [1, 2, 2, 2, 3, 3, 3, 6]), (168, [1, 2, 2, 2, 3, 3, 4, 5]), (28, [1, 2, 2, 2, 3, 4, 4, 4]), (-1442, [1, 2, 2, 2, 3, 12])]

def node78Piece85UnitOutput_sector0_chunk1 : RawPoly ℕ := [(504, [1, 2, 2, 2, 4, 11]), (504, [1, 2, 2, 2, 5, 10]), (504, [1, 2, 2, 2, 6, 9]), (570, [1, 2, 2, 2, 7, 8]), (1008, [1, 2, 2, 3, 3, 11]), (1008, [1, 2, 2, 3, 4, 10]), (1008, [1, 2, 2, 3, 5, 9]), (1008, [1, 2, 2, 3, 6, 8]), (792, [1, 2, 2, 3, 7, 7]), (432, [1, 2, 2, 4, 6, 7]), (216, [1, 2, 2, 5, 5, 7]), (3024, [1, 2, 2, 17]), (288, [1, 2, 3, 3, 6, 7]), (288, [1, 2, 3, 4, 5, 7]), (2016, [1, 2, 3, 16]), (864, [1, 2, 7, 12]), (192, [1, 3, 7, 11]), (4, [2, 2, 2, 2, 2, 2, 3, 7]), (168, [2, 2, 2, 2, 3, 11]), (72, [2, 2, 2, 2, 7, 7]), (168, [2, 2, 2, 3, 3, 10]), (168, [2, 2, 2, 3, 4, 9]), (168, [2, 2, 2, 3, 5, 8]), (328, [2, 2, 2, 3, 6, 7])]

def node78Piece85UnitOutput_sector0_chunk2 : RawPoly ℕ := [(72, [2, 2, 2, 4, 5, 7]), (504, [2, 2, 2, 16]), (144, [2, 2, 3, 3, 5, 7]), (72, [2, 2, 3, 4, 4, 7]), (1008, [2, 2, 3, 15]), (432, [2, 2, 7, 11]), (288, [2, 3, 7, 10])]

def node78Piece85UnitOutput_sector0 : RawPoly ℕ := [node78Piece85UnitOutput_sector0_chunk0, node78Piece85UnitOutput_sector0_chunk1, node78Piece85UnitOutput_sector0_chunk2].flatten

def node78Piece85UnitOutput : SectorVector := [(0, node78Piece85UnitOutput_sector0)]

theorem node78Piece85_check : VectorCertificate (neutralBoundS JR (-2) node78Piece85UnitInput) node78Piece85UnitOutput := by decide +kernel

theorem node78Piece85_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece85Input) = evaluate node78Piece85Output :=
  mode_of_scaled _ _ (-160/3) node78Piece85UnitInput node78Piece85UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece85_check)

def node78Piece86Input_sector0 : RawPoly ℕ := [(-860/3, [1, 2, 2, 2, 4, 6])]

def node78Piece86Input : SectorVector := [(0, node78Piece86Input_sector0)]
def node78Piece86Output_sector0_chunk0 : RawPoly ℕ := [(-3440/3, [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]), (-20640, [1, 1, 1, 2, 2, 2, 4, 9]), (-13760, [1, 1, 1, 2, 2, 2, 6, 7]), (-20640, [1, 1, 1, 2, 2, 4, 5, 6]), (-41280, [1, 1, 2, 2, 2, 2, 4, 8]), (-27520, [1, 1, 2, 2, 2, 2, 6, 6]), (-41280, [1, 1, 2, 2, 2, 3, 4, 7]), (-27520, [1, 1, 2, 2, 2, 3, 5, 6]), (-98040, [1, 1, 2, 2, 2, 4, 4, 6]), (-20640, [1, 1, 2, 2, 2, 4, 5, 5]), (-165120, [1, 1, 2, 2, 2, 14]), (-20640, [1, 1, 2, 2, 3, 3, 4, 6]), (-247680, [1, 1, 2, 2, 4, 12]), (-165120, [1, 1, 2, 2, 6, 10]), (-82560, [1, 1, 2, 4, 6, 8]), (-20640, [1, 2, 2, 2, 2, 2, 4, 7]), (-13760, [1, 2, 2, 2, 2, 2, 5, 6]), (-292400/3, [1, 2, 2, 2, 2, 3, 4, 6]), (-41280, [1, 2, 2, 2, 2, 4, 4, 5]), (-165120, [1, 2, 2, 2, 2, 13]), (-13760/3, [1, 2, 2, 2, 3, 3, 3, 6]), (-20640, [1, 2, 2, 2, 3, 3, 4, 5]), (-20640, [1, 2, 2, 2, 3, 4, 4, 4]), (-165120, [1, 2, 2, 2, 3, 12])]

def node78Piece86Output_sector0_chunk1 : RawPoly ℕ := [(158240, [1, 2, 2, 2, 4, 11]), (-165120, [1, 2, 2, 2, 5, 10]), (-364640/3, [1, 2, 2, 2, 6, 9]), (-165120, [1, 2, 2, 2, 7, 8]), (-247680, [1, 2, 2, 3, 4, 10]), (-165120, [1, 2, 2, 3, 6, 8]), (-247680, [1, 2, 2, 4, 4, 9]), (-247680, [1, 2, 2, 4, 5, 8]), (-371520, [1, 2, 2, 4, 6, 7]), (-165120, [1, 2, 2, 5, 6, 6]), (-990720, [1, 2, 2, 17]), (-82560, [1, 2, 3, 4, 6, 6]), (-82560, [1, 2, 4, 4, 5, 6]), (-495360, [1, 2, 4, 15]), (-330240, [1, 2, 6, 13]), (-55040, [1, 4, 6, 11]), (-3440/3, [2, 2, 2, 2, 2, 2, 4, 6]), (-41280, [2, 2, 2, 2, 4, 10]), (-27520, [2, 2, 2, 2, 6, 8]), (-41280, [2, 2, 2, 3, 4, 9]), (-27520, [2, 2, 2, 3, 6, 7]), (-41280, [2, 2, 2, 4, 4, 8]), (-41280, [2, 2, 2, 4, 5, 7]), (-220160/3, [2, 2, 2, 4, 6, 6])]

def node78Piece86Output_sector0_chunk2 : RawPoly ℕ := [(-13760, [2, 2, 2, 5, 5, 6]), (-165120, [2, 2, 2, 16]), (-41280, [2, 2, 3, 4, 5, 6]), (-20640, [2, 2, 4, 4, 4, 6]), (-247680, [2, 2, 4, 14]), (-165120, [2, 2, 6, 12]), (-82560, [2, 4, 6, 10])]

def node78Piece86Output_sector0 : RawPoly ℕ := [node78Piece86Output_sector0_chunk0, node78Piece86Output_sector0_chunk1, node78Piece86Output_sector0_chunk2].flatten

def node78Piece86Output : SectorVector := [(0, node78Piece86Output_sector0)]

def node78Piece86UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 4, 6])]

def node78Piece86UnitInput_sector0 : RawPoly ℕ := [node78Piece86UnitInput_sector0_chunk0].flatten

def node78Piece86UnitInput : SectorVector := [(0, node78Piece86UnitInput_sector0)]

def node78Piece86UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]), (72, [1, 1, 1, 2, 2, 2, 4, 9]), (48, [1, 1, 1, 2, 2, 2, 6, 7]), (72, [1, 1, 1, 2, 2, 4, 5, 6]), (144, [1, 1, 2, 2, 2, 2, 4, 8]), (96, [1, 1, 2, 2, 2, 2, 6, 6]), (144, [1, 1, 2, 2, 2, 3, 4, 7]), (96, [1, 1, 2, 2, 2, 3, 5, 6]), (342, [1, 1, 2, 2, 2, 4, 4, 6]), (72, [1, 1, 2, 2, 2, 4, 5, 5]), (576, [1, 1, 2, 2, 2, 14]), (72, [1, 1, 2, 2, 3, 3, 4, 6]), (864, [1, 1, 2, 2, 4, 12]), (576, [1, 1, 2, 2, 6, 10]), (288, [1, 1, 2, 4, 6, 8]), (72, [1, 2, 2, 2, 2, 2, 4, 7]), (48, [1, 2, 2, 2, 2, 2, 5, 6]), (340, [1, 2, 2, 2, 2, 3, 4, 6]), (144, [1, 2, 2, 2, 2, 4, 4, 5]), (576, [1, 2, 2, 2, 2, 13]), (16, [1, 2, 2, 2, 3, 3, 3, 6]), (72, [1, 2, 2, 2, 3, 3, 4, 5]), (72, [1, 2, 2, 2, 3, 4, 4, 4]), (576, [1, 2, 2, 2, 3, 12])]

def node78Piece86UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-552, [1, 2, 2, 2, 4, 11]), (576, [1, 2, 2, 2, 5, 10]), (424, [1, 2, 2, 2, 6, 9]), (576, [1, 2, 2, 2, 7, 8]), (864, [1, 2, 2, 3, 4, 10]), (576, [1, 2, 2, 3, 6, 8]), (864, [1, 2, 2, 4, 4, 9]), (864, [1, 2, 2, 4, 5, 8]), (1296, [1, 2, 2, 4, 6, 7]), (576, [1, 2, 2, 5, 6, 6]), (3456, [1, 2, 2, 17]), (288, [1, 2, 3, 4, 6, 6]), (288, [1, 2, 4, 4, 5, 6]), (1728, [1, 2, 4, 15]), (1152, [1, 2, 6, 13]), (192, [1, 4, 6, 11]), (4, [2, 2, 2, 2, 2, 2, 4, 6]), (144, [2, 2, 2, 2, 4, 10]), (96, [2, 2, 2, 2, 6, 8]), (144, [2, 2, 2, 3, 4, 9]), (96, [2, 2, 2, 3, 6, 7]), (144, [2, 2, 2, 4, 4, 8]), (144, [2, 2, 2, 4, 5, 7]), (256, [2, 2, 2, 4, 6, 6])]

def node78Piece86UnitOutput_sector0_chunk2 : RawPoly ℕ := [(48, [2, 2, 2, 5, 5, 6]), (576, [2, 2, 2, 16]), (144, [2, 2, 3, 4, 5, 6]), (72, [2, 2, 4, 4, 4, 6]), (864, [2, 2, 4, 14]), (576, [2, 2, 6, 12]), (288, [2, 4, 6, 10])]

def node78Piece86UnitOutput_sector0 : RawPoly ℕ := [node78Piece86UnitOutput_sector0_chunk0, node78Piece86UnitOutput_sector0_chunk1, node78Piece86UnitOutput_sector0_chunk2].flatten

def node78Piece86UnitOutput : SectorVector := [(0, node78Piece86UnitOutput_sector0)]

theorem node78Piece86_check : VectorCertificate (neutralBoundS JR (-2) node78Piece86UnitInput) node78Piece86UnitOutput := by decide +kernel

theorem node78Piece86_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece86Input) = evaluate node78Piece86Output :=
  mode_of_scaled _ _ (-860/3) node78Piece86UnitInput node78Piece86UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece86_check)

def node78Piece87Input_sector0 : RawPoly ℕ := [(-336/5, [1, 2, 2, 2, 5, 5])]

def node78Piece87Input : SectorVector := [(0, node78Piece87Input_sector0)]
def node78Piece87Output_sector0_chunk0 : RawPoly ℕ := [(-1344/5, [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]), (-8064, [1, 1, 1, 2, 2, 2, 5, 8]), (-24192/5, [1, 1, 1, 2, 2, 5, 5, 5]), (-16128, [1, 1, 2, 2, 2, 2, 5, 7]), (-16128, [1, 1, 2, 2, 2, 3, 5, 6]), (-26208, [1, 1, 2, 2, 2, 4, 5, 5]), (-40320, [1, 1, 2, 2, 2, 14]), (-24192/5, [1, 1, 2, 2, 3, 3, 5, 5]), (-96768, [1, 1, 2, 2, 5, 11]), (-96768/5, [1, 1, 2, 5, 5, 8]), (-8064, [1, 2, 2, 2, 2, 2, 5, 6]), (-22848, [1, 2, 2, 2, 2, 3, 5, 5]), (-8064, [1, 2, 2, 2, 2, 4, 4, 5]), (-40320, [1, 2, 2, 2, 2, 13]), (-8064, [1, 2, 2, 2, 3, 3, 4, 5]), (-40320, [1, 2, 2, 2, 3, 12]), (-40320, [1, 2, 2, 2, 4, 11]), (32256, [1, 2, 2, 2, 5, 10]), (-40320, [1, 2, 2, 2, 6, 9]), (-40320, [1, 2, 2, 2, 7, 8]), (-96768, [1, 2, 2, 3, 5, 9]), (-96768, [1, 2, 2, 4, 5, 8]), (-435456/5, [1, 2, 2, 5, 5, 7]), (-48384, [1, 2, 2, 5, 6, 6])]

def node78Piece87Output_sector0_chunk1 : RawPoly ℕ := [(-241920, [1, 2, 2, 17]), (-96768/5, [1, 2, 3, 5, 5, 6]), (-96768/5, [1, 2, 4, 5, 5, 5]), (-193536, [1, 2, 5, 14]), (-64512/5, [1, 5, 5, 11]), (-1344/5, [2, 2, 2, 2, 2, 2, 5, 5]), (-16128, [2, 2, 2, 2, 5, 9]), (-16128, [2, 2, 2, 3, 5, 8]), (-16128, [2, 2, 2, 4, 5, 7]), (-110208/5, [2, 2, 2, 5, 5, 6]), (-40320, [2, 2, 2, 16]), (-48384/5, [2, 2, 3, 5, 5, 5]), (-24192/5, [2, 2, 4, 4, 5, 5]), (-96768, [2, 2, 5, 13]), (-96768/5, [2, 5, 5, 10])]

def node78Piece87Output_sector0 : RawPoly ℕ := [node78Piece87Output_sector0_chunk0, node78Piece87Output_sector0_chunk1].flatten

def node78Piece87Output : SectorVector := [(0, node78Piece87Output_sector0)]

def node78Piece87UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 5, 5])]

def node78Piece87UnitInput_sector0 : RawPoly ℕ := [node78Piece87UnitInput_sector0_chunk0].flatten

def node78Piece87UnitInput : SectorVector := [(0, node78Piece87UnitInput_sector0)]

def node78Piece87UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]), (120, [1, 1, 1, 2, 2, 2, 5, 8]), (72, [1, 1, 1, 2, 2, 5, 5, 5]), (240, [1, 1, 2, 2, 2, 2, 5, 7]), (240, [1, 1, 2, 2, 2, 3, 5, 6]), (390, [1, 1, 2, 2, 2, 4, 5, 5]), (600, [1, 1, 2, 2, 2, 14]), (72, [1, 1, 2, 2, 3, 3, 5, 5]), (1440, [1, 1, 2, 2, 5, 11]), (288, [1, 1, 2, 5, 5, 8]), (120, [1, 2, 2, 2, 2, 2, 5, 6]), (340, [1, 2, 2, 2, 2, 3, 5, 5]), (120, [1, 2, 2, 2, 2, 4, 4, 5]), (600, [1, 2, 2, 2, 2, 13]), (120, [1, 2, 2, 2, 3, 3, 4, 5]), (600, [1, 2, 2, 2, 3, 12]), (600, [1, 2, 2, 2, 4, 11]), (-480, [1, 2, 2, 2, 5, 10]), (600, [1, 2, 2, 2, 6, 9]), (600, [1, 2, 2, 2, 7, 8]), (1440, [1, 2, 2, 3, 5, 9]), (1440, [1, 2, 2, 4, 5, 8]), (1296, [1, 2, 2, 5, 5, 7]), (720, [1, 2, 2, 5, 6, 6])]

def node78Piece87UnitOutput_sector0_chunk1 : RawPoly ℕ := [(3600, [1, 2, 2, 17]), (288, [1, 2, 3, 5, 5, 6]), (288, [1, 2, 4, 5, 5, 5]), (2880, [1, 2, 5, 14]), (192, [1, 5, 5, 11]), (4, [2, 2, 2, 2, 2, 2, 5, 5]), (240, [2, 2, 2, 2, 5, 9]), (240, [2, 2, 2, 3, 5, 8]), (240, [2, 2, 2, 4, 5, 7]), (328, [2, 2, 2, 5, 5, 6]), (600, [2, 2, 2, 16]), (144, [2, 2, 3, 5, 5, 5]), (72, [2, 2, 4, 4, 5, 5]), (1440, [2, 2, 5, 13]), (288, [2, 5, 5, 10])]

def node78Piece87UnitOutput_sector0 : RawPoly ℕ := [node78Piece87UnitOutput_sector0_chunk0, node78Piece87UnitOutput_sector0_chunk1].flatten

def node78Piece87UnitOutput : SectorVector := [(0, node78Piece87UnitOutput_sector0)]

theorem node78Piece87_check : VectorCertificate (neutralBoundS JR (-2) node78Piece87UnitInput) node78Piece87UnitOutput := by decide +kernel

theorem node78Piece87_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece87Input) = evaluate node78Piece87Output :=
  mode_of_scaled _ _ (-336/5) node78Piece87UnitInput node78Piece87UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece87_check)

def node78Piece88Input_sector0 : RawPoly ℕ := [(2320/9, [1, 2, 2, 3, 3, 6])]

def node78Piece88Input : SectorVector := [(0, node78Piece88Input_sector0)]
def node78Piece88Output_sector0_chunk0 : RawPoly ℕ := [(9280/9, [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]), (18560, [1, 1, 1, 2, 2, 3, 3, 9]), (18560, [1, 1, 1, 2, 2, 3, 6, 6]), (37120/3, [1, 1, 1, 2, 3, 3, 5, 6]), (37120, [1, 1, 2, 2, 2, 3, 3, 8]), (37120, [1, 1, 2, 2, 2, 3, 5, 6]), (37120, [1, 1, 2, 2, 3, 3, 3, 7]), (301600/3, [1, 1, 2, 2, 3, 3, 4, 6]), (18560, [1, 1, 2, 2, 3, 3, 5, 5]), (222720, [1, 1, 2, 2, 3, 13]), (55680, [1, 1, 2, 2, 6, 10]), (37120/3, [1, 1, 2, 3, 3, 3, 3, 6]), (148480, [1, 1, 2, 3, 3, 12]), (148480, [1, 1, 2, 3, 6, 9]), (74240/3, [1, 1, 3, 3, 6, 8]), (18560, [1, 2, 2, 2, 2, 3, 3, 7]), (18560, [1, 2, 2, 2, 2, 3, 4, 6]), (677440/9, [1, 2, 2, 2, 3, 3, 3, 6]), (37120, [1, 2, 2, 2, 3, 3, 4, 5]), (222720, [1, 2, 2, 2, 3, 12]), (55680, [1, 2, 2, 2, 6, 9]), (18560, [1, 2, 2, 3, 3, 3, 3, 5]), (18560, [1, 2, 2, 3, 3, 3, 4, 4]), (-426880/3, [1, 2, 2, 3, 3, 11])]

def node78Piece88Output_sector0_chunk1 : RawPoly ℕ := [(222720, [1, 2, 2, 3, 4, 10]), (222720, [1, 2, 2, 3, 5, 9]), (714560/3, [1, 2, 2, 3, 6, 8]), (111360, [1, 2, 2, 3, 7, 7]), (55680, [1, 2, 2, 4, 6, 7]), (55680, [1, 2, 2, 5, 6, 6]), (334080, [1, 2, 2, 17]), (148480, [1, 2, 3, 3, 3, 10]), (148480, [1, 2, 3, 3, 4, 9]), (148480, [1, 2, 3, 3, 5, 8]), (742400/3, [1, 2, 3, 3, 6, 7]), (148480, [1, 2, 3, 4, 6, 6]), (74240, [1, 2, 3, 5, 5, 6]), (890880, [1, 2, 3, 16]), (222720, [1, 2, 6, 13]), (74240/3, [1, 3, 3, 3, 6, 6]), (74240/3, [1, 3, 3, 4, 5, 6]), (148480, [1, 3, 3, 15]), (148480, [1, 3, 6, 12]), (9280/9, [2, 2, 2, 2, 2, 3, 3, 6]), (37120, [2, 2, 2, 3, 3, 10]), (37120, [2, 2, 2, 3, 6, 7]), (37120, [2, 2, 3, 3, 3, 9]), (37120, [2, 2, 3, 3, 4, 8])]

def node78Piece88Output_sector0_chunk2 : RawPoly ℕ := [(37120, [2, 2, 3, 3, 5, 7]), (593920/9, [2, 2, 3, 3, 6, 6]), (37120, [2, 2, 3, 4, 5, 6]), (222720, [2, 2, 3, 15]), (55680, [2, 2, 6, 12]), (74240/3, [2, 3, 3, 3, 5, 6]), (37120/3, [2, 3, 3, 4, 4, 6]), (148480, [2, 3, 3, 14]), (148480, [2, 3, 6, 11]), (74240/3, [3, 3, 6, 10])]

def node78Piece88Output_sector0 : RawPoly ℕ := [node78Piece88Output_sector0_chunk0, node78Piece88Output_sector0_chunk1, node78Piece88Output_sector0_chunk2].flatten

def node78Piece88Output : SectorVector := [(0, node78Piece88Output_sector0)]

def node78Piece88UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 3, 3, 6])]

def node78Piece88UnitInput_sector0 : RawPoly ℕ := [node78Piece88UnitInput_sector0_chunk0].flatten

def node78Piece88UnitInput : SectorVector := [(0, node78Piece88UnitInput_sector0)]

def node78Piece88UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]), (72, [1, 1, 1, 2, 2, 3, 3, 9]), (72, [1, 1, 1, 2, 2, 3, 6, 6]), (48, [1, 1, 1, 2, 3, 3, 5, 6]), (144, [1, 1, 2, 2, 2, 3, 3, 8]), (144, [1, 1, 2, 2, 2, 3, 5, 6]), (144, [1, 1, 2, 2, 3, 3, 3, 7]), (390, [1, 1, 2, 2, 3, 3, 4, 6]), (72, [1, 1, 2, 2, 3, 3, 5, 5]), (864, [1, 1, 2, 2, 3, 13]), (216, [1, 1, 2, 2, 6, 10]), (48, [1, 1, 2, 3, 3, 3, 3, 6]), (576, [1, 1, 2, 3, 3, 12]), (576, [1, 1, 2, 3, 6, 9]), (96, [1, 1, 3, 3, 6, 8]), (72, [1, 2, 2, 2, 2, 3, 3, 7]), (72, [1, 2, 2, 2, 2, 3, 4, 6]), (292, [1, 2, 2, 2, 3, 3, 3, 6]), (144, [1, 2, 2, 2, 3, 3, 4, 5]), (864, [1, 2, 2, 2, 3, 12]), (216, [1, 2, 2, 2, 6, 9]), (72, [1, 2, 2, 3, 3, 3, 3, 5]), (72, [1, 2, 2, 3, 3, 3, 4, 4]), (-552, [1, 2, 2, 3, 3, 11])]

def node78Piece88UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 2, 2, 3, 4, 10]), (864, [1, 2, 2, 3, 5, 9]), (924, [1, 2, 2, 3, 6, 8]), (432, [1, 2, 2, 3, 7, 7]), (216, [1, 2, 2, 4, 6, 7]), (216, [1, 2, 2, 5, 6, 6]), (1296, [1, 2, 2, 17]), (576, [1, 2, 3, 3, 3, 10]), (576, [1, 2, 3, 3, 4, 9]), (576, [1, 2, 3, 3, 5, 8]), (960, [1, 2, 3, 3, 6, 7]), (576, [1, 2, 3, 4, 6, 6]), (288, [1, 2, 3, 5, 5, 6]), (3456, [1, 2, 3, 16]), (864, [1, 2, 6, 13]), (96, [1, 3, 3, 3, 6, 6]), (96, [1, 3, 3, 4, 5, 6]), (576, [1, 3, 3, 15]), (576, [1, 3, 6, 12]), (4, [2, 2, 2, 2, 2, 3, 3, 6]), (144, [2, 2, 2, 3, 3, 10]), (144, [2, 2, 2, 3, 6, 7]), (144, [2, 2, 3, 3, 3, 9]), (144, [2, 2, 3, 3, 4, 8])]

def node78Piece88UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [2, 2, 3, 3, 5, 7]), (256, [2, 2, 3, 3, 6, 6]), (144, [2, 2, 3, 4, 5, 6]), (864, [2, 2, 3, 15]), (216, [2, 2, 6, 12]), (96, [2, 3, 3, 3, 5, 6]), (48, [2, 3, 3, 4, 4, 6]), (576, [2, 3, 3, 14]), (576, [2, 3, 6, 11]), (96, [3, 3, 6, 10])]

def node78Piece88UnitOutput_sector0 : RawPoly ℕ := [node78Piece88UnitOutput_sector0_chunk0, node78Piece88UnitOutput_sector0_chunk1, node78Piece88UnitOutput_sector0_chunk2].flatten

def node78Piece88UnitOutput : SectorVector := [(0, node78Piece88UnitOutput_sector0)]

theorem node78Piece88_check : VectorCertificate (neutralBoundS JR (-2) node78Piece88UnitInput) node78Piece88UnitOutput := by decide +kernel

theorem node78Piece88_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece88Input) = evaluate node78Piece88Output :=
  mode_of_scaled _ _ (2320/9) node78Piece88UnitInput node78Piece88UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece88_check)

def node78Piece89Input_sector0 : RawPoly ℕ := [(-16, [1, 2, 2, 3, 4, 5])]

def node78Piece89Input : SectorVector := [(0, node78Piece89Input_sector0)]
def node78Piece89Output_sector0_chunk0 : RawPoly ℕ := [(-64, [1, 1, 1, 1, 2, 2, 2, 3, 4, 5]), (-960, [1, 1, 1, 2, 2, 3, 4, 8]), (-768, [1, 1, 1, 2, 2, 3, 5, 7]), (-576, [1, 1, 1, 2, 2, 4, 5, 6]), (-768, [1, 1, 1, 2, 3, 4, 5, 5]), (-1920, [1, 1, 2, 2, 2, 3, 4, 7]), (-1536, [1, 1, 2, 2, 2, 3, 5, 6]), (-1152, [1, 1, 2, 2, 2, 4, 5, 5]), (-1920, [1, 1, 2, 2, 3, 3, 4, 6]), (-1536, [1, 1, 2, 2, 3, 3, 5, 5]), (-5472, [1, 1, 2, 2, 3, 4, 4, 5]), (-7680, [1, 1, 2, 2, 3, 13]), (-5760, [1, 1, 2, 2, 4, 12]), (-4608, [1, 1, 2, 2, 5, 11]), (-768, [1, 1, 2, 3, 3, 3, 4, 5]), (-7680, [1, 1, 2, 3, 4, 11]), (-6144, [1, 1, 2, 3, 5, 10]), (-4608, [1, 1, 2, 4, 5, 9]), (-1536, [1, 1, 3, 4, 5, 8]), (-960, [1, 2, 2, 2, 2, 3, 4, 6]), (-768, [1, 2, 2, 2, 2, 3, 5, 5]), (-576, [1, 2, 2, 2, 2, 4, 4, 5]), (-5248, [1, 2, 2, 2, 3, 3, 4, 5]), (-960, [1, 2, 2, 2, 3, 4, 4, 4])]

def node78Piece89Output_sector0_chunk1 : RawPoly ℕ := [(-7680, [1, 2, 2, 2, 3, 12]), (-5760, [1, 2, 2, 2, 4, 11]), (-4608, [1, 2, 2, 2, 5, 10]), (-256, [1, 2, 2, 3, 3, 3, 3, 5]), (-960, [1, 2, 2, 3, 3, 3, 4, 4]), (-7680, [1, 2, 2, 3, 3, 11]), (-960, [1, 2, 2, 3, 4, 10]), (-6784, [1, 2, 2, 3, 5, 9]), (-7680, [1, 2, 2, 3, 6, 8]), (-3840, [1, 2, 2, 3, 7, 7]), (-5760, [1, 2, 2, 4, 4, 9]), (-9120, [1, 2, 2, 4, 5, 8]), (-5760, [1, 2, 2, 4, 6, 7]), (-4608, [1, 2, 2, 5, 5, 7]), (-2304, [1, 2, 2, 5, 6, 6]), (-23040, [1, 2, 2, 17]), (-7680, [1, 2, 3, 3, 4, 9]), (-6144, [1, 2, 3, 3, 5, 8]), (-7680, [1, 2, 3, 4, 4, 8]), (-15360, [1, 2, 3, 4, 5, 7]), (-3840, [1, 2, 3, 4, 6, 6]), (-6144, [1, 2, 3, 5, 5, 6]), (-30720, [1, 2, 3, 16]), (-4608, [1, 2, 4, 4, 5, 6])]

def node78Piece89Output_sector0_chunk2 : RawPoly ℕ := [(-2304, [1, 2, 4, 5, 5, 5]), (-23040, [1, 2, 4, 15]), (-18432, [1, 2, 5, 14]), (-1536, [1, 3, 3, 4, 5, 6]), (-1536, [1, 3, 4, 4, 5, 5]), (-7680, [1, 3, 4, 14]), (-6144, [1, 3, 5, 13]), (-4608, [1, 4, 5, 12]), (-64, [2, 2, 2, 2, 2, 3, 4, 5]), (-1920, [2, 2, 2, 3, 4, 9]), (-1536, [2, 2, 2, 3, 5, 8]), (-1152, [2, 2, 2, 4, 5, 7]), (-1920, [2, 2, 3, 3, 4, 8]), (-1536, [2, 2, 3, 3, 5, 7]), (-1920, [2, 2, 3, 4, 4, 7]), (-5248, [2, 2, 3, 4, 5, 6]), (-768, [2, 2, 3, 5, 5, 5]), (-7680, [2, 2, 3, 15]), (-1152, [2, 2, 4, 4, 5, 5]), (-5760, [2, 2, 4, 14]), (-4608, [2, 2, 5, 13]), (-1536, [2, 3, 3, 4, 5, 5]), (-768, [2, 3, 4, 4, 4, 5]), (-7680, [2, 3, 4, 13])]

def node78Piece89Output_sector0_chunk3 : RawPoly ℕ := [(-6144, [2, 3, 5, 12]), (-4608, [2, 4, 5, 11]), (-1536, [3, 4, 5, 10])]

def node78Piece89Output_sector0 : RawPoly ℕ := [node78Piece89Output_sector0_chunk0, node78Piece89Output_sector0_chunk1, node78Piece89Output_sector0_chunk2, node78Piece89Output_sector0_chunk3].flatten

def node78Piece89Output : SectorVector := [(0, node78Piece89Output_sector0)]

def node78Piece89UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 3, 4, 5])]

def node78Piece89UnitInput_sector0 : RawPoly ℕ := [node78Piece89UnitInput_sector0_chunk0].flatten

def node78Piece89UnitInput : SectorVector := [(0, node78Piece89UnitInput_sector0)]

def node78Piece89UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 3, 4, 5]), (60, [1, 1, 1, 2, 2, 3, 4, 8]), (48, [1, 1, 1, 2, 2, 3, 5, 7]), (36, [1, 1, 1, 2, 2, 4, 5, 6]), (48, [1, 1, 1, 2, 3, 4, 5, 5]), (120, [1, 1, 2, 2, 2, 3, 4, 7]), (96, [1, 1, 2, 2, 2, 3, 5, 6]), (72, [1, 1, 2, 2, 2, 4, 5, 5]), (120, [1, 1, 2, 2, 3, 3, 4, 6]), (96, [1, 1, 2, 2, 3, 3, 5, 5]), (342, [1, 1, 2, 2, 3, 4, 4, 5]), (480, [1, 1, 2, 2, 3, 13]), (360, [1, 1, 2, 2, 4, 12]), (288, [1, 1, 2, 2, 5, 11]), (48, [1, 1, 2, 3, 3, 3, 4, 5]), (480, [1, 1, 2, 3, 4, 11]), (384, [1, 1, 2, 3, 5, 10]), (288, [1, 1, 2, 4, 5, 9]), (96, [1, 1, 3, 4, 5, 8]), (60, [1, 2, 2, 2, 2, 3, 4, 6]), (48, [1, 2, 2, 2, 2, 3, 5, 5]), (36, [1, 2, 2, 2, 2, 4, 4, 5]), (328, [1, 2, 2, 2, 3, 3, 4, 5]), (60, [1, 2, 2, 2, 3, 4, 4, 4])]

def node78Piece89UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [1, 2, 2, 2, 3, 12]), (360, [1, 2, 2, 2, 4, 11]), (288, [1, 2, 2, 2, 5, 10]), (16, [1, 2, 2, 3, 3, 3, 3, 5]), (60, [1, 2, 2, 3, 3, 3, 4, 4]), (480, [1, 2, 2, 3, 3, 11]), (60, [1, 2, 2, 3, 4, 10]), (424, [1, 2, 2, 3, 5, 9]), (480, [1, 2, 2, 3, 6, 8]), (240, [1, 2, 2, 3, 7, 7]), (360, [1, 2, 2, 4, 4, 9]), (570, [1, 2, 2, 4, 5, 8]), (360, [1, 2, 2, 4, 6, 7]), (288, [1, 2, 2, 5, 5, 7]), (144, [1, 2, 2, 5, 6, 6]), (1440, [1, 2, 2, 17]), (480, [1, 2, 3, 3, 4, 9]), (384, [1, 2, 3, 3, 5, 8]), (480, [1, 2, 3, 4, 4, 8]), (960, [1, 2, 3, 4, 5, 7]), (240, [1, 2, 3, 4, 6, 6]), (384, [1, 2, 3, 5, 5, 6]), (1920, [1, 2, 3, 16]), (288, [1, 2, 4, 4, 5, 6])]

def node78Piece89UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [1, 2, 4, 5, 5, 5]), (1440, [1, 2, 4, 15]), (1152, [1, 2, 5, 14]), (96, [1, 3, 3, 4, 5, 6]), (96, [1, 3, 4, 4, 5, 5]), (480, [1, 3, 4, 14]), (384, [1, 3, 5, 13]), (288, [1, 4, 5, 12]), (4, [2, 2, 2, 2, 2, 3, 4, 5]), (120, [2, 2, 2, 3, 4, 9]), (96, [2, 2, 2, 3, 5, 8]), (72, [2, 2, 2, 4, 5, 7]), (120, [2, 2, 3, 3, 4, 8]), (96, [2, 2, 3, 3, 5, 7]), (120, [2, 2, 3, 4, 4, 7]), (328, [2, 2, 3, 4, 5, 6]), (48, [2, 2, 3, 5, 5, 5]), (480, [2, 2, 3, 15]), (72, [2, 2, 4, 4, 5, 5]), (360, [2, 2, 4, 14]), (288, [2, 2, 5, 13]), (96, [2, 3, 3, 4, 5, 5]), (48, [2, 3, 4, 4, 4, 5]), (480, [2, 3, 4, 13])]

def node78Piece89UnitOutput_sector0_chunk3 : RawPoly ℕ := [(384, [2, 3, 5, 12]), (288, [2, 4, 5, 11]), (96, [3, 4, 5, 10])]

def node78Piece89UnitOutput_sector0 : RawPoly ℕ := [node78Piece89UnitOutput_sector0_chunk0, node78Piece89UnitOutput_sector0_chunk1, node78Piece89UnitOutput_sector0_chunk2, node78Piece89UnitOutput_sector0_chunk3].flatten

def node78Piece89UnitOutput : SectorVector := [(0, node78Piece89UnitOutput_sector0)]

theorem node78Piece89_check : VectorCertificate (neutralBoundS JR (-2) node78Piece89UnitInput) node78Piece89UnitOutput := by decide +kernel

theorem node78Piece89_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece89Input) = evaluate node78Piece89Output :=
  mode_of_scaled _ _ (-16) node78Piece89UnitInput node78Piece89UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece89_check)

def node78Piece90Input_sector0 : RawPoly ℕ := [(-265/2, [1, 2, 2, 4, 4, 4])]

def node78Piece90Input : SectorVector := [(0, node78Piece90Input_sector0)]
def node78Piece90Output_sector0_chunk0 : RawPoly ℕ := [(-530, [1, 1, 1, 1, 2, 2, 2, 4, 4, 4]), (-19080, [1, 1, 1, 2, 2, 4, 4, 7]), (-6360, [1, 1, 1, 2, 4, 4, 4, 5]), (-38160, [1, 1, 2, 2, 2, 4, 4, 6]), (-38160, [1, 1, 2, 2, 3, 4, 4, 5]), (-32595, [1, 1, 2, 2, 4, 4, 4, 4]), (-152640, [1, 1, 2, 2, 4, 12]), (-6360, [1, 1, 2, 3, 3, 4, 4, 4]), (-152640, [1, 1, 2, 4, 4, 10]), (-12720, [1, 1, 4, 4, 4, 8]), (-19080, [1, 2, 2, 2, 2, 4, 4, 5]), (-48230, [1, 2, 2, 2, 3, 4, 4, 4]), (-152640, [1, 2, 2, 2, 4, 11]), (-6360, [1, 2, 2, 3, 3, 3, 4, 4]), (-152640, [1, 2, 2, 3, 4, 10]), (-15900, [1, 2, 2, 4, 4, 9]), (-152640, [1, 2, 2, 4, 5, 8]), (-152640, [1, 2, 2, 4, 6, 7]), (-203520, [1, 2, 2, 17]), (-152640, [1, 2, 3, 4, 4, 8]), (-127200, [1, 2, 4, 4, 4, 7]), (-152640, [1, 2, 4, 4, 5, 6]), (-610560, [1, 2, 4, 15]), (-12720, [1, 3, 4, 4, 4, 6])]

def node78Piece90Output_sector0_chunk1 : RawPoly ℕ := [(-12720, [1, 4, 4, 4, 4, 5]), (-152640, [1, 4, 4, 13]), (-530, [2, 2, 2, 2, 2, 4, 4, 4]), (-38160, [2, 2, 2, 4, 4, 8]), (-38160, [2, 2, 3, 4, 4, 7]), (-43460, [2, 2, 4, 4, 4, 6]), (-19080, [2, 2, 4, 4, 5, 5]), (-152640, [2, 2, 4, 14]), (-12720, [2, 3, 4, 4, 4, 5]), (-6360, [2, 4, 4, 4, 4, 4]), (-152640, [2, 4, 4, 12]), (-12720, [4, 4, 4, 10])]

def node78Piece90Output_sector0 : RawPoly ℕ := [node78Piece90Output_sector0_chunk0, node78Piece90Output_sector0_chunk1].flatten

def node78Piece90Output : SectorVector := [(0, node78Piece90Output_sector0)]

def node78Piece90UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 4, 4, 4])]

def node78Piece90UnitInput_sector0 : RawPoly ℕ := [node78Piece90UnitInput_sector0_chunk0].flatten

def node78Piece90UnitInput : SectorVector := [(0, node78Piece90UnitInput_sector0)]

def node78Piece90UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 4, 4, 4]), (144, [1, 1, 1, 2, 2, 4, 4, 7]), (48, [1, 1, 1, 2, 4, 4, 4, 5]), (288, [1, 1, 2, 2, 2, 4, 4, 6]), (288, [1, 1, 2, 2, 3, 4, 4, 5]), (246, [1, 1, 2, 2, 4, 4, 4, 4]), (1152, [1, 1, 2, 2, 4, 12]), (48, [1, 1, 2, 3, 3, 4, 4, 4]), (1152, [1, 1, 2, 4, 4, 10]), (96, [1, 1, 4, 4, 4, 8]), (144, [1, 2, 2, 2, 2, 4, 4, 5]), (364, [1, 2, 2, 2, 3, 4, 4, 4]), (1152, [1, 2, 2, 2, 4, 11]), (48, [1, 2, 2, 3, 3, 3, 4, 4]), (1152, [1, 2, 2, 3, 4, 10]), (120, [1, 2, 2, 4, 4, 9]), (1152, [1, 2, 2, 4, 5, 8]), (1152, [1, 2, 2, 4, 6, 7]), (1536, [1, 2, 2, 17]), (1152, [1, 2, 3, 4, 4, 8]), (960, [1, 2, 4, 4, 4, 7]), (1152, [1, 2, 4, 4, 5, 6]), (4608, [1, 2, 4, 15]), (96, [1, 3, 4, 4, 4, 6])]

def node78Piece90UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [1, 4, 4, 4, 4, 5]), (1152, [1, 4, 4, 13]), (4, [2, 2, 2, 2, 2, 4, 4, 4]), (288, [2, 2, 2, 4, 4, 8]), (288, [2, 2, 3, 4, 4, 7]), (328, [2, 2, 4, 4, 4, 6]), (144, [2, 2, 4, 4, 5, 5]), (1152, [2, 2, 4, 14]), (96, [2, 3, 4, 4, 4, 5]), (48, [2, 4, 4, 4, 4, 4]), (1152, [2, 4, 4, 12]), (96, [4, 4, 4, 10])]

def node78Piece90UnitOutput_sector0 : RawPoly ℕ := [node78Piece90UnitOutput_sector0_chunk0, node78Piece90UnitOutput_sector0_chunk1].flatten

def node78Piece90UnitOutput : SectorVector := [(0, node78Piece90UnitOutput_sector0)]

theorem node78Piece90_check : VectorCertificate (neutralBoundS JR (-2) node78Piece90UnitInput) node78Piece90UnitOutput := by decide +kernel

theorem node78Piece90_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece90Input) = evaluate node78Piece90Output :=
  mode_of_scaled _ _ (-265/2) node78Piece90UnitInput node78Piece90UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece90_check)

def node78Piece91Input_sector0 : RawPoly ℕ := [(-110, [1, 2, 2, 12])]

def node78Piece91Input : SectorVector := [(0, node78Piece91Input_sector0)]
def node78Piece91Output_sector0_chunk0 : RawPoly ℕ := [(-440, [1, 1, 1, 1, 2, 2, 2, 12]), (-15840, [1, 1, 1, 2, 2, 15]), (-5280, [1, 1, 1, 2, 5, 12]), (-31680, [1, 1, 2, 2, 2, 14]), (-31680, [1, 1, 2, 2, 3, 13]), (-42900, [1, 1, 2, 2, 4, 12]), (-31680, [1, 1, 2, 2, 5, 11]), (-31680, [1, 1, 2, 2, 6, 10]), (-31680, [1, 1, 2, 2, 7, 9]), (-15840, [1, 1, 2, 2, 8, 8]), (-5280, [1, 1, 2, 3, 3, 12]), (-126720, [1, 1, 2, 18]), (-10560, [1, 1, 8, 12]), (-15840, [1, 2, 2, 2, 2, 13]), (-40040, [1, 2, 2, 2, 3, 12]), (-31680, [1, 2, 2, 2, 4, 11]), (-31680, [1, 2, 2, 2, 5, 10]), (-31680, [1, 2, 2, 2, 6, 9]), (-31680, [1, 2, 2, 2, 7, 8]), (-15840, [1, 2, 2, 3, 3, 11]), (-31680, [1, 2, 2, 3, 4, 10]), (-31680, [1, 2, 2, 3, 5, 9]), (-31680, [1, 2, 2, 3, 6, 8]), (-15840, [1, 2, 2, 3, 7, 7])]

def node78Piece91Output_sector0_chunk1 : RawPoly ℕ := [(-15840, [1, 2, 2, 4, 4, 9]), (-31680, [1, 2, 2, 4, 5, 8]), (-31680, [1, 2, 2, 4, 6, 7]), (-15840, [1, 2, 2, 5, 5, 7]), (-15840, [1, 2, 2, 5, 6, 6]), (1222320, [1, 2, 2, 17]), (-126720, [1, 2, 3, 16]), (-126720, [1, 2, 4, 15]), (-126720, [1, 2, 5, 14]), (-126720, [1, 2, 6, 13]), (-105600, [1, 2, 7, 12]), (-126720, [1, 2, 8, 11]), (-126720, [1, 2, 9, 10]), (-10560, [1, 3, 6, 12]), (-10560, [1, 4, 5, 12]), (-126720, [1, 21]), (-440, [2, 2, 2, 2, 2, 12]), (-31680, [2, 2, 2, 16]), (-31680, [2, 2, 3, 15]), (-31680, [2, 2, 4, 14]), (-31680, [2, 2, 5, 13]), (-36080, [2, 2, 6, 12]), (-31680, [2, 2, 7, 11]), (-31680, [2, 2, 8, 10])]

def node78Piece91Output_sector0_chunk2 : RawPoly ℕ := [(-15840, [2, 2, 9, 9]), (-10560, [2, 3, 5, 12]), (-5280, [2, 4, 4, 12]), (-126720, [2, 20]), (-10560, [10, 12])]

def node78Piece91Output_sector0 : RawPoly ℕ := [node78Piece91Output_sector0_chunk0, node78Piece91Output_sector0_chunk1, node78Piece91Output_sector0_chunk2].flatten

def node78Piece91Output : SectorVector := [(0, node78Piece91Output_sector0)]

def node78Piece91UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 12])]

def node78Piece91UnitInput_sector0 : RawPoly ℕ := [node78Piece91UnitInput_sector0_chunk0].flatten

def node78Piece91UnitInput : SectorVector := [(0, node78Piece91UnitInput_sector0)]

def node78Piece91UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 12]), (144, [1, 1, 1, 2, 2, 15]), (48, [1, 1, 1, 2, 5, 12]), (288, [1, 1, 2, 2, 2, 14]), (288, [1, 1, 2, 2, 3, 13]), (390, [1, 1, 2, 2, 4, 12]), (288, [1, 1, 2, 2, 5, 11]), (288, [1, 1, 2, 2, 6, 10]), (288, [1, 1, 2, 2, 7, 9]), (144, [1, 1, 2, 2, 8, 8]), (48, [1, 1, 2, 3, 3, 12]), (1152, [1, 1, 2, 18]), (96, [1, 1, 8, 12]), (144, [1, 2, 2, 2, 2, 13]), (364, [1, 2, 2, 2, 3, 12]), (288, [1, 2, 2, 2, 4, 11]), (288, [1, 2, 2, 2, 5, 10]), (288, [1, 2, 2, 2, 6, 9]), (288, [1, 2, 2, 2, 7, 8]), (144, [1, 2, 2, 3, 3, 11]), (288, [1, 2, 2, 3, 4, 10]), (288, [1, 2, 2, 3, 5, 9]), (288, [1, 2, 2, 3, 6, 8]), (144, [1, 2, 2, 3, 7, 7])]

def node78Piece91UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [1, 2, 2, 4, 4, 9]), (288, [1, 2, 2, 4, 5, 8]), (288, [1, 2, 2, 4, 6, 7]), (144, [1, 2, 2, 5, 5, 7]), (144, [1, 2, 2, 5, 6, 6]), (-11112, [1, 2, 2, 17]), (1152, [1, 2, 3, 16]), (1152, [1, 2, 4, 15]), (1152, [1, 2, 5, 14]), (1152, [1, 2, 6, 13]), (960, [1, 2, 7, 12]), (1152, [1, 2, 8, 11]), (1152, [1, 2, 9, 10]), (96, [1, 3, 6, 12]), (96, [1, 4, 5, 12]), (1152, [1, 21]), (4, [2, 2, 2, 2, 2, 12]), (288, [2, 2, 2, 16]), (288, [2, 2, 3, 15]), (288, [2, 2, 4, 14]), (288, [2, 2, 5, 13]), (328, [2, 2, 6, 12]), (288, [2, 2, 7, 11]), (288, [2, 2, 8, 10])]

def node78Piece91UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [2, 2, 9, 9]), (96, [2, 3, 5, 12]), (48, [2, 4, 4, 12]), (1152, [2, 20]), (96, [10, 12])]

def node78Piece91UnitOutput_sector0 : RawPoly ℕ := [node78Piece91UnitOutput_sector0_chunk0, node78Piece91UnitOutput_sector0_chunk1, node78Piece91UnitOutput_sector0_chunk2].flatten

def node78Piece91UnitOutput : SectorVector := [(0, node78Piece91UnitOutput_sector0)]

theorem node78Piece91_check : VectorCertificate (neutralBoundS JR (-2) node78Piece91UnitInput) node78Piece91UnitOutput := by decide +kernel

theorem node78Piece91_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece91Input) = evaluate node78Piece91Output :=
  mode_of_scaled _ _ (-110) node78Piece91UnitInput node78Piece91UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece91_check)

def node78Piece92Input_sector0 : RawPoly ℕ := [(7424/27, [1, 2, 3, 3, 3, 5])]

def node78Piece92Input : SectorVector := [(0, node78Piece92Input_sector0)]
def node78Piece92Output_sector0_chunk0 : RawPoly ℕ := [(29696/27, [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]), (148480/9, [1, 1, 1, 2, 3, 3, 3, 8]), (29696, [1, 1, 1, 2, 3, 3, 5, 6]), (59392/9, [1, 1, 1, 3, 3, 3, 5, 5]), (296960/9, [1, 1, 2, 2, 3, 3, 3, 7]), (59392, [1, 1, 2, 2, 3, 3, 5, 5]), (296960/9, [1, 1, 2, 3, 3, 3, 3, 6]), (965120/9, [1, 1, 2, 3, 3, 3, 4, 5]), (296960, [1, 1, 2, 3, 3, 12]), (178176, [1, 1, 2, 3, 5, 10]), (59392/9, [1, 1, 3, 3, 3, 3, 3, 5]), (593920/9, [1, 1, 3, 3, 3, 11]), (118784, [1, 1, 3, 3, 5, 9]), (148480/9, [1, 2, 2, 2, 3, 3, 3, 6]), (29696, [1, 2, 2, 2, 3, 3, 4, 5]), (2078720/27, [1, 2, 2, 3, 3, 3, 3, 5]), (148480/9, [1, 2, 2, 3, 3, 3, 4, 4]), (296960, [1, 2, 2, 3, 3, 11]), (178176, [1, 2, 2, 3, 5, 9]), (148480/9, [1, 2, 3, 3, 3, 3, 3, 4]), (148480/9, [1, 2, 3, 3, 3, 10]), (296960, [1, 2, 3, 3, 4, 9]), (876032/3, [1, 2, 3, 3, 5, 8]), (296960, [1, 2, 3, 3, 6, 7])]

def node78Piece92Output_sector0_chunk1 : RawPoly ℕ := [(178176, [1, 2, 3, 4, 5, 7]), (178176, [1, 2, 3, 5, 5, 6]), (890880, [1, 2, 3, 16]), (178176, [1, 2, 5, 14]), (593920/9, [1, 3, 3, 3, 3, 9]), (593920/9, [1, 3, 3, 3, 4, 8]), (1306624/9, [1, 3, 3, 3, 5, 7]), (296960/9, [1, 3, 3, 3, 6, 6]), (118784, [1, 3, 3, 4, 5, 6]), (59392, [1, 3, 3, 5, 5, 5]), (593920, [1, 3, 3, 15]), (356352, [1, 3, 5, 13]), (29696/27, [2, 2, 2, 2, 3, 3, 3, 5]), (296960/9, [2, 2, 3, 3, 3, 9]), (59392, [2, 2, 3, 3, 5, 7]), (296960/9, [2, 3, 3, 3, 3, 8]), (296960/9, [2, 3, 3, 3, 4, 7]), (2435072/27, [2, 3, 3, 3, 5, 6]), (59392, [2, 3, 3, 4, 5, 5]), (296960, [2, 3, 3, 14]), (178176, [2, 3, 5, 12]), (118784/9, [3, 3, 3, 3, 5, 5]), (59392/9, [3, 3, 3, 4, 4, 5]), (593920/9, [3, 3, 3, 13])]

def node78Piece92Output_sector0_chunk2 : RawPoly ℕ := [(118784, [3, 3, 5, 11])]

def node78Piece92Output_sector0 : RawPoly ℕ := [node78Piece92Output_sector0_chunk0, node78Piece92Output_sector0_chunk1, node78Piece92Output_sector0_chunk2].flatten

def node78Piece92Output : SectorVector := [(0, node78Piece92Output_sector0)]

def node78Piece92UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 3, 3, 3, 5])]

def node78Piece92UnitInput_sector0 : RawPoly ℕ := [node78Piece92UnitInput_sector0_chunk0].flatten

def node78Piece92UnitInput : SectorVector := [(0, node78Piece92UnitInput_sector0)]

def node78Piece92UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]), (60, [1, 1, 1, 2, 3, 3, 3, 8]), (108, [1, 1, 1, 2, 3, 3, 5, 6]), (24, [1, 1, 1, 3, 3, 3, 5, 5]), (120, [1, 1, 2, 2, 3, 3, 3, 7]), (216, [1, 1, 2, 2, 3, 3, 5, 5]), (120, [1, 1, 2, 3, 3, 3, 3, 6]), (390, [1, 1, 2, 3, 3, 3, 4, 5]), (1080, [1, 1, 2, 3, 3, 12]), (648, [1, 1, 2, 3, 5, 10]), (24, [1, 1, 3, 3, 3, 3, 3, 5]), (240, [1, 1, 3, 3, 3, 11]), (432, [1, 1, 3, 3, 5, 9]), (60, [1, 2, 2, 2, 3, 3, 3, 6]), (108, [1, 2, 2, 2, 3, 3, 4, 5]), (280, [1, 2, 2, 3, 3, 3, 3, 5]), (60, [1, 2, 2, 3, 3, 3, 4, 4]), (1080, [1, 2, 2, 3, 3, 11]), (648, [1, 2, 2, 3, 5, 9]), (60, [1, 2, 3, 3, 3, 3, 3, 4]), (60, [1, 2, 3, 3, 3, 10]), (1080, [1, 2, 3, 3, 4, 9]), (1062, [1, 2, 3, 3, 5, 8]), (1080, [1, 2, 3, 3, 6, 7])]

def node78Piece92UnitOutput_sector0_chunk1 : RawPoly ℕ := [(648, [1, 2, 3, 4, 5, 7]), (648, [1, 2, 3, 5, 5, 6]), (3240, [1, 2, 3, 16]), (648, [1, 2, 5, 14]), (240, [1, 3, 3, 3, 3, 9]), (240, [1, 3, 3, 3, 4, 8]), (528, [1, 3, 3, 3, 5, 7]), (120, [1, 3, 3, 3, 6, 6]), (432, [1, 3, 3, 4, 5, 6]), (216, [1, 3, 3, 5, 5, 5]), (2160, [1, 3, 3, 15]), (1296, [1, 3, 5, 13]), (4, [2, 2, 2, 2, 3, 3, 3, 5]), (120, [2, 2, 3, 3, 3, 9]), (216, [2, 2, 3, 3, 5, 7]), (120, [2, 3, 3, 3, 3, 8]), (120, [2, 3, 3, 3, 4, 7]), (328, [2, 3, 3, 3, 5, 6]), (216, [2, 3, 3, 4, 5, 5]), (1080, [2, 3, 3, 14]), (648, [2, 3, 5, 12]), (48, [3, 3, 3, 3, 5, 5]), (24, [3, 3, 3, 4, 4, 5]), (240, [3, 3, 3, 13])]

def node78Piece92UnitOutput_sector0_chunk2 : RawPoly ℕ := [(432, [3, 3, 5, 11])]

def node78Piece92UnitOutput_sector0 : RawPoly ℕ := [node78Piece92UnitOutput_sector0_chunk0, node78Piece92UnitOutput_sector0_chunk1, node78Piece92UnitOutput_sector0_chunk2].flatten

def node78Piece92UnitOutput : SectorVector := [(0, node78Piece92UnitOutput_sector0)]

theorem node78Piece92_check : VectorCertificate (neutralBoundS JR (-2) node78Piece92UnitInput) node78Piece92UnitOutput := by decide +kernel

theorem node78Piece92_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece92Input) = evaluate node78Piece92Output :=
  mode_of_scaled _ _ (7424/27) node78Piece92UnitInput node78Piece92UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece92_check)

def node78Piece93Input_sector0 : RawPoly ℕ := [(160/3, [1, 2, 3, 3, 4, 4])]

def node78Piece93Input : SectorVector := [(0, node78Piece93Input_sector0)]
def node78Piece93Output_sector0_chunk0 : RawPoly ℕ := [(640/3, [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]), (5120, [1, 1, 1, 2, 3, 3, 4, 7]), (3840, [1, 1, 1, 2, 3, 4, 4, 6]), (1280, [1, 1, 1, 3, 3, 4, 4, 5]), (10240, [1, 1, 2, 2, 3, 3, 4, 6]), (7680, [1, 1, 2, 2, 3, 4, 4, 5]), (10240, [1, 1, 2, 3, 3, 3, 4, 5]), (15680, [1, 1, 2, 3, 3, 4, 4, 4]), (20480, [1, 1, 2, 3, 3, 12]), (61440, [1, 1, 2, 3, 4, 11]), (11520, [1, 1, 2, 4, 4, 10]), (1280, [1, 1, 3, 3, 3, 3, 4, 4]), (20480, [1, 1, 3, 3, 4, 10]), (15360, [1, 1, 3, 4, 4, 9]), (5120, [1, 2, 2, 2, 3, 3, 4, 5]), (3840, [1, 2, 2, 2, 3, 4, 4, 4]), (50560/3, [1, 2, 2, 3, 3, 3, 4, 4]), (20480, [1, 2, 2, 3, 3, 11]), (61440, [1, 2, 2, 3, 4, 10]), (11520, [1, 2, 2, 4, 4, 9]), (5120/3, [1, 2, 3, 3, 3, 3, 3, 4]), (20480, [1, 2, 3, 3, 3, 10]), (74240/3, [1, 2, 3, 3, 4, 9]), (20480, [1, 2, 3, 3, 5, 8])]

def node78Piece93Output_sector0_chunk1 : RawPoly ℕ := [(20480, [1, 2, 3, 3, 6, 7]), (49280, [1, 2, 3, 4, 4, 8]), (61440, [1, 2, 3, 4, 5, 7]), (30720, [1, 2, 3, 4, 6, 6]), (122880, [1, 2, 3, 16]), (11520, [1, 2, 4, 4, 4, 7]), (11520, [1, 2, 4, 4, 5, 6]), (92160, [1, 2, 4, 15]), (20480, [1, 3, 3, 3, 4, 8]), (28160, [1, 3, 3, 4, 4, 7]), (20480, [1, 3, 3, 4, 5, 6]), (40960, [1, 3, 3, 15]), (15360, [1, 3, 4, 4, 4, 6]), (7680, [1, 3, 4, 4, 5, 5]), (122880, [1, 3, 4, 14]), (23040, [1, 4, 4, 13]), (640/3, [2, 2, 2, 2, 3, 3, 4, 4]), (10240, [2, 2, 3, 3, 4, 8]), (7680, [2, 2, 3, 4, 4, 7]), (10240, [2, 3, 3, 3, 4, 7]), (52480/3, [2, 3, 3, 4, 4, 6]), (5120, [2, 3, 3, 4, 5, 5]), (20480, [2, 3, 3, 14]), (7680, [2, 3, 4, 4, 4, 5])]

def node78Piece93Output_sector0_chunk2 : RawPoly ℕ := [(61440, [2, 3, 4, 13]), (11520, [2, 4, 4, 12]), (2560, [3, 3, 3, 4, 4, 5]), (1280, [3, 3, 4, 4, 4, 4]), (20480, [3, 3, 4, 12]), (15360, [3, 4, 4, 11])]

def node78Piece93Output_sector0 : RawPoly ℕ := [node78Piece93Output_sector0_chunk0, node78Piece93Output_sector0_chunk1, node78Piece93Output_sector0_chunk2].flatten

def node78Piece93Output : SectorVector := [(0, node78Piece93Output_sector0)]

def node78Piece93UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 3, 3, 4, 4])]

def node78Piece93UnitInput_sector0 : RawPoly ℕ := [node78Piece93UnitInput_sector0_chunk0].flatten

def node78Piece93UnitInput : SectorVector := [(0, node78Piece93UnitInput_sector0)]

def node78Piece93UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]), (96, [1, 1, 1, 2, 3, 3, 4, 7]), (72, [1, 1, 1, 2, 3, 4, 4, 6]), (24, [1, 1, 1, 3, 3, 4, 4, 5]), (192, [1, 1, 2, 2, 3, 3, 4, 6]), (144, [1, 1, 2, 2, 3, 4, 4, 5]), (192, [1, 1, 2, 3, 3, 3, 4, 5]), (294, [1, 1, 2, 3, 3, 4, 4, 4]), (384, [1, 1, 2, 3, 3, 12]), (1152, [1, 1, 2, 3, 4, 11]), (216, [1, 1, 2, 4, 4, 10]), (24, [1, 1, 3, 3, 3, 3, 4, 4]), (384, [1, 1, 3, 3, 4, 10]), (288, [1, 1, 3, 4, 4, 9]), (96, [1, 2, 2, 2, 3, 3, 4, 5]), (72, [1, 2, 2, 2, 3, 4, 4, 4]), (316, [1, 2, 2, 3, 3, 3, 4, 4]), (384, [1, 2, 2, 3, 3, 11]), (1152, [1, 2, 2, 3, 4, 10]), (216, [1, 2, 2, 4, 4, 9]), (32, [1, 2, 3, 3, 3, 3, 3, 4]), (384, [1, 2, 3, 3, 3, 10]), (464, [1, 2, 3, 3, 4, 9]), (384, [1, 2, 3, 3, 5, 8])]

def node78Piece93UnitOutput_sector0_chunk1 : RawPoly ℕ := [(384, [1, 2, 3, 3, 6, 7]), (924, [1, 2, 3, 4, 4, 8]), (1152, [1, 2, 3, 4, 5, 7]), (576, [1, 2, 3, 4, 6, 6]), (2304, [1, 2, 3, 16]), (216, [1, 2, 4, 4, 4, 7]), (216, [1, 2, 4, 4, 5, 6]), (1728, [1, 2, 4, 15]), (384, [1, 3, 3, 3, 4, 8]), (528, [1, 3, 3, 4, 4, 7]), (384, [1, 3, 3, 4, 5, 6]), (768, [1, 3, 3, 15]), (288, [1, 3, 4, 4, 4, 6]), (144, [1, 3, 4, 4, 5, 5]), (2304, [1, 3, 4, 14]), (432, [1, 4, 4, 13]), (4, [2, 2, 2, 2, 3, 3, 4, 4]), (192, [2, 2, 3, 3, 4, 8]), (144, [2, 2, 3, 4, 4, 7]), (192, [2, 3, 3, 3, 4, 7]), (328, [2, 3, 3, 4, 4, 6]), (96, [2, 3, 3, 4, 5, 5]), (384, [2, 3, 3, 14]), (144, [2, 3, 4, 4, 4, 5])]

def node78Piece93UnitOutput_sector0_chunk2 : RawPoly ℕ := [(1152, [2, 3, 4, 13]), (216, [2, 4, 4, 12]), (48, [3, 3, 3, 4, 4, 5]), (24, [3, 3, 4, 4, 4, 4]), (384, [3, 3, 4, 12]), (288, [3, 4, 4, 11])]

def node78Piece93UnitOutput_sector0 : RawPoly ℕ := [node78Piece93UnitOutput_sector0_chunk0, node78Piece93UnitOutput_sector0_chunk1, node78Piece93UnitOutput_sector0_chunk2].flatten

def node78Piece93UnitOutput : SectorVector := [(0, node78Piece93UnitOutput_sector0)]

theorem node78Piece93_check : VectorCertificate (neutralBoundS JR (-2) node78Piece93UnitInput) node78Piece93UnitOutput := by decide +kernel

theorem node78Piece93_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece93Input) = evaluate node78Piece93Output :=
  mode_of_scaled _ _ (160/3) node78Piece93UnitInput node78Piece93UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece93_check)

def node78Piece94Input_sector0 : RawPoly ℕ := [(2880/11, [1, 2, 3, 11])]

def node78Piece94Input : SectorVector := [(0, node78Piece94Input_sector0)]
def node78Piece94Output_sector0_chunk0 : RawPoly ℕ := [(11520/11, [1, 1, 1, 1, 2, 2, 3, 11]), (34560, [1, 1, 1, 2, 3, 14]), (103680/11, [1, 1, 1, 2, 6, 11]), (69120/11, [1, 1, 1, 3, 5, 11]), (69120, [1, 1, 2, 2, 3, 13]), (207360/11, [1, 1, 2, 2, 5, 11]), (69120, [1, 1, 2, 3, 3, 12]), (1123200/11, [1, 1, 2, 3, 4, 11]), (69120, [1, 1, 2, 3, 5, 10]), (69120, [1, 1, 2, 3, 6, 9]), (69120, [1, 1, 2, 3, 7, 8]), (207360, [1, 1, 2, 18]), (69120/11, [1, 1, 3, 3, 3, 11]), (138240, [1, 1, 3, 17]), (414720/11, [1, 1, 9, 11]), (34560, [1, 2, 2, 2, 3, 12]), (103680/11, [1, 2, 2, 2, 4, 11]), (92160, [1, 2, 2, 3, 3, 11]), (69120, [1, 2, 2, 3, 4, 10]), (69120, [1, 2, 2, 3, 5, 9]), (69120, [1, 2, 2, 3, 6, 8]), (34560, [1, 2, 2, 3, 7, 7]), (207360, [1, 2, 2, 17]), (34560, [1, 2, 3, 3, 3, 10])]

def node78Piece94Output_sector0_chunk1 : RawPoly ℕ := [(69120, [1, 2, 3, 3, 4, 9]), (69120, [1, 2, 3, 3, 5, 8]), (69120, [1, 2, 3, 3, 6, 7]), (34560, [1, 2, 3, 4, 4, 8]), (69120, [1, 2, 3, 4, 5, 7]), (34560, [1, 2, 3, 4, 6, 6]), (34560, [1, 2, 3, 5, 5, 6]), (-2194560, [1, 2, 3, 16]), (207360, [1, 2, 4, 15]), (207360, [1, 2, 5, 14]), (207360, [1, 2, 6, 13]), (207360, [1, 2, 7, 12]), (1641600/11, [1, 2, 8, 11]), (207360, [1, 2, 9, 10]), (138240, [1, 3, 3, 15]), (138240, [1, 3, 4, 14]), (138240, [1, 3, 5, 13]), (138240, [1, 3, 6, 12]), (138240, [1, 3, 7, 11]), (138240, [1, 3, 8, 10]), (69120, [1, 3, 9, 9]), (414720/11, [1, 4, 6, 11]), (207360/11, [1, 5, 5, 11]), (414720, [1, 21])]

def node78Piece94Output_sector0_chunk2 : RawPoly ℕ := [(11520/11, [2, 2, 2, 2, 3, 11]), (69120, [2, 2, 3, 15]), (207360/11, [2, 2, 7, 11]), (69120, [2, 3, 3, 14]), (69120, [2, 3, 4, 13]), (69120, [2, 3, 5, 12]), (944640/11, [2, 3, 6, 11]), (69120, [2, 3, 7, 10]), (69120, [2, 3, 8, 9]), (207360/11, [2, 4, 5, 11]), (207360, [2, 20]), (138240/11, [3, 3, 5, 11]), (69120/11, [3, 4, 4, 11]), (138240, [3, 19]), (414720/11, [11, 11])]

def node78Piece94Output_sector0 : RawPoly ℕ := [node78Piece94Output_sector0_chunk0, node78Piece94Output_sector0_chunk1, node78Piece94Output_sector0_chunk2].flatten

def node78Piece94Output : SectorVector := [(0, node78Piece94Output_sector0)]

def node78Piece94UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 3, 11])]

def node78Piece94UnitInput_sector0 : RawPoly ℕ := [node78Piece94UnitInput_sector0_chunk0].flatten

def node78Piece94UnitInput : SectorVector := [(0, node78Piece94UnitInput_sector0)]

def node78Piece94UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 3, 11]), (132, [1, 1, 1, 2, 3, 14]), (36, [1, 1, 1, 2, 6, 11]), (24, [1, 1, 1, 3, 5, 11]), (264, [1, 1, 2, 2, 3, 13]), (72, [1, 1, 2, 2, 5, 11]), (264, [1, 1, 2, 3, 3, 12]), (390, [1, 1, 2, 3, 4, 11]), (264, [1, 1, 2, 3, 5, 10]), (264, [1, 1, 2, 3, 6, 9]), (264, [1, 1, 2, 3, 7, 8]), (792, [1, 1, 2, 18]), (24, [1, 1, 3, 3, 3, 11]), (528, [1, 1, 3, 17]), (144, [1, 1, 9, 11]), (132, [1, 2, 2, 2, 3, 12]), (36, [1, 2, 2, 2, 4, 11]), (352, [1, 2, 2, 3, 3, 11]), (264, [1, 2, 2, 3, 4, 10]), (264, [1, 2, 2, 3, 5, 9]), (264, [1, 2, 2, 3, 6, 8]), (132, [1, 2, 2, 3, 7, 7]), (792, [1, 2, 2, 17]), (132, [1, 2, 3, 3, 3, 10])]

def node78Piece94UnitOutput_sector0_chunk1 : RawPoly ℕ := [(264, [1, 2, 3, 3, 4, 9]), (264, [1, 2, 3, 3, 5, 8]), (264, [1, 2, 3, 3, 6, 7]), (132, [1, 2, 3, 4, 4, 8]), (264, [1, 2, 3, 4, 5, 7]), (132, [1, 2, 3, 4, 6, 6]), (132, [1, 2, 3, 5, 5, 6]), (-8382, [1, 2, 3, 16]), (792, [1, 2, 4, 15]), (792, [1, 2, 5, 14]), (792, [1, 2, 6, 13]), (792, [1, 2, 7, 12]), (570, [1, 2, 8, 11]), (792, [1, 2, 9, 10]), (528, [1, 3, 3, 15]), (528, [1, 3, 4, 14]), (528, [1, 3, 5, 13]), (528, [1, 3, 6, 12]), (528, [1, 3, 7, 11]), (528, [1, 3, 8, 10]), (264, [1, 3, 9, 9]), (144, [1, 4, 6, 11]), (72, [1, 5, 5, 11]), (1584, [1, 21])]

def node78Piece94UnitOutput_sector0_chunk2 : RawPoly ℕ := [(4, [2, 2, 2, 2, 3, 11]), (264, [2, 2, 3, 15]), (72, [2, 2, 7, 11]), (264, [2, 3, 3, 14]), (264, [2, 3, 4, 13]), (264, [2, 3, 5, 12]), (328, [2, 3, 6, 11]), (264, [2, 3, 7, 10]), (264, [2, 3, 8, 9]), (72, [2, 4, 5, 11]), (792, [2, 20]), (48, [3, 3, 5, 11]), (24, [3, 4, 4, 11]), (528, [3, 19]), (144, [11, 11])]

def node78Piece94UnitOutput_sector0 : RawPoly ℕ := [node78Piece94UnitOutput_sector0_chunk0, node78Piece94UnitOutput_sector0_chunk1, node78Piece94UnitOutput_sector0_chunk2].flatten

def node78Piece94UnitOutput : SectorVector := [(0, node78Piece94UnitOutput_sector0)]

theorem node78Piece94_check : VectorCertificate (neutralBoundS JR (-2) node78Piece94UnitInput) node78Piece94UnitOutput := by decide +kernel

theorem node78Piece94_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece94Input) = evaluate node78Piece94Output :=
  mode_of_scaled _ _ (2880/11) node78Piece94UnitInput node78Piece94UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece94_check)

def node78Piece95Input_sector0 : RawPoly ℕ := [(-168, [1, 2, 4, 10])]

def node78Piece95Input : SectorVector := [(0, node78Piece95Input_sector0)]
def node78Piece95Output_sector0_chunk0 : RawPoly ℕ := [(-672, [1, 1, 1, 1, 2, 2, 4, 10]), (-20160, [1, 1, 1, 2, 4, 13]), (-8064, [1, 1, 1, 2, 7, 10]), (-4032, [1, 1, 1, 4, 5, 10]), (-40320, [1, 1, 2, 2, 4, 12]), (-16128, [1, 1, 2, 2, 6, 10]), (-40320, [1, 1, 2, 3, 4, 11]), (-16128, [1, 1, 2, 3, 5, 10]), (-57456, [1, 1, 2, 4, 4, 10]), (-40320, [1, 1, 2, 4, 5, 9]), (-40320, [1, 1, 2, 4, 6, 8]), (-20160, [1, 1, 2, 4, 7, 7]), (-161280, [1, 1, 2, 18]), (-4032, [1, 1, 3, 3, 4, 10]), (-80640, [1, 1, 4, 16]), (-32256, [1, 1, 10, 10]), (-20160, [1, 2, 2, 2, 4, 11]), (-8064, [1, 2, 2, 2, 5, 10]), (-65184, [1, 2, 2, 3, 4, 10]), (-40320, [1, 2, 2, 4, 4, 9]), (-40320, [1, 2, 2, 4, 5, 8]), (-40320, [1, 2, 2, 4, 6, 7]), (-161280, [1, 2, 2, 17]), (-2688, [1, 2, 3, 3, 3, 10])]

def node78Piece95Output_sector0_chunk1 : RawPoly ℕ := [(-20160, [1, 2, 3, 3, 4, 9]), (-40320, [1, 2, 3, 4, 4, 8]), (-40320, [1, 2, 3, 4, 5, 7]), (-20160, [1, 2, 3, 4, 6, 6]), (-161280, [1, 2, 3, 16]), (-20160, [1, 2, 4, 4, 4, 7]), (-40320, [1, 2, 4, 4, 5, 6]), (-6720, [1, 2, 4, 5, 5, 5]), (1021440, [1, 2, 4, 15]), (-161280, [1, 2, 5, 14]), (-161280, [1, 2, 6, 13]), (-161280, [1, 2, 7, 12]), (-161280, [1, 2, 8, 11]), (-71232, [1, 2, 9, 10]), (-80640, [1, 3, 4, 14]), (-32256, [1, 3, 8, 10]), (-80640, [1, 4, 4, 13]), (-80640, [1, 4, 5, 12]), (-80640, [1, 4, 6, 11]), (-88704, [1, 4, 7, 10]), (-80640, [1, 4, 8, 9]), (-32256, [1, 5, 6, 10]), (-322560, [1, 21]), (-672, [2, 2, 2, 2, 4, 10])]

def node78Piece95Output_sector0_chunk2 : RawPoly ℕ := [(-40320, [2, 2, 4, 14]), (-16128, [2, 2, 8, 10]), (-40320, [2, 3, 4, 13]), (-16128, [2, 3, 7, 10]), (-40320, [2, 4, 4, 12]), (-40320, [2, 4, 5, 11]), (-55104, [2, 4, 6, 10]), (-40320, [2, 4, 7, 9]), (-20160, [2, 4, 8, 8]), (-8064, [2, 5, 5, 10]), (-161280, [2, 20]), (-8064, [3, 4, 5, 10]), (-4032, [4, 4, 4, 10]), (-80640, [4, 18]), (-32256, [10, 12])]

def node78Piece95Output_sector0 : RawPoly ℕ := [node78Piece95Output_sector0_chunk0, node78Piece95Output_sector0_chunk1, node78Piece95Output_sector0_chunk2].flatten

def node78Piece95Output : SectorVector := [(0, node78Piece95Output_sector0)]

def node78Piece95UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 4, 10])]

def node78Piece95UnitInput_sector0 : RawPoly ℕ := [node78Piece95UnitInput_sector0_chunk0].flatten

def node78Piece95UnitInput : SectorVector := [(0, node78Piece95UnitInput_sector0)]

def node78Piece95UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 4, 10]), (120, [1, 1, 1, 2, 4, 13]), (48, [1, 1, 1, 2, 7, 10]), (24, [1, 1, 1, 4, 5, 10]), (240, [1, 1, 2, 2, 4, 12]), (96, [1, 1, 2, 2, 6, 10]), (240, [1, 1, 2, 3, 4, 11]), (96, [1, 1, 2, 3, 5, 10]), (342, [1, 1, 2, 4, 4, 10]), (240, [1, 1, 2, 4, 5, 9]), (240, [1, 1, 2, 4, 6, 8]), (120, [1, 1, 2, 4, 7, 7]), (960, [1, 1, 2, 18]), (24, [1, 1, 3, 3, 4, 10]), (480, [1, 1, 4, 16]), (192, [1, 1, 10, 10]), (120, [1, 2, 2, 2, 4, 11]), (48, [1, 2, 2, 2, 5, 10]), (388, [1, 2, 2, 3, 4, 10]), (240, [1, 2, 2, 4, 4, 9]), (240, [1, 2, 2, 4, 5, 8]), (240, [1, 2, 2, 4, 6, 7]), (960, [1, 2, 2, 17]), (16, [1, 2, 3, 3, 3, 10])]

def node78Piece95UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 2, 3, 3, 4, 9]), (240, [1, 2, 3, 4, 4, 8]), (240, [1, 2, 3, 4, 5, 7]), (120, [1, 2, 3, 4, 6, 6]), (960, [1, 2, 3, 16]), (120, [1, 2, 4, 4, 4, 7]), (240, [1, 2, 4, 4, 5, 6]), (40, [1, 2, 4, 5, 5, 5]), (-6080, [1, 2, 4, 15]), (960, [1, 2, 5, 14]), (960, [1, 2, 6, 13]), (960, [1, 2, 7, 12]), (960, [1, 2, 8, 11]), (424, [1, 2, 9, 10]), (480, [1, 3, 4, 14]), (192, [1, 3, 8, 10]), (480, [1, 4, 4, 13]), (480, [1, 4, 5, 12]), (480, [1, 4, 6, 11]), (528, [1, 4, 7, 10]), (480, [1, 4, 8, 9]), (192, [1, 5, 6, 10]), (1920, [1, 21]), (4, [2, 2, 2, 2, 4, 10])]

def node78Piece95UnitOutput_sector0_chunk2 : RawPoly ℕ := [(240, [2, 2, 4, 14]), (96, [2, 2, 8, 10]), (240, [2, 3, 4, 13]), (96, [2, 3, 7, 10]), (240, [2, 4, 4, 12]), (240, [2, 4, 5, 11]), (328, [2, 4, 6, 10]), (240, [2, 4, 7, 9]), (120, [2, 4, 8, 8]), (48, [2, 5, 5, 10]), (960, [2, 20]), (48, [3, 4, 5, 10]), (24, [4, 4, 4, 10]), (480, [4, 18]), (192, [10, 12])]

def node78Piece95UnitOutput_sector0 : RawPoly ℕ := [node78Piece95UnitOutput_sector0_chunk0, node78Piece95UnitOutput_sector0_chunk1, node78Piece95UnitOutput_sector0_chunk2].flatten

def node78Piece95UnitOutput : SectorVector := [(0, node78Piece95UnitOutput_sector0)]

theorem node78Piece95_check : VectorCertificate (neutralBoundS JR (-2) node78Piece95UnitInput) node78Piece95UnitOutput := by decide +kernel

theorem node78Piece95_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece95Input) = evaluate node78Piece95Output :=
  mode_of_scaled _ _ (-168) node78Piece95UnitInput node78Piece95UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece95_check)

end VOA.Classification.COne.OrbC2h
