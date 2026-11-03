import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch12_1
import VOA.Classification.COne.OrbC2hStateNode8
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node12Piece48Input_sector0 : RawPoly ℕ := [(480/13, [1, 13])]

def node12Piece48Input : SectorVector := [(0, node12Piece48Input_sector0)]
def node12Piece48Output_sector0_chunk0 : RawPoly ℕ := [(1920/13, [1, 1, 1, 1, 3, 13]), (2880/13, [1, 1, 1, 2, 2, 13]), (5760, [1, 1, 1, 17]), (11520, [1, 1, 2, 16]), (11520, [1, 1, 3, 15]), (11520, [1, 1, 4, 14]), (11520, [1, 1, 5, 13]), (11520, [1, 1, 6, 12]), (11520, [1, 1, 7, 11]), (11520, [1, 1, 8, 10]), (5760, [1, 1, 9, 9]), (5760, [1, 2, 2, 15]), (11520, [1, 2, 3, 14]), (162720/13, [1, 2, 4, 13]), (11520, [1, 2, 5, 12]), (11520, [1, 2, 6, 11]), (11520, [1, 2, 7, 10]), (11520, [1, 2, 8, 9]), (82560/13, [1, 3, 3, 13]), (11520, [1, 3, 4, 12]), (11520, [1, 3, 5, 11]), (11520, [1, 3, 6, 10]), (11520, [1, 3, 7, 9]), (5760, [1, 3, 8, 8])]

def node12Piece48Output_sector0_chunk1 : RawPoly ℕ := [(5760, [1, 4, 4, 11]), (11520, [1, 4, 5, 10]), (11520, [1, 4, 6, 9]), (11520, [1, 4, 7, 8]), (5760, [1, 5, 5, 9]), (11520, [1, 5, 6, 8]), (5760, [1, 5, 7, 7]), (5760, [1, 6, 6, 7]), (-599040, [1, 19]), (5760/13, [2, 2, 3, 13]), (11520, [2, 18]), (11520, [3, 17]), (11520, [4, 16]), (11520, [5, 15]), (11520, [6, 14]), (115200/13, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node12Piece48Output_sector0 : RawPoly ℕ := [node12Piece48Output_sector0_chunk0, node12Piece48Output_sector0_chunk1].flatten

def node12Piece48Output : SectorVector := [(0, node12Piece48Output_sector0)]

def node12Piece48UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 13])]

def node12Piece48UnitInput_sector0 : RawPoly ℕ := [node12Piece48UnitInput_sector0_chunk0].flatten

def node12Piece48UnitInput : SectorVector := [(0, node12Piece48UnitInput_sector0)]

def node12Piece48UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 13]), (6, [1, 1, 1, 2, 2, 13]), (156, [1, 1, 1, 17]), (312, [1, 1, 2, 16]), (312, [1, 1, 3, 15]), (312, [1, 1, 4, 14]), (312, [1, 1, 5, 13]), (312, [1, 1, 6, 12]), (312, [1, 1, 7, 11]), (312, [1, 1, 8, 10]), (156, [1, 1, 9, 9]), (156, [1, 2, 2, 15]), (312, [1, 2, 3, 14]), (339, [1, 2, 4, 13]), (312, [1, 2, 5, 12]), (312, [1, 2, 6, 11]), (312, [1, 2, 7, 10]), (312, [1, 2, 8, 9]), (172, [1, 3, 3, 13]), (312, [1, 3, 4, 12]), (312, [1, 3, 5, 11]), (312, [1, 3, 6, 10]), (312, [1, 3, 7, 9]), (156, [1, 3, 8, 8])]

def node12Piece48UnitOutput_sector0_chunk1 : RawPoly ℕ := [(156, [1, 4, 4, 11]), (312, [1, 4, 5, 10]), (312, [1, 4, 6, 9]), (312, [1, 4, 7, 8]), (156, [1, 5, 5, 9]), (312, [1, 5, 6, 8]), (156, [1, 5, 7, 7]), (156, [1, 6, 6, 7]), (-16224, [1, 19]), (12, [2, 2, 3, 13]), (312, [2, 18]), (312, [3, 17]), (312, [4, 16]), (312, [5, 15]), (312, [6, 14]), (240, [7, 13]), (312, [8, 12]), (312, [9, 11]), (156, [10, 10])]

def node12Piece48UnitOutput_sector0 : RawPoly ℕ := [node12Piece48UnitOutput_sector0_chunk0, node12Piece48UnitOutput_sector0_chunk1].flatten

def node12Piece48UnitOutput : SectorVector := [(0, node12Piece48UnitOutput_sector0)]

theorem node12Piece48_check : VectorCertificate (neutralBoundS JR (-3) node12Piece48UnitInput) node12Piece48UnitOutput := by decide +kernel

theorem node12Piece48_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece48Input) = evaluate node12Piece48Output :=
  mode_of_scaled _ _ (480/13) node12Piece48UnitInput node12Piece48UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece48_check)

def node12Piece49Input_sector0 : RawPoly ℕ := [(-88, [2, 2, 2, 2, 2, 4])]

def node12Piece49Input : SectorVector := [(0, node12Piece49Input_sector0)]
def node12Piece49Output_sector0 : RawPoly ℕ := [(-352, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-528, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-4224, [1, 1, 2, 2, 2, 2, 2, 8]), (-10560, [1, 1, 2, 2, 2, 2, 4, 6]), (-8448, [1, 2, 2, 2, 2, 2, 2, 7]), (-8448, [1, 2, 2, 2, 2, 2, 3, 6]), (-28512, [1, 2, 2, 2, 2, 2, 4, 5]), (-21120, [1, 2, 2, 2, 2, 3, 4, 4]), (-84480, [1, 2, 2, 2, 2, 11]), (-84480, [1, 2, 2, 2, 4, 9]), (-4224, [2, 2, 2, 2, 2, 2, 2, 6]), (-8448, [2, 2, 2, 2, 2, 2, 3, 5]), (-15048, [2, 2, 2, 2, 2, 2, 4, 4]), (-15136, [2, 2, 2, 2, 2, 3, 3, 4]), (-1056, [2, 2, 2, 2, 2, 10]), (-84480, [2, 2, 2, 2, 3, 9]), (-66000, [2, 2, 2, 2, 4, 8]), (-84480, [2, 2, 2, 2, 5, 7]), (-42240, [2, 2, 2, 2, 6, 6]), (-84480, [2, 2, 2, 3, 4, 7]), (-84480, [2, 2, 2, 4, 4, 6]), (-42240, [2, 2, 2, 4, 5, 5]), (-337920, [2, 2, 2, 14]), (-168960, [2, 2, 4, 12])]

def node12Piece49Output : SectorVector := [(0, node12Piece49Output_sector0)]

def node12Piece49UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 4])]

def node12Piece49UnitInput_sector0 : RawPoly ℕ := [node12Piece49UnitInput_sector0_chunk0].flatten

def node12Piece49UnitInput : SectorVector := [(0, node12Piece49UnitInput_sector0)]

def node12Piece49UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (48, [1, 1, 2, 2, 2, 2, 2, 8]), (120, [1, 1, 2, 2, 2, 2, 4, 6]), (96, [1, 2, 2, 2, 2, 2, 2, 7]), (96, [1, 2, 2, 2, 2, 2, 3, 6]), (324, [1, 2, 2, 2, 2, 2, 4, 5]), (240, [1, 2, 2, 2, 2, 3, 4, 4]), (960, [1, 2, 2, 2, 2, 11]), (960, [1, 2, 2, 2, 4, 9]), (48, [2, 2, 2, 2, 2, 2, 2, 6]), (96, [2, 2, 2, 2, 2, 2, 3, 5]), (171, [2, 2, 2, 2, 2, 2, 4, 4]), (172, [2, 2, 2, 2, 2, 3, 3, 4]), (12, [2, 2, 2, 2, 2, 10]), (960, [2, 2, 2, 2, 3, 9]), (750, [2, 2, 2, 2, 4, 8]), (960, [2, 2, 2, 2, 5, 7]), (480, [2, 2, 2, 2, 6, 6]), (960, [2, 2, 2, 3, 4, 7]), (960, [2, 2, 2, 4, 4, 6]), (480, [2, 2, 2, 4, 5, 5]), (3840, [2, 2, 2, 14]), (1920, [2, 2, 4, 12])]

def node12Piece49UnitOutput_sector0 : RawPoly ℕ := [node12Piece49UnitOutput_sector0_chunk0].flatten

def node12Piece49UnitOutput : SectorVector := [(0, node12Piece49UnitOutput_sector0)]

theorem node12Piece49_check : VectorCertificate (neutralBoundS JR (-3) node12Piece49UnitInput) node12Piece49UnitOutput := by decide +kernel

theorem node12Piece49_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece49Input) = evaluate node12Piece49Output :=
  mode_of_scaled _ _ (-88) node12Piece49UnitInput node12Piece49UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece49_check)

def node12Piece50Input_sector0 : RawPoly ℕ := [(-160/3, [2, 2, 2, 2, 3, 3])]

def node12Piece50Input : SectorVector := [(0, node12Piece50Input_sector0)]
def node12Piece50Output_sector0_chunk0 : RawPoly ℕ := [(-640/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (-320, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-3840, [1, 1, 2, 2, 2, 2, 3, 7]), (-5120, [1, 1, 2, 2, 2, 3, 3, 6]), (-7680, [1, 2, 2, 2, 2, 2, 3, 6]), (-17280, [1, 2, 2, 2, 2, 3, 3, 5]), (-3840, [1, 2, 2, 2, 2, 3, 4, 4]), (-11520, [1, 2, 2, 2, 2, 11]), (-10240, [1, 2, 2, 2, 3, 3, 3, 4]), (-61440, [1, 2, 2, 2, 3, 10]), (-30720, [1, 2, 2, 3, 3, 9]), (-3840, [2, 2, 2, 2, 2, 2, 3, 5]), (-12960, [2, 2, 2, 2, 2, 3, 3, 4]), (-11520, [2, 2, 2, 2, 2, 10]), (-19840/3, [2, 2, 2, 2, 3, 3, 3, 3]), (-17920, [2, 2, 2, 2, 3, 9]), (-11520, [2, 2, 2, 2, 4, 8]), (-11520, [2, 2, 2, 2, 5, 7]), (-5760, [2, 2, 2, 2, 6, 6]), (-42240, [2, 2, 2, 3, 3, 8]), (-61440, [2, 2, 2, 3, 4, 7]), (-61440, [2, 2, 2, 3, 5, 6]), (-92160, [2, 2, 2, 14]), (-30720, [2, 2, 3, 3, 3, 7])]

def node12Piece50Output_sector0_chunk1 : RawPoly ℕ := [(-30720, [2, 2, 3, 3, 4, 6]), (-15360, [2, 2, 3, 3, 5, 5]), (-184320, [2, 2, 3, 13]), (-40960, [2, 3, 3, 12])]

def node12Piece50Output_sector0 : RawPoly ℕ := [node12Piece50Output_sector0_chunk0, node12Piece50Output_sector0_chunk1].flatten

def node12Piece50Output : SectorVector := [(0, node12Piece50Output_sector0)]

def node12Piece50UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 3, 3])]

def node12Piece50UnitInput_sector0 : RawPoly ℕ := [node12Piece50UnitInput_sector0_chunk0].flatten

def node12Piece50UnitInput : SectorVector := [(0, node12Piece50UnitInput_sector0)]

def node12Piece50UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (6, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (72, [1, 1, 2, 2, 2, 2, 3, 7]), (96, [1, 1, 2, 2, 2, 3, 3, 6]), (144, [1, 2, 2, 2, 2, 2, 3, 6]), (324, [1, 2, 2, 2, 2, 3, 3, 5]), (72, [1, 2, 2, 2, 2, 3, 4, 4]), (216, [1, 2, 2, 2, 2, 11]), (192, [1, 2, 2, 2, 3, 3, 3, 4]), (1152, [1, 2, 2, 2, 3, 10]), (576, [1, 2, 2, 3, 3, 9]), (72, [2, 2, 2, 2, 2, 2, 3, 5]), (243, [2, 2, 2, 2, 2, 3, 3, 4]), (216, [2, 2, 2, 2, 2, 10]), (124, [2, 2, 2, 2, 3, 3, 3, 3]), (336, [2, 2, 2, 2, 3, 9]), (216, [2, 2, 2, 2, 4, 8]), (216, [2, 2, 2, 2, 5, 7]), (108, [2, 2, 2, 2, 6, 6]), (792, [2, 2, 2, 3, 3, 8]), (1152, [2, 2, 2, 3, 4, 7]), (1152, [2, 2, 2, 3, 5, 6]), (1728, [2, 2, 2, 14]), (576, [2, 2, 3, 3, 3, 7])]

def node12Piece50UnitOutput_sector0_chunk1 : RawPoly ℕ := [(576, [2, 2, 3, 3, 4, 6]), (288, [2, 2, 3, 3, 5, 5]), (3456, [2, 2, 3, 13]), (768, [2, 3, 3, 12])]

def node12Piece50UnitOutput_sector0 : RawPoly ℕ := [node12Piece50UnitOutput_sector0_chunk0, node12Piece50UnitOutput_sector0_chunk1].flatten

def node12Piece50UnitOutput : SectorVector := [(0, node12Piece50UnitOutput_sector0)]

theorem node12Piece50_check : VectorCertificate (neutralBoundS JR (-3) node12Piece50UnitInput) node12Piece50UnitOutput := by decide +kernel

theorem node12Piece50_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece50Input) = evaluate node12Piece50Output :=
  mode_of_scaled _ _ (-160/3) node12Piece50UnitInput node12Piece50UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece50_check)

def node12Piece51Input_sector0 : RawPoly ℕ := [(-180, [2, 2, 2, 8])]

def node12Piece51Input : SectorVector := [(0, node12Piece51Input_sector0)]
def node12Piece51Output_sector0_chunk0 : RawPoly ℕ := [(-720, [1, 1, 1, 2, 2, 2, 3, 8]), (-1080, [1, 1, 2, 2, 2, 2, 2, 8]), (-17280, [1, 1, 2, 2, 2, 12]), (-12960, [1, 1, 2, 2, 6, 8]), (-34560, [1, 2, 2, 2, 2, 11]), (-34560, [1, 2, 2, 2, 3, 10]), (-34560, [1, 2, 2, 2, 4, 9]), (-58320, [1, 2, 2, 2, 5, 8]), (-34560, [1, 2, 2, 2, 6, 7]), (-25920, [1, 2, 2, 3, 4, 8]), (-207360, [1, 2, 2, 15]), (-51840, [1, 2, 8, 9]), (-17280, [2, 2, 2, 2, 2, 10]), (-34560, [2, 2, 2, 2, 3, 9]), (-48060, [2, 2, 2, 2, 4, 8]), (-34560, [2, 2, 2, 2, 5, 7]), (-17280, [2, 2, 2, 2, 6, 6]), (-30960, [2, 2, 2, 3, 3, 8]), (-34560, [2, 2, 2, 3, 4, 7]), (-34560, [2, 2, 2, 3, 5, 6]), (-17280, [2, 2, 2, 4, 4, 6]), (-17280, [2, 2, 2, 4, 5, 5]), (652320, [2, 2, 2, 14]), (-207360, [2, 2, 3, 13])]

def node12Piece51Output_sector0_chunk1 : RawPoly ℕ := [(-207360, [2, 2, 4, 12]), (-207360, [2, 2, 5, 11]), (-207360, [2, 2, 6, 10]), (-207360, [2, 2, 7, 9]), (-29160, [2, 2, 8, 8]), (-51840, [2, 3, 7, 8]), (-51840, [2, 4, 6, 8]), (-25920, [2, 5, 5, 8]), (-414720, [2, 18]), (-34560, [8, 12])]

def node12Piece51Output_sector0 : RawPoly ℕ := [node12Piece51Output_sector0_chunk0, node12Piece51Output_sector0_chunk1].flatten

def node12Piece51Output : SectorVector := [(0, node12Piece51Output_sector0)]

def node12Piece51UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 8])]

def node12Piece51UnitInput_sector0 : RawPoly ℕ := [node12Piece51UnitInput_sector0_chunk0].flatten

def node12Piece51UnitInput : SectorVector := [(0, node12Piece51UnitInput_sector0)]

def node12Piece51UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 3, 8]), (6, [1, 1, 2, 2, 2, 2, 2, 8]), (96, [1, 1, 2, 2, 2, 12]), (72, [1, 1, 2, 2, 6, 8]), (192, [1, 2, 2, 2, 2, 11]), (192, [1, 2, 2, 2, 3, 10]), (192, [1, 2, 2, 2, 4, 9]), (324, [1, 2, 2, 2, 5, 8]), (192, [1, 2, 2, 2, 6, 7]), (144, [1, 2, 2, 3, 4, 8]), (1152, [1, 2, 2, 15]), (288, [1, 2, 8, 9]), (96, [2, 2, 2, 2, 2, 10]), (192, [2, 2, 2, 2, 3, 9]), (267, [2, 2, 2, 2, 4, 8]), (192, [2, 2, 2, 2, 5, 7]), (96, [2, 2, 2, 2, 6, 6]), (172, [2, 2, 2, 3, 3, 8]), (192, [2, 2, 2, 3, 4, 7]), (192, [2, 2, 2, 3, 5, 6]), (96, [2, 2, 2, 4, 4, 6]), (96, [2, 2, 2, 4, 5, 5]), (-3624, [2, 2, 2, 14]), (1152, [2, 2, 3, 13])]

def node12Piece51UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1152, [2, 2, 4, 12]), (1152, [2, 2, 5, 11]), (1152, [2, 2, 6, 10]), (1152, [2, 2, 7, 9]), (162, [2, 2, 8, 8]), (288, [2, 3, 7, 8]), (288, [2, 4, 6, 8]), (144, [2, 5, 5, 8]), (2304, [2, 18]), (192, [8, 12])]

def node12Piece51UnitOutput_sector0 : RawPoly ℕ := [node12Piece51UnitOutput_sector0_chunk0, node12Piece51UnitOutput_sector0_chunk1].flatten

def node12Piece51UnitOutput : SectorVector := [(0, node12Piece51UnitOutput_sector0)]

theorem node12Piece51_check : VectorCertificate (neutralBoundS JR (-3) node12Piece51UnitInput) node12Piece51UnitOutput := by decide +kernel

theorem node12Piece51_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece51Input) = evaluate node12Piece51Output :=
  mode_of_scaled _ _ (-180) node12Piece51UnitInput node12Piece51UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece51_check)

def node12Piece52Input_sector0 : RawPoly ℕ := [(-480/7, [2, 2, 3, 7])]

def node12Piece52Input : SectorVector := [(0, node12Piece52Input_sector0)]
def node12Piece52Output_sector0_chunk0 : RawPoly ℕ := [(-1920/7, [1, 1, 1, 2, 2, 3, 3, 7]), (-2880/7, [1, 1, 2, 2, 2, 2, 3, 7]), (-5760, [1, 1, 2, 2, 3, 11]), (-17280/7, [1, 1, 2, 2, 7, 7]), (-23040/7, [1, 1, 2, 3, 6, 7]), (-11520, [1, 2, 2, 2, 3, 10]), (-34560/7, [1, 2, 2, 2, 6, 7]), (-11520, [1, 2, 2, 3, 3, 9]), (-11520, [1, 2, 2, 3, 4, 8]), (-155520/7, [1, 2, 2, 3, 5, 7]), (-5760, [1, 2, 2, 3, 6, 6]), (-17280/7, [1, 2, 2, 4, 4, 7]), (-34560, [1, 2, 2, 15]), (-46080/7, [1, 2, 3, 3, 4, 7]), (-46080, [1, 2, 3, 14]), (-138240/7, [1, 2, 7, 10]), (-46080/7, [1, 3, 7, 9]), (-5760, [2, 2, 2, 2, 3, 9]), (-17280/7, [2, 2, 2, 2, 5, 7]), (-11520, [2, 2, 2, 3, 3, 8]), (-139680/7, [2, 2, 2, 3, 4, 7]), (-11520, [2, 2, 2, 3, 5, 6]), (-34560, [2, 2, 2, 14]), (-71040/7, [2, 2, 3, 3, 3, 7])]

def node12Piece52Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 2, 3, 3, 4, 6]), (-5760, [2, 2, 3, 3, 5, 5]), (-5760, [2, 2, 3, 4, 4, 5]), (155520, [2, 2, 3, 13]), (-34560, [2, 2, 4, 12]), (-34560, [2, 2, 5, 11]), (-34560, [2, 2, 6, 10]), (-132480/7, [2, 2, 7, 9]), (-17280, [2, 2, 8, 8]), (-46080, [2, 3, 3, 12]), (-46080, [2, 3, 4, 11]), (-46080, [2, 3, 5, 10]), (-46080, [2, 3, 6, 9]), (-40320, [2, 3, 7, 8]), (-138240/7, [2, 4, 7, 7]), (-138240/7, [2, 5, 6, 7]), (-138240, [2, 18]), (-46080/7, [3, 3, 7, 7]), (-46080/7, [3, 4, 6, 7]), (-23040/7, [3, 5, 5, 7]), (-46080, [3, 17]), (-138240/7, [7, 13])]

def node12Piece52Output_sector0 : RawPoly ℕ := [node12Piece52Output_sector0_chunk0, node12Piece52Output_sector0_chunk1].flatten

def node12Piece52Output : SectorVector := [(0, node12Piece52Output_sector0)]

def node12Piece52UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 7])]

def node12Piece52UnitInput_sector0 : RawPoly ℕ := [node12Piece52UnitInput_sector0_chunk0].flatten

def node12Piece52UnitInput : SectorVector := [(0, node12Piece52UnitInput_sector0)]

def node12Piece52UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 3, 7]), (6, [1, 1, 2, 2, 2, 2, 3, 7]), (84, [1, 1, 2, 2, 3, 11]), (36, [1, 1, 2, 2, 7, 7]), (48, [1, 1, 2, 3, 6, 7]), (168, [1, 2, 2, 2, 3, 10]), (72, [1, 2, 2, 2, 6, 7]), (168, [1, 2, 2, 3, 3, 9]), (168, [1, 2, 2, 3, 4, 8]), (324, [1, 2, 2, 3, 5, 7]), (84, [1, 2, 2, 3, 6, 6]), (36, [1, 2, 2, 4, 4, 7]), (504, [1, 2, 2, 15]), (96, [1, 2, 3, 3, 4, 7]), (672, [1, 2, 3, 14]), (288, [1, 2, 7, 10]), (96, [1, 3, 7, 9]), (84, [2, 2, 2, 2, 3, 9]), (36, [2, 2, 2, 2, 5, 7]), (168, [2, 2, 2, 3, 3, 8]), (291, [2, 2, 2, 3, 4, 7]), (168, [2, 2, 2, 3, 5, 6]), (504, [2, 2, 2, 14]), (148, [2, 2, 3, 3, 3, 7])]

def node12Piece52UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [2, 2, 3, 3, 4, 6]), (84, [2, 2, 3, 3, 5, 5]), (84, [2, 2, 3, 4, 4, 5]), (-2268, [2, 2, 3, 13]), (504, [2, 2, 4, 12]), (504, [2, 2, 5, 11]), (504, [2, 2, 6, 10]), (276, [2, 2, 7, 9]), (252, [2, 2, 8, 8]), (672, [2, 3, 3, 12]), (672, [2, 3, 4, 11]), (672, [2, 3, 5, 10]), (672, [2, 3, 6, 9]), (588, [2, 3, 7, 8]), (288, [2, 4, 7, 7]), (288, [2, 5, 6, 7]), (2016, [2, 18]), (96, [3, 3, 7, 7]), (96, [3, 4, 6, 7]), (48, [3, 5, 5, 7]), (672, [3, 17]), (288, [7, 13])]

def node12Piece52UnitOutput_sector0 : RawPoly ℕ := [node12Piece52UnitOutput_sector0_chunk0, node12Piece52UnitOutput_sector0_chunk1].flatten

def node12Piece52UnitOutput : SectorVector := [(0, node12Piece52UnitOutput_sector0)]

theorem node12Piece52_check : VectorCertificate (neutralBoundS JR (-3) node12Piece52UnitInput) node12Piece52UnitOutput := by decide +kernel

theorem node12Piece52_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece52Input) = evaluate node12Piece52Output :=
  mode_of_scaled _ _ (-480/7) node12Piece52UnitInput node12Piece52UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece52_check)

def node12Piece53Input_sector0 : RawPoly ℕ := [(-280, [2, 2, 4, 6])]

def node12Piece53Input : SectorVector := [(0, node12Piece53Input_sector0)]
def node12Piece53Output_sector0_chunk0 : RawPoly ℕ := [(-1120, [1, 1, 1, 2, 2, 3, 4, 6]), (-1680, [1, 1, 2, 2, 2, 2, 4, 6]), (-20160, [1, 1, 2, 2, 4, 10]), (-13440, [1, 1, 2, 2, 6, 8]), (-13440, [1, 1, 2, 4, 6, 6]), (-40320, [1, 2, 2, 2, 4, 9]), (-26880, [1, 2, 2, 2, 6, 7]), (-40320, [1, 2, 2, 3, 4, 8]), (-26880, [1, 2, 2, 3, 6, 6]), (-40320, [1, 2, 2, 4, 4, 7]), (-90720, [1, 2, 2, 4, 5, 6]), (-161280, [1, 2, 2, 15]), (-26880, [1, 2, 3, 4, 4, 6]), (-161280, [1, 2, 4, 13]), (-107520, [1, 2, 6, 11]), (-26880, [1, 4, 6, 9]), (-20160, [2, 2, 2, 2, 4, 8]), (-13440, [2, 2, 2, 2, 6, 6]), (-40320, [2, 2, 2, 3, 4, 7]), (-26880, [2, 2, 2, 3, 5, 6]), (-68040, [2, 2, 2, 4, 4, 6]), (-20160, [2, 2, 2, 4, 5, 5]), (-161280, [2, 2, 2, 14]), (-48160, [2, 2, 3, 3, 4, 6])]

def node12Piece53Output_sector0_chunk1 : RawPoly ℕ := [(-40320, [2, 2, 3, 4, 4, 5]), (-161280, [2, 2, 3, 13]), (-6720, [2, 2, 4, 4, 4, 4]), (344400, [2, 2, 4, 12]), (-161280, [2, 2, 5, 11]), (-3360, [2, 2, 6, 10]), (-161280, [2, 2, 7, 9]), (-80640, [2, 2, 8, 8]), (-161280, [2, 3, 4, 11]), (-107520, [2, 3, 6, 9]), (-161280, [2, 4, 4, 10]), (-161280, [2, 4, 5, 9]), (-164640, [2, 4, 6, 8]), (-80640, [2, 4, 7, 7]), (-107520, [2, 5, 6, 7]), (-53760, [2, 6, 6, 6]), (-645120, [2, 18]), (-26880, [3, 4, 6, 7]), (-26880, [4, 4, 6, 6]), (-13440, [4, 5, 5, 6]), (-161280, [4, 16]), (-107520, [6, 14])]

def node12Piece53Output_sector0 : RawPoly ℕ := [node12Piece53Output_sector0_chunk0, node12Piece53Output_sector0_chunk1].flatten

def node12Piece53Output : SectorVector := [(0, node12Piece53Output_sector0)]

def node12Piece53UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 4, 6])]

def node12Piece53UnitInput_sector0 : RawPoly ℕ := [node12Piece53UnitInput_sector0_chunk0].flatten

def node12Piece53UnitInput : SectorVector := [(0, node12Piece53UnitInput_sector0)]

def node12Piece53UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 4, 6]), (6, [1, 1, 2, 2, 2, 2, 4, 6]), (72, [1, 1, 2, 2, 4, 10]), (48, [1, 1, 2, 2, 6, 8]), (48, [1, 1, 2, 4, 6, 6]), (144, [1, 2, 2, 2, 4, 9]), (96, [1, 2, 2, 2, 6, 7]), (144, [1, 2, 2, 3, 4, 8]), (96, [1, 2, 2, 3, 6, 6]), (144, [1, 2, 2, 4, 4, 7]), (324, [1, 2, 2, 4, 5, 6]), (576, [1, 2, 2, 15]), (96, [1, 2, 3, 4, 4, 6]), (576, [1, 2, 4, 13]), (384, [1, 2, 6, 11]), (96, [1, 4, 6, 9]), (72, [2, 2, 2, 2, 4, 8]), (48, [2, 2, 2, 2, 6, 6]), (144, [2, 2, 2, 3, 4, 7]), (96, [2, 2, 2, 3, 5, 6]), (243, [2, 2, 2, 4, 4, 6]), (72, [2, 2, 2, 4, 5, 5]), (576, [2, 2, 2, 14]), (172, [2, 2, 3, 3, 4, 6])]

def node12Piece53UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [2, 2, 3, 4, 4, 5]), (576, [2, 2, 3, 13]), (24, [2, 2, 4, 4, 4, 4]), (-1230, [2, 2, 4, 12]), (576, [2, 2, 5, 11]), (12, [2, 2, 6, 10]), (576, [2, 2, 7, 9]), (288, [2, 2, 8, 8]), (576, [2, 3, 4, 11]), (384, [2, 3, 6, 9]), (576, [2, 4, 4, 10]), (576, [2, 4, 5, 9]), (588, [2, 4, 6, 8]), (288, [2, 4, 7, 7]), (384, [2, 5, 6, 7]), (192, [2, 6, 6, 6]), (2304, [2, 18]), (96, [3, 4, 6, 7]), (96, [4, 4, 6, 6]), (48, [4, 5, 5, 6]), (576, [4, 16]), (384, [6, 14])]

def node12Piece53UnitOutput_sector0 : RawPoly ℕ := [node12Piece53UnitOutput_sector0_chunk0, node12Piece53UnitOutput_sector0_chunk1].flatten

def node12Piece53UnitOutput : SectorVector := [(0, node12Piece53UnitOutput_sector0)]

theorem node12Piece53_check : VectorCertificate (neutralBoundS JR (-3) node12Piece53UnitInput) node12Piece53UnitOutput := by decide +kernel

theorem node12Piece53_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece53Input) = evaluate node12Piece53Output :=
  mode_of_scaled _ _ (-280) node12Piece53UnitInput node12Piece53UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece53_check)

def node12Piece54Input_sector0 : RawPoly ℕ := [(-384/5, [2, 2, 5, 5])]

def node12Piece54Input : SectorVector := [(0, node12Piece54Input_sector0)]
def node12Piece54Output_sector0_chunk0 : RawPoly ℕ := [(-1536/5, [1, 1, 1, 2, 2, 3, 5, 5]), (-2304/5, [1, 1, 2, 2, 2, 2, 5, 5]), (-9216, [1, 1, 2, 2, 5, 9]), (-18432/5, [1, 1, 2, 5, 5, 6]), (-18432, [1, 2, 2, 2, 5, 8]), (-18432, [1, 2, 2, 3, 5, 7]), (-18432, [1, 2, 2, 4, 5, 6]), (-78336/5, [1, 2, 2, 5, 5, 5]), (-46080, [1, 2, 2, 15]), (-36864/5, [1, 2, 3, 4, 5, 5]), (-73728, [1, 2, 5, 12]), (-36864/5, [1, 5, 5, 9]), (-9216, [2, 2, 2, 2, 5, 7]), (-18432, [2, 2, 2, 3, 5, 6]), (-111744/5, [2, 2, 2, 4, 5, 5]), (-46080, [2, 2, 2, 14]), (-66048/5, [2, 2, 3, 3, 5, 5]), (-9216, [2, 2, 3, 4, 4, 5]), (-46080, [2, 2, 3, 13]), (-46080, [2, 2, 4, 12]), (119808, [2, 2, 5, 11]), (-46080, [2, 2, 6, 10]), (-46080, [2, 2, 7, 9]), (-23040, [2, 2, 8, 8])]

def node12Piece54Output_sector0_chunk1 : RawPoly ℕ := [(-73728, [2, 3, 5, 10]), (-73728, [2, 4, 5, 9]), (-225792/5, [2, 5, 5, 8]), (-73728, [2, 5, 6, 7]), (-184320, [2, 18]), (-36864/5, [3, 5, 5, 7]), (-36864/5, [4, 5, 5, 6]), (-18432/5, [5, 5, 5, 5]), (-73728, [5, 15])]

def node12Piece54Output_sector0 : RawPoly ℕ := [node12Piece54Output_sector0_chunk0, node12Piece54Output_sector0_chunk1].flatten

def node12Piece54Output : SectorVector := [(0, node12Piece54Output_sector0)]

def node12Piece54UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 5, 5])]

def node12Piece54UnitInput_sector0 : RawPoly ℕ := [node12Piece54UnitInput_sector0_chunk0].flatten

def node12Piece54UnitInput : SectorVector := [(0, node12Piece54UnitInput_sector0)]

def node12Piece54UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 5, 5]), (6, [1, 1, 2, 2, 2, 2, 5, 5]), (120, [1, 1, 2, 2, 5, 9]), (48, [1, 1, 2, 5, 5, 6]), (240, [1, 2, 2, 2, 5, 8]), (240, [1, 2, 2, 3, 5, 7]), (240, [1, 2, 2, 4, 5, 6]), (204, [1, 2, 2, 5, 5, 5]), (600, [1, 2, 2, 15]), (96, [1, 2, 3, 4, 5, 5]), (960, [1, 2, 5, 12]), (96, [1, 5, 5, 9]), (120, [2, 2, 2, 2, 5, 7]), (240, [2, 2, 2, 3, 5, 6]), (291, [2, 2, 2, 4, 5, 5]), (600, [2, 2, 2, 14]), (172, [2, 2, 3, 3, 5, 5]), (120, [2, 2, 3, 4, 4, 5]), (600, [2, 2, 3, 13]), (600, [2, 2, 4, 12]), (-1560, [2, 2, 5, 11]), (600, [2, 2, 6, 10]), (600, [2, 2, 7, 9]), (300, [2, 2, 8, 8])]

def node12Piece54UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [2, 3, 5, 10]), (960, [2, 4, 5, 9]), (588, [2, 5, 5, 8]), (960, [2, 5, 6, 7]), (2400, [2, 18]), (96, [3, 5, 5, 7]), (96, [4, 5, 5, 6]), (48, [5, 5, 5, 5]), (960, [5, 15])]

def node12Piece54UnitOutput_sector0 : RawPoly ℕ := [node12Piece54UnitOutput_sector0_chunk0, node12Piece54UnitOutput_sector0_chunk1].flatten

def node12Piece54UnitOutput : SectorVector := [(0, node12Piece54UnitOutput_sector0)]

theorem node12Piece54_check : VectorCertificate (neutralBoundS JR (-3) node12Piece54UnitInput) node12Piece54UnitOutput := by decide +kernel

theorem node12Piece54_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece54Input) = evaluate node12Piece54Output :=
  mode_of_scaled _ _ (-384/5) node12Piece54UnitInput node12Piece54UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece54_check)

def node12Piece55Input_sector0 : RawPoly ℕ := [(160, [2, 3, 3, 6])]

def node12Piece55Input : SectorVector := [(0, node12Piece55Input_sector0)]
def node12Piece55Output_sector0_chunk0 : RawPoly ℕ := [(640, [1, 1, 1, 2, 3, 3, 3, 6]), (960, [1, 1, 2, 2, 2, 3, 3, 6]), (11520, [1, 1, 2, 3, 3, 10]), (11520, [1, 1, 2, 3, 6, 7]), (3840, [1, 1, 3, 3, 6, 6]), (23040, [1, 2, 2, 3, 3, 9]), (23040, [1, 2, 2, 3, 6, 6]), (23040, [1, 2, 3, 3, 3, 8]), (23040, [1, 2, 3, 3, 4, 7]), (51840, [1, 2, 3, 3, 5, 6]), (11520, [1, 2, 3, 4, 4, 6]), (138240, [1, 2, 3, 14]), (34560, [1, 2, 6, 11]), (7680, [1, 3, 3, 3, 4, 6]), (46080, [1, 3, 3, 13]), (46080, [1, 3, 6, 10]), (11520, [2, 2, 2, 3, 3, 8]), (11520, [2, 2, 2, 3, 5, 6]), (23040, [2, 2, 3, 3, 3, 7]), (50400, [2, 2, 3, 3, 4, 6]), (11520, [2, 2, 3, 3, 5, 5]), (138240, [2, 2, 3, 13]), (34560, [2, 2, 6, 10]), (19840, [2, 3, 3, 3, 3, 6])]

def node12Piece55Output_sector0_chunk1 : RawPoly ℕ := [(23040, [2, 3, 3, 3, 4, 5]), (3840, [2, 3, 3, 4, 4, 4]), (-196800, [2, 3, 3, 12]), (138240, [2, 3, 4, 11]), (138240, [2, 3, 5, 10]), (53760, [2, 3, 6, 9]), (138240, [2, 3, 7, 8]), (34560, [2, 4, 6, 8]), (34560, [2, 5, 6, 7]), (17280, [2, 6, 6, 6]), (207360, [2, 18]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (54720, [3, 3, 6, 8]), (23040, [3, 3, 7, 7]), (46080, [3, 4, 6, 7]), (46080, [3, 5, 6, 6]), (276480, [3, 17]), (69120, [6, 14])]

def node12Piece55Output_sector0 : RawPoly ℕ := [node12Piece55Output_sector0_chunk0, node12Piece55Output_sector0_chunk1].flatten

def node12Piece55Output : SectorVector := [(0, node12Piece55Output_sector0)]

def node12Piece55UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 6])]

def node12Piece55UnitInput_sector0 : RawPoly ℕ := [node12Piece55UnitInput_sector0_chunk0].flatten

def node12Piece55UnitInput : SectorVector := [(0, node12Piece55UnitInput_sector0)]

def node12Piece55UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 3, 6]), (6, [1, 1, 2, 2, 2, 3, 3, 6]), (72, [1, 1, 2, 3, 3, 10]), (72, [1, 1, 2, 3, 6, 7]), (24, [1, 1, 3, 3, 6, 6]), (144, [1, 2, 2, 3, 3, 9]), (144, [1, 2, 2, 3, 6, 6]), (144, [1, 2, 3, 3, 3, 8]), (144, [1, 2, 3, 3, 4, 7]), (324, [1, 2, 3, 3, 5, 6]), (72, [1, 2, 3, 4, 4, 6]), (864, [1, 2, 3, 14]), (216, [1, 2, 6, 11]), (48, [1, 3, 3, 3, 4, 6]), (288, [1, 3, 3, 13]), (288, [1, 3, 6, 10]), (72, [2, 2, 2, 3, 3, 8]), (72, [2, 2, 2, 3, 5, 6]), (144, [2, 2, 3, 3, 3, 7]), (315, [2, 2, 3, 3, 4, 6]), (72, [2, 2, 3, 3, 5, 5]), (864, [2, 2, 3, 13]), (216, [2, 2, 6, 10]), (124, [2, 3, 3, 3, 3, 6])]

def node12Piece55UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [2, 3, 3, 3, 4, 5]), (24, [2, 3, 3, 4, 4, 4]), (-1230, [2, 3, 3, 12]), (864, [2, 3, 4, 11]), (864, [2, 3, 5, 10]), (336, [2, 3, 6, 9]), (864, [2, 3, 7, 8]), (216, [2, 4, 6, 8]), (216, [2, 5, 6, 7]), (108, [2, 6, 6, 6]), (1296, [2, 18]), (288, [3, 3, 3, 11]), (288, [3, 3, 4, 10]), (288, [3, 3, 5, 9]), (342, [3, 3, 6, 8]), (144, [3, 3, 7, 7]), (288, [3, 4, 6, 7]), (288, [3, 5, 6, 6]), (1728, [3, 17]), (432, [6, 14])]

def node12Piece55UnitOutput_sector0 : RawPoly ℕ := [node12Piece55UnitOutput_sector0_chunk0, node12Piece55UnitOutput_sector0_chunk1].flatten

def node12Piece55UnitOutput : SectorVector := [(0, node12Piece55UnitOutput_sector0)]

theorem node12Piece55_check : VectorCertificate (neutralBoundS JR (-3) node12Piece55UnitInput) node12Piece55UnitOutput := by decide +kernel

theorem node12Piece55_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece55Input) = evaluate node12Piece55Output :=
  mode_of_scaled _ _ (160) node12Piece55UnitInput node12Piece55UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece55_check)

def node12Piece56Input_sector0 : RawPoly ℕ := [(-16, [2, 3, 4, 5])]

def node12Piece56Input : SectorVector := [(0, node12Piece56Input_sector0)]
def node12Piece56Output_sector0_chunk0 : RawPoly ℕ := [(-64, [1, 1, 1, 2, 3, 3, 4, 5]), (-96, [1, 1, 2, 2, 2, 3, 4, 5]), (-960, [1, 1, 2, 3, 4, 9]), (-768, [1, 1, 2, 3, 5, 8]), (-576, [1, 1, 2, 4, 5, 7]), (-384, [1, 1, 3, 4, 5, 6]), (-1920, [1, 2, 2, 3, 4, 8]), (-1536, [1, 2, 2, 3, 5, 7]), (-1152, [1, 2, 2, 4, 5, 6]), (-1920, [1, 2, 3, 3, 4, 7]), (-1536, [1, 2, 3, 3, 5, 6]), (-1920, [1, 2, 3, 4, 4, 6]), (-4224, [1, 2, 3, 4, 5, 5]), (-7680, [1, 2, 3, 14]), (-576, [1, 2, 4, 4, 4, 5]), (-5760, [1, 2, 4, 13]), (-4608, [1, 2, 5, 12]), (-768, [1, 3, 3, 4, 4, 5]), (-3840, [1, 3, 4, 12]), (-3072, [1, 3, 5, 11]), (-2304, [1, 4, 5, 10]), (-960, [2, 2, 2, 3, 4, 7]), (-768, [2, 2, 2, 3, 5, 6]), (-576, [2, 2, 2, 4, 5, 5])]

def node12Piece56Output_sector0_chunk1 : RawPoly ℕ := [(-1920, [2, 2, 3, 3, 4, 6]), (-1536, [2, 2, 3, 3, 5, 5]), (-4272, [2, 2, 3, 4, 4, 5]), (-7680, [2, 2, 3, 13]), (-5760, [2, 2, 4, 12]), (-4608, [2, 2, 5, 11]), (-2368, [2, 3, 3, 3, 4, 5]), (-960, [2, 3, 3, 4, 4, 4]), (-7680, [2, 3, 3, 12]), (7680, [2, 3, 4, 11]), (-192, [2, 3, 5, 10]), (-7680, [2, 3, 6, 9]), (-7680, [2, 3, 7, 8]), (-5760, [2, 4, 4, 10]), (-4416, [2, 4, 5, 9]), (-5760, [2, 4, 6, 8]), (-2880, [2, 4, 7, 7]), (-4608, [2, 5, 5, 8]), (-4608, [2, 5, 6, 7]), (-23040, [2, 18]), (-3840, [3, 3, 4, 10]), (-3072, [3, 3, 5, 9]), (-3840, [3, 4, 4, 9]), (-5472, [3, 4, 5, 8])]

def node12Piece56Output_sector0_chunk2 : RawPoly ℕ := [(-3840, [3, 4, 6, 7]), (-3072, [3, 5, 5, 7]), (-1536, [3, 5, 6, 6]), (-15360, [3, 17]), (-2304, [4, 4, 5, 7]), (-2304, [4, 5, 5, 6]), (-11520, [4, 16]), (-9216, [5, 15])]

def node12Piece56Output_sector0 : RawPoly ℕ := [node12Piece56Output_sector0_chunk0, node12Piece56Output_sector0_chunk1, node12Piece56Output_sector0_chunk2].flatten

def node12Piece56Output : SectorVector := [(0, node12Piece56Output_sector0)]

def node12Piece56UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 4, 5])]

def node12Piece56UnitInput_sector0 : RawPoly ℕ := [node12Piece56UnitInput_sector0_chunk0].flatten

def node12Piece56UnitInput : SectorVector := [(0, node12Piece56UnitInput_sector0)]

def node12Piece56UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 5]), (6, [1, 1, 2, 2, 2, 3, 4, 5]), (60, [1, 1, 2, 3, 4, 9]), (48, [1, 1, 2, 3, 5, 8]), (36, [1, 1, 2, 4, 5, 7]), (24, [1, 1, 3, 4, 5, 6]), (120, [1, 2, 2, 3, 4, 8]), (96, [1, 2, 2, 3, 5, 7]), (72, [1, 2, 2, 4, 5, 6]), (120, [1, 2, 3, 3, 4, 7]), (96, [1, 2, 3, 3, 5, 6]), (120, [1, 2, 3, 4, 4, 6]), (264, [1, 2, 3, 4, 5, 5]), (480, [1, 2, 3, 14]), (36, [1, 2, 4, 4, 4, 5]), (360, [1, 2, 4, 13]), (288, [1, 2, 5, 12]), (48, [1, 3, 3, 4, 4, 5]), (240, [1, 3, 4, 12]), (192, [1, 3, 5, 11]), (144, [1, 4, 5, 10]), (60, [2, 2, 2, 3, 4, 7]), (48, [2, 2, 2, 3, 5, 6]), (36, [2, 2, 2, 4, 5, 5])]

def node12Piece56UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [2, 2, 3, 3, 4, 6]), (96, [2, 2, 3, 3, 5, 5]), (267, [2, 2, 3, 4, 4, 5]), (480, [2, 2, 3, 13]), (360, [2, 2, 4, 12]), (288, [2, 2, 5, 11]), (148, [2, 3, 3, 3, 4, 5]), (60, [2, 3, 3, 4, 4, 4]), (480, [2, 3, 3, 12]), (-480, [2, 3, 4, 11]), (12, [2, 3, 5, 10]), (480, [2, 3, 6, 9]), (480, [2, 3, 7, 8]), (360, [2, 4, 4, 10]), (276, [2, 4, 5, 9]), (360, [2, 4, 6, 8]), (180, [2, 4, 7, 7]), (288, [2, 5, 5, 8]), (288, [2, 5, 6, 7]), (1440, [2, 18]), (240, [3, 3, 4, 10]), (192, [3, 3, 5, 9]), (240, [3, 4, 4, 9]), (342, [3, 4, 5, 8])]

def node12Piece56UnitOutput_sector0_chunk2 : RawPoly ℕ := [(240, [3, 4, 6, 7]), (192, [3, 5, 5, 7]), (96, [3, 5, 6, 6]), (960, [3, 17]), (144, [4, 4, 5, 7]), (144, [4, 5, 5, 6]), (720, [4, 16]), (576, [5, 15])]

def node12Piece56UnitOutput_sector0 : RawPoly ℕ := [node12Piece56UnitOutput_sector0_chunk0, node12Piece56UnitOutput_sector0_chunk1, node12Piece56UnitOutput_sector0_chunk2].flatten

def node12Piece56UnitOutput : SectorVector := [(0, node12Piece56UnitOutput_sector0)]

theorem node12Piece56_check : VectorCertificate (neutralBoundS JR (-3) node12Piece56UnitInput) node12Piece56UnitOutput := by decide +kernel

theorem node12Piece56_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece56Input) = evaluate node12Piece56Output :=
  mode_of_scaled _ _ (-16) node12Piece56UnitInput node12Piece56UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece56_check)

def node12Piece57Input_sector0 : RawPoly ℕ := [(-80, [2, 4, 4, 4])]

def node12Piece57Input : SectorVector := [(0, node12Piece57Input_sector0)]
def node12Piece57Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 2, 3, 4, 4, 4]), (-480, [1, 1, 2, 2, 2, 4, 4, 4]), (-11520, [1, 1, 2, 4, 4, 8]), (-1920, [1, 1, 4, 4, 4, 6]), (-23040, [1, 2, 2, 4, 4, 7]), (-23040, [1, 2, 3, 4, 4, 6]), (-25920, [1, 2, 4, 4, 4, 5]), (-92160, [1, 2, 4, 13]), (-3840, [1, 3, 4, 4, 4, 4]), (-46080, [1, 4, 4, 11]), (-11520, [2, 2, 2, 4, 4, 6]), (-23040, [2, 2, 3, 4, 4, 5]), (-13680, [2, 2, 4, 4, 4, 4]), (-92160, [2, 2, 4, 12]), (-13760, [2, 3, 3, 4, 4, 4]), (-92160, [2, 3, 4, 11]), (89280, [2, 4, 4, 10]), (-92160, [2, 4, 5, 9]), (-92160, [2, 4, 6, 8]), (-46080, [2, 4, 7, 7]), (-122880, [2, 18]), (-46080, [3, 4, 4, 9]), (-27360, [4, 4, 4, 8]), (-46080, [4, 4, 5, 7])]

def node12Piece57Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [4, 4, 6, 6]), (-184320, [4, 16])]

def node12Piece57Output_sector0 : RawPoly ℕ := [node12Piece57Output_sector0_chunk0, node12Piece57Output_sector0_chunk1].flatten

def node12Piece57Output : SectorVector := [(0, node12Piece57Output_sector0)]

def node12Piece57UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 4, 4])]

def node12Piece57UnitInput_sector0 : RawPoly ℕ := [node12Piece57UnitInput_sector0_chunk0].flatten

def node12Piece57UnitInput : SectorVector := [(0, node12Piece57UnitInput_sector0)]

def node12Piece57UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 4, 4]), (6, [1, 1, 2, 2, 2, 4, 4, 4]), (144, [1, 1, 2, 4, 4, 8]), (24, [1, 1, 4, 4, 4, 6]), (288, [1, 2, 2, 4, 4, 7]), (288, [1, 2, 3, 4, 4, 6]), (324, [1, 2, 4, 4, 4, 5]), (1152, [1, 2, 4, 13]), (48, [1, 3, 4, 4, 4, 4]), (576, [1, 4, 4, 11]), (144, [2, 2, 2, 4, 4, 6]), (288, [2, 2, 3, 4, 4, 5]), (171, [2, 2, 4, 4, 4, 4]), (1152, [2, 2, 4, 12]), (172, [2, 3, 3, 4, 4, 4]), (1152, [2, 3, 4, 11]), (-1116, [2, 4, 4, 10]), (1152, [2, 4, 5, 9]), (1152, [2, 4, 6, 8]), (576, [2, 4, 7, 7]), (1536, [2, 18]), (576, [3, 4, 4, 9]), (342, [4, 4, 4, 8]), (576, [4, 4, 5, 7])]

def node12Piece57UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [4, 4, 6, 6]), (2304, [4, 16])]

def node12Piece57UnitOutput_sector0 : RawPoly ℕ := [node12Piece57UnitOutput_sector0_chunk0, node12Piece57UnitOutput_sector0_chunk1].flatten

def node12Piece57UnitOutput : SectorVector := [(0, node12Piece57UnitOutput_sector0)]

theorem node12Piece57_check : VectorCertificate (neutralBoundS JR (-3) node12Piece57UnitInput) node12Piece57UnitOutput := by decide +kernel

theorem node12Piece57_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece57Input) = evaluate node12Piece57Output :=
  mode_of_scaled _ _ (-80) node12Piece57UnitInput node12Piece57UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece57_check)

def node12Piece58Input_sector0 : RawPoly ℕ := [(-80, [2, 12])]

def node12Piece58Input : SectorVector := [(0, node12Piece58Input_sector0)]
def node12Piece58Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 2, 3, 12]), (-480, [1, 1, 2, 2, 2, 12]), (-11520, [1, 1, 2, 16]), (-1920, [1, 1, 6, 12]), (-23040, [1, 2, 2, 15]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-25920, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-23040, [1, 2, 7, 10]), (-23040, [1, 2, 8, 9]), (-3840, [1, 3, 4, 12]), (-46080, [1, 19]), (-11520, [2, 2, 2, 14]), (-23040, [2, 2, 3, 13]), (-25200, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10]), (-23040, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8]), (-13760, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9])]

def node12Piece58Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (1026240, [2, 18]), (-46080, [3, 17]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-27360, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node12Piece58Output_sector0 : RawPoly ℕ := [node12Piece58Output_sector0_chunk0, node12Piece58Output_sector0_chunk1].flatten

def node12Piece58Output : SectorVector := [(0, node12Piece58Output_sector0)]

def node12Piece58UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 12])]

def node12Piece58UnitInput_sector0 : RawPoly ℕ := [node12Piece58UnitInput_sector0_chunk0].flatten

def node12Piece58UnitInput : SectorVector := [(0, node12Piece58UnitInput_sector0)]

def node12Piece58UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 12]), (6, [1, 1, 2, 2, 2, 12]), (144, [1, 1, 2, 16]), (24, [1, 1, 6, 12]), (288, [1, 2, 2, 15]), (288, [1, 2, 3, 14]), (288, [1, 2, 4, 13]), (324, [1, 2, 5, 12]), (288, [1, 2, 6, 11]), (288, [1, 2, 7, 10]), (288, [1, 2, 8, 9]), (48, [1, 3, 4, 12]), (576, [1, 19]), (144, [2, 2, 2, 14]), (288, [2, 2, 3, 13]), (315, [2, 2, 4, 12]), (288, [2, 2, 5, 11]), (288, [2, 2, 6, 10]), (288, [2, 2, 7, 9]), (144, [2, 2, 8, 8]), (172, [2, 3, 3, 12]), (288, [2, 3, 4, 11]), (288, [2, 3, 5, 10]), (288, [2, 3, 6, 9])]

def node12Piece58UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [2, 3, 7, 8]), (144, [2, 4, 4, 10]), (288, [2, 4, 5, 9]), (288, [2, 4, 6, 8]), (144, [2, 4, 7, 7]), (144, [2, 5, 5, 8]), (288, [2, 5, 6, 7]), (48, [2, 6, 6, 6]), (-12828, [2, 18]), (576, [3, 17]), (576, [4, 16]), (576, [5, 15]), (576, [6, 14]), (576, [7, 13]), (342, [8, 12]), (576, [9, 11]), (288, [10, 10])]

def node12Piece58UnitOutput_sector0 : RawPoly ℕ := [node12Piece58UnitOutput_sector0_chunk0, node12Piece58UnitOutput_sector0_chunk1].flatten

def node12Piece58UnitOutput : SectorVector := [(0, node12Piece58UnitOutput_sector0)]

theorem node12Piece58_check : VectorCertificate (neutralBoundS JR (-3) node12Piece58UnitInput) node12Piece58UnitOutput := by decide +kernel

theorem node12Piece58_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece58Input) = evaluate node12Piece58Output :=
  mode_of_scaled _ _ (-80) node12Piece58UnitInput node12Piece58UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece58_check)

def node12Piece59Input_sector0 : RawPoly ℕ := [(2432/27, [3, 3, 3, 5])]

def node12Piece59Input : SectorVector := [(0, node12Piece59Input_sector0)]
def node12Piece59Output_sector0_chunk0 : RawPoly ℕ := [(9728/27, [1, 1, 1, 3, 3, 3, 3, 5]), (4864/9, [1, 1, 2, 2, 3, 3, 3, 5]), (48640/9, [1, 1, 3, 3, 3, 9]), (9728, [1, 1, 3, 3, 5, 7]), (97280/9, [1, 2, 3, 3, 3, 8]), (19456, [1, 2, 3, 3, 5, 6]), (97280/9, [1, 3, 3, 3, 3, 7]), (97280/9, [1, 3, 3, 3, 4, 6]), (214016/9, [1, 3, 3, 3, 5, 5]), (9728, [1, 3, 3, 4, 4, 5]), (97280, [1, 3, 3, 13]), (58368, [1, 3, 5, 11]), (48640/9, [2, 2, 3, 3, 3, 7]), (9728, [2, 2, 3, 3, 5, 5]), (97280/9, [2, 3, 3, 3, 3, 6]), (274816/9, [2, 3, 3, 3, 4, 5]), (97280, [2, 3, 3, 12]), (58368, [2, 3, 5, 10]), (243200/27, [3, 3, 3, 3, 3, 5]), (48640/9, [3, 3, 3, 3, 4, 4]), (-389120/9, [3, 3, 3, 11]), (97280, [3, 3, 4, 10]), (48640/3, [3, 3, 5, 9]), (97280, [3, 3, 6, 8])]

def node12Piece59Output_sector0_chunk1 : RawPoly ℕ := [(48640, [3, 3, 7, 7]), (58368, [3, 4, 5, 8]), (58368, [3, 5, 5, 7]), (29184, [3, 5, 6, 6]), (291840, [3, 17]), (58368, [5, 15])]

def node12Piece59Output_sector0 : RawPoly ℕ := [node12Piece59Output_sector0_chunk0, node12Piece59Output_sector0_chunk1].flatten

def node12Piece59Output : SectorVector := [(0, node12Piece59Output_sector0)]

def node12Piece59UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 5])]

def node12Piece59UnitInput_sector0 : RawPoly ℕ := [node12Piece59UnitInput_sector0_chunk0].flatten

def node12Piece59UnitInput : SectorVector := [(0, node12Piece59UnitInput_sector0)]

def node12Piece59UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 3, 5]), (6, [1, 1, 2, 2, 3, 3, 3, 5]), (60, [1, 1, 3, 3, 3, 9]), (108, [1, 1, 3, 3, 5, 7]), (120, [1, 2, 3, 3, 3, 8]), (216, [1, 2, 3, 3, 5, 6]), (120, [1, 3, 3, 3, 3, 7]), (120, [1, 3, 3, 3, 4, 6]), (264, [1, 3, 3, 3, 5, 5]), (108, [1, 3, 3, 4, 4, 5]), (1080, [1, 3, 3, 13]), (648, [1, 3, 5, 11]), (60, [2, 2, 3, 3, 3, 7]), (108, [2, 2, 3, 3, 5, 5]), (120, [2, 3, 3, 3, 3, 6]), (339, [2, 3, 3, 3, 4, 5]), (1080, [2, 3, 3, 12]), (648, [2, 3, 5, 10]), (100, [3, 3, 3, 3, 3, 5]), (60, [3, 3, 3, 3, 4, 4]), (-480, [3, 3, 3, 11]), (1080, [3, 3, 4, 10]), (180, [3, 3, 5, 9]), (1080, [3, 3, 6, 8])]

def node12Piece59UnitOutput_sector0_chunk1 : RawPoly ℕ := [(540, [3, 3, 7, 7]), (648, [3, 4, 5, 8]), (648, [3, 5, 5, 7]), (324, [3, 5, 6, 6]), (3240, [3, 17]), (648, [5, 15])]

def node12Piece59UnitOutput_sector0 : RawPoly ℕ := [node12Piece59UnitOutput_sector0_chunk0, node12Piece59UnitOutput_sector0_chunk1].flatten

def node12Piece59UnitOutput : SectorVector := [(0, node12Piece59UnitOutput_sector0)]

theorem node12Piece59_check : VectorCertificate (neutralBoundS JR (-3) node12Piece59UnitInput) node12Piece59UnitOutput := by decide +kernel

theorem node12Piece59_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece59Input) = evaluate node12Piece59Output :=
  mode_of_scaled _ _ (2432/27) node12Piece59UnitInput node12Piece59UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece59_check)

def node12Piece60Input_sector0 : RawPoly ℕ := [(80/3, [3, 3, 4, 4])]

def node12Piece60Input : SectorVector := [(0, node12Piece60Input_sector0)]
def node12Piece60Output_sector0_chunk0 : RawPoly ℕ := [(320/3, [1, 1, 1, 3, 3, 3, 4, 4]), (160, [1, 1, 2, 2, 3, 3, 4, 4]), (2560, [1, 1, 3, 3, 4, 8]), (1920, [1, 1, 3, 4, 4, 7]), (5120, [1, 2, 3, 3, 4, 7]), (3840, [1, 2, 3, 4, 4, 6]), (5120, [1, 3, 3, 3, 4, 6]), (8640, [1, 3, 3, 4, 4, 5]), (10240, [1, 3, 3, 13]), (1920, [1, 3, 4, 4, 4, 4]), (30720, [1, 3, 4, 12]), (5760, [1, 4, 4, 11]), (2560, [2, 2, 3, 3, 4, 6]), (1920, [2, 2, 3, 4, 4, 5]), (5120, [2, 3, 3, 3, 4, 5]), (6480, [2, 3, 3, 4, 4, 4]), (10240, [2, 3, 3, 12]), (30720, [2, 3, 4, 11]), (5760, [2, 4, 4, 10]), (9920/3, [3, 3, 3, 3, 4, 4]), (10240, [3, 3, 3, 11]), (-9600, [3, 3, 4, 10]), (10240, [3, 3, 5, 9]), (10240, [3, 3, 6, 8])]

def node12Piece60Output_sector0_chunk1 : RawPoly ℕ := [(5120, [3, 3, 7, 7]), (8960, [3, 4, 4, 9]), (30720, [3, 4, 5, 8]), (30720, [3, 4, 6, 7]), (61440, [3, 17]), (5760, [4, 4, 4, 8]), (5760, [4, 4, 5, 7]), (2880, [4, 4, 6, 6]), (46080, [4, 16])]

def node12Piece60Output_sector0 : RawPoly ℕ := [node12Piece60Output_sector0_chunk0, node12Piece60Output_sector0_chunk1].flatten

def node12Piece60Output : SectorVector := [(0, node12Piece60Output_sector0)]

def node12Piece60UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 4, 4])]

def node12Piece60UnitInput_sector0 : RawPoly ℕ := [node12Piece60UnitInput_sector0_chunk0].flatten

def node12Piece60UnitInput : SectorVector := [(0, node12Piece60UnitInput_sector0)]

def node12Piece60UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 4, 4]), (6, [1, 1, 2, 2, 3, 3, 4, 4]), (96, [1, 1, 3, 3, 4, 8]), (72, [1, 1, 3, 4, 4, 7]), (192, [1, 2, 3, 3, 4, 7]), (144, [1, 2, 3, 4, 4, 6]), (192, [1, 3, 3, 3, 4, 6]), (324, [1, 3, 3, 4, 4, 5]), (384, [1, 3, 3, 13]), (72, [1, 3, 4, 4, 4, 4]), (1152, [1, 3, 4, 12]), (216, [1, 4, 4, 11]), (96, [2, 2, 3, 3, 4, 6]), (72, [2, 2, 3, 4, 4, 5]), (192, [2, 3, 3, 3, 4, 5]), (243, [2, 3, 3, 4, 4, 4]), (384, [2, 3, 3, 12]), (1152, [2, 3, 4, 11]), (216, [2, 4, 4, 10]), (124, [3, 3, 3, 3, 4, 4]), (384, [3, 3, 3, 11]), (-360, [3, 3, 4, 10]), (384, [3, 3, 5, 9]), (384, [3, 3, 6, 8])]

def node12Piece60UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [3, 3, 7, 7]), (336, [3, 4, 4, 9]), (1152, [3, 4, 5, 8]), (1152, [3, 4, 6, 7]), (2304, [3, 17]), (216, [4, 4, 4, 8]), (216, [4, 4, 5, 7]), (108, [4, 4, 6, 6]), (1728, [4, 16])]

def node12Piece60UnitOutput_sector0 : RawPoly ℕ := [node12Piece60UnitOutput_sector0_chunk0, node12Piece60UnitOutput_sector0_chunk1].flatten

def node12Piece60UnitOutput : SectorVector := [(0, node12Piece60UnitOutput_sector0)]

theorem node12Piece60_check : VectorCertificate (neutralBoundS JR (-3) node12Piece60UnitInput) node12Piece60UnitOutput := by decide +kernel

theorem node12Piece60_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece60Input) = evaluate node12Piece60Output :=
  mode_of_scaled _ _ (80/3) node12Piece60UnitInput node12Piece60UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece60_check)

def node12Piece61Input_sector0 : RawPoly ℕ := [(960/11, [3, 11])]

def node12Piece61Input : SectorVector := [(0, node12Piece61Input_sector0)]
def node12Piece61Output_sector0_chunk0 : RawPoly ℕ := [(3840/11, [1, 1, 1, 3, 3, 11]), (5760/11, [1, 1, 2, 2, 3, 11]), (11520, [1, 1, 3, 15]), (34560/11, [1, 1, 7, 11]), (23040, [1, 2, 3, 14]), (69120/11, [1, 2, 6, 11]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (311040/11, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (23040, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (34560/11, [1, 4, 4, 11]), (69120, [1, 19]), (11520, [2, 2, 3, 13]), (34560/11, [2, 2, 5, 11]), (23040, [2, 3, 3, 12]), (325440/11, [2, 3, 4, 11]), (23040, [2, 3, 5, 10]), (23040, [2, 3, 6, 9]), (23040, [2, 3, 7, 8]), (69120, [2, 18]), (142080/11, [3, 3, 3, 11]), (23040, [3, 3, 4, 10])]

def node12Piece61Output_sector0_chunk1 : RawPoly ℕ := [(23040, [3, 3, 5, 9]), (23040, [3, 3, 6, 8]), (11520, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (23040, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-864000, [3, 17]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14]), (69120, [7, 13]), (69120, [8, 12]), (264960/11, [9, 11]), (34560, [10, 10])]

def node12Piece61Output_sector0 : RawPoly ℕ := [node12Piece61Output_sector0_chunk0, node12Piece61Output_sector0_chunk1].flatten

def node12Piece61Output : SectorVector := [(0, node12Piece61Output_sector0)]

def node12Piece61UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 11])]

def node12Piece61UnitInput_sector0 : RawPoly ℕ := [node12Piece61UnitInput_sector0_chunk0].flatten

def node12Piece61UnitInput : SectorVector := [(0, node12Piece61UnitInput_sector0)]

def node12Piece61UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 11]), (6, [1, 1, 2, 2, 3, 11]), (132, [1, 1, 3, 15]), (36, [1, 1, 7, 11]), (264, [1, 2, 3, 14]), (72, [1, 2, 6, 11]), (264, [1, 3, 3, 13]), (264, [1, 3, 4, 12]), (324, [1, 3, 5, 11]), (264, [1, 3, 6, 10]), (264, [1, 3, 7, 9]), (132, [1, 3, 8, 8]), (36, [1, 4, 4, 11]), (792, [1, 19]), (132, [2, 2, 3, 13]), (36, [2, 2, 5, 11]), (264, [2, 3, 3, 12]), (339, [2, 3, 4, 11]), (264, [2, 3, 5, 10]), (264, [2, 3, 6, 9]), (264, [2, 3, 7, 8]), (792, [2, 18]), (148, [3, 3, 3, 11]), (264, [3, 3, 4, 10])]

def node12Piece61UnitOutput_sector0_chunk1 : RawPoly ℕ := [(264, [3, 3, 5, 9]), (264, [3, 3, 6, 8]), (132, [3, 3, 7, 7]), (132, [3, 4, 4, 9]), (264, [3, 4, 5, 8]), (264, [3, 4, 6, 7]), (132, [3, 5, 5, 7]), (132, [3, 5, 6, 6]), (-9900, [3, 17]), (792, [4, 16]), (792, [5, 15]), (792, [6, 14]), (792, [7, 13]), (792, [8, 12]), (276, [9, 11]), (396, [10, 10])]

def node12Piece61UnitOutput_sector0 : RawPoly ℕ := [node12Piece61UnitOutput_sector0_chunk0, node12Piece61UnitOutput_sector0_chunk1].flatten

def node12Piece61UnitOutput : SectorVector := [(0, node12Piece61UnitOutput_sector0)]

theorem node12Piece61_check : VectorCertificate (neutralBoundS JR (-3) node12Piece61UnitInput) node12Piece61UnitOutput := by decide +kernel

theorem node12Piece61_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece61Input) = evaluate node12Piece61Output :=
  mode_of_scaled _ _ (960/11) node12Piece61UnitInput node12Piece61UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece61_check)

def node12Piece62Input_sector0 : RawPoly ℕ := [(-48, [4, 10])]

def node12Piece62Input : SectorVector := [(0, node12Piece62Input_sector0)]
def node12Piece62Output_sector0_chunk0 : RawPoly ℕ := [(-192, [1, 1, 1, 3, 4, 10]), (-288, [1, 1, 2, 2, 4, 10]), (-5760, [1, 1, 4, 14]), (-2304, [1, 1, 8, 10]), (-11520, [1, 2, 4, 13]), (-4608, [1, 2, 7, 10]), (-11520, [1, 3, 4, 12]), (-4608, [1, 3, 6, 10]), (-11520, [1, 4, 4, 11]), (-15552, [1, 4, 5, 10]), (-11520, [1, 4, 6, 9]), (-11520, [1, 4, 7, 8]), (-46080, [1, 19]), (-5760, [2, 2, 4, 12]), (-2304, [2, 2, 6, 10]), (-11520, [2, 3, 4, 11]), (-4608, [2, 3, 5, 10]), (-13968, [2, 4, 4, 10]), (-11520, [2, 4, 5, 9]), (-11520, [2, 4, 6, 8]), (-5760, [2, 4, 7, 7]), (-46080, [2, 18]), (-8256, [3, 3, 4, 10]), (-11520, [3, 4, 4, 9])]

def node12Piece62Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [3, 4, 5, 8]), (-11520, [3, 4, 6, 7]), (-46080, [3, 17]), (-5760, [4, 4, 4, 8]), (-11520, [4, 4, 5, 7]), (-5760, [4, 4, 6, 6]), (-5760, [4, 5, 5, 6]), (355680, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (-46080, [9, 11]), (22464, [10, 10])]

def node12Piece62Output_sector0 : RawPoly ℕ := [node12Piece62Output_sector0_chunk0, node12Piece62Output_sector0_chunk1].flatten

def node12Piece62Output : SectorVector := [(0, node12Piece62Output_sector0)]

def node12Piece62UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 10])]

def node12Piece62UnitInput_sector0 : RawPoly ℕ := [node12Piece62UnitInput_sector0_chunk0].flatten

def node12Piece62UnitInput : SectorVector := [(0, node12Piece62UnitInput_sector0)]

def node12Piece62UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 10]), (6, [1, 1, 2, 2, 4, 10]), (120, [1, 1, 4, 14]), (48, [1, 1, 8, 10]), (240, [1, 2, 4, 13]), (96, [1, 2, 7, 10]), (240, [1, 3, 4, 12]), (96, [1, 3, 6, 10]), (240, [1, 4, 4, 11]), (324, [1, 4, 5, 10]), (240, [1, 4, 6, 9]), (240, [1, 4, 7, 8]), (960, [1, 19]), (120, [2, 2, 4, 12]), (48, [2, 2, 6, 10]), (240, [2, 3, 4, 11]), (96, [2, 3, 5, 10]), (291, [2, 4, 4, 10]), (240, [2, 4, 5, 9]), (240, [2, 4, 6, 8]), (120, [2, 4, 7, 7]), (960, [2, 18]), (172, [3, 3, 4, 10]), (240, [3, 4, 4, 9])]

def node12Piece62UnitOutput_sector0_chunk1 : RawPoly ℕ := [(240, [3, 4, 5, 8]), (240, [3, 4, 6, 7]), (960, [3, 17]), (120, [4, 4, 4, 8]), (240, [4, 4, 5, 7]), (120, [4, 4, 6, 6]), (120, [4, 5, 5, 6]), (-7410, [4, 16]), (960, [5, 15]), (960, [6, 14]), (960, [7, 13]), (960, [8, 12]), (960, [9, 11]), (-468, [10, 10])]

def node12Piece62UnitOutput_sector0 : RawPoly ℕ := [node12Piece62UnitOutput_sector0_chunk0, node12Piece62UnitOutput_sector0_chunk1].flatten

def node12Piece62UnitOutput : SectorVector := [(0, node12Piece62UnitOutput_sector0)]

theorem node12Piece62_check : VectorCertificate (neutralBoundS JR (-3) node12Piece62UnitInput) node12Piece62UnitOutput := by decide +kernel

theorem node12Piece62_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece62Input) = evaluate node12Piece62Output :=
  mode_of_scaled _ _ (-48) node12Piece62UnitInput node12Piece62UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece62_check)

def node12Piece63Input_sector0 : RawPoly ℕ := [(32/3, [5, 9])]

def node12Piece63Input : SectorVector := [(0, node12Piece63Input_sector0)]
def node12Piece63Output_sector0_chunk0 : RawPoly ℕ := [(128/3, [1, 1, 1, 3, 5, 9]), (64, [1, 1, 2, 2, 5, 9]), (1152, [1, 1, 5, 13]), (640, [1, 1, 9, 9]), (2304, [1, 2, 5, 12]), (1280, [1, 2, 8, 9]), (2304, [1, 3, 5, 11]), (1280, [1, 3, 7, 9]), (2304, [1, 4, 5, 10]), (1280, [1, 4, 6, 9]), (2816, [1, 5, 5, 9]), (2304, [1, 5, 6, 8]), (1152, [1, 5, 7, 7]), (11520, [1, 19]), (1152, [2, 2, 5, 11]), (640, [2, 2, 7, 9]), (2304, [2, 3, 5, 10]), (1280, [2, 3, 6, 9]), (3616, [2, 4, 5, 9]), (2304, [2, 5, 5, 8]), (2304, [2, 5, 6, 7]), (11520, [2, 18]), (5504/3, [3, 3, 5, 9]), (640, [3, 4, 4, 9])]

def node12Piece63Output_sector0_chunk1 : RawPoly ℕ := [(2304, [3, 4, 5, 8]), (2304, [3, 5, 5, 7]), (1152, [3, 5, 6, 6]), (11520, [3, 17]), (1152, [4, 4, 5, 7]), (2304, [4, 5, 5, 6]), (11520, [4, 16]), (384, [5, 5, 5, 5]), (-56832, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (11520, [8, 12]), (-5120, [9, 11]), (5760, [10, 10])]

def node12Piece63Output_sector0 : RawPoly ℕ := [node12Piece63Output_sector0_chunk0, node12Piece63Output_sector0_chunk1].flatten

def node12Piece63Output : SectorVector := [(0, node12Piece63Output_sector0)]

def node12Piece63UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 9])]

def node12Piece63UnitInput_sector0 : RawPoly ℕ := [node12Piece63UnitInput_sector0_chunk0].flatten

def node12Piece63UnitInput : SectorVector := [(0, node12Piece63UnitInput_sector0)]

def node12Piece63UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 5, 9]), (6, [1, 1, 2, 2, 5, 9]), (108, [1, 1, 5, 13]), (60, [1, 1, 9, 9]), (216, [1, 2, 5, 12]), (120, [1, 2, 8, 9]), (216, [1, 3, 5, 11]), (120, [1, 3, 7, 9]), (216, [1, 4, 5, 10]), (120, [1, 4, 6, 9]), (264, [1, 5, 5, 9]), (216, [1, 5, 6, 8]), (108, [1, 5, 7, 7]), (1080, [1, 19]), (108, [2, 2, 5, 11]), (60, [2, 2, 7, 9]), (216, [2, 3, 5, 10]), (120, [2, 3, 6, 9]), (339, [2, 4, 5, 9]), (216, [2, 5, 5, 8]), (216, [2, 5, 6, 7]), (1080, [2, 18]), (172, [3, 3, 5, 9]), (60, [3, 4, 4, 9])]

def node12Piece63UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [3, 4, 5, 8]), (216, [3, 5, 5, 7]), (108, [3, 5, 6, 6]), (1080, [3, 17]), (108, [4, 4, 5, 7]), (216, [4, 5, 5, 6]), (1080, [4, 16]), (36, [5, 5, 5, 5]), (-5328, [5, 15]), (1080, [6, 14]), (1080, [7, 13]), (1080, [8, 12]), (-480, [9, 11]), (540, [10, 10])]

def node12Piece63UnitOutput_sector0 : RawPoly ℕ := [node12Piece63UnitOutput_sector0_chunk0, node12Piece63UnitOutput_sector0_chunk1].flatten

def node12Piece63UnitOutput : SectorVector := [(0, node12Piece63UnitOutput_sector0)]

theorem node12Piece63_check : VectorCertificate (neutralBoundS JR (-3) node12Piece63UnitInput) node12Piece63UnitOutput := by decide +kernel

theorem node12Piece63_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece63Input) = evaluate node12Piece63Output :=
  mode_of_scaled _ _ (32/3) node12Piece63UnitInput node12Piece63UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece63_check)

end VOA.Classification.COne.OrbC2h
