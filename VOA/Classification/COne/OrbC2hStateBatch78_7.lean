import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch78_5
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

def node78Piece112Input_sector0 : RawPoly ℕ := [(-370/3, [2, 2, 2, 3, 4, 4])]

def node78Piece112Input : SectorVector := [(0, node78Piece112Input_sector0)]
def node78Piece112Output_sector0_chunk0 : RawPoly ℕ := [(-1480/3, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (-11840, [1, 1, 2, 2, 2, 3, 4, 7]), (-4440, [1, 1, 2, 2, 2, 4, 4, 6]), (-8880, [1, 1, 2, 2, 3, 4, 4, 5]), (-23680, [1, 2, 2, 2, 2, 3, 4, 6]), (-8880, [1, 2, 2, 2, 2, 4, 4, 5]), (-23680, [1, 2, 2, 2, 3, 3, 4, 5]), (-37740, [1, 2, 2, 2, 3, 4, 4, 4]), (-47360, [1, 2, 2, 2, 3, 12]), (-71040, [1, 2, 2, 2, 4, 11]), (-8880, [1, 2, 2, 3, 3, 3, 4, 4]), (-142080, [1, 2, 2, 3, 4, 10]), (-53280, [1, 2, 2, 4, 4, 9]), (-35520, [1, 2, 3, 4, 4, 8]), (-11840, [2, 2, 2, 2, 2, 3, 4, 5]), (-4440, [2, 2, 2, 2, 2, 4, 4, 4]), (-112480/3, [2, 2, 2, 2, 3, 3, 4, 4]), (-47360, [2, 2, 2, 2, 3, 11]), (-71040, [2, 2, 2, 2, 4, 10]), (-11840/3, [2, 2, 2, 3, 3, 3, 3, 4]), (-47360, [2, 2, 2, 3, 3, 10]), (-171680/3, [2, 2, 2, 3, 4, 9]), (-47360, [2, 2, 2, 3, 5, 8]), (-47360, [2, 2, 2, 3, 6, 7])]

def node78Piece112Output_sector0_chunk1 : RawPoly ℕ := [(-70300, [2, 2, 2, 4, 4, 8]), (-71040, [2, 2, 2, 4, 5, 7]), (-35520, [2, 2, 2, 4, 6, 6]), (-142080, [2, 2, 2, 16]), (-142080, [2, 2, 3, 3, 4, 8]), (-159840, [2, 2, 3, 4, 4, 7]), (-142080, [2, 2, 3, 4, 5, 6]), (-284160, [2, 2, 3, 15]), (-53280, [2, 2, 4, 4, 4, 6]), (-26640, [2, 2, 4, 4, 5, 5]), (-426240, [2, 2, 4, 14]), (-35520, [2, 3, 3, 4, 4, 6]), (-35520, [2, 3, 4, 4, 4, 5]), (-284160, [2, 3, 4, 13]), (-106560, [2, 4, 4, 12]), (-23680, [3, 4, 4, 11])]

def node78Piece112Output_sector0 : RawPoly ℕ := [node78Piece112Output_sector0_chunk0, node78Piece112Output_sector0_chunk1].flatten

def node78Piece112Output : SectorVector := [(0, node78Piece112Output_sector0)]

def node78Piece112UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 3, 4, 4])]

def node78Piece112UnitInput_sector0 : RawPoly ℕ := [node78Piece112UnitInput_sector0_chunk0].flatten

def node78Piece112UnitInput : SectorVector := [(0, node78Piece112UnitInput_sector0)]

def node78Piece112UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (96, [1, 1, 2, 2, 2, 3, 4, 7]), (36, [1, 1, 2, 2, 2, 4, 4, 6]), (72, [1, 1, 2, 2, 3, 4, 4, 5]), (192, [1, 2, 2, 2, 2, 3, 4, 6]), (72, [1, 2, 2, 2, 2, 4, 4, 5]), (192, [1, 2, 2, 2, 3, 3, 4, 5]), (306, [1, 2, 2, 2, 3, 4, 4, 4]), (384, [1, 2, 2, 2, 3, 12]), (576, [1, 2, 2, 2, 4, 11]), (72, [1, 2, 2, 3, 3, 3, 4, 4]), (1152, [1, 2, 2, 3, 4, 10]), (432, [1, 2, 2, 4, 4, 9]), (288, [1, 2, 3, 4, 4, 8]), (96, [2, 2, 2, 2, 2, 3, 4, 5]), (36, [2, 2, 2, 2, 2, 4, 4, 4]), (304, [2, 2, 2, 2, 3, 3, 4, 4]), (384, [2, 2, 2, 2, 3, 11]), (576, [2, 2, 2, 2, 4, 10]), (32, [2, 2, 2, 3, 3, 3, 3, 4]), (384, [2, 2, 2, 3, 3, 10]), (464, [2, 2, 2, 3, 4, 9]), (384, [2, 2, 2, 3, 5, 8]), (384, [2, 2, 2, 3, 6, 7])]

def node78Piece112UnitOutput_sector0_chunk1 : RawPoly ℕ := [(570, [2, 2, 2, 4, 4, 8]), (576, [2, 2, 2, 4, 5, 7]), (288, [2, 2, 2, 4, 6, 6]), (1152, [2, 2, 2, 16]), (1152, [2, 2, 3, 3, 4, 8]), (1296, [2, 2, 3, 4, 4, 7]), (1152, [2, 2, 3, 4, 5, 6]), (2304, [2, 2, 3, 15]), (432, [2, 2, 4, 4, 4, 6]), (216, [2, 2, 4, 4, 5, 5]), (3456, [2, 2, 4, 14]), (288, [2, 3, 3, 4, 4, 6]), (288, [2, 3, 4, 4, 4, 5]), (2304, [2, 3, 4, 13]), (864, [2, 4, 4, 12]), (192, [3, 4, 4, 11])]

def node78Piece112UnitOutput_sector0 : RawPoly ℕ := [node78Piece112UnitOutput_sector0_chunk0, node78Piece112UnitOutput_sector0_chunk1].flatten

def node78Piece112UnitOutput : SectorVector := [(0, node78Piece112UnitOutput_sector0)]

theorem node78Piece112_check : VectorCertificate (neutralBoundS JR (-2) node78Piece112UnitInput) node78Piece112UnitOutput := by decide +kernel

theorem node78Piece112_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece112Input) = evaluate node78Piece112Output :=
  mode_of_scaled _ _ (-370/3) node78Piece112UnitInput node78Piece112UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece112_check)

def node78Piece113Input_sector0 : RawPoly ℕ := [(-1440/11, [2, 2, 2, 11])]

def node78Piece113Input : SectorVector := [(0, node78Piece113Input_sector0)]
def node78Piece113Output_sector0_chunk0 : RawPoly ℕ := [(-5760/11, [1, 1, 1, 2, 2, 2, 2, 11]), (-17280, [1, 1, 2, 2, 2, 14]), (-103680/11, [1, 1, 2, 2, 5, 11]), (-34560, [1, 2, 2, 2, 2, 13]), (-34560, [1, 2, 2, 2, 3, 12]), (-578880/11, [1, 2, 2, 2, 4, 11]), (-34560, [1, 2, 2, 2, 5, 10]), (-34560, [1, 2, 2, 2, 6, 9]), (-34560, [1, 2, 2, 2, 7, 8]), (-103680/11, [1, 2, 2, 3, 3, 11]), (-207360, [1, 2, 2, 17]), (-414720/11, [1, 2, 8, 11]), (-17280, [2, 2, 2, 2, 2, 12]), (-489600/11, [2, 2, 2, 2, 3, 11]), (-34560, [2, 2, 2, 2, 4, 10]), (-34560, [2, 2, 2, 2, 5, 9]), (-34560, [2, 2, 2, 2, 6, 8]), (-17280, [2, 2, 2, 2, 7, 7]), (-17280, [2, 2, 2, 3, 3, 10]), (-34560, [2, 2, 2, 3, 4, 9]), (-34560, [2, 2, 2, 3, 5, 8]), (-34560, [2, 2, 2, 3, 6, 7]), (-17280, [2, 2, 2, 4, 4, 8]), (-34560, [2, 2, 2, 4, 5, 7])]

def node78Piece113Output_sector0_chunk1 : RawPoly ℕ := [(-17280, [2, 2, 2, 4, 6, 6]), (-17280, [2, 2, 2, 5, 5, 6]), (1097280, [2, 2, 2, 16]), (-207360, [2, 2, 3, 15]), (-207360, [2, 2, 4, 14]), (-207360, [2, 2, 5, 13]), (-207360, [2, 2, 6, 12]), (-1866240/11, [2, 2, 7, 11]), (-207360, [2, 2, 8, 10]), (-103680, [2, 2, 9, 9]), (-414720/11, [2, 3, 6, 11]), (-414720/11, [2, 4, 5, 11]), (-414720, [2, 20]), (-276480/11, [11, 11])]

def node78Piece113Output_sector0 : RawPoly ℕ := [node78Piece113Output_sector0_chunk0, node78Piece113Output_sector0_chunk1].flatten

def node78Piece113Output : SectorVector := [(0, node78Piece113Output_sector0)]

def node78Piece113UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 11])]

def node78Piece113UnitInput_sector0 : RawPoly ℕ := [node78Piece113UnitInput_sector0_chunk0].flatten

def node78Piece113UnitInput : SectorVector := [(0, node78Piece113UnitInput_sector0)]

def node78Piece113UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 11]), (132, [1, 1, 2, 2, 2, 14]), (72, [1, 1, 2, 2, 5, 11]), (264, [1, 2, 2, 2, 2, 13]), (264, [1, 2, 2, 2, 3, 12]), (402, [1, 2, 2, 2, 4, 11]), (264, [1, 2, 2, 2, 5, 10]), (264, [1, 2, 2, 2, 6, 9]), (264, [1, 2, 2, 2, 7, 8]), (72, [1, 2, 2, 3, 3, 11]), (1584, [1, 2, 2, 17]), (288, [1, 2, 8, 11]), (132, [2, 2, 2, 2, 2, 12]), (340, [2, 2, 2, 2, 3, 11]), (264, [2, 2, 2, 2, 4, 10]), (264, [2, 2, 2, 2, 5, 9]), (264, [2, 2, 2, 2, 6, 8]), (132, [2, 2, 2, 2, 7, 7]), (132, [2, 2, 2, 3, 3, 10]), (264, [2, 2, 2, 3, 4, 9]), (264, [2, 2, 2, 3, 5, 8]), (264, [2, 2, 2, 3, 6, 7]), (132, [2, 2, 2, 4, 4, 8]), (264, [2, 2, 2, 4, 5, 7])]

def node78Piece113UnitOutput_sector0_chunk1 : RawPoly ℕ := [(132, [2, 2, 2, 4, 6, 6]), (132, [2, 2, 2, 5, 5, 6]), (-8382, [2, 2, 2, 16]), (1584, [2, 2, 3, 15]), (1584, [2, 2, 4, 14]), (1584, [2, 2, 5, 13]), (1584, [2, 2, 6, 12]), (1296, [2, 2, 7, 11]), (1584, [2, 2, 8, 10]), (792, [2, 2, 9, 9]), (288, [2, 3, 6, 11]), (288, [2, 4, 5, 11]), (3168, [2, 20]), (192, [11, 11])]

def node78Piece113UnitOutput_sector0 : RawPoly ℕ := [node78Piece113UnitOutput_sector0_chunk0, node78Piece113UnitOutput_sector0_chunk1].flatten

def node78Piece113UnitOutput : SectorVector := [(0, node78Piece113UnitOutput_sector0)]

theorem node78Piece113_check : VectorCertificate (neutralBoundS JR (-2) node78Piece113UnitInput) node78Piece113UnitOutput := by decide +kernel

theorem node78Piece113_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece113Input) = evaluate node78Piece113Output :=
  mode_of_scaled _ _ (-1440/11) node78Piece113UnitInput node78Piece113UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece113_check)

def node78Piece114Input_sector0 : RawPoly ℕ := [(1120/27, [2, 2, 3, 3, 3, 4])]

def node78Piece114Input : SectorVector := [(0, node78Piece114Input_sector0)]
def node78Piece114Output_sector0_chunk0 : RawPoly ℕ := [(4480/27, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (17920/9, [1, 1, 2, 2, 3, 3, 3, 7]), (4480, [1, 1, 2, 2, 3, 3, 4, 6]), (17920/9, [1, 1, 2, 3, 3, 3, 4, 5]), (35840/9, [1, 2, 2, 2, 3, 3, 3, 6]), (8960, [1, 2, 2, 2, 3, 3, 4, 5]), (35840/9, [1, 2, 2, 3, 3, 3, 3, 5]), (132160/9, [1, 2, 2, 3, 3, 3, 4, 4]), (35840, [1, 2, 2, 3, 3, 11]), (26880, [1, 2, 2, 3, 4, 10]), (17920/9, [1, 2, 3, 3, 3, 3, 3, 4]), (143360/9, [1, 2, 3, 3, 3, 10]), (35840, [1, 2, 3, 3, 4, 9]), (35840/9, [1, 3, 3, 3, 4, 8]), (17920/9, [2, 2, 2, 2, 3, 3, 3, 5]), (4480, [2, 2, 2, 2, 3, 3, 4, 4]), (286720/27, [2, 2, 2, 3, 3, 3, 3, 4]), (35840, [2, 2, 2, 3, 3, 10]), (26880, [2, 2, 2, 3, 4, 9]), (17920/27, [2, 2, 3, 3, 3, 3, 3, 3]), (474880/27, [2, 2, 3, 3, 3, 9]), (132160/3, [2, 2, 3, 3, 4, 8]), (35840, [2, 2, 3, 3, 5, 7]), (17920, [2, 2, 3, 3, 6, 6])]

def node78Piece114Output_sector0_chunk1 : RawPoly ℕ := [(26880, [2, 2, 3, 4, 4, 7]), (26880, [2, 2, 3, 4, 5, 6]), (107520, [2, 2, 3, 15]), (26880, [2, 2, 4, 14]), (143360/9, [2, 3, 3, 3, 3, 8]), (358400/9, [2, 3, 3, 3, 4, 7]), (143360/9, [2, 3, 3, 3, 5, 6]), (35840, [2, 3, 3, 4, 4, 6]), (17920, [2, 3, 3, 4, 5, 5]), (143360, [2, 3, 3, 14]), (107520, [2, 3, 4, 13]), (35840/9, [3, 3, 3, 3, 4, 6]), (35840/9, [3, 3, 3, 4, 4, 5]), (143360/9, [3, 3, 3, 13]), (35840, [3, 3, 4, 12])]

def node78Piece114Output_sector0 : RawPoly ℕ := [node78Piece114Output_sector0_chunk0, node78Piece114Output_sector0_chunk1].flatten

def node78Piece114Output : SectorVector := [(0, node78Piece114Output_sector0)]

def node78Piece114UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 3, 3, 4])]

def node78Piece114UnitInput_sector0 : RawPoly ℕ := [node78Piece114UnitInput_sector0_chunk0].flatten

def node78Piece114UnitInput : SectorVector := [(0, node78Piece114UnitInput_sector0)]

def node78Piece114UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (48, [1, 1, 2, 2, 3, 3, 3, 7]), (108, [1, 1, 2, 2, 3, 3, 4, 6]), (48, [1, 1, 2, 3, 3, 3, 4, 5]), (96, [1, 2, 2, 2, 3, 3, 3, 6]), (216, [1, 2, 2, 2, 3, 3, 4, 5]), (96, [1, 2, 2, 3, 3, 3, 3, 5]), (354, [1, 2, 2, 3, 3, 3, 4, 4]), (864, [1, 2, 2, 3, 3, 11]), (648, [1, 2, 2, 3, 4, 10]), (48, [1, 2, 3, 3, 3, 3, 3, 4]), (384, [1, 2, 3, 3, 3, 10]), (864, [1, 2, 3, 3, 4, 9]), (96, [1, 3, 3, 3, 4, 8]), (48, [2, 2, 2, 2, 3, 3, 3, 5]), (108, [2, 2, 2, 2, 3, 3, 4, 4]), (256, [2, 2, 2, 3, 3, 3, 3, 4]), (864, [2, 2, 2, 3, 3, 10]), (648, [2, 2, 2, 3, 4, 9]), (16, [2, 2, 3, 3, 3, 3, 3, 3]), (424, [2, 2, 3, 3, 3, 9]), (1062, [2, 2, 3, 3, 4, 8]), (864, [2, 2, 3, 3, 5, 7]), (432, [2, 2, 3, 3, 6, 6])]

def node78Piece114UnitOutput_sector0_chunk1 : RawPoly ℕ := [(648, [2, 2, 3, 4, 4, 7]), (648, [2, 2, 3, 4, 5, 6]), (2592, [2, 2, 3, 15]), (648, [2, 2, 4, 14]), (384, [2, 3, 3, 3, 3, 8]), (960, [2, 3, 3, 3, 4, 7]), (384, [2, 3, 3, 3, 5, 6]), (864, [2, 3, 3, 4, 4, 6]), (432, [2, 3, 3, 4, 5, 5]), (3456, [2, 3, 3, 14]), (2592, [2, 3, 4, 13]), (96, [3, 3, 3, 3, 4, 6]), (96, [3, 3, 3, 4, 4, 5]), (384, [3, 3, 3, 13]), (864, [3, 3, 4, 12])]

def node78Piece114UnitOutput_sector0 : RawPoly ℕ := [node78Piece114UnitOutput_sector0_chunk0, node78Piece114UnitOutput_sector0_chunk1].flatten

def node78Piece114UnitOutput : SectorVector := [(0, node78Piece114UnitOutput_sector0)]

theorem node78Piece114_check : VectorCertificate (neutralBoundS JR (-2) node78Piece114UnitInput) node78Piece114UnitOutput := by decide +kernel

theorem node78Piece114_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece114Input) = evaluate node78Piece114Output :=
  mode_of_scaled _ _ (1120/27) node78Piece114UnitInput node78Piece114UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece114_check)

def node78Piece115Input_sector0 : RawPoly ℕ := [(-48, [2, 2, 3, 10])]

def node78Piece115Input : SectorVector := [(0, node78Piece115Input_sector0)]
def node78Piece115Output_sector0_chunk0 : RawPoly ℕ := [(-192, [1, 1, 1, 2, 2, 2, 3, 10]), (-5760, [1, 1, 2, 2, 3, 13]), (-1728, [1, 1, 2, 2, 6, 10]), (-2304, [1, 1, 2, 3, 5, 10]), (-11520, [1, 2, 2, 2, 3, 12]), (-3456, [1, 2, 2, 2, 5, 10]), (-11520, [1, 2, 2, 3, 3, 11]), (-19296, [1, 2, 2, 3, 4, 10]), (-11520, [1, 2, 2, 3, 5, 9]), (-11520, [1, 2, 2, 3, 6, 8]), (-5760, [1, 2, 2, 3, 7, 7]), (-34560, [1, 2, 2, 17]), (-2304, [1, 2, 3, 3, 3, 10]), (-46080, [1, 2, 3, 16]), (-13824, [1, 2, 9, 10]), (-4608, [1, 3, 8, 10]), (-5760, [2, 2, 2, 2, 3, 11]), (-1728, [2, 2, 2, 2, 4, 10]), (-15744, [2, 2, 2, 3, 3, 10]), (-11520, [2, 2, 2, 3, 4, 9]), (-11520, [2, 2, 2, 3, 5, 8]), (-11520, [2, 2, 2, 3, 6, 7]), (-34560, [2, 2, 2, 16]), (-5760, [2, 2, 3, 3, 3, 9])]

def node78Piece115Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 2, 3, 3, 4, 8]), (-11520, [2, 2, 3, 3, 5, 7]), (-5760, [2, 2, 3, 3, 6, 6]), (-5760, [2, 2, 3, 4, 4, 7]), (-11520, [2, 2, 3, 4, 5, 6]), (-1920, [2, 2, 3, 5, 5, 5]), (291840, [2, 2, 3, 15]), (-34560, [2, 2, 4, 14]), (-34560, [2, 2, 5, 13]), (-34560, [2, 2, 6, 12]), (-34560, [2, 2, 7, 11]), (-27360, [2, 2, 8, 10]), (-17280, [2, 2, 9, 9]), (-46080, [2, 3, 3, 14]), (-46080, [2, 3, 4, 13]), (-46080, [2, 3, 5, 12]), (-46080, [2, 3, 6, 11]), (-46080, [2, 3, 7, 10]), (-46080, [2, 3, 8, 9]), (-13824, [2, 4, 6, 10]), (-6912, [2, 5, 5, 10]), (-138240, [2, 20]), (-4608, [3, 3, 6, 10]), (-4608, [3, 4, 5, 10])]

def node78Piece115Output_sector0_chunk2 : RawPoly ℕ := [(-46080, [3, 19]), (-13824, [10, 12])]

def node78Piece115Output_sector0 : RawPoly ℕ := [node78Piece115Output_sector0_chunk0, node78Piece115Output_sector0_chunk1, node78Piece115Output_sector0_chunk2].flatten

def node78Piece115Output : SectorVector := [(0, node78Piece115Output_sector0)]

def node78Piece115UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 10])]

def node78Piece115UnitInput_sector0 : RawPoly ℕ := [node78Piece115UnitInput_sector0_chunk0].flatten

def node78Piece115UnitInput : SectorVector := [(0, node78Piece115UnitInput_sector0)]

def node78Piece115UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 3, 10]), (120, [1, 1, 2, 2, 3, 13]), (36, [1, 1, 2, 2, 6, 10]), (48, [1, 1, 2, 3, 5, 10]), (240, [1, 2, 2, 2, 3, 12]), (72, [1, 2, 2, 2, 5, 10]), (240, [1, 2, 2, 3, 3, 11]), (402, [1, 2, 2, 3, 4, 10]), (240, [1, 2, 2, 3, 5, 9]), (240, [1, 2, 2, 3, 6, 8]), (120, [1, 2, 2, 3, 7, 7]), (720, [1, 2, 2, 17]), (48, [1, 2, 3, 3, 3, 10]), (960, [1, 2, 3, 16]), (288, [1, 2, 9, 10]), (96, [1, 3, 8, 10]), (120, [2, 2, 2, 2, 3, 11]), (36, [2, 2, 2, 2, 4, 10]), (328, [2, 2, 2, 3, 3, 10]), (240, [2, 2, 2, 3, 4, 9]), (240, [2, 2, 2, 3, 5, 8]), (240, [2, 2, 2, 3, 6, 7]), (720, [2, 2, 2, 16]), (120, [2, 2, 3, 3, 3, 9])]

def node78Piece115UnitOutput_sector0_chunk1 : RawPoly ℕ := [(240, [2, 2, 3, 3, 4, 8]), (240, [2, 2, 3, 3, 5, 7]), (120, [2, 2, 3, 3, 6, 6]), (120, [2, 2, 3, 4, 4, 7]), (240, [2, 2, 3, 4, 5, 6]), (40, [2, 2, 3, 5, 5, 5]), (-6080, [2, 2, 3, 15]), (720, [2, 2, 4, 14]), (720, [2, 2, 5, 13]), (720, [2, 2, 6, 12]), (720, [2, 2, 7, 11]), (570, [2, 2, 8, 10]), (360, [2, 2, 9, 9]), (960, [2, 3, 3, 14]), (960, [2, 3, 4, 13]), (960, [2, 3, 5, 12]), (960, [2, 3, 6, 11]), (960, [2, 3, 7, 10]), (960, [2, 3, 8, 9]), (288, [2, 4, 6, 10]), (144, [2, 5, 5, 10]), (2880, [2, 20]), (96, [3, 3, 6, 10]), (96, [3, 4, 5, 10])]

def node78Piece115UnitOutput_sector0_chunk2 : RawPoly ℕ := [(960, [3, 19]), (288, [10, 12])]

def node78Piece115UnitOutput_sector0 : RawPoly ℕ := [node78Piece115UnitOutput_sector0_chunk0, node78Piece115UnitOutput_sector0_chunk1, node78Piece115UnitOutput_sector0_chunk2].flatten

def node78Piece115UnitOutput : SectorVector := [(0, node78Piece115UnitOutput_sector0)]

theorem node78Piece115_check : VectorCertificate (neutralBoundS JR (-2) node78Piece115UnitInput) node78Piece115UnitOutput := by decide +kernel

theorem node78Piece115_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece115Input) = evaluate node78Piece115Output :=
  mode_of_scaled _ _ (-48) node78Piece115UnitInput node78Piece115UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece115_check)

def node78Piece116Input_sector0 : RawPoly ℕ := [(-560/3, [2, 2, 4, 9])]

def node78Piece116Input : SectorVector := [(0, node78Piece116Input_sector0)]
def node78Piece116Output_sector0_chunk0 : RawPoly ℕ := [(-2240/3, [1, 1, 1, 2, 2, 2, 4, 9]), (-20160, [1, 1, 2, 2, 4, 12]), (-8960, [1, 1, 2, 2, 7, 9]), (-8960, [1, 1, 2, 4, 5, 9]), (-40320, [1, 2, 2, 2, 4, 11]), (-17920, [1, 2, 2, 2, 6, 9]), (-40320, [1, 2, 2, 3, 4, 10]), (-17920, [1, 2, 2, 3, 5, 9]), (-66080, [1, 2, 2, 4, 4, 9]), (-40320, [1, 2, 2, 4, 5, 8]), (-40320, [1, 2, 2, 4, 6, 7]), (-161280, [1, 2, 2, 17]), (-8960, [1, 2, 3, 3, 4, 9]), (-161280, [1, 2, 4, 15]), (-71680, [1, 2, 9, 10]), (-17920, [1, 4, 8, 9]), (-20160, [2, 2, 2, 2, 4, 10]), (-8960, [2, 2, 2, 2, 5, 9]), (-203840/3, [2, 2, 2, 3, 4, 9]), (-40320, [2, 2, 2, 4, 4, 8]), (-40320, [2, 2, 2, 4, 5, 7]), (-20160, [2, 2, 2, 4, 6, 6]), (-161280, [2, 2, 2, 16]), (-8960/3, [2, 2, 3, 3, 3, 9])]

def node78Piece116Output_sector0_chunk1 : RawPoly ℕ := [(-20160, [2, 2, 3, 3, 4, 8]), (-40320, [2, 2, 3, 4, 4, 7]), (-40320, [2, 2, 3, 4, 5, 6]), (-161280, [2, 2, 3, 15]), (-20160, [2, 2, 4, 4, 4, 6]), (-20160, [2, 2, 4, 4, 5, 5]), (779520, [2, 2, 4, 14]), (-161280, [2, 2, 5, 13]), (-161280, [2, 2, 6, 12]), (-161280, [2, 2, 7, 11]), (-161280, [2, 2, 8, 10]), (4480/3, [2, 2, 9, 9]), (-161280, [2, 3, 4, 13]), (-71680, [2, 3, 8, 9]), (-161280, [2, 4, 4, 12]), (-161280, [2, 4, 5, 11]), (-161280, [2, 4, 6, 10]), (-179200, [2, 4, 7, 9]), (-80640, [2, 4, 8, 8]), (-71680, [2, 5, 6, 9]), (-645120, [2, 20]), (-17920, [3, 4, 6, 9]), (-17920, [4, 4, 5, 9]), (-161280, [4, 18])]

def node78Piece116Output_sector0_chunk2 : RawPoly ℕ := [(-71680, [9, 13])]

def node78Piece116Output_sector0 : RawPoly ℕ := [node78Piece116Output_sector0_chunk0, node78Piece116Output_sector0_chunk1, node78Piece116Output_sector0_chunk2].flatten

def node78Piece116Output : SectorVector := [(0, node78Piece116Output_sector0)]

def node78Piece116UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 4, 9])]

def node78Piece116UnitInput_sector0 : RawPoly ℕ := [node78Piece116UnitInput_sector0_chunk0].flatten

def node78Piece116UnitInput : SectorVector := [(0, node78Piece116UnitInput_sector0)]

def node78Piece116UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 4, 9]), (108, [1, 1, 2, 2, 4, 12]), (48, [1, 1, 2, 2, 7, 9]), (48, [1, 1, 2, 4, 5, 9]), (216, [1, 2, 2, 2, 4, 11]), (96, [1, 2, 2, 2, 6, 9]), (216, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 5, 9]), (354, [1, 2, 2, 4, 4, 9]), (216, [1, 2, 2, 4, 5, 8]), (216, [1, 2, 2, 4, 6, 7]), (864, [1, 2, 2, 17]), (48, [1, 2, 3, 3, 4, 9]), (864, [1, 2, 4, 15]), (384, [1, 2, 9, 10]), (96, [1, 4, 8, 9]), (108, [2, 2, 2, 2, 4, 10]), (48, [2, 2, 2, 2, 5, 9]), (364, [2, 2, 2, 3, 4, 9]), (216, [2, 2, 2, 4, 4, 8]), (216, [2, 2, 2, 4, 5, 7]), (108, [2, 2, 2, 4, 6, 6]), (864, [2, 2, 2, 16]), (16, [2, 2, 3, 3, 3, 9])]

def node78Piece116UnitOutput_sector0_chunk1 : RawPoly ℕ := [(108, [2, 2, 3, 3, 4, 8]), (216, [2, 2, 3, 4, 4, 7]), (216, [2, 2, 3, 4, 5, 6]), (864, [2, 2, 3, 15]), (108, [2, 2, 4, 4, 4, 6]), (108, [2, 2, 4, 4, 5, 5]), (-4176, [2, 2, 4, 14]), (864, [2, 2, 5, 13]), (864, [2, 2, 6, 12]), (864, [2, 2, 7, 11]), (864, [2, 2, 8, 10]), (-8, [2, 2, 9, 9]), (864, [2, 3, 4, 13]), (384, [2, 3, 8, 9]), (864, [2, 4, 4, 12]), (864, [2, 4, 5, 11]), (864, [2, 4, 6, 10]), (960, [2, 4, 7, 9]), (432, [2, 4, 8, 8]), (384, [2, 5, 6, 9]), (3456, [2, 20]), (96, [3, 4, 6, 9]), (96, [4, 4, 5, 9]), (864, [4, 18])]

def node78Piece116UnitOutput_sector0_chunk2 : RawPoly ℕ := [(384, [9, 13])]

def node78Piece116UnitOutput_sector0 : RawPoly ℕ := [node78Piece116UnitOutput_sector0_chunk0, node78Piece116UnitOutput_sector0_chunk1, node78Piece116UnitOutput_sector0_chunk2].flatten

def node78Piece116UnitOutput : SectorVector := [(0, node78Piece116UnitOutput_sector0)]

theorem node78Piece116_check : VectorCertificate (neutralBoundS JR (-2) node78Piece116UnitInput) node78Piece116UnitOutput := by decide +kernel

theorem node78Piece116_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece116Input) = evaluate node78Piece116Output :=
  mode_of_scaled _ _ (-560/3) node78Piece116UnitInput node78Piece116UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece116_check)

def node78Piece117Input_sector0 : RawPoly ℕ := [(-108, [2, 2, 5, 8])]

def node78Piece117Input : SectorVector := [(0, node78Piece117Input_sector0)]
def node78Piece117Output_sector0_chunk0 : RawPoly ℕ := [(-432, [1, 1, 1, 2, 2, 2, 5, 8]), (-10368, [1, 1, 2, 2, 5, 11]), (-6480, [1, 1, 2, 2, 8, 8]), (-5184, [1, 1, 2, 5, 5, 8]), (-20736, [1, 2, 2, 2, 5, 10]), (-12960, [1, 2, 2, 2, 7, 8]), (-20736, [1, 2, 2, 3, 5, 9]), (-12960, [1, 2, 2, 3, 6, 8]), (-43416, [1, 2, 2, 4, 5, 8]), (-20736, [1, 2, 2, 5, 5, 7]), (-10368, [1, 2, 2, 5, 6, 6]), (-103680, [1, 2, 2, 17]), (-5184, [1, 2, 3, 3, 5, 8]), (-82944, [1, 2, 5, 14]), (-51840, [1, 2, 8, 11]), (-10368, [1, 5, 8, 8]), (-10368, [2, 2, 2, 2, 5, 9]), (-6480, [2, 2, 2, 2, 6, 8]), (-39312, [2, 2, 2, 3, 5, 8]), (-6480, [2, 2, 2, 4, 4, 8]), (-20736, [2, 2, 2, 4, 5, 7]), (-20736, [2, 2, 2, 5, 5, 6]), (-103680, [2, 2, 2, 16]), (-6480, [2, 2, 3, 3, 4, 8])]

def node78Piece117Output_sector0_chunk1 : RawPoly ℕ := [(-10368, [2, 2, 3, 3, 5, 7]), (-20736, [2, 2, 3, 4, 5, 6]), (-10368, [2, 2, 3, 5, 5, 5]), (-103680, [2, 2, 3, 15]), (-10368, [2, 2, 4, 4, 5, 5]), (-103680, [2, 2, 4, 14]), (285120, [2, 2, 5, 13]), (-103680, [2, 2, 6, 12]), (-103680, [2, 2, 7, 11]), (-6480, [2, 2, 8, 10]), (-51840, [2, 2, 9, 9]), (-82944, [2, 3, 5, 12]), (-51840, [2, 3, 8, 9]), (-82944, [2, 4, 5, 11]), (-51840, [2, 4, 8, 8]), (-82944, [2, 5, 5, 10]), (-82944, [2, 5, 6, 9]), (-103680, [2, 5, 7, 8]), (-25920, [2, 6, 6, 8]), (-414720, [2, 20]), (-10368, [3, 5, 6, 8]), (-10368, [4, 5, 5, 8]), (-82944, [5, 17]), (-51840, [8, 14])]

def node78Piece117Output_sector0 : RawPoly ℕ := [node78Piece117Output_sector0_chunk0, node78Piece117Output_sector0_chunk1].flatten

def node78Piece117Output : SectorVector := [(0, node78Piece117Output_sector0)]

def node78Piece117UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 5, 8])]

def node78Piece117UnitInput_sector0 : RawPoly ℕ := [node78Piece117UnitInput_sector0_chunk0].flatten

def node78Piece117UnitInput : SectorVector := [(0, node78Piece117UnitInput_sector0)]

def node78Piece117UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 5, 8]), (96, [1, 1, 2, 2, 5, 11]), (60, [1, 1, 2, 2, 8, 8]), (48, [1, 1, 2, 5, 5, 8]), (192, [1, 2, 2, 2, 5, 10]), (120, [1, 2, 2, 2, 7, 8]), (192, [1, 2, 2, 3, 5, 9]), (120, [1, 2, 2, 3, 6, 8]), (402, [1, 2, 2, 4, 5, 8]), (192, [1, 2, 2, 5, 5, 7]), (96, [1, 2, 2, 5, 6, 6]), (960, [1, 2, 2, 17]), (48, [1, 2, 3, 3, 5, 8]), (768, [1, 2, 5, 14]), (480, [1, 2, 8, 11]), (96, [1, 5, 8, 8]), (96, [2, 2, 2, 2, 5, 9]), (60, [2, 2, 2, 2, 6, 8]), (364, [2, 2, 2, 3, 5, 8]), (60, [2, 2, 2, 4, 4, 8]), (192, [2, 2, 2, 4, 5, 7]), (192, [2, 2, 2, 5, 5, 6]), (960, [2, 2, 2, 16]), (60, [2, 2, 3, 3, 4, 8])]

def node78Piece117UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [2, 2, 3, 3, 5, 7]), (192, [2, 2, 3, 4, 5, 6]), (96, [2, 2, 3, 5, 5, 5]), (960, [2, 2, 3, 15]), (96, [2, 2, 4, 4, 5, 5]), (960, [2, 2, 4, 14]), (-2640, [2, 2, 5, 13]), (960, [2, 2, 6, 12]), (960, [2, 2, 7, 11]), (60, [2, 2, 8, 10]), (480, [2, 2, 9, 9]), (768, [2, 3, 5, 12]), (480, [2, 3, 8, 9]), (768, [2, 4, 5, 11]), (480, [2, 4, 8, 8]), (768, [2, 5, 5, 10]), (768, [2, 5, 6, 9]), (960, [2, 5, 7, 8]), (240, [2, 6, 6, 8]), (3840, [2, 20]), (96, [3, 5, 6, 8]), (96, [4, 5, 5, 8]), (768, [5, 17]), (480, [8, 14])]

def node78Piece117UnitOutput_sector0 : RawPoly ℕ := [node78Piece117UnitOutput_sector0_chunk0, node78Piece117UnitOutput_sector0_chunk1].flatten

def node78Piece117UnitOutput : SectorVector := [(0, node78Piece117UnitOutput_sector0)]

theorem node78Piece117_check : VectorCertificate (neutralBoundS JR (-2) node78Piece117UnitInput) node78Piece117UnitOutput := by decide +kernel

theorem node78Piece117_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece117Input) = evaluate node78Piece117Output :=
  mode_of_scaled _ _ (-108) node78Piece117UnitInput node78Piece117UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece117_check)

def node78Piece118Input_sector0 : RawPoly ℕ := [(-800/7, [2, 2, 6, 7])]

def node78Piece118Input : SectorVector := [(0, node78Piece118Input_sector0)]
def node78Piece118Output_sector0_chunk0 : RawPoly ℕ := [(-3200/7, [1, 1, 1, 2, 2, 2, 6, 7]), (-9600, [1, 1, 2, 2, 6, 10]), (-57600/7, [1, 1, 2, 2, 7, 9]), (-38400/7, [1, 1, 2, 5, 6, 7]), (-19200, [1, 2, 2, 2, 6, 9]), (-115200/7, [1, 2, 2, 2, 7, 8]), (-19200, [1, 2, 2, 3, 6, 8]), (-115200/7, [1, 2, 2, 3, 7, 7]), (-321600/7, [1, 2, 2, 4, 6, 7]), (-57600/7, [1, 2, 2, 5, 5, 7]), (-19200, [1, 2, 2, 5, 6, 6]), (-115200, [1, 2, 2, 17]), (-38400/7, [1, 2, 3, 3, 6, 7]), (-76800, [1, 2, 6, 13]), (-460800/7, [1, 2, 7, 12]), (-76800/7, [1, 6, 7, 8]), (-9600, [2, 2, 2, 2, 6, 8]), (-57600/7, [2, 2, 2, 2, 7, 7]), (-41600, [2, 2, 2, 3, 6, 7]), (-115200/7, [2, 2, 2, 4, 5, 7]), (-19200, [2, 2, 2, 4, 6, 6]), (-9600, [2, 2, 2, 5, 5, 6]), (-115200, [2, 2, 2, 16]), (-57600/7, [2, 2, 3, 3, 5, 7])]

def node78Piece118Output_sector0_chunk1 : RawPoly ℕ := [(-9600, [2, 2, 3, 3, 6, 6]), (-57600/7, [2, 2, 3, 4, 4, 7]), (-19200, [2, 2, 3, 4, 5, 6]), (-115200, [2, 2, 3, 15]), (-3200, [2, 2, 4, 4, 4, 6]), (-115200, [2, 2, 4, 14]), (-115200, [2, 2, 5, 13]), (164800, [2, 2, 6, 12]), (441600/7, [2, 2, 7, 11]), (-115200, [2, 2, 8, 10]), (-57600, [2, 2, 9, 9]), (-76800, [2, 3, 6, 11]), (-460800/7, [2, 3, 7, 10]), (-76800, [2, 4, 6, 10]), (-460800/7, [2, 4, 7, 9]), (-76800, [2, 5, 6, 9]), (-460800/7, [2, 5, 7, 8]), (-76800, [2, 6, 6, 8]), (-499200/7, [2, 6, 7, 7]), (-460800, [2, 20]), (-76800/7, [3, 6, 6, 7]), (-76800/7, [4, 5, 6, 7]), (-76800, [6, 16]), (-460800/7, [7, 15])]

def node78Piece118Output_sector0 : RawPoly ℕ := [node78Piece118Output_sector0_chunk0, node78Piece118Output_sector0_chunk1].flatten

def node78Piece118Output : SectorVector := [(0, node78Piece118Output_sector0)]

def node78Piece118UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 6, 7])]

def node78Piece118UnitInput_sector0 : RawPoly ℕ := [node78Piece118UnitInput_sector0_chunk0].flatten

def node78Piece118UnitInput : SectorVector := [(0, node78Piece118UnitInput_sector0)]

def node78Piece118UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 6, 7]), (84, [1, 1, 2, 2, 6, 10]), (72, [1, 1, 2, 2, 7, 9]), (48, [1, 1, 2, 5, 6, 7]), (168, [1, 2, 2, 2, 6, 9]), (144, [1, 2, 2, 2, 7, 8]), (168, [1, 2, 2, 3, 6, 8]), (144, [1, 2, 2, 3, 7, 7]), (402, [1, 2, 2, 4, 6, 7]), (72, [1, 2, 2, 5, 5, 7]), (168, [1, 2, 2, 5, 6, 6]), (1008, [1, 2, 2, 17]), (48, [1, 2, 3, 3, 6, 7]), (672, [1, 2, 6, 13]), (576, [1, 2, 7, 12]), (96, [1, 6, 7, 8]), (84, [2, 2, 2, 2, 6, 8]), (72, [2, 2, 2, 2, 7, 7]), (364, [2, 2, 2, 3, 6, 7]), (144, [2, 2, 2, 4, 5, 7]), (168, [2, 2, 2, 4, 6, 6]), (84, [2, 2, 2, 5, 5, 6]), (1008, [2, 2, 2, 16]), (72, [2, 2, 3, 3, 5, 7])]

def node78Piece118UnitOutput_sector0_chunk1 : RawPoly ℕ := [(84, [2, 2, 3, 3, 6, 6]), (72, [2, 2, 3, 4, 4, 7]), (168, [2, 2, 3, 4, 5, 6]), (1008, [2, 2, 3, 15]), (28, [2, 2, 4, 4, 4, 6]), (1008, [2, 2, 4, 14]), (1008, [2, 2, 5, 13]), (-1442, [2, 2, 6, 12]), (-552, [2, 2, 7, 11]), (1008, [2, 2, 8, 10]), (504, [2, 2, 9, 9]), (672, [2, 3, 6, 11]), (576, [2, 3, 7, 10]), (672, [2, 4, 6, 10]), (576, [2, 4, 7, 9]), (672, [2, 5, 6, 9]), (576, [2, 5, 7, 8]), (672, [2, 6, 6, 8]), (624, [2, 6, 7, 7]), (4032, [2, 20]), (96, [3, 6, 6, 7]), (96, [4, 5, 6, 7]), (672, [6, 16]), (576, [7, 15])]

def node78Piece118UnitOutput_sector0 : RawPoly ℕ := [node78Piece118UnitOutput_sector0_chunk0, node78Piece118UnitOutput_sector0_chunk1].flatten

def node78Piece118UnitOutput : SectorVector := [(0, node78Piece118UnitOutput_sector0)]

theorem node78Piece118_check : VectorCertificate (neutralBoundS JR (-2) node78Piece118UnitInput) node78Piece118UnitOutput := by decide +kernel

theorem node78Piece118_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece118Input) = evaluate node78Piece118Output :=
  mode_of_scaled _ _ (-800/7) node78Piece118UnitInput node78Piece118UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece118_check)

def node78Piece119Input_sector0 : RawPoly ℕ := [(1216/81, [2, 3, 3, 3, 3, 3])]

def node78Piece119Input : SectorVector := [(0, node78Piece119Input_sector0)]
def node78Piece119Output_sector0 : RawPoly ℕ := [(4864/81, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (24320/9, [1, 1, 2, 3, 3, 3, 3, 6]), (9728/27, [1, 1, 3, 3, 3, 3, 3, 5]), (48640/9, [1, 2, 2, 3, 3, 3, 3, 5]), (162944/27, [1, 2, 3, 3, 3, 3, 3, 4]), (97280/3, [1, 2, 3, 3, 3, 10]), (9728/27, [1, 3, 3, 3, 3, 3, 3, 3]), (97280/9, [1, 3, 3, 3, 3, 9]), (24320/9, [2, 2, 2, 3, 3, 3, 3, 4]), (252928/81, [2, 2, 3, 3, 3, 3, 3, 3]), (97280/3, [2, 2, 3, 3, 3, 9]), (279680/27, [2, 3, 3, 3, 3, 8]), (97280/3, [2, 3, 3, 3, 4, 7]), (97280/3, [2, 3, 3, 3, 5, 6]), (97280, [2, 3, 3, 14]), (214016/27, [3, 3, 3, 3, 3, 7]), (97280/9, [3, 3, 3, 3, 4, 6]), (48640/9, [3, 3, 3, 3, 5, 5]), (194560/3, [3, 3, 3, 13])]

def node78Piece119Output : SectorVector := [(0, node78Piece119Output_sector0)]

def node78Piece119UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 3, 3, 3])]

def node78Piece119UnitInput_sector0 : RawPoly ℕ := [node78Piece119UnitInput_sector0_chunk0].flatten

def node78Piece119UnitInput : SectorVector := [(0, node78Piece119UnitInput_sector0)]

def node78Piece119UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (180, [1, 1, 2, 3, 3, 3, 3, 6]), (24, [1, 1, 3, 3, 3, 3, 3, 5]), (360, [1, 2, 2, 3, 3, 3, 3, 5]), (402, [1, 2, 3, 3, 3, 3, 3, 4]), (2160, [1, 2, 3, 3, 3, 10]), (24, [1, 3, 3, 3, 3, 3, 3, 3]), (720, [1, 3, 3, 3, 3, 9]), (180, [2, 2, 2, 3, 3, 3, 3, 4]), (208, [2, 2, 3, 3, 3, 3, 3, 3]), (2160, [2, 2, 3, 3, 3, 9]), (690, [2, 3, 3, 3, 3, 8]), (2160, [2, 3, 3, 3, 4, 7]), (2160, [2, 3, 3, 3, 5, 6]), (6480, [2, 3, 3, 14]), (528, [3, 3, 3, 3, 3, 7]), (720, [3, 3, 3, 3, 4, 6]), (360, [3, 3, 3, 3, 5, 5]), (4320, [3, 3, 3, 13])]

def node78Piece119UnitOutput_sector0 : RawPoly ℕ := [node78Piece119UnitOutput_sector0_chunk0].flatten

def node78Piece119UnitOutput : SectorVector := [(0, node78Piece119UnitOutput_sector0)]

theorem node78Piece119_check : VectorCertificate (neutralBoundS JR (-2) node78Piece119UnitInput) node78Piece119UnitOutput := by decide +kernel

theorem node78Piece119_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece119Input) = evaluate node78Piece119Output :=
  mode_of_scaled _ _ (1216/81) node78Piece119UnitInput node78Piece119UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece119_check)

def node78Piece120Input_sector0 : RawPoly ℕ := [(320/3, [2, 3, 3, 9])]

def node78Piece120Input : SectorVector := [(0, node78Piece120Input_sector0)]
def node78Piece120Output_sector0_chunk0 : RawPoly ℕ := [(1280/3, [1, 1, 1, 2, 2, 3, 3, 9]), (11520, [1, 1, 2, 3, 3, 12]), (7680, [1, 1, 2, 3, 6, 9]), (2560, [1, 1, 3, 3, 5, 9]), (23040, [1, 2, 2, 3, 3, 11]), (15360, [1, 2, 2, 3, 5, 9]), (23040, [1, 2, 3, 3, 3, 10]), (42880, [1, 2, 3, 3, 4, 9]), (23040, [1, 2, 3, 3, 5, 8]), (23040, [1, 2, 3, 3, 6, 7]), (138240, [1, 2, 3, 16]), (23040, [1, 2, 9, 10]), (2560, [1, 3, 3, 3, 3, 9]), (46080, [1, 3, 3, 15]), (30720, [1, 3, 9, 9]), (11520, [2, 2, 2, 3, 3, 10]), (7680, [2, 2, 2, 3, 4, 9]), (101120/3, [2, 2, 3, 3, 3, 9]), (23040, [2, 2, 3, 3, 4, 8]), (23040, [2, 2, 3, 3, 5, 7]), (11520, [2, 2, 3, 3, 6, 6]), (138240, [2, 2, 3, 15]), (23040, [2, 2, 9, 9]), (11520, [2, 3, 3, 3, 3, 8])]

def node78Piece120Output_sector0_chunk1 : RawPoly ℕ := [(23040, [2, 3, 3, 3, 4, 7]), (23040, [2, 3, 3, 3, 5, 6]), (11520, [2, 3, 3, 4, 4, 6]), (11520, [2, 3, 3, 4, 5, 5]), (-445440, [2, 3, 3, 14]), (138240, [2, 3, 4, 13]), (138240, [2, 3, 5, 12]), (138240, [2, 3, 6, 11]), (138240, [2, 3, 7, 10]), (98560, [2, 3, 8, 9]), (23040, [2, 4, 7, 9]), (23040, [2, 5, 6, 9]), (207360, [2, 20]), (46080, [3, 3, 3, 13]), (46080, [3, 3, 4, 12]), (46080, [3, 3, 5, 11]), (46080, [3, 3, 6, 10]), (56320, [3, 3, 7, 9]), (23040, [3, 3, 8, 8]), (30720, [3, 4, 6, 9]), (15360, [3, 5, 5, 9]), (276480, [3, 19]), (46080, [9, 13])]

def node78Piece120Output_sector0 : RawPoly ℕ := [node78Piece120Output_sector0_chunk0, node78Piece120Output_sector0_chunk1].flatten

def node78Piece120Output : SectorVector := [(0, node78Piece120Output_sector0)]

def node78Piece120UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 9])]

def node78Piece120UnitInput_sector0 : RawPoly ℕ := [node78Piece120UnitInput_sector0_chunk0].flatten

def node78Piece120UnitInput : SectorVector := [(0, node78Piece120UnitInput_sector0)]

def node78Piece120UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 3, 9]), (108, [1, 1, 2, 3, 3, 12]), (72, [1, 1, 2, 3, 6, 9]), (24, [1, 1, 3, 3, 5, 9]), (216, [1, 2, 2, 3, 3, 11]), (144, [1, 2, 2, 3, 5, 9]), (216, [1, 2, 3, 3, 3, 10]), (402, [1, 2, 3, 3, 4, 9]), (216, [1, 2, 3, 3, 5, 8]), (216, [1, 2, 3, 3, 6, 7]), (1296, [1, 2, 3, 16]), (216, [1, 2, 9, 10]), (24, [1, 3, 3, 3, 3, 9]), (432, [1, 3, 3, 15]), (288, [1, 3, 9, 9]), (108, [2, 2, 2, 3, 3, 10]), (72, [2, 2, 2, 3, 4, 9]), (316, [2, 2, 3, 3, 3, 9]), (216, [2, 2, 3, 3, 4, 8]), (216, [2, 2, 3, 3, 5, 7]), (108, [2, 2, 3, 3, 6, 6]), (1296, [2, 2, 3, 15]), (216, [2, 2, 9, 9]), (108, [2, 3, 3, 3, 3, 8])]

def node78Piece120UnitOutput_sector0_chunk1 : RawPoly ℕ := [(216, [2, 3, 3, 3, 4, 7]), (216, [2, 3, 3, 3, 5, 6]), (108, [2, 3, 3, 4, 4, 6]), (108, [2, 3, 3, 4, 5, 5]), (-4176, [2, 3, 3, 14]), (1296, [2, 3, 4, 13]), (1296, [2, 3, 5, 12]), (1296, [2, 3, 6, 11]), (1296, [2, 3, 7, 10]), (924, [2, 3, 8, 9]), (216, [2, 4, 7, 9]), (216, [2, 5, 6, 9]), (1944, [2, 20]), (432, [3, 3, 3, 13]), (432, [3, 3, 4, 12]), (432, [3, 3, 5, 11]), (432, [3, 3, 6, 10]), (528, [3, 3, 7, 9]), (216, [3, 3, 8, 8]), (288, [3, 4, 6, 9]), (144, [3, 5, 5, 9]), (2592, [3, 19]), (432, [9, 13])]

def node78Piece120UnitOutput_sector0 : RawPoly ℕ := [node78Piece120UnitOutput_sector0_chunk0, node78Piece120UnitOutput_sector0_chunk1].flatten

def node78Piece120UnitOutput : SectorVector := [(0, node78Piece120UnitOutput_sector0)]

theorem node78Piece120_check : VectorCertificate (neutralBoundS JR (-2) node78Piece120UnitInput) node78Piece120UnitOutput := by decide +kernel

theorem node78Piece120_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece120Input) = evaluate node78Piece120Output :=
  mode_of_scaled _ _ (320/3) node78Piece120UnitInput node78Piece120UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece120_check)

def node78Piece121Input_sector0 : RawPoly ℕ := [(-30, [2, 3, 4, 8])]

def node78Piece121Input : SectorVector := [(0, node78Piece121Input_sector0)]
def node78Piece121Output_sector0_chunk0 : RawPoly ℕ := [(-120, [1, 1, 1, 2, 2, 3, 4, 8]), (-2880, [1, 1, 2, 3, 4, 11]), (-1440, [1, 1, 2, 3, 7, 8]), (-1080, [1, 1, 2, 4, 6, 8]), (-720, [1, 1, 3, 4, 5, 8]), (-5760, [1, 2, 2, 3, 4, 10]), (-2880, [1, 2, 2, 3, 6, 8]), (-2160, [1, 2, 2, 4, 5, 8]), (-5760, [1, 2, 3, 3, 4, 9]), (-2880, [1, 2, 3, 3, 5, 8]), (-10620, [1, 2, 3, 4, 4, 8]), (-5760, [1, 2, 3, 4, 5, 7]), (-2880, [1, 2, 3, 4, 6, 6]), (-23040, [1, 2, 3, 16]), (-17280, [1, 2, 4, 15]), (-8640, [1, 2, 8, 11]), (-720, [1, 3, 3, 3, 4, 8]), (-11520, [1, 3, 4, 14]), (-5760, [1, 3, 8, 10]), (-4320, [1, 4, 8, 9]), (-2880, [2, 2, 2, 3, 4, 9]), (-1440, [2, 2, 2, 3, 5, 8]), (-1080, [2, 2, 2, 4, 4, 8]), (-10560, [2, 2, 3, 3, 4, 8])]

def node78Piece121Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [2, 2, 3, 4, 4, 7]), (-5760, [2, 2, 3, 4, 5, 6]), (-23040, [2, 2, 3, 15]), (-17280, [2, 2, 4, 14]), (-8640, [2, 2, 8, 10]), (-480, [2, 3, 3, 3, 3, 8]), (-2880, [2, 3, 3, 3, 4, 7]), (-5760, [2, 3, 3, 4, 4, 6]), (-2880, [2, 3, 3, 4, 5, 5]), (-23040, [2, 3, 3, 14]), (-2880, [2, 3, 4, 4, 4, 5]), (79200, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12]), (-23040, [2, 3, 6, 11]), (-23040, [2, 3, 7, 10]), (-12720, [2, 3, 8, 9]), (-17280, [2, 4, 4, 12]), (-17280, [2, 4, 5, 11]), (-17280, [2, 4, 6, 10]), (-17280, [2, 4, 7, 9]), (-8460, [2, 4, 8, 8]), (-8640, [2, 5, 7, 8]), (-4320, [2, 6, 6, 8]), (-69120, [2, 20])]

def node78Piece121Output_sector0_chunk2 : RawPoly ℕ := [(-11520, [3, 3, 4, 12]), (-5760, [3, 3, 8, 8]), (-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-15840, [3, 4, 7, 8]), (-5760, [3, 5, 6, 8]), (-46080, [3, 19]), (-4320, [4, 4, 6, 8]), (-2160, [4, 5, 5, 8]), (-34560, [4, 18]), (-17280, [8, 14])]

def node78Piece121Output_sector0 : RawPoly ℕ := [node78Piece121Output_sector0_chunk0, node78Piece121Output_sector0_chunk1, node78Piece121Output_sector0_chunk2].flatten

def node78Piece121Output : SectorVector := [(0, node78Piece121Output_sector0)]

def node78Piece121UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 4, 8])]

def node78Piece121UnitInput_sector0 : RawPoly ℕ := [node78Piece121UnitInput_sector0_chunk0].flatten

def node78Piece121UnitInput : SectorVector := [(0, node78Piece121UnitInput_sector0)]

def node78Piece121UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 4, 8]), (96, [1, 1, 2, 3, 4, 11]), (48, [1, 1, 2, 3, 7, 8]), (36, [1, 1, 2, 4, 6, 8]), (24, [1, 1, 3, 4, 5, 8]), (192, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 6, 8]), (72, [1, 2, 2, 4, 5, 8]), (192, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 5, 8]), (354, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (96, [1, 2, 3, 4, 6, 6]), (768, [1, 2, 3, 16]), (576, [1, 2, 4, 15]), (288, [1, 2, 8, 11]), (24, [1, 3, 3, 3, 4, 8]), (384, [1, 3, 4, 14]), (192, [1, 3, 8, 10]), (144, [1, 4, 8, 9]), (96, [2, 2, 2, 3, 4, 9]), (48, [2, 2, 2, 3, 5, 8]), (36, [2, 2, 2, 4, 4, 8]), (352, [2, 2, 3, 3, 4, 8])]

def node78Piece121UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [2, 2, 3, 4, 4, 7]), (192, [2, 2, 3, 4, 5, 6]), (768, [2, 2, 3, 15]), (576, [2, 2, 4, 14]), (288, [2, 2, 8, 10]), (16, [2, 3, 3, 3, 3, 8]), (96, [2, 3, 3, 3, 4, 7]), (192, [2, 3, 3, 4, 4, 6]), (96, [2, 3, 3, 4, 5, 5]), (768, [2, 3, 3, 14]), (96, [2, 3, 4, 4, 4, 5]), (-2640, [2, 3, 4, 13]), (768, [2, 3, 5, 12]), (768, [2, 3, 6, 11]), (768, [2, 3, 7, 10]), (424, [2, 3, 8, 9]), (576, [2, 4, 4, 12]), (576, [2, 4, 5, 11]), (576, [2, 4, 6, 10]), (576, [2, 4, 7, 9]), (282, [2, 4, 8, 8]), (288, [2, 5, 7, 8]), (144, [2, 6, 6, 8]), (2304, [2, 20])]

def node78Piece121UnitOutput_sector0_chunk2 : RawPoly ℕ := [(384, [3, 3, 4, 12]), (192, [3, 3, 8, 8]), (384, [3, 4, 4, 11]), (384, [3, 4, 5, 10]), (384, [3, 4, 6, 9]), (528, [3, 4, 7, 8]), (192, [3, 5, 6, 8]), (1536, [3, 19]), (144, [4, 4, 6, 8]), (72, [4, 5, 5, 8]), (1152, [4, 18]), (576, [8, 14])]

def node78Piece121UnitOutput_sector0 : RawPoly ℕ := [node78Piece121UnitOutput_sector0_chunk0, node78Piece121UnitOutput_sector0_chunk1, node78Piece121UnitOutput_sector0_chunk2].flatten

def node78Piece121UnitOutput : SectorVector := [(0, node78Piece121UnitOutput_sector0)]

theorem node78Piece121_check : VectorCertificate (neutralBoundS JR (-2) node78Piece121UnitInput) node78Piece121UnitOutput := by decide +kernel

theorem node78Piece121_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece121Input) = evaluate node78Piece121Output :=
  mode_of_scaled _ _ (-30) node78Piece121UnitInput node78Piece121UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece121_check)

def node78Piece122Input_sector0 : RawPoly ℕ := [(64, [2, 3, 5, 7])]

def node78Piece122Input : SectorVector := [(0, node78Piece122Input_sector0)]
def node78Piece122Output_sector0_chunk0 : RawPoly ℕ := [(256, [1, 1, 1, 2, 2, 3, 5, 7]), (5376, [1, 1, 2, 3, 5, 10]), (3840, [1, 1, 2, 3, 7, 8]), (2304, [1, 1, 2, 5, 6, 7]), (1536, [1, 1, 3, 5, 5, 7]), (10752, [1, 2, 2, 3, 5, 9]), (7680, [1, 2, 2, 3, 7, 7]), (4608, [1, 2, 2, 5, 5, 7]), (10752, [1, 2, 3, 3, 5, 8]), (7680, [1, 2, 3, 3, 6, 7]), (25728, [1, 2, 3, 4, 5, 7]), (10752, [1, 2, 3, 5, 5, 6]), (53760, [1, 2, 3, 16]), (32256, [1, 2, 5, 14]), (23040, [1, 2, 7, 12]), (1536, [1, 3, 3, 3, 5, 7]), (21504, [1, 3, 5, 13]), (15360, [1, 3, 7, 11]), (9216, [1, 5, 7, 9]), (5376, [2, 2, 2, 3, 5, 8]), (3840, [2, 2, 2, 3, 6, 7]), (2304, [2, 2, 2, 4, 5, 7]), (22528, [2, 2, 3, 3, 5, 7]), (3840, [2, 2, 3, 4, 4, 7])]

def node78Piece122Output_sector0_chunk1 : RawPoly ℕ := [(10752, [2, 2, 3, 4, 5, 6]), (5376, [2, 2, 3, 5, 5, 5]), (53760, [2, 2, 3, 15]), (32256, [2, 2, 5, 13]), (23040, [2, 2, 7, 11]), (3840, [2, 3, 3, 3, 4, 7]), (5376, [2, 3, 3, 3, 5, 6]), (10752, [2, 3, 3, 4, 5, 5]), (53760, [2, 3, 3, 14]), (1792, [2, 3, 4, 4, 4, 5]), (53760, [2, 3, 4, 13]), (-92288, [2, 3, 5, 12]), (53760, [2, 3, 6, 11]), (3840, [2, 3, 7, 10]), (53760, [2, 3, 8, 9]), (32256, [2, 4, 5, 11]), (23040, [2, 4, 7, 9]), (32256, [2, 5, 5, 10]), (32256, [2, 5, 6, 9]), (36480, [2, 5, 7, 8]), (23040, [2, 6, 7, 7]), (161280, [2, 20]), (21504, [3, 3, 5, 11]), (15360, [3, 3, 7, 9])]

def node78Piece122Output_sector0_chunk2 : RawPoly ℕ := [(21504, [3, 4, 5, 10]), (15360, [3, 4, 7, 8]), (21504, [3, 5, 5, 9]), (21504, [3, 5, 6, 8]), (23040, [3, 5, 7, 7]), (7680, [3, 6, 6, 7]), (107520, [3, 19]), (9216, [4, 5, 6, 7]), (4608, [5, 5, 5, 7]), (64512, [5, 17]), (46080, [7, 15])]

def node78Piece122Output_sector0 : RawPoly ℕ := [node78Piece122Output_sector0_chunk0, node78Piece122Output_sector0_chunk1, node78Piece122Output_sector0_chunk2].flatten

def node78Piece122Output : SectorVector := [(0, node78Piece122Output_sector0)]

def node78Piece122UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 5, 7])]

def node78Piece122UnitInput_sector0 : RawPoly ℕ := [node78Piece122UnitInput_sector0_chunk0].flatten

def node78Piece122UnitInput : SectorVector := [(0, node78Piece122UnitInput_sector0)]

def node78Piece122UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 5, 7]), (84, [1, 1, 2, 3, 5, 10]), (60, [1, 1, 2, 3, 7, 8]), (36, [1, 1, 2, 5, 6, 7]), (24, [1, 1, 3, 5, 5, 7]), (168, [1, 2, 2, 3, 5, 9]), (120, [1, 2, 2, 3, 7, 7]), (72, [1, 2, 2, 5, 5, 7]), (168, [1, 2, 3, 3, 5, 8]), (120, [1, 2, 3, 3, 6, 7]), (402, [1, 2, 3, 4, 5, 7]), (168, [1, 2, 3, 5, 5, 6]), (840, [1, 2, 3, 16]), (504, [1, 2, 5, 14]), (360, [1, 2, 7, 12]), (24, [1, 3, 3, 3, 5, 7]), (336, [1, 3, 5, 13]), (240, [1, 3, 7, 11]), (144, [1, 5, 7, 9]), (84, [2, 2, 2, 3, 5, 8]), (60, [2, 2, 2, 3, 6, 7]), (36, [2, 2, 2, 4, 5, 7]), (352, [2, 2, 3, 3, 5, 7]), (60, [2, 2, 3, 4, 4, 7])]

def node78Piece122UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [2, 2, 3, 4, 5, 6]), (84, [2, 2, 3, 5, 5, 5]), (840, [2, 2, 3, 15]), (504, [2, 2, 5, 13]), (360, [2, 2, 7, 11]), (60, [2, 3, 3, 3, 4, 7]), (84, [2, 3, 3, 3, 5, 6]), (168, [2, 3, 3, 4, 5, 5]), (840, [2, 3, 3, 14]), (28, [2, 3, 4, 4, 4, 5]), (840, [2, 3, 4, 13]), (-1442, [2, 3, 5, 12]), (840, [2, 3, 6, 11]), (60, [2, 3, 7, 10]), (840, [2, 3, 8, 9]), (504, [2, 4, 5, 11]), (360, [2, 4, 7, 9]), (504, [2, 5, 5, 10]), (504, [2, 5, 6, 9]), (570, [2, 5, 7, 8]), (360, [2, 6, 7, 7]), (2520, [2, 20]), (336, [3, 3, 5, 11]), (240, [3, 3, 7, 9])]

def node78Piece122UnitOutput_sector0_chunk2 : RawPoly ℕ := [(336, [3, 4, 5, 10]), (240, [3, 4, 7, 8]), (336, [3, 5, 5, 9]), (336, [3, 5, 6, 8]), (360, [3, 5, 7, 7]), (120, [3, 6, 6, 7]), (1680, [3, 19]), (144, [4, 5, 6, 7]), (72, [5, 5, 5, 7]), (1008, [5, 17]), (720, [7, 15])]

def node78Piece122UnitOutput_sector0 : RawPoly ℕ := [node78Piece122UnitOutput_sector0_chunk0, node78Piece122UnitOutput_sector0_chunk1, node78Piece122UnitOutput_sector0_chunk2].flatten

def node78Piece122UnitOutput : SectorVector := [(0, node78Piece122UnitOutput_sector0)]

theorem node78Piece122_check : VectorCertificate (neutralBoundS JR (-2) node78Piece122UnitInput) node78Piece122UnitOutput := by decide +kernel

theorem node78Piece122_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece122Input) = evaluate node78Piece122Output :=
  mode_of_scaled _ _ (64) node78Piece122UnitInput node78Piece122UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece122_check)

def node78Piece123Input_sector0 : RawPoly ℕ := [(200/9, [2, 3, 6, 6])]

def node78Piece123Input : SectorVector := [(0, node78Piece123Input_sector0)]
def node78Piece123Output_sector0_chunk0 : RawPoly ℕ := [(800/9, [1, 1, 1, 2, 2, 3, 6, 6]), (3200, [1, 1, 2, 3, 6, 9]), (800, [1, 1, 2, 6, 6, 6]), (1600/3, [1, 1, 3, 5, 6, 6]), (6400, [1, 2, 2, 3, 6, 8]), (1600, [1, 2, 2, 5, 6, 6]), (6400, [1, 2, 3, 3, 6, 7]), (26800/3, [1, 2, 3, 4, 6, 6]), (3200, [1, 2, 3, 5, 5, 6]), (19200, [1, 2, 3, 16]), (19200, [1, 2, 6, 13]), (1600/3, [1, 3, 3, 3, 6, 6]), (12800, [1, 3, 6, 12]), (3200, [1, 6, 6, 9]), (3200, [2, 2, 2, 3, 6, 7]), (800, [2, 2, 2, 4, 6, 6]), (70400/9, [2, 2, 3, 3, 6, 6]), (6400, [2, 2, 3, 4, 5, 6]), (19200, [2, 2, 3, 15]), (19200, [2, 2, 6, 12]), (3200, [2, 3, 3, 3, 5, 6]), (3200, [2, 3, 3, 4, 4, 6]), (19200, [2, 3, 3, 14]), (19200, [2, 3, 4, 13])]

def node78Piece123Output_sector0_chunk1 : RawPoly ℕ := [(19200, [2, 3, 5, 12]), (-131200/3, [2, 3, 6, 11]), (19200, [2, 3, 7, 10]), (19200, [2, 3, 8, 9]), (19200, [2, 4, 6, 10]), (19200, [2, 5, 6, 9]), (38000/3, [2, 6, 6, 8]), (9600, [2, 6, 7, 7]), (57600, [2, 20]), (12800, [3, 3, 6, 10]), (12800, [3, 4, 6, 9]), (12800, [3, 5, 6, 8]), (35200/3, [3, 6, 6, 7]), (38400, [3, 19]), (3200, [4, 6, 6, 6]), (1600, [5, 5, 6, 6]), (38400, [6, 16])]

def node78Piece123Output_sector0 : RawPoly ℕ := [node78Piece123Output_sector0_chunk0, node78Piece123Output_sector0_chunk1].flatten

def node78Piece123Output : SectorVector := [(0, node78Piece123Output_sector0)]

def node78Piece123UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 6, 6])]

def node78Piece123UnitInput_sector0 : RawPoly ℕ := [node78Piece123UnitInput_sector0_chunk0].flatten

def node78Piece123UnitInput : SectorVector := [(0, node78Piece123UnitInput_sector0)]

def node78Piece123UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 6, 6]), (144, [1, 1, 2, 3, 6, 9]), (36, [1, 1, 2, 6, 6, 6]), (24, [1, 1, 3, 5, 6, 6]), (288, [1, 2, 2, 3, 6, 8]), (72, [1, 2, 2, 5, 6, 6]), (288, [1, 2, 3, 3, 6, 7]), (402, [1, 2, 3, 4, 6, 6]), (144, [1, 2, 3, 5, 5, 6]), (864, [1, 2, 3, 16]), (864, [1, 2, 6, 13]), (24, [1, 3, 3, 3, 6, 6]), (576, [1, 3, 6, 12]), (144, [1, 6, 6, 9]), (144, [2, 2, 2, 3, 6, 7]), (36, [2, 2, 2, 4, 6, 6]), (352, [2, 2, 3, 3, 6, 6]), (288, [2, 2, 3, 4, 5, 6]), (864, [2, 2, 3, 15]), (864, [2, 2, 6, 12]), (144, [2, 3, 3, 3, 5, 6]), (144, [2, 3, 3, 4, 4, 6]), (864, [2, 3, 3, 14]), (864, [2, 3, 4, 13])]

def node78Piece123UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [2, 3, 5, 12]), (-1968, [2, 3, 6, 11]), (864, [2, 3, 7, 10]), (864, [2, 3, 8, 9]), (864, [2, 4, 6, 10]), (864, [2, 5, 6, 9]), (570, [2, 6, 6, 8]), (432, [2, 6, 7, 7]), (2592, [2, 20]), (576, [3, 3, 6, 10]), (576, [3, 4, 6, 9]), (576, [3, 5, 6, 8]), (528, [3, 6, 6, 7]), (1728, [3, 19]), (144, [4, 6, 6, 6]), (72, [5, 5, 6, 6]), (1728, [6, 16])]

def node78Piece123UnitOutput_sector0 : RawPoly ℕ := [node78Piece123UnitOutput_sector0_chunk0, node78Piece123UnitOutput_sector0_chunk1].flatten

def node78Piece123UnitOutput : SectorVector := [(0, node78Piece123UnitOutput_sector0)]

theorem node78Piece123_check : VectorCertificate (neutralBoundS JR (-2) node78Piece123UnitInput) node78Piece123UnitOutput := by decide +kernel

theorem node78Piece123_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece123Input) = evaluate node78Piece123Output :=
  mode_of_scaled _ _ (200/9) node78Piece123UnitInput node78Piece123UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece123_check)

def node78Piece124Input_sector0 : RawPoly ℕ := [(-720/7, [2, 4, 4, 7])]

def node78Piece124Input : SectorVector := [(0, node78Piece124Input_sector0)]
def node78Piece124Output_sector0_chunk0 : RawPoly ℕ := [(-2880/7, [1, 1, 1, 2, 2, 4, 4, 7]), (-8640, [1, 1, 2, 4, 4, 10]), (-69120/7, [1, 1, 2, 4, 7, 7]), (-17280/7, [1, 1, 4, 4, 5, 7]), (-17280, [1, 2, 2, 4, 4, 9]), (-138240/7, [1, 2, 2, 4, 6, 7]), (-17280, [1, 2, 3, 4, 4, 8]), (-138240/7, [1, 2, 3, 4, 5, 7]), (-220320/7, [1, 2, 4, 4, 4, 7]), (-17280, [1, 2, 4, 4, 5, 6]), (-138240, [1, 2, 4, 15]), (-276480/7, [1, 2, 7, 12]), (-17280/7, [1, 3, 3, 4, 4, 7]), (-34560, [1, 4, 4, 13]), (-276480/7, [1, 4, 7, 10]), (-8640, [2, 2, 2, 4, 4, 8]), (-69120/7, [2, 2, 2, 4, 5, 7]), (-279360/7, [2, 2, 3, 4, 4, 7]), (-17280, [2, 2, 4, 4, 4, 6]), (-8640, [2, 2, 4, 4, 5, 5]), (-138240, [2, 2, 4, 14]), (-276480/7, [2, 2, 7, 11]), (-23040/7, [2, 3, 3, 3, 4, 7]), (-8640, [2, 3, 3, 4, 4, 6])]

def node78Piece124Output_sector0_chunk1 : RawPoly ℕ := [(-17280, [2, 3, 4, 4, 4, 5]), (-138240, [2, 3, 4, 13]), (-276480/7, [2, 3, 7, 10]), (-2880, [2, 4, 4, 4, 4, 4]), (148320, [2, 4, 4, 12]), (-138240, [2, 4, 5, 11]), (-138240, [2, 4, 6, 10]), (-334080/7, [2, 4, 7, 9]), (-69120, [2, 4, 8, 8]), (-276480/7, [2, 5, 7, 8]), (-276480/7, [2, 6, 7, 7]), (-276480, [2, 20]), (-34560, [3, 4, 4, 11]), (-276480/7, [3, 4, 7, 8]), (-34560, [4, 4, 4, 10]), (-34560, [4, 4, 5, 9]), (-34560, [4, 4, 6, 8]), (-259200/7, [4, 4, 7, 7]), (-276480/7, [4, 5, 6, 7]), (-276480, [4, 18]), (-552960/7, [7, 15])]

def node78Piece124Output_sector0 : RawPoly ℕ := [node78Piece124Output_sector0_chunk0, node78Piece124Output_sector0_chunk1].flatten

def node78Piece124Output : SectorVector := [(0, node78Piece124Output_sector0)]

def node78Piece124UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 4, 7])]

def node78Piece124UnitInput_sector0 : RawPoly ℕ := [node78Piece124UnitInput_sector0_chunk0].flatten

def node78Piece124UnitInput : SectorVector := [(0, node78Piece124UnitInput_sector0)]

def node78Piece124UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 4, 4, 7]), (84, [1, 1, 2, 4, 4, 10]), (96, [1, 1, 2, 4, 7, 7]), (24, [1, 1, 4, 4, 5, 7]), (168, [1, 2, 2, 4, 4, 9]), (192, [1, 2, 2, 4, 6, 7]), (168, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (306, [1, 2, 4, 4, 4, 7]), (168, [1, 2, 4, 4, 5, 6]), (1344, [1, 2, 4, 15]), (384, [1, 2, 7, 12]), (24, [1, 3, 3, 4, 4, 7]), (336, [1, 4, 4, 13]), (384, [1, 4, 7, 10]), (84, [2, 2, 2, 4, 4, 8]), (96, [2, 2, 2, 4, 5, 7]), (388, [2, 2, 3, 4, 4, 7]), (168, [2, 2, 4, 4, 4, 6]), (84, [2, 2, 4, 4, 5, 5]), (1344, [2, 2, 4, 14]), (384, [2, 2, 7, 11]), (32, [2, 3, 3, 3, 4, 7]), (84, [2, 3, 3, 4, 4, 6])]

def node78Piece124UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [2, 3, 4, 4, 4, 5]), (1344, [2, 3, 4, 13]), (384, [2, 3, 7, 10]), (28, [2, 4, 4, 4, 4, 4]), (-1442, [2, 4, 4, 12]), (1344, [2, 4, 5, 11]), (1344, [2, 4, 6, 10]), (464, [2, 4, 7, 9]), (672, [2, 4, 8, 8]), (384, [2, 5, 7, 8]), (384, [2, 6, 7, 7]), (2688, [2, 20]), (336, [3, 4, 4, 11]), (384, [3, 4, 7, 8]), (336, [4, 4, 4, 10]), (336, [4, 4, 5, 9]), (336, [4, 4, 6, 8]), (360, [4, 4, 7, 7]), (384, [4, 5, 6, 7]), (2688, [4, 18]), (768, [7, 15])]

def node78Piece124UnitOutput_sector0 : RawPoly ℕ := [node78Piece124UnitOutput_sector0_chunk0, node78Piece124UnitOutput_sector0_chunk1].flatten

def node78Piece124UnitOutput : SectorVector := [(0, node78Piece124UnitOutput_sector0)]

theorem node78Piece124_check : VectorCertificate (neutralBoundS JR (-2) node78Piece124UnitInput) node78Piece124UnitOutput := by decide +kernel

theorem node78Piece124_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece124Input) = evaluate node78Piece124Output :=
  mode_of_scaled _ _ (-720/7) node78Piece124UnitInput node78Piece124UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece124_check)

def node78Piece125Input_sector0 : RawPoly ℕ := [(-112, [2, 4, 5, 6])]

def node78Piece125Input : SectorVector := [(0, node78Piece125Input_sector0)]
def node78Piece125Output_sector0_chunk0 : RawPoly ℕ := [(-448, [1, 1, 1, 2, 2, 4, 5, 6]), (-8064, [1, 1, 2, 4, 5, 9]), (-6720, [1, 1, 2, 4, 6, 8]), (-5376, [1, 1, 2, 5, 6, 7]), (-2688, [1, 1, 4, 5, 5, 6]), (-16128, [1, 2, 2, 4, 5, 8]), (-13440, [1, 2, 2, 4, 6, 7]), (-10752, [1, 2, 2, 5, 6, 6]), (-16128, [1, 2, 3, 4, 5, 7]), (-13440, [1, 2, 3, 4, 6, 6]), (-10752, [1, 2, 3, 5, 5, 6]), (-39648, [1, 2, 4, 4, 5, 6]), (-8064, [1, 2, 4, 5, 5, 5]), (-80640, [1, 2, 4, 15]), (-64512, [1, 2, 5, 14]), (-53760, [1, 2, 6, 13]), (-2688, [1, 3, 3, 4, 5, 6]), (-32256, [1, 4, 5, 12]), (-26880, [1, 4, 6, 11]), (-21504, [1, 5, 6, 10]), (-8064, [2, 2, 2, 4, 5, 7]), (-6720, [2, 2, 2, 4, 6, 6]), (-5376, [2, 2, 2, 5, 5, 6]), (-43456, [2, 2, 3, 4, 5, 6])]

def node78Piece125Output_sector0_chunk1 : RawPoly ℕ := [(-6720, [2, 2, 4, 4, 4, 6]), (-16128, [2, 2, 4, 4, 5, 5]), (-80640, [2, 2, 4, 14]), (-64512, [2, 2, 5, 13]), (-53760, [2, 2, 6, 12]), (-1792, [2, 3, 3, 3, 5, 6]), (-6720, [2, 3, 3, 4, 4, 6]), (-8064, [2, 3, 3, 4, 5, 5]), (-8064, [2, 3, 4, 4, 4, 5]), (-80640, [2, 3, 4, 13]), (-64512, [2, 3, 5, 12]), (-53760, [2, 3, 6, 11]), (-80640, [2, 4, 4, 12]), (61824, [2, 4, 5, 11]), (-6720, [2, 4, 6, 10]), (-80640, [2, 4, 7, 9]), (-40320, [2, 4, 8, 8]), (-64512, [2, 5, 5, 10]), (-47488, [2, 5, 6, 9]), (-64512, [2, 5, 7, 8]), (-53760, [2, 6, 6, 8]), (-26880, [2, 6, 7, 7]), (-322560, [2, 20]), (-32256, [3, 4, 5, 10])]

def node78Piece125Output_sector0_chunk2 : RawPoly ℕ := [(-26880, [3, 4, 6, 9]), (-21504, [3, 5, 6, 8]), (-32256, [4, 4, 5, 9]), (-26880, [4, 4, 6, 8]), (-32256, [4, 5, 5, 8]), (-59136, [4, 5, 6, 7]), (-13440, [4, 6, 6, 6]), (-161280, [4, 18]), (-21504, [5, 5, 6, 6]), (-129024, [5, 17]), (-107520, [6, 16])]

def node78Piece125Output_sector0 : RawPoly ℕ := [node78Piece125Output_sector0_chunk0, node78Piece125Output_sector0_chunk1, node78Piece125Output_sector0_chunk2].flatten

def node78Piece125Output : SectorVector := [(0, node78Piece125Output_sector0)]

def node78Piece125UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 5, 6])]

def node78Piece125UnitInput_sector0 : RawPoly ℕ := [node78Piece125UnitInput_sector0_chunk0].flatten

def node78Piece125UnitInput : SectorVector := [(0, node78Piece125UnitInput_sector0)]

def node78Piece125UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 4, 5, 6]), (72, [1, 1, 2, 4, 5, 9]), (60, [1, 1, 2, 4, 6, 8]), (48, [1, 1, 2, 5, 6, 7]), (24, [1, 1, 4, 5, 5, 6]), (144, [1, 2, 2, 4, 5, 8]), (120, [1, 2, 2, 4, 6, 7]), (96, [1, 2, 2, 5, 6, 6]), (144, [1, 2, 3, 4, 5, 7]), (120, [1, 2, 3, 4, 6, 6]), (96, [1, 2, 3, 5, 5, 6]), (354, [1, 2, 4, 4, 5, 6]), (72, [1, 2, 4, 5, 5, 5]), (720, [1, 2, 4, 15]), (576, [1, 2, 5, 14]), (480, [1, 2, 6, 13]), (24, [1, 3, 3, 4, 5, 6]), (288, [1, 4, 5, 12]), (240, [1, 4, 6, 11]), (192, [1, 5, 6, 10]), (72, [2, 2, 2, 4, 5, 7]), (60, [2, 2, 2, 4, 6, 6]), (48, [2, 2, 2, 5, 5, 6]), (388, [2, 2, 3, 4, 5, 6])]

def node78Piece125UnitOutput_sector0_chunk1 : RawPoly ℕ := [(60, [2, 2, 4, 4, 4, 6]), (144, [2, 2, 4, 4, 5, 5]), (720, [2, 2, 4, 14]), (576, [2, 2, 5, 13]), (480, [2, 2, 6, 12]), (16, [2, 3, 3, 3, 5, 6]), (60, [2, 3, 3, 4, 4, 6]), (72, [2, 3, 3, 4, 5, 5]), (72, [2, 3, 4, 4, 4, 5]), (720, [2, 3, 4, 13]), (576, [2, 3, 5, 12]), (480, [2, 3, 6, 11]), (720, [2, 4, 4, 12]), (-552, [2, 4, 5, 11]), (60, [2, 4, 6, 10]), (720, [2, 4, 7, 9]), (360, [2, 4, 8, 8]), (576, [2, 5, 5, 10]), (424, [2, 5, 6, 9]), (576, [2, 5, 7, 8]), (480, [2, 6, 6, 8]), (240, [2, 6, 7, 7]), (2880, [2, 20]), (288, [3, 4, 5, 10])]

def node78Piece125UnitOutput_sector0_chunk2 : RawPoly ℕ := [(240, [3, 4, 6, 9]), (192, [3, 5, 6, 8]), (288, [4, 4, 5, 9]), (240, [4, 4, 6, 8]), (288, [4, 5, 5, 8]), (528, [4, 5, 6, 7]), (120, [4, 6, 6, 6]), (1440, [4, 18]), (192, [5, 5, 6, 6]), (1152, [5, 17]), (960, [6, 16])]

def node78Piece125UnitOutput_sector0 : RawPoly ℕ := [node78Piece125UnitOutput_sector0_chunk0, node78Piece125UnitOutput_sector0_chunk1, node78Piece125UnitOutput_sector0_chunk2].flatten

def node78Piece125UnitOutput : SectorVector := [(0, node78Piece125UnitOutput_sector0)]

theorem node78Piece125_check : VectorCertificate (neutralBoundS JR (-2) node78Piece125UnitInput) node78Piece125UnitOutput := by decide +kernel

theorem node78Piece125_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece125Input) = evaluate node78Piece125Output :=
  mode_of_scaled _ _ (-112) node78Piece125UnitInput node78Piece125UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece125_check)

def node78Piece126Input_sector0 : RawPoly ℕ := [(-64/25, [2, 5, 5, 5])]

def node78Piece126Input : SectorVector := [(0, node78Piece126Input_sector0)]
def node78Piece126Output_sector0_chunk0 : RawPoly ℕ := [(-256/25, [1, 1, 1, 2, 2, 5, 5, 5]), (-2304/5, [1, 1, 2, 5, 5, 8]), (-1536/25, [1, 1, 5, 5, 5, 5]), (-4608/5, [1, 2, 2, 5, 5, 7]), (-4608/5, [1, 2, 3, 5, 5, 6]), (-25728/25, [1, 2, 4, 5, 5, 5]), (-4608, [1, 2, 5, 14]), (-1536/25, [1, 3, 3, 5, 5, 5]), (-9216/5, [1, 5, 5, 11]), (-2304/5, [2, 2, 2, 5, 5, 6]), (-24832/25, [2, 2, 3, 5, 5, 5]), (-2304/5, [2, 2, 4, 4, 5, 5]), (-4608, [2, 2, 5, 13]), (-2304/5, [2, 3, 3, 4, 5, 5]), (-4608, [2, 3, 5, 12]), (-4608, [2, 4, 5, 11]), (20736/5, [2, 5, 5, 10]), (-4608, [2, 5, 6, 9]), (-4608, [2, 5, 7, 8]), (-7680, [2, 20]), (-9216/5, [3, 5, 5, 9]), (-9216/5, [4, 5, 5, 8]), (-33792/25, [5, 5, 5, 7]), (-4608/5, [5, 5, 6, 6])]

def node78Piece126Output_sector0_chunk1 : RawPoly ℕ := [(-9216, [5, 17])]

def node78Piece126Output_sector0 : RawPoly ℕ := [node78Piece126Output_sector0_chunk0, node78Piece126Output_sector0_chunk1].flatten

def node78Piece126Output : SectorVector := [(0, node78Piece126Output_sector0)]

def node78Piece126UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 5, 5, 5])]

def node78Piece126UnitInput_sector0 : RawPoly ℕ := [node78Piece126UnitInput_sector0_chunk0].flatten

def node78Piece126UnitInput : SectorVector := [(0, node78Piece126UnitInput_sector0)]

def node78Piece126UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 5, 5, 5]), (180, [1, 1, 2, 5, 5, 8]), (24, [1, 1, 5, 5, 5, 5]), (360, [1, 2, 2, 5, 5, 7]), (360, [1, 2, 3, 5, 5, 6]), (402, [1, 2, 4, 5, 5, 5]), (1800, [1, 2, 5, 14]), (24, [1, 3, 3, 5, 5, 5]), (720, [1, 5, 5, 11]), (180, [2, 2, 2, 5, 5, 6]), (388, [2, 2, 3, 5, 5, 5]), (180, [2, 2, 4, 4, 5, 5]), (1800, [2, 2, 5, 13]), (180, [2, 3, 3, 4, 5, 5]), (1800, [2, 3, 5, 12]), (1800, [2, 4, 5, 11]), (-1620, [2, 5, 5, 10]), (1800, [2, 5, 6, 9]), (1800, [2, 5, 7, 8]), (3000, [2, 20]), (720, [3, 5, 5, 9]), (720, [4, 5, 5, 8]), (528, [5, 5, 5, 7]), (360, [5, 5, 6, 6])]

def node78Piece126UnitOutput_sector0_chunk1 : RawPoly ℕ := [(3600, [5, 17])]

def node78Piece126UnitOutput_sector0 : RawPoly ℕ := [node78Piece126UnitOutput_sector0_chunk0, node78Piece126UnitOutput_sector0_chunk1].flatten

def node78Piece126UnitOutput : SectorVector := [(0, node78Piece126UnitOutput_sector0)]

theorem node78Piece126_check : VectorCertificate (neutralBoundS JR (-2) node78Piece126UnitInput) node78Piece126UnitOutput := by decide +kernel

theorem node78Piece126_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece126Input) = evaluate node78Piece126Output :=
  mode_of_scaled _ _ (-64/25) node78Piece126UnitInput node78Piece126UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece126_check)

def node78Piece127Input_sector0 : RawPoly ℕ := [(-64, [2, 15])]

def node78Piece127Input : SectorVector := [(0, node78Piece127Input_sector0)]
def node78Piece127Output_sector0_chunk0 : RawPoly ℕ := [(-256, [1, 1, 1, 2, 2, 15]), (-11520, [1, 1, 2, 18]), (-1536, [1, 1, 5, 15]), (-23040, [1, 2, 2, 17]), (-23040, [1, 2, 3, 16]), (-25728, [1, 2, 4, 15]), (-23040, [1, 2, 5, 14]), (-23040, [1, 2, 6, 13]), (-23040, [1, 2, 7, 12]), (-23040, [1, 2, 8, 11]), (-23040, [1, 2, 9, 10]), (-1536, [1, 3, 3, 15]), (-46080, [1, 21]), (-11520, [2, 2, 2, 16]), (-24832, [2, 2, 3, 15]), (-23040, [2, 2, 4, 14]), (-23040, [2, 2, 5, 13]), (-23040, [2, 2, 6, 12]), (-23040, [2, 2, 7, 11]), (-23040, [2, 2, 8, 10]), (-11520, [2, 2, 9, 9]), (-11520, [2, 3, 3, 14]), (-23040, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12])]

def node78Piece127Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 3, 6, 11]), (-23040, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-11520, [2, 4, 4, 12]), (-23040, [2, 4, 5, 11]), (-23040, [2, 4, 6, 10]), (-23040, [2, 4, 7, 9]), (-11520, [2, 4, 8, 8]), (-11520, [2, 5, 5, 10]), (-23040, [2, 5, 6, 9]), (-23040, [2, 5, 7, 8]), (-11520, [2, 6, 6, 8]), (-11520, [2, 6, 7, 7]), (1418880, [2, 20]), (-46080, [3, 19]), (-46080, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-33792, [7, 15]), (-46080, [8, 14]), (-46080, [9, 13]), (-46080, [10, 12]), (-23040, [11, 11])]

def node78Piece127Output_sector0 : RawPoly ℕ := [node78Piece127Output_sector0_chunk0, node78Piece127Output_sector0_chunk1].flatten

def node78Piece127Output : SectorVector := [(0, node78Piece127Output_sector0)]

def node78Piece127UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 15])]

def node78Piece127UnitInput_sector0 : RawPoly ℕ := [node78Piece127UnitInput_sector0_chunk0].flatten

def node78Piece127UnitInput : SectorVector := [(0, node78Piece127UnitInput_sector0)]

def node78Piece127UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 15]), (180, [1, 1, 2, 18]), (24, [1, 1, 5, 15]), (360, [1, 2, 2, 17]), (360, [1, 2, 3, 16]), (402, [1, 2, 4, 15]), (360, [1, 2, 5, 14]), (360, [1, 2, 6, 13]), (360, [1, 2, 7, 12]), (360, [1, 2, 8, 11]), (360, [1, 2, 9, 10]), (24, [1, 3, 3, 15]), (720, [1, 21]), (180, [2, 2, 2, 16]), (388, [2, 2, 3, 15]), (360, [2, 2, 4, 14]), (360, [2, 2, 5, 13]), (360, [2, 2, 6, 12]), (360, [2, 2, 7, 11]), (360, [2, 2, 8, 10]), (180, [2, 2, 9, 9]), (180, [2, 3, 3, 14]), (360, [2, 3, 4, 13]), (360, [2, 3, 5, 12])]

def node78Piece127UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [2, 3, 6, 11]), (360, [2, 3, 7, 10]), (360, [2, 3, 8, 9]), (180, [2, 4, 4, 12]), (360, [2, 4, 5, 11]), (360, [2, 4, 6, 10]), (360, [2, 4, 7, 9]), (180, [2, 4, 8, 8]), (180, [2, 5, 5, 10]), (360, [2, 5, 6, 9]), (360, [2, 5, 7, 8]), (180, [2, 6, 6, 8]), (180, [2, 6, 7, 7]), (-22170, [2, 20]), (720, [3, 19]), (720, [4, 18]), (720, [5, 17]), (720, [6, 16]), (528, [7, 15]), (720, [8, 14]), (720, [9, 13]), (720, [10, 12]), (360, [11, 11])]

def node78Piece127UnitOutput_sector0 : RawPoly ℕ := [node78Piece127UnitOutput_sector0_chunk0, node78Piece127UnitOutput_sector0_chunk1].flatten

def node78Piece127UnitOutput : SectorVector := [(0, node78Piece127UnitOutput_sector0)]

theorem node78Piece127_check : VectorCertificate (neutralBoundS JR (-2) node78Piece127UnitInput) node78Piece127UnitOutput := by decide +kernel

theorem node78Piece127_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node78Piece127Input) = evaluate node78Piece127Output :=
  mode_of_scaled _ _ (-64) node78Piece127UnitInput node78Piece127UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node78Piece127_check)

end VOA.Classification.COne.OrbC2h
