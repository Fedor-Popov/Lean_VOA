import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hTwenty
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node77Piece0Input_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node77Piece0Input : SectorVector := [(-1, node77Piece0Input_sector0)]
def node77Piece0Output_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (126, [0, 1, 1, 1, 1, 1, 1, 7]), (1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (211, [0, 1, 1, 1, 1, 1, 2, 6]), (226, [0, 1, 1, 1, 1, 1, 3, 5]), (231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 5]), (120, [0, 1, 1, 1, 1, 2, 3, 4]), (20, [0, 1, 1, 1, 1, 3, 3, 3]), (170, [0, 1, 1, 1, 1, 9]), (240, [0, 1, 1, 1, 2, 8]), (240, [0, 1, 1, 1, 3, 7]), (240, [0, 1, 1, 1, 4, 6]), (120, [0, 1, 1, 1, 5, 5]), (240, [0, 1, 1, 11]), (-96, [1, 1, 1, 1, 1, 1, 1, 6]), (-192, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (-96, [1, 1, 1, 1, 1, 2, 2, 4]), (-96, [1, 1, 1, 1, 1, 2, 3, 3]), (-696, [1, 1, 1, 1, 1, 8])]

def node77Piece0Output_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (-960, [1, 1, 1, 1, 4, 5]), (-1920, [1, 1, 1, 10])]

def node77Piece0Output_sector0 : RawPoly ℕ := [node77Piece0Output_sector0_chunk0, node77Piece0Output_sector0_chunk1].flatten

def node77Piece0Output : SectorVector := [(-1, node77Piece0Output_sector0)]

def node77Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node77Piece0UnitInput_sector0 : RawPoly ℕ := [node77Piece0UnitInput_sector0_chunk0].flatten

def node77Piece0UnitInput : SectorVector := [(-1, node77Piece0UnitInput_sector0)]

def node77Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (126, [0, 1, 1, 1, 1, 1, 1, 7]), (1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (211, [0, 1, 1, 1, 1, 1, 2, 6]), (226, [0, 1, 1, 1, 1, 1, 3, 5]), (231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 5]), (120, [0, 1, 1, 1, 1, 2, 3, 4]), (20, [0, 1, 1, 1, 1, 3, 3, 3]), (170, [0, 1, 1, 1, 1, 9]), (240, [0, 1, 1, 1, 2, 8]), (240, [0, 1, 1, 1, 3, 7]), (240, [0, 1, 1, 1, 4, 6]), (120, [0, 1, 1, 1, 5, 5]), (240, [0, 1, 1, 11]), (-96, [1, 1, 1, 1, 1, 1, 1, 6]), (-192, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (-96, [1, 1, 1, 1, 1, 2, 2, 4]), (-96, [1, 1, 1, 1, 1, 2, 3, 3]), (-696, [1, 1, 1, 1, 1, 8])]

def node77Piece0UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (-960, [1, 1, 1, 1, 4, 5]), (-1920, [1, 1, 1, 10])]

def node77Piece0UnitOutput_sector0 : RawPoly ℕ := [node77Piece0UnitOutput_sector0_chunk0, node77Piece0UnitOutput_sector0_chunk1].flatten

def node77Piece0UnitOutput : SectorVector := [(-1, node77Piece0UnitOutput_sector0)]

theorem node77Piece0_check : VectorCertificate (neutralBoundS JR (-5) node77Piece0UnitInput) node77Piece0UnitOutput := by decide +kernel

theorem node77Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece0Input) = evaluate node77Piece0Output :=
  mode_of_scaled _ _ (1) node77Piece0UnitInput node77Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece0_check)

def node77Piece1Input_sector0 : RawPoly ℕ := [(10, [0, 1, 1, 3])]

def node77Piece1Input : SectorVector := [(-1, node77Piece1Input_sector0)]
def node77Piece1Output_sector0_chunk0 : RawPoly ℕ := [(40, [0, 1, 1, 1, 1, 1, 3, 5]), (120, [0, 1, 1, 1, 1, 2, 3, 4]), (60, [0, 1, 1, 1, 1, 3, 3, 3]), (360, [0, 1, 1, 1, 1, 9]), (120, [0, 1, 1, 1, 2, 2, 3, 3]), (720, [0, 1, 1, 1, 2, 8]), (1620, [0, 1, 1, 1, 3, 7]), (720, [0, 1, 1, 1, 4, 6]), (360, [0, 1, 1, 1, 5, 5]), (10, [0, 1, 1, 2, 2, 2, 2, 3]), (360, [0, 1, 1, 2, 2, 7]), (2110, [0, 1, 1, 2, 3, 6]), (720, [0, 1, 1, 2, 4, 5]), (1900, [0, 1, 1, 3, 3, 5]), (1155, [0, 1, 1, 3, 4, 4]), (-2580, [0, 1, 1, 11]), (240, [0, 1, 2, 2, 3, 5]), (480, [0, 1, 2, 3, 3, 4]), (1440, [0, 1, 2, 10]), (80, [0, 1, 3, 3, 3, 3]), (1400, [0, 1, 3, 9]), (1440, [0, 1, 4, 8]), (1440, [0, 1, 5, 7]), (720, [0, 1, 6, 6])]

def node77Piece1Output_sector0_chunk1 : RawPoly ℕ := [(240, [0, 2, 3, 8]), (240, [0, 3, 3, 7]), (240, [0, 3, 4, 6]), (120, [0, 3, 5, 5]), (720, [0, 13]), (-960, [1, 1, 1, 1, 3, 6]), (-1920, [1, 1, 1, 2, 3, 5]), (-1920, [1, 1, 1, 3, 3, 4]), (-5760, [1, 1, 1, 10]), (-960, [1, 1, 2, 2, 3, 4]), (-960, [1, 1, 2, 3, 3, 3]), (-5760, [1, 1, 2, 9]), (-6960, [1, 1, 3, 8]), (-5760, [1, 1, 4, 7]), (-5760, [1, 1, 5, 6]), (-3840, [1, 2, 3, 7]), (-3840, [1, 3, 3, 6]), (-3840, [1, 3, 4, 5]), (-11520, [1, 12]), (-1920, [3, 10])]

def node77Piece1Output_sector0 : RawPoly ℕ := [node77Piece1Output_sector0_chunk0, node77Piece1Output_sector0_chunk1].flatten

def node77Piece1Output : SectorVector := [(-1, node77Piece1Output_sector0)]

def node77Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node77Piece1UnitInput_sector0 : RawPoly ℕ := [node77Piece1UnitInput_sector0_chunk0].flatten

def node77Piece1UnitInput : SectorVector := [(-1, node77Piece1UnitInput_sector0)]

def node77Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 3, 5]), (12, [0, 1, 1, 1, 1, 2, 3, 4]), (6, [0, 1, 1, 1, 1, 3, 3, 3]), (36, [0, 1, 1, 1, 1, 9]), (12, [0, 1, 1, 1, 2, 2, 3, 3]), (72, [0, 1, 1, 1, 2, 8]), (162, [0, 1, 1, 1, 3, 7]), (72, [0, 1, 1, 1, 4, 6]), (36, [0, 1, 1, 1, 5, 5]), (1, [0, 1, 1, 2, 2, 2, 2, 3]), (36, [0, 1, 1, 2, 2, 7]), (211, [0, 1, 1, 2, 3, 6]), (72, [0, 1, 1, 2, 4, 5]), (190, [0, 1, 1, 3, 3, 5]), (231/2, [0, 1, 1, 3, 4, 4]), (-258, [0, 1, 1, 11]), (24, [0, 1, 2, 2, 3, 5]), (48, [0, 1, 2, 3, 3, 4]), (144, [0, 1, 2, 10]), (8, [0, 1, 3, 3, 3, 3]), (140, [0, 1, 3, 9]), (144, [0, 1, 4, 8]), (144, [0, 1, 5, 7]), (72, [0, 1, 6, 6])]

def node77Piece1UnitOutput_sector0_chunk1 : RawPoly ℕ := [(24, [0, 2, 3, 8]), (24, [0, 3, 3, 7]), (24, [0, 3, 4, 6]), (12, [0, 3, 5, 5]), (72, [0, 13]), (-96, [1, 1, 1, 1, 3, 6]), (-192, [1, 1, 1, 2, 3, 5]), (-192, [1, 1, 1, 3, 3, 4]), (-576, [1, 1, 1, 10]), (-96, [1, 1, 2, 2, 3, 4]), (-96, [1, 1, 2, 3, 3, 3]), (-576, [1, 1, 2, 9]), (-696, [1, 1, 3, 8]), (-576, [1, 1, 4, 7]), (-576, [1, 1, 5, 6]), (-384, [1, 2, 3, 7]), (-384, [1, 3, 3, 6]), (-384, [1, 3, 4, 5]), (-1152, [1, 12]), (-192, [3, 10])]

def node77Piece1UnitOutput_sector0 : RawPoly ℕ := [node77Piece1UnitOutput_sector0_chunk0, node77Piece1UnitOutput_sector0_chunk1].flatten

def node77Piece1UnitOutput : SectorVector := [(-1, node77Piece1UnitOutput_sector0)]

theorem node77Piece1_check : VectorCertificate (neutralBoundS JR (-5) node77Piece1UnitInput) node77Piece1UnitOutput := by decide +kernel

theorem node77Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece1Input) = evaluate node77Piece1Output :=
  mode_of_scaled _ _ (10) node77Piece1UnitInput node77Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece1_check)

def node77Piece2Input_sector0 : RawPoly ℕ := [(15/2, [0, 1, 2, 2])]

def node77Piece2Input : SectorVector := [(-1, node77Piece2Input_sector0)]
def node77Piece2Output_sector0_chunk0 : RawPoly ℕ := [(30, [0, 1, 1, 1, 1, 2, 2, 5]), (90, [0, 1, 1, 1, 2, 2, 2, 4]), (45, [0, 1, 1, 1, 2, 2, 3, 3]), (360, [0, 1, 1, 1, 2, 8]), (90, [0, 1, 1, 2, 2, 2, 2, 3]), (1305, [0, 1, 1, 2, 2, 7]), (720, [0, 1, 1, 2, 3, 6]), (720, [0, 1, 1, 2, 4, 5]), (720, [0, 1, 1, 11]), (15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (2445/2, [0, 1, 2, 2, 2, 6]), (1695, [0, 1, 2, 2, 3, 5]), (3465/4, [0, 1, 2, 2, 4, 4]), (360, [0, 1, 2, 3, 3, 4]), (-630, [0, 1, 2, 10]), (720, [0, 1, 3, 9]), (720, [0, 1, 4, 8]), (720, [0, 1, 5, 7]), (360, [0, 1, 6, 6]), (90, [0, 2, 2, 2, 2, 5]), (180, [0, 2, 2, 2, 3, 4]), (30, [0, 2, 2, 3, 3, 3]), (615, [0, 2, 2, 9]), (720, [0, 2, 3, 8])]

def node77Piece2Output_sector0_chunk1 : RawPoly ℕ := [(720, [0, 2, 4, 7]), (720, [0, 2, 5, 6]), (720, [0, 13]), (-720, [1, 1, 1, 2, 2, 6]), (-1440, [1, 1, 2, 2, 2, 5]), (-1440, [1, 1, 2, 2, 3, 4]), (-5760, [1, 1, 2, 9]), (-720, [1, 2, 2, 2, 2, 4]), (-720, [1, 2, 2, 2, 3, 3]), (-5220, [1, 2, 2, 8]), (-5760, [1, 2, 3, 7]), (-5760, [1, 2, 4, 6]), (-2880, [1, 2, 5, 5]), (-5760, [1, 12]), (-1440, [2, 2, 2, 7]), (-1440, [2, 2, 3, 6]), (-1440, [2, 2, 4, 5]), (-5760, [2, 11])]

def node77Piece2Output_sector0 : RawPoly ℕ := [node77Piece2Output_sector0_chunk0, node77Piece2Output_sector0_chunk1].flatten

def node77Piece2Output : SectorVector := [(-1, node77Piece2Output_sector0)]

def node77Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node77Piece2UnitInput_sector0 : RawPoly ℕ := [node77Piece2UnitInput_sector0_chunk0].flatten

def node77Piece2UnitInput : SectorVector := [(-1, node77Piece2UnitInput_sector0)]

def node77Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 5]), (12, [0, 1, 1, 1, 2, 2, 2, 4]), (6, [0, 1, 1, 1, 2, 2, 3, 3]), (48, [0, 1, 1, 1, 2, 8]), (12, [0, 1, 1, 2, 2, 2, 2, 3]), (174, [0, 1, 1, 2, 2, 7]), (96, [0, 1, 1, 2, 3, 6]), (96, [0, 1, 1, 2, 4, 5]), (96, [0, 1, 1, 11]), (1, [0, 1, 2, 2, 2, 2, 2, 2]), (163, [0, 1, 2, 2, 2, 6]), (226, [0, 1, 2, 2, 3, 5]), (231/2, [0, 1, 2, 2, 4, 4]), (48, [0, 1, 2, 3, 3, 4]), (-84, [0, 1, 2, 10]), (96, [0, 1, 3, 9]), (96, [0, 1, 4, 8]), (96, [0, 1, 5, 7]), (48, [0, 1, 6, 6]), (12, [0, 2, 2, 2, 2, 5]), (24, [0, 2, 2, 2, 3, 4]), (4, [0, 2, 2, 3, 3, 3]), (82, [0, 2, 2, 9]), (96, [0, 2, 3, 8])]

def node77Piece2UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [0, 2, 4, 7]), (96, [0, 2, 5, 6]), (96, [0, 13]), (-96, [1, 1, 1, 2, 2, 6]), (-192, [1, 1, 2, 2, 2, 5]), (-192, [1, 1, 2, 2, 3, 4]), (-768, [1, 1, 2, 9]), (-96, [1, 2, 2, 2, 2, 4]), (-96, [1, 2, 2, 2, 3, 3]), (-696, [1, 2, 2, 8]), (-768, [1, 2, 3, 7]), (-768, [1, 2, 4, 6]), (-384, [1, 2, 5, 5]), (-768, [1, 12]), (-192, [2, 2, 2, 7]), (-192, [2, 2, 3, 6]), (-192, [2, 2, 4, 5]), (-768, [2, 11])]

def node77Piece2UnitOutput_sector0 : RawPoly ℕ := [node77Piece2UnitOutput_sector0_chunk0, node77Piece2UnitOutput_sector0_chunk1].flatten

def node77Piece2UnitOutput : SectorVector := [(-1, node77Piece2UnitOutput_sector0)]

theorem node77Piece2_check : VectorCertificate (neutralBoundS JR (-5) node77Piece2UnitInput) node77Piece2UnitOutput := by decide +kernel

theorem node77Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece2Input) = evaluate node77Piece2Output :=
  mode_of_scaled _ _ (15/2) node77Piece2UnitInput node77Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece2_check)

def node77Piece3Input_sector0 : RawPoly ℕ := [(6, [0, 5])]

def node77Piece3Input : SectorVector := [(-1, node77Piece3Input_sector0)]
def node77Piece3Output_sector0_chunk0 : RawPoly ℕ := [(24, [0, 1, 1, 1, 5, 5]), (72, [0, 1, 1, 2, 4, 5]), (36, [0, 1, 1, 3, 3, 5]), (360, [0, 1, 1, 11]), (72, [0, 1, 2, 2, 3, 5]), (720, [0, 1, 2, 10]), (720, [0, 1, 3, 9]), (720, [0, 1, 4, 8]), (1116, [0, 1, 5, 7]), (360, [0, 1, 6, 6]), (6, [0, 2, 2, 2, 2, 5]), (360, [0, 2, 2, 9]), (720, [0, 2, 3, 8]), (720, [0, 2, 4, 7]), (1266, [0, 2, 5, 6]), (360, [0, 3, 3, 7]), (720, [0, 3, 4, 6]), (996, [0, 3, 5, 5]), (693, [0, 4, 4, 5]), (-8820, [0, 13]), (-576, [1, 1, 5, 6]), (-1152, [1, 2, 5, 5]), (-1152, [1, 3, 4, 5]), (-5760, [1, 12])]

def node77Piece3Output_sector0_chunk1 : RawPoly ℕ := [(-576, [2, 2, 4, 5]), (-576, [2, 3, 3, 5]), (-5760, [2, 11]), (-5760, [3, 10]), (-5760, [4, 9]), (-4176, [5, 8]), (-5760, [6, 7])]

def node77Piece3Output_sector0 : RawPoly ℕ := [node77Piece3Output_sector0_chunk0, node77Piece3Output_sector0_chunk1].flatten

def node77Piece3Output : SectorVector := [(-1, node77Piece3Output_sector0)]

def node77Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node77Piece3UnitInput_sector0 : RawPoly ℕ := [node77Piece3UnitInput_sector0_chunk0].flatten

def node77Piece3UnitInput : SectorVector := [(-1, node77Piece3UnitInput_sector0)]

def node77Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 5, 5]), (12, [0, 1, 1, 2, 4, 5]), (6, [0, 1, 1, 3, 3, 5]), (60, [0, 1, 1, 11]), (12, [0, 1, 2, 2, 3, 5]), (120, [0, 1, 2, 10]), (120, [0, 1, 3, 9]), (120, [0, 1, 4, 8]), (186, [0, 1, 5, 7]), (60, [0, 1, 6, 6]), (1, [0, 2, 2, 2, 2, 5]), (60, [0, 2, 2, 9]), (120, [0, 2, 3, 8]), (120, [0, 2, 4, 7]), (211, [0, 2, 5, 6]), (60, [0, 3, 3, 7]), (120, [0, 3, 4, 6]), (166, [0, 3, 5, 5]), (231/2, [0, 4, 4, 5]), (-1470, [0, 13]), (-96, [1, 1, 5, 6]), (-192, [1, 2, 5, 5]), (-192, [1, 3, 4, 5]), (-960, [1, 12])]

def node77Piece3UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-96, [2, 2, 4, 5]), (-96, [2, 3, 3, 5]), (-960, [2, 11]), (-960, [3, 10]), (-960, [4, 9]), (-696, [5, 8]), (-960, [6, 7])]

def node77Piece3UnitOutput_sector0 : RawPoly ℕ := [node77Piece3UnitOutput_sector0_chunk0, node77Piece3UnitOutput_sector0_chunk1].flatten

def node77Piece3UnitOutput : SectorVector := [(-1, node77Piece3UnitOutput_sector0)]

theorem node77Piece3_check : VectorCertificate (neutralBoundS JR (-5) node77Piece3UnitInput) node77Piece3UnitOutput := by decide +kernel

theorem node77Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece3Input) = evaluate node77Piece3Output :=
  mode_of_scaled _ _ (6) node77Piece3UnitInput node77Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece3_check)

def node77Piece4Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node77Piece4Input : SectorVector := [(-1, node77Piece4Input_sector0)]
def node77Piece4Output_sector0_chunk0 : RawPoly ℕ := [(-240, [0, 1, 1, 1, 1, 1, 2, 6]), (-480, [0, 1, 1, 1, 1, 2, 2, 5]), (-480, [0, 1, 1, 1, 1, 2, 3, 4]), (-960, [0, 1, 1, 1, 1, 9]), (-240, [0, 1, 1, 1, 2, 2, 2, 4]), (-240, [0, 1, 1, 1, 2, 2, 3, 3]), (-1740, [0, 1, 1, 1, 2, 8]), (-960, [0, 1, 1, 1, 3, 7]), (-960, [0, 1, 1, 1, 4, 6]), (-480, [0, 1, 1, 1, 5, 5]), (-1440, [0, 1, 1, 2, 2, 7]), (-1440, [0, 1, 1, 2, 3, 6]), (-1440, [0, 1, 1, 2, 4, 5]), (-2880, [0, 1, 1, 11]), (-1440, [0, 1, 2, 10]), (80, [1, 1, 1, 1, 1, 1, 2, 5]), (240, [1, 1, 1, 1, 1, 2, 2, 4]), (120, [1, 1, 1, 1, 1, 2, 3, 3]), (480, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (3000, [1, 1, 1, 1, 2, 7]), (960, [1, 1, 1, 1, 3, 6]), (960, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2])]

def node77Piece4Output_sector0_chunk1 : RawPoly ℕ := [(3740, [1, 1, 1, 2, 2, 6]), (4520, [1, 1, 1, 2, 3, 5]), (2310, [1, 1, 1, 2, 4, 4]), (480, [1, 1, 1, 3, 3, 4]), (120, [1, 1, 1, 10]), (720, [1, 1, 2, 2, 2, 5]), (1440, [1, 1, 2, 2, 3, 4]), (240, [1, 1, 2, 3, 3, 3]), (3480, [1, 1, 2, 9]), (2880, [1, 1, 3, 8]), (2880, [1, 1, 4, 7]), (2880, [1, 1, 5, 6]), (1440, [1, 2, 2, 8]), (1440, [1, 2, 3, 7]), (1440, [1, 2, 4, 6]), (720, [1, 2, 5, 5]), (2880, [1, 12]), (480, [2, 11])]

def node77Piece4Output_sector0 : RawPoly ℕ := [node77Piece4Output_sector0_chunk0, node77Piece4Output_sector0_chunk1].flatten

def node77Piece4Output : SectorVector := [(-1, node77Piece4Output_sector0)]

def node77Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node77Piece4UnitInput_sector0 : RawPoly ℕ := [node77Piece4UnitInput_sector0_chunk0].flatten

def node77Piece4UnitInput : SectorVector := [(-1, node77Piece4UnitInput_sector0)]

def node77Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 1, 1, 2, 6]), (-24, [0, 1, 1, 1, 1, 2, 2, 5]), (-24, [0, 1, 1, 1, 1, 2, 3, 4]), (-48, [0, 1, 1, 1, 1, 9]), (-12, [0, 1, 1, 1, 2, 2, 2, 4]), (-12, [0, 1, 1, 1, 2, 2, 3, 3]), (-87, [0, 1, 1, 1, 2, 8]), (-48, [0, 1, 1, 1, 3, 7]), (-48, [0, 1, 1, 1, 4, 6]), (-24, [0, 1, 1, 1, 5, 5]), (-72, [0, 1, 1, 2, 2, 7]), (-72, [0, 1, 1, 2, 3, 6]), (-72, [0, 1, 1, 2, 4, 5]), (-144, [0, 1, 1, 11]), (-72, [0, 1, 2, 10]), (4, [1, 1, 1, 1, 1, 1, 2, 5]), (12, [1, 1, 1, 1, 1, 2, 2, 4]), (6, [1, 1, 1, 1, 1, 2, 3, 3]), (24, [1, 1, 1, 1, 1, 8]), (12, [1, 1, 1, 1, 2, 2, 2, 3]), (150, [1, 1, 1, 1, 2, 7]), (48, [1, 1, 1, 1, 3, 6]), (48, [1, 1, 1, 1, 4, 5]), (1, [1, 1, 1, 2, 2, 2, 2, 2])]

def node77Piece4UnitOutput_sector0_chunk1 : RawPoly ℕ := [(187, [1, 1, 1, 2, 2, 6]), (226, [1, 1, 1, 2, 3, 5]), (231/2, [1, 1, 1, 2, 4, 4]), (24, [1, 1, 1, 3, 3, 4]), (6, [1, 1, 1, 10]), (36, [1, 1, 2, 2, 2, 5]), (72, [1, 1, 2, 2, 3, 4]), (12, [1, 1, 2, 3, 3, 3]), (174, [1, 1, 2, 9]), (144, [1, 1, 3, 8]), (144, [1, 1, 4, 7]), (144, [1, 1, 5, 6]), (72, [1, 2, 2, 8]), (72, [1, 2, 3, 7]), (72, [1, 2, 4, 6]), (36, [1, 2, 5, 5]), (144, [1, 12]), (24, [2, 11])]

def node77Piece4UnitOutput_sector0 : RawPoly ℕ := [node77Piece4UnitOutput_sector0_chunk0, node77Piece4UnitOutput_sector0_chunk1].flatten

def node77Piece4UnitOutput : SectorVector := [(-1, node77Piece4UnitOutput_sector0)]

theorem node77Piece4_check : VectorCertificate (neutralBoundS JR (-5) node77Piece4UnitInput) node77Piece4UnitOutput := by decide +kernel

theorem node77Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece4Input) = evaluate node77Piece4Output :=
  mode_of_scaled _ _ (20) node77Piece4UnitInput node77Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece4_check)

def node77Piece5Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node77Piece5Input : SectorVector := [(-1, node77Piece5Input_sector0)]
def node77Piece5Output_sector0_chunk0 : RawPoly ℕ := [(-360, [0, 1, 1, 1, 4, 6]), (-720, [0, 1, 1, 2, 4, 5]), (-720, [0, 1, 1, 3, 4, 4]), (-2880, [0, 1, 1, 11]), (-360, [0, 1, 2, 2, 4, 4]), (-360, [0, 1, 2, 3, 3, 4]), (-2880, [0, 1, 2, 10]), (-2880, [0, 1, 3, 9]), (-2610, [0, 1, 4, 8]), (-2880, [0, 1, 5, 7]), (-1440, [0, 1, 6, 6]), (-720, [0, 2, 4, 7]), (-720, [0, 3, 4, 6]), (-720, [0, 4, 4, 5]), (-2880, [0, 13]), (120, [1, 1, 1, 1, 4, 5]), (360, [1, 1, 1, 2, 4, 4]), (180, [1, 1, 1, 3, 3, 4]), (1440, [1, 1, 1, 10]), (360, [1, 1, 2, 2, 3, 4]), (2880, [1, 1, 2, 9]), (2880, [1, 1, 3, 8]), (5220, [1, 1, 4, 7]), (2880, [1, 1, 5, 6])]

def node77Piece5Output_sector0_chunk1 : RawPoly ℕ := [(30, [1, 2, 2, 2, 2, 4]), (1440, [1, 2, 2, 8]), (2880, [1, 2, 3, 7]), (6330, [1, 2, 4, 6]), (1440, [1, 2, 5, 5]), (1440, [1, 3, 3, 6]), (6780, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-22200, [1, 12]), (360, [2, 2, 4, 5]), (720, [2, 3, 4, 4]), (2880, [2, 11]), (120, [3, 3, 3, 4]), (2880, [3, 10]), (2460, [4, 9]), (2880, [5, 8]), (2880, [6, 7])]

def node77Piece5Output_sector0 : RawPoly ℕ := [node77Piece5Output_sector0_chunk0, node77Piece5Output_sector0_chunk1].flatten

def node77Piece5Output : SectorVector := [(-1, node77Piece5Output_sector0)]

def node77Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node77Piece5UnitInput_sector0 : RawPoly ℕ := [node77Piece5UnitInput_sector0_chunk0].flatten

def node77Piece5UnitInput : SectorVector := [(-1, node77Piece5UnitInput_sector0)]

def node77Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 4, 6]), (-24, [0, 1, 1, 2, 4, 5]), (-24, [0, 1, 1, 3, 4, 4]), (-96, [0, 1, 1, 11]), (-12, [0, 1, 2, 2, 4, 4]), (-12, [0, 1, 2, 3, 3, 4]), (-96, [0, 1, 2, 10]), (-96, [0, 1, 3, 9]), (-87, [0, 1, 4, 8]), (-96, [0, 1, 5, 7]), (-48, [0, 1, 6, 6]), (-24, [0, 2, 4, 7]), (-24, [0, 3, 4, 6]), (-24, [0, 4, 4, 5]), (-96, [0, 13]), (4, [1, 1, 1, 1, 4, 5]), (12, [1, 1, 1, 2, 4, 4]), (6, [1, 1, 1, 3, 3, 4]), (48, [1, 1, 1, 10]), (12, [1, 1, 2, 2, 3, 4]), (96, [1, 1, 2, 9]), (96, [1, 1, 3, 8]), (174, [1, 1, 4, 7]), (96, [1, 1, 5, 6])]

def node77Piece5UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 4]), (48, [1, 2, 2, 8]), (96, [1, 2, 3, 7]), (211, [1, 2, 4, 6]), (48, [1, 2, 5, 5]), (48, [1, 3, 3, 6]), (226, [1, 3, 4, 5]), (167/2, [1, 4, 4, 4]), (-740, [1, 12]), (12, [2, 2, 4, 5]), (24, [2, 3, 4, 4]), (96, [2, 11]), (4, [3, 3, 3, 4]), (96, [3, 10]), (82, [4, 9]), (96, [5, 8]), (96, [6, 7])]

def node77Piece5UnitOutput_sector0 : RawPoly ℕ := [node77Piece5UnitOutput_sector0_chunk0, node77Piece5UnitOutput_sector0_chunk1].flatten

def node77Piece5UnitOutput : SectorVector := [(-1, node77Piece5UnitOutput_sector0)]

theorem node77Piece5_check : VectorCertificate (neutralBoundS JR (-5) node77Piece5UnitInput) node77Piece5UnitOutput := by decide +kernel

theorem node77Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece5Input) = evaluate node77Piece5Output :=
  mode_of_scaled _ _ (30) node77Piece5UnitInput node77Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece5_check)

def node77Piece6Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node77Piece6Input : SectorVector := [(-1, node77Piece6Input_sector0)]
def node77Piece6Output_sector0_chunk0 : RawPoly ℕ := [(-240, [0, 1, 1, 2, 3, 6]), (-480, [0, 1, 2, 2, 3, 5]), (-480, [0, 1, 2, 3, 3, 4]), (-1440, [0, 1, 2, 10]), (-960, [0, 1, 3, 9]), (-240, [0, 2, 2, 2, 3, 4]), (-240, [0, 2, 2, 3, 3, 3]), (-1440, [0, 2, 2, 9]), (-1740, [0, 2, 3, 8]), (-1440, [0, 2, 4, 7]), (-1440, [0, 2, 5, 6]), (-960, [0, 3, 3, 7]), (-960, [0, 3, 4, 6]), (-480, [0, 3, 5, 5]), (-2880, [0, 13]), (80, [1, 1, 1, 2, 3, 5]), (240, [1, 1, 2, 2, 3, 4]), (120, [1, 1, 2, 3, 3, 3]), (720, [1, 1, 2, 9]), (480, [1, 1, 3, 8]), (240, [1, 2, 2, 2, 3, 3]), (1440, [1, 2, 2, 8]), (3720, [1, 2, 3, 7]), (1440, [1, 2, 4, 6])]

def node77Piece6Output_sector0_chunk1 : RawPoly ℕ := [(720, [1, 2, 5, 5]), (960, [1, 3, 3, 6]), (960, [1, 3, 4, 5]), (2880, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (720, [2, 2, 2, 7]), (3740, [2, 2, 3, 6]), (1440, [2, 2, 4, 5]), (3800, [2, 3, 3, 5]), (2310, [2, 3, 4, 4]), (-5160, [2, 11]), (480, [3, 3, 3, 4]), (120, [3, 10]), (2880, [4, 9]), (2880, [5, 8]), (2880, [6, 7])]

def node77Piece6Output_sector0 : RawPoly ℕ := [node77Piece6Output_sector0_chunk0, node77Piece6Output_sector0_chunk1].flatten

def node77Piece6Output : SectorVector := [(-1, node77Piece6Output_sector0)]

def node77Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node77Piece6UnitInput_sector0 : RawPoly ℕ := [node77Piece6UnitInput_sector0_chunk0].flatten

def node77Piece6UnitInput : SectorVector := [(-1, node77Piece6UnitInput_sector0)]

def node77Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 2, 3, 6]), (-24, [0, 1, 2, 2, 3, 5]), (-24, [0, 1, 2, 3, 3, 4]), (-72, [0, 1, 2, 10]), (-48, [0, 1, 3, 9]), (-12, [0, 2, 2, 2, 3, 4]), (-12, [0, 2, 2, 3, 3, 3]), (-72, [0, 2, 2, 9]), (-87, [0, 2, 3, 8]), (-72, [0, 2, 4, 7]), (-72, [0, 2, 5, 6]), (-48, [0, 3, 3, 7]), (-48, [0, 3, 4, 6]), (-24, [0, 3, 5, 5]), (-144, [0, 13]), (4, [1, 1, 1, 2, 3, 5]), (12, [1, 1, 2, 2, 3, 4]), (6, [1, 1, 2, 3, 3, 3]), (36, [1, 1, 2, 9]), (24, [1, 1, 3, 8]), (12, [1, 2, 2, 2, 3, 3]), (72, [1, 2, 2, 8]), (186, [1, 2, 3, 7]), (72, [1, 2, 4, 6])]

def node77Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [1, 2, 5, 5]), (48, [1, 3, 3, 6]), (48, [1, 3, 4, 5]), (144, [1, 12]), (1, [2, 2, 2, 2, 2, 3]), (36, [2, 2, 2, 7]), (187, [2, 2, 3, 6]), (72, [2, 2, 4, 5]), (190, [2, 3, 3, 5]), (231/2, [2, 3, 4, 4]), (-258, [2, 11]), (24, [3, 3, 3, 4]), (6, [3, 10]), (144, [4, 9]), (144, [5, 8]), (144, [6, 7])]

def node77Piece6UnitOutput_sector0 : RawPoly ℕ := [node77Piece6UnitOutput_sector0_chunk0, node77Piece6UnitOutput_sector0_chunk1].flatten

def node77Piece6UnitOutput : SectorVector := [(-1, node77Piece6UnitOutput_sector0)]

theorem node77Piece6_check : VectorCertificate (neutralBoundS JR (-5) node77Piece6UnitInput) node77Piece6UnitOutput := by decide +kernel

theorem node77Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece6Input) = evaluate node77Piece6Output :=
  mode_of_scaled _ _ (20) node77Piece6UnitInput node77Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece6_check)

def node77Piece7Input_sector0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1])]

def node77Piece7Input : SectorVector := [(1, node77Piece7Input_sector0)]
def node77Piece7Output_sector0_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (-12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (-126, [0, 1, 1, 1, 1, 1, 1, 7]), (-1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (-211, [0, 1, 1, 1, 1, 1, 2, 6]), (-226, [0, 1, 1, 1, 1, 1, 3, 5]), (-231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (-60, [0, 1, 1, 1, 1, 2, 2, 5]), (-120, [0, 1, 1, 1, 1, 2, 3, 4]), (-20, [0, 1, 1, 1, 1, 3, 3, 3]), (-170, [0, 1, 1, 1, 1, 9]), (-240, [0, 1, 1, 1, 2, 8]), (-240, [0, 1, 1, 1, 3, 7]), (-240, [0, 1, 1, 1, 4, 6]), (-120, [0, 1, 1, 1, 5, 5]), (-240, [0, 1, 1, 11]), (-96, [1, 1, 1, 1, 1, 1, 1, 6]), (-192, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (-96, [1, 1, 1, 1, 1, 2, 2, 4]), (-96, [1, 1, 1, 1, 1, 2, 3, 3]), (-696, [1, 1, 1, 1, 1, 8])]

def node77Piece7Output_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (-960, [1, 1, 1, 1, 4, 5]), (-1920, [1, 1, 1, 10])]

def node77Piece7Output_sector0 : RawPoly ℕ := [node77Piece7Output_sector0_chunk0, node77Piece7Output_sector0_chunk1].flatten

def node77Piece7Output : SectorVector := [(1, node77Piece7Output_sector0)]

def node77Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node77Piece7UnitInput_sector0 : RawPoly ℕ := [node77Piece7UnitInput_sector0_chunk0].flatten

def node77Piece7UnitInput : SectorVector := [(1, node77Piece7UnitInput_sector0)]

def node77Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (126, [0, 1, 1, 1, 1, 1, 1, 7]), (1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (211, [0, 1, 1, 1, 1, 1, 2, 6]), (226, [0, 1, 1, 1, 1, 1, 3, 5]), (231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 5]), (120, [0, 1, 1, 1, 1, 2, 3, 4]), (20, [0, 1, 1, 1, 1, 3, 3, 3]), (170, [0, 1, 1, 1, 1, 9]), (240, [0, 1, 1, 1, 2, 8]), (240, [0, 1, 1, 1, 3, 7]), (240, [0, 1, 1, 1, 4, 6]), (120, [0, 1, 1, 1, 5, 5]), (240, [0, 1, 1, 11]), (96, [1, 1, 1, 1, 1, 1, 1, 6]), (192, [1, 1, 1, 1, 1, 1, 2, 5]), (192, [1, 1, 1, 1, 1, 1, 3, 4]), (96, [1, 1, 1, 1, 1, 2, 2, 4]), (96, [1, 1, 1, 1, 1, 2, 3, 3]), (696, [1, 1, 1, 1, 1, 8])]

def node77Piece7UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [1, 1, 1, 1, 2, 7]), (960, [1, 1, 1, 1, 3, 6]), (960, [1, 1, 1, 1, 4, 5]), (1920, [1, 1, 1, 10])]

def node77Piece7UnitOutput_sector0 : RawPoly ℕ := [node77Piece7UnitOutput_sector0_chunk0, node77Piece7UnitOutput_sector0_chunk1].flatten

def node77Piece7UnitOutput : SectorVector := [(1, node77Piece7UnitOutput_sector0)]

theorem node77Piece7_check : VectorCertificate (neutralBoundS JR (-5) node77Piece7UnitInput) node77Piece7UnitOutput := by decide +kernel

theorem node77Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece7Input) = evaluate node77Piece7Output :=
  mode_of_scaled _ _ (-1) node77Piece7UnitInput node77Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece7_check)

def node77Piece8Input_sector0 : RawPoly ℕ := [(-10, [0, 1, 1, 3])]

def node77Piece8Input : SectorVector := [(1, node77Piece8Input_sector0)]
def node77Piece8Output_sector0_chunk0 : RawPoly ℕ := [(-40, [0, 1, 1, 1, 1, 1, 3, 5]), (-120, [0, 1, 1, 1, 1, 2, 3, 4]), (-60, [0, 1, 1, 1, 1, 3, 3, 3]), (-360, [0, 1, 1, 1, 1, 9]), (-120, [0, 1, 1, 1, 2, 2, 3, 3]), (-720, [0, 1, 1, 1, 2, 8]), (-1620, [0, 1, 1, 1, 3, 7]), (-720, [0, 1, 1, 1, 4, 6]), (-360, [0, 1, 1, 1, 5, 5]), (-10, [0, 1, 1, 2, 2, 2, 2, 3]), (-360, [0, 1, 1, 2, 2, 7]), (-2110, [0, 1, 1, 2, 3, 6]), (-720, [0, 1, 1, 2, 4, 5]), (-1900, [0, 1, 1, 3, 3, 5]), (-1155, [0, 1, 1, 3, 4, 4]), (2580, [0, 1, 1, 11]), (-240, [0, 1, 2, 2, 3, 5]), (-480, [0, 1, 2, 3, 3, 4]), (-1440, [0, 1, 2, 10]), (-80, [0, 1, 3, 3, 3, 3]), (-1400, [0, 1, 3, 9]), (-1440, [0, 1, 4, 8]), (-1440, [0, 1, 5, 7]), (-720, [0, 1, 6, 6])]

def node77Piece8Output_sector0_chunk1 : RawPoly ℕ := [(-240, [0, 2, 3, 8]), (-240, [0, 3, 3, 7]), (-240, [0, 3, 4, 6]), (-120, [0, 3, 5, 5]), (-720, [0, 13]), (-960, [1, 1, 1, 1, 3, 6]), (-1920, [1, 1, 1, 2, 3, 5]), (-1920, [1, 1, 1, 3, 3, 4]), (-5760, [1, 1, 1, 10]), (-960, [1, 1, 2, 2, 3, 4]), (-960, [1, 1, 2, 3, 3, 3]), (-5760, [1, 1, 2, 9]), (-6960, [1, 1, 3, 8]), (-5760, [1, 1, 4, 7]), (-5760, [1, 1, 5, 6]), (-3840, [1, 2, 3, 7]), (-3840, [1, 3, 3, 6]), (-3840, [1, 3, 4, 5]), (-11520, [1, 12]), (-1920, [3, 10])]

def node77Piece8Output_sector0 : RawPoly ℕ := [node77Piece8Output_sector0_chunk0, node77Piece8Output_sector0_chunk1].flatten

def node77Piece8Output : SectorVector := [(1, node77Piece8Output_sector0)]

def node77Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node77Piece8UnitInput_sector0 : RawPoly ℕ := [node77Piece8UnitInput_sector0_chunk0].flatten

def node77Piece8UnitInput : SectorVector := [(1, node77Piece8UnitInput_sector0)]

def node77Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 3, 5]), (12, [0, 1, 1, 1, 1, 2, 3, 4]), (6, [0, 1, 1, 1, 1, 3, 3, 3]), (36, [0, 1, 1, 1, 1, 9]), (12, [0, 1, 1, 1, 2, 2, 3, 3]), (72, [0, 1, 1, 1, 2, 8]), (162, [0, 1, 1, 1, 3, 7]), (72, [0, 1, 1, 1, 4, 6]), (36, [0, 1, 1, 1, 5, 5]), (1, [0, 1, 1, 2, 2, 2, 2, 3]), (36, [0, 1, 1, 2, 2, 7]), (211, [0, 1, 1, 2, 3, 6]), (72, [0, 1, 1, 2, 4, 5]), (190, [0, 1, 1, 3, 3, 5]), (231/2, [0, 1, 1, 3, 4, 4]), (-258, [0, 1, 1, 11]), (24, [0, 1, 2, 2, 3, 5]), (48, [0, 1, 2, 3, 3, 4]), (144, [0, 1, 2, 10]), (8, [0, 1, 3, 3, 3, 3]), (140, [0, 1, 3, 9]), (144, [0, 1, 4, 8]), (144, [0, 1, 5, 7]), (72, [0, 1, 6, 6])]

def node77Piece8UnitOutput_sector0_chunk1 : RawPoly ℕ := [(24, [0, 2, 3, 8]), (24, [0, 3, 3, 7]), (24, [0, 3, 4, 6]), (12, [0, 3, 5, 5]), (72, [0, 13]), (96, [1, 1, 1, 1, 3, 6]), (192, [1, 1, 1, 2, 3, 5]), (192, [1, 1, 1, 3, 3, 4]), (576, [1, 1, 1, 10]), (96, [1, 1, 2, 2, 3, 4]), (96, [1, 1, 2, 3, 3, 3]), (576, [1, 1, 2, 9]), (696, [1, 1, 3, 8]), (576, [1, 1, 4, 7]), (576, [1, 1, 5, 6]), (384, [1, 2, 3, 7]), (384, [1, 3, 3, 6]), (384, [1, 3, 4, 5]), (1152, [1, 12]), (192, [3, 10])]

def node77Piece8UnitOutput_sector0 : RawPoly ℕ := [node77Piece8UnitOutput_sector0_chunk0, node77Piece8UnitOutput_sector0_chunk1].flatten

def node77Piece8UnitOutput : SectorVector := [(1, node77Piece8UnitOutput_sector0)]

theorem node77Piece8_check : VectorCertificate (neutralBoundS JR (-5) node77Piece8UnitInput) node77Piece8UnitOutput := by decide +kernel

theorem node77Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece8Input) = evaluate node77Piece8Output :=
  mode_of_scaled _ _ (-10) node77Piece8UnitInput node77Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece8_check)

def node77Piece9Input_sector0 : RawPoly ℕ := [(-15/2, [0, 1, 2, 2])]

def node77Piece9Input : SectorVector := [(1, node77Piece9Input_sector0)]
def node77Piece9Output_sector0_chunk0 : RawPoly ℕ := [(-30, [0, 1, 1, 1, 1, 2, 2, 5]), (-90, [0, 1, 1, 1, 2, 2, 2, 4]), (-45, [0, 1, 1, 1, 2, 2, 3, 3]), (-360, [0, 1, 1, 1, 2, 8]), (-90, [0, 1, 1, 2, 2, 2, 2, 3]), (-1305, [0, 1, 1, 2, 2, 7]), (-720, [0, 1, 1, 2, 3, 6]), (-720, [0, 1, 1, 2, 4, 5]), (-720, [0, 1, 1, 11]), (-15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (-2445/2, [0, 1, 2, 2, 2, 6]), (-1695, [0, 1, 2, 2, 3, 5]), (-3465/4, [0, 1, 2, 2, 4, 4]), (-360, [0, 1, 2, 3, 3, 4]), (630, [0, 1, 2, 10]), (-720, [0, 1, 3, 9]), (-720, [0, 1, 4, 8]), (-720, [0, 1, 5, 7]), (-360, [0, 1, 6, 6]), (-90, [0, 2, 2, 2, 2, 5]), (-180, [0, 2, 2, 2, 3, 4]), (-30, [0, 2, 2, 3, 3, 3]), (-615, [0, 2, 2, 9]), (-720, [0, 2, 3, 8])]

def node77Piece9Output_sector0_chunk1 : RawPoly ℕ := [(-720, [0, 2, 4, 7]), (-720, [0, 2, 5, 6]), (-720, [0, 13]), (-720, [1, 1, 1, 2, 2, 6]), (-1440, [1, 1, 2, 2, 2, 5]), (-1440, [1, 1, 2, 2, 3, 4]), (-5760, [1, 1, 2, 9]), (-720, [1, 2, 2, 2, 2, 4]), (-720, [1, 2, 2, 2, 3, 3]), (-5220, [1, 2, 2, 8]), (-5760, [1, 2, 3, 7]), (-5760, [1, 2, 4, 6]), (-2880, [1, 2, 5, 5]), (-5760, [1, 12]), (-1440, [2, 2, 2, 7]), (-1440, [2, 2, 3, 6]), (-1440, [2, 2, 4, 5]), (-5760, [2, 11])]

def node77Piece9Output_sector0 : RawPoly ℕ := [node77Piece9Output_sector0_chunk0, node77Piece9Output_sector0_chunk1].flatten

def node77Piece9Output : SectorVector := [(1, node77Piece9Output_sector0)]

def node77Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node77Piece9UnitInput_sector0 : RawPoly ℕ := [node77Piece9UnitInput_sector0_chunk0].flatten

def node77Piece9UnitInput : SectorVector := [(1, node77Piece9UnitInput_sector0)]

def node77Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 5]), (12, [0, 1, 1, 1, 2, 2, 2, 4]), (6, [0, 1, 1, 1, 2, 2, 3, 3]), (48, [0, 1, 1, 1, 2, 8]), (12, [0, 1, 1, 2, 2, 2, 2, 3]), (174, [0, 1, 1, 2, 2, 7]), (96, [0, 1, 1, 2, 3, 6]), (96, [0, 1, 1, 2, 4, 5]), (96, [0, 1, 1, 11]), (1, [0, 1, 2, 2, 2, 2, 2, 2]), (163, [0, 1, 2, 2, 2, 6]), (226, [0, 1, 2, 2, 3, 5]), (231/2, [0, 1, 2, 2, 4, 4]), (48, [0, 1, 2, 3, 3, 4]), (-84, [0, 1, 2, 10]), (96, [0, 1, 3, 9]), (96, [0, 1, 4, 8]), (96, [0, 1, 5, 7]), (48, [0, 1, 6, 6]), (12, [0, 2, 2, 2, 2, 5]), (24, [0, 2, 2, 2, 3, 4]), (4, [0, 2, 2, 3, 3, 3]), (82, [0, 2, 2, 9]), (96, [0, 2, 3, 8])]

def node77Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [0, 2, 4, 7]), (96, [0, 2, 5, 6]), (96, [0, 13]), (96, [1, 1, 1, 2, 2, 6]), (192, [1, 1, 2, 2, 2, 5]), (192, [1, 1, 2, 2, 3, 4]), (768, [1, 1, 2, 9]), (96, [1, 2, 2, 2, 2, 4]), (96, [1, 2, 2, 2, 3, 3]), (696, [1, 2, 2, 8]), (768, [1, 2, 3, 7]), (768, [1, 2, 4, 6]), (384, [1, 2, 5, 5]), (768, [1, 12]), (192, [2, 2, 2, 7]), (192, [2, 2, 3, 6]), (192, [2, 2, 4, 5]), (768, [2, 11])]

def node77Piece9UnitOutput_sector0 : RawPoly ℕ := [node77Piece9UnitOutput_sector0_chunk0, node77Piece9UnitOutput_sector0_chunk1].flatten

def node77Piece9UnitOutput : SectorVector := [(1, node77Piece9UnitOutput_sector0)]

theorem node77Piece9_check : VectorCertificate (neutralBoundS JR (-5) node77Piece9UnitInput) node77Piece9UnitOutput := by decide +kernel

theorem node77Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece9Input) = evaluate node77Piece9Output :=
  mode_of_scaled _ _ (-15/2) node77Piece9UnitInput node77Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece9_check)

def node77Piece10Input_sector0 : RawPoly ℕ := [(-6, [0, 5])]

def node77Piece10Input : SectorVector := [(1, node77Piece10Input_sector0)]
def node77Piece10Output_sector0_chunk0 : RawPoly ℕ := [(-24, [0, 1, 1, 1, 5, 5]), (-72, [0, 1, 1, 2, 4, 5]), (-36, [0, 1, 1, 3, 3, 5]), (-360, [0, 1, 1, 11]), (-72, [0, 1, 2, 2, 3, 5]), (-720, [0, 1, 2, 10]), (-720, [0, 1, 3, 9]), (-720, [0, 1, 4, 8]), (-1116, [0, 1, 5, 7]), (-360, [0, 1, 6, 6]), (-6, [0, 2, 2, 2, 2, 5]), (-360, [0, 2, 2, 9]), (-720, [0, 2, 3, 8]), (-720, [0, 2, 4, 7]), (-1266, [0, 2, 5, 6]), (-360, [0, 3, 3, 7]), (-720, [0, 3, 4, 6]), (-996, [0, 3, 5, 5]), (-693, [0, 4, 4, 5]), (8820, [0, 13]), (-576, [1, 1, 5, 6]), (-1152, [1, 2, 5, 5]), (-1152, [1, 3, 4, 5]), (-5760, [1, 12])]

def node77Piece10Output_sector0_chunk1 : RawPoly ℕ := [(-576, [2, 2, 4, 5]), (-576, [2, 3, 3, 5]), (-5760, [2, 11]), (-5760, [3, 10]), (-5760, [4, 9]), (-4176, [5, 8]), (-5760, [6, 7])]

def node77Piece10Output_sector0 : RawPoly ℕ := [node77Piece10Output_sector0_chunk0, node77Piece10Output_sector0_chunk1].flatten

def node77Piece10Output : SectorVector := [(1, node77Piece10Output_sector0)]

def node77Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node77Piece10UnitInput_sector0 : RawPoly ℕ := [node77Piece10UnitInput_sector0_chunk0].flatten

def node77Piece10UnitInput : SectorVector := [(1, node77Piece10UnitInput_sector0)]

def node77Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 5, 5]), (12, [0, 1, 1, 2, 4, 5]), (6, [0, 1, 1, 3, 3, 5]), (60, [0, 1, 1, 11]), (12, [0, 1, 2, 2, 3, 5]), (120, [0, 1, 2, 10]), (120, [0, 1, 3, 9]), (120, [0, 1, 4, 8]), (186, [0, 1, 5, 7]), (60, [0, 1, 6, 6]), (1, [0, 2, 2, 2, 2, 5]), (60, [0, 2, 2, 9]), (120, [0, 2, 3, 8]), (120, [0, 2, 4, 7]), (211, [0, 2, 5, 6]), (60, [0, 3, 3, 7]), (120, [0, 3, 4, 6]), (166, [0, 3, 5, 5]), (231/2, [0, 4, 4, 5]), (-1470, [0, 13]), (96, [1, 1, 5, 6]), (192, [1, 2, 5, 5]), (192, [1, 3, 4, 5]), (960, [1, 12])]

def node77Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [2, 2, 4, 5]), (96, [2, 3, 3, 5]), (960, [2, 11]), (960, [3, 10]), (960, [4, 9]), (696, [5, 8]), (960, [6, 7])]

def node77Piece10UnitOutput_sector0 : RawPoly ℕ := [node77Piece10UnitOutput_sector0_chunk0, node77Piece10UnitOutput_sector0_chunk1].flatten

def node77Piece10UnitOutput : SectorVector := [(1, node77Piece10UnitOutput_sector0)]

theorem node77Piece10_check : VectorCertificate (neutralBoundS JR (-5) node77Piece10UnitInput) node77Piece10UnitOutput := by decide +kernel

theorem node77Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece10Input) = evaluate node77Piece10Output :=
  mode_of_scaled _ _ (-6) node77Piece10UnitInput node77Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece10_check)

def node77Piece11Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node77Piece11Input : SectorVector := [(1, node77Piece11Input_sector0)]
def node77Piece11Output_sector0_chunk0 : RawPoly ℕ := [(240, [0, 1, 1, 1, 1, 1, 2, 6]), (480, [0, 1, 1, 1, 1, 2, 2, 5]), (480, [0, 1, 1, 1, 1, 2, 3, 4]), (960, [0, 1, 1, 1, 1, 9]), (240, [0, 1, 1, 1, 2, 2, 2, 4]), (240, [0, 1, 1, 1, 2, 2, 3, 3]), (1740, [0, 1, 1, 1, 2, 8]), (960, [0, 1, 1, 1, 3, 7]), (960, [0, 1, 1, 1, 4, 6]), (480, [0, 1, 1, 1, 5, 5]), (1440, [0, 1, 1, 2, 2, 7]), (1440, [0, 1, 1, 2, 3, 6]), (1440, [0, 1, 1, 2, 4, 5]), (2880, [0, 1, 1, 11]), (1440, [0, 1, 2, 10]), (80, [1, 1, 1, 1, 1, 1, 2, 5]), (240, [1, 1, 1, 1, 1, 2, 2, 4]), (120, [1, 1, 1, 1, 1, 2, 3, 3]), (480, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (3000, [1, 1, 1, 1, 2, 7]), (960, [1, 1, 1, 1, 3, 6]), (960, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2])]

def node77Piece11Output_sector0_chunk1 : RawPoly ℕ := [(3740, [1, 1, 1, 2, 2, 6]), (4520, [1, 1, 1, 2, 3, 5]), (2310, [1, 1, 1, 2, 4, 4]), (480, [1, 1, 1, 3, 3, 4]), (120, [1, 1, 1, 10]), (720, [1, 1, 2, 2, 2, 5]), (1440, [1, 1, 2, 2, 3, 4]), (240, [1, 1, 2, 3, 3, 3]), (3480, [1, 1, 2, 9]), (2880, [1, 1, 3, 8]), (2880, [1, 1, 4, 7]), (2880, [1, 1, 5, 6]), (1440, [1, 2, 2, 8]), (1440, [1, 2, 3, 7]), (1440, [1, 2, 4, 6]), (720, [1, 2, 5, 5]), (2880, [1, 12]), (480, [2, 11])]

def node77Piece11Output_sector0 : RawPoly ℕ := [node77Piece11Output_sector0_chunk0, node77Piece11Output_sector0_chunk1].flatten

def node77Piece11Output : SectorVector := [(1, node77Piece11Output_sector0)]

def node77Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node77Piece11UnitInput_sector0 : RawPoly ℕ := [node77Piece11UnitInput_sector0_chunk0].flatten

def node77Piece11UnitInput : SectorVector := [(1, node77Piece11UnitInput_sector0)]

def node77Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 1, 1, 2, 6]), (24, [0, 1, 1, 1, 1, 2, 2, 5]), (24, [0, 1, 1, 1, 1, 2, 3, 4]), (48, [0, 1, 1, 1, 1, 9]), (12, [0, 1, 1, 1, 2, 2, 2, 4]), (12, [0, 1, 1, 1, 2, 2, 3, 3]), (87, [0, 1, 1, 1, 2, 8]), (48, [0, 1, 1, 1, 3, 7]), (48, [0, 1, 1, 1, 4, 6]), (24, [0, 1, 1, 1, 5, 5]), (72, [0, 1, 1, 2, 2, 7]), (72, [0, 1, 1, 2, 3, 6]), (72, [0, 1, 1, 2, 4, 5]), (144, [0, 1, 1, 11]), (72, [0, 1, 2, 10]), (4, [1, 1, 1, 1, 1, 1, 2, 5]), (12, [1, 1, 1, 1, 1, 2, 2, 4]), (6, [1, 1, 1, 1, 1, 2, 3, 3]), (24, [1, 1, 1, 1, 1, 8]), (12, [1, 1, 1, 1, 2, 2, 2, 3]), (150, [1, 1, 1, 1, 2, 7]), (48, [1, 1, 1, 1, 3, 6]), (48, [1, 1, 1, 1, 4, 5]), (1, [1, 1, 1, 2, 2, 2, 2, 2])]

def node77Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(187, [1, 1, 1, 2, 2, 6]), (226, [1, 1, 1, 2, 3, 5]), (231/2, [1, 1, 1, 2, 4, 4]), (24, [1, 1, 1, 3, 3, 4]), (6, [1, 1, 1, 10]), (36, [1, 1, 2, 2, 2, 5]), (72, [1, 1, 2, 2, 3, 4]), (12, [1, 1, 2, 3, 3, 3]), (174, [1, 1, 2, 9]), (144, [1, 1, 3, 8]), (144, [1, 1, 4, 7]), (144, [1, 1, 5, 6]), (72, [1, 2, 2, 8]), (72, [1, 2, 3, 7]), (72, [1, 2, 4, 6]), (36, [1, 2, 5, 5]), (144, [1, 12]), (24, [2, 11])]

def node77Piece11UnitOutput_sector0 : RawPoly ℕ := [node77Piece11UnitOutput_sector0_chunk0, node77Piece11UnitOutput_sector0_chunk1].flatten

def node77Piece11UnitOutput : SectorVector := [(1, node77Piece11UnitOutput_sector0)]

theorem node77Piece11_check : VectorCertificate (neutralBoundS JR (-5) node77Piece11UnitInput) node77Piece11UnitOutput := by decide +kernel

theorem node77Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece11Input) = evaluate node77Piece11Output :=
  mode_of_scaled _ _ (20) node77Piece11UnitInput node77Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece11_check)

def node77Piece12Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node77Piece12Input : SectorVector := [(1, node77Piece12Input_sector0)]
def node77Piece12Output_sector0_chunk0 : RawPoly ℕ := [(360, [0, 1, 1, 1, 4, 6]), (720, [0, 1, 1, 2, 4, 5]), (720, [0, 1, 1, 3, 4, 4]), (2880, [0, 1, 1, 11]), (360, [0, 1, 2, 2, 4, 4]), (360, [0, 1, 2, 3, 3, 4]), (2880, [0, 1, 2, 10]), (2880, [0, 1, 3, 9]), (2610, [0, 1, 4, 8]), (2880, [0, 1, 5, 7]), (1440, [0, 1, 6, 6]), (720, [0, 2, 4, 7]), (720, [0, 3, 4, 6]), (720, [0, 4, 4, 5]), (2880, [0, 13]), (120, [1, 1, 1, 1, 4, 5]), (360, [1, 1, 1, 2, 4, 4]), (180, [1, 1, 1, 3, 3, 4]), (1440, [1, 1, 1, 10]), (360, [1, 1, 2, 2, 3, 4]), (2880, [1, 1, 2, 9]), (2880, [1, 1, 3, 8]), (5220, [1, 1, 4, 7]), (2880, [1, 1, 5, 6])]

def node77Piece12Output_sector0_chunk1 : RawPoly ℕ := [(30, [1, 2, 2, 2, 2, 4]), (1440, [1, 2, 2, 8]), (2880, [1, 2, 3, 7]), (6330, [1, 2, 4, 6]), (1440, [1, 2, 5, 5]), (1440, [1, 3, 3, 6]), (6780, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-22200, [1, 12]), (360, [2, 2, 4, 5]), (720, [2, 3, 4, 4]), (2880, [2, 11]), (120, [3, 3, 3, 4]), (2880, [3, 10]), (2460, [4, 9]), (2880, [5, 8]), (2880, [6, 7])]

def node77Piece12Output_sector0 : RawPoly ℕ := [node77Piece12Output_sector0_chunk0, node77Piece12Output_sector0_chunk1].flatten

def node77Piece12Output : SectorVector := [(1, node77Piece12Output_sector0)]

def node77Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node77Piece12UnitInput_sector0 : RawPoly ℕ := [node77Piece12UnitInput_sector0_chunk0].flatten

def node77Piece12UnitInput : SectorVector := [(1, node77Piece12UnitInput_sector0)]

def node77Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 4, 6]), (24, [0, 1, 1, 2, 4, 5]), (24, [0, 1, 1, 3, 4, 4]), (96, [0, 1, 1, 11]), (12, [0, 1, 2, 2, 4, 4]), (12, [0, 1, 2, 3, 3, 4]), (96, [0, 1, 2, 10]), (96, [0, 1, 3, 9]), (87, [0, 1, 4, 8]), (96, [0, 1, 5, 7]), (48, [0, 1, 6, 6]), (24, [0, 2, 4, 7]), (24, [0, 3, 4, 6]), (24, [0, 4, 4, 5]), (96, [0, 13]), (4, [1, 1, 1, 1, 4, 5]), (12, [1, 1, 1, 2, 4, 4]), (6, [1, 1, 1, 3, 3, 4]), (48, [1, 1, 1, 10]), (12, [1, 1, 2, 2, 3, 4]), (96, [1, 1, 2, 9]), (96, [1, 1, 3, 8]), (174, [1, 1, 4, 7]), (96, [1, 1, 5, 6])]

def node77Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 4]), (48, [1, 2, 2, 8]), (96, [1, 2, 3, 7]), (211, [1, 2, 4, 6]), (48, [1, 2, 5, 5]), (48, [1, 3, 3, 6]), (226, [1, 3, 4, 5]), (167/2, [1, 4, 4, 4]), (-740, [1, 12]), (12, [2, 2, 4, 5]), (24, [2, 3, 4, 4]), (96, [2, 11]), (4, [3, 3, 3, 4]), (96, [3, 10]), (82, [4, 9]), (96, [5, 8]), (96, [6, 7])]

def node77Piece12UnitOutput_sector0 : RawPoly ℕ := [node77Piece12UnitOutput_sector0_chunk0, node77Piece12UnitOutput_sector0_chunk1].flatten

def node77Piece12UnitOutput : SectorVector := [(1, node77Piece12UnitOutput_sector0)]

theorem node77Piece12_check : VectorCertificate (neutralBoundS JR (-5) node77Piece12UnitInput) node77Piece12UnitOutput := by decide +kernel

theorem node77Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece12Input) = evaluate node77Piece12Output :=
  mode_of_scaled _ _ (30) node77Piece12UnitInput node77Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece12_check)

def node77Piece13Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node77Piece13Input : SectorVector := [(1, node77Piece13Input_sector0)]
def node77Piece13Output_sector0_chunk0 : RawPoly ℕ := [(240, [0, 1, 1, 2, 3, 6]), (480, [0, 1, 2, 2, 3, 5]), (480, [0, 1, 2, 3, 3, 4]), (1440, [0, 1, 2, 10]), (960, [0, 1, 3, 9]), (240, [0, 2, 2, 2, 3, 4]), (240, [0, 2, 2, 3, 3, 3]), (1440, [0, 2, 2, 9]), (1740, [0, 2, 3, 8]), (1440, [0, 2, 4, 7]), (1440, [0, 2, 5, 6]), (960, [0, 3, 3, 7]), (960, [0, 3, 4, 6]), (480, [0, 3, 5, 5]), (2880, [0, 13]), (80, [1, 1, 1, 2, 3, 5]), (240, [1, 1, 2, 2, 3, 4]), (120, [1, 1, 2, 3, 3, 3]), (720, [1, 1, 2, 9]), (480, [1, 1, 3, 8]), (240, [1, 2, 2, 2, 3, 3]), (1440, [1, 2, 2, 8]), (3720, [1, 2, 3, 7]), (1440, [1, 2, 4, 6])]

def node77Piece13Output_sector0_chunk1 : RawPoly ℕ := [(720, [1, 2, 5, 5]), (960, [1, 3, 3, 6]), (960, [1, 3, 4, 5]), (2880, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (720, [2, 2, 2, 7]), (3740, [2, 2, 3, 6]), (1440, [2, 2, 4, 5]), (3800, [2, 3, 3, 5]), (2310, [2, 3, 4, 4]), (-5160, [2, 11]), (480, [3, 3, 3, 4]), (120, [3, 10]), (2880, [4, 9]), (2880, [5, 8]), (2880, [6, 7])]

def node77Piece13Output_sector0 : RawPoly ℕ := [node77Piece13Output_sector0_chunk0, node77Piece13Output_sector0_chunk1].flatten

def node77Piece13Output : SectorVector := [(1, node77Piece13Output_sector0)]

def node77Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node77Piece13UnitInput_sector0 : RawPoly ℕ := [node77Piece13UnitInput_sector0_chunk0].flatten

def node77Piece13UnitInput : SectorVector := [(1, node77Piece13UnitInput_sector0)]

def node77Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 2, 3, 6]), (24, [0, 1, 2, 2, 3, 5]), (24, [0, 1, 2, 3, 3, 4]), (72, [0, 1, 2, 10]), (48, [0, 1, 3, 9]), (12, [0, 2, 2, 2, 3, 4]), (12, [0, 2, 2, 3, 3, 3]), (72, [0, 2, 2, 9]), (87, [0, 2, 3, 8]), (72, [0, 2, 4, 7]), (72, [0, 2, 5, 6]), (48, [0, 3, 3, 7]), (48, [0, 3, 4, 6]), (24, [0, 3, 5, 5]), (144, [0, 13]), (4, [1, 1, 1, 2, 3, 5]), (12, [1, 1, 2, 2, 3, 4]), (6, [1, 1, 2, 3, 3, 3]), (36, [1, 1, 2, 9]), (24, [1, 1, 3, 8]), (12, [1, 2, 2, 2, 3, 3]), (72, [1, 2, 2, 8]), (186, [1, 2, 3, 7]), (72, [1, 2, 4, 6])]

def node77Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [1, 2, 5, 5]), (48, [1, 3, 3, 6]), (48, [1, 3, 4, 5]), (144, [1, 12]), (1, [2, 2, 2, 2, 2, 3]), (36, [2, 2, 2, 7]), (187, [2, 2, 3, 6]), (72, [2, 2, 4, 5]), (190, [2, 3, 3, 5]), (231/2, [2, 3, 4, 4]), (-258, [2, 11]), (24, [3, 3, 3, 4]), (6, [3, 10]), (144, [4, 9]), (144, [5, 8]), (144, [6, 7])]

def node77Piece13UnitOutput_sector0 : RawPoly ℕ := [node77Piece13UnitOutput_sector0_chunk0, node77Piece13UnitOutput_sector0_chunk1].flatten

def node77Piece13UnitOutput : SectorVector := [(1, node77Piece13UnitOutput_sector0)]

theorem node77Piece13_check : VectorCertificate (neutralBoundS JR (-5) node77Piece13UnitInput) node77Piece13UnitOutput := by decide +kernel

theorem node77Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-5)
    (evaluate node77Piece13Input) = evaluate node77Piece13Output :=
  mode_of_scaled _ _ (20) node77Piece13UnitInput node77Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node77Piece13_check)

def node77Pieces : List (SectorVector × SectorVector) := [(node77Piece0Input, node77Piece0Output), (node77Piece1Input, node77Piece1Output), (node77Piece2Input, node77Piece2Output), (node77Piece3Input, node77Piece3Output), (node77Piece4Input, node77Piece4Output), (node77Piece5Input, node77Piece5Output), (node77Piece6Input, node77Piece6Output), (node77Piece7Input, node77Piece7Output), (node77Piece8Input, node77Piece8Output), (node77Piece9Input, node77Piece9Output), (node77Piece10Input, node77Piece10Output), (node77Piece11Input, node77Piece11Output), (node77Piece12Input, node77Piece12Output), (node77Piece13Input, node77Piece13Output)]

theorem node77Pieces_input : VectorCertificate (node77Pieces.flatMap Prod.fst) nineData := by decide +kernel

theorem node77Pieces_each : ∀ p ∈ node77Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-5) (evaluate p.1) = evaluate p.2 := by
  simp only [node77Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node77Piece0_value, node77Piece1_value, node77Piece2_value, node77Piece3_value, node77Piece4_value, node77Piece5_value, node77Piece6_value, node77Piece7_value, node77Piece8_value, node77Piece9_value, node77Piece10_value, node77Piece11_value, node77Piece12_value, node77Piece13_value, by simp⟩
end VOA.Classification.COne.OrbC2h
