import VOA.Classification.COne.OrbC2hDirectNeutral
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

def node83Piece0Input_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node83Piece0Input : SectorVector := [(-1, node83Piece0Input_sector0)]
def node83Piece0Output_sector0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (136, [0, 1, 1, 1, 1, 1, 1, 6]), (216, [0, 1, 1, 1, 1, 1, 2, 5]), (226, [0, 1, 1, 1, 1, 1, 3, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 4]), (60, [0, 1, 1, 1, 1, 2, 3, 3]), (270, [0, 1, 1, 1, 1, 8]), (240, [0, 1, 1, 1, 2, 7]), (240, [0, 1, 1, 1, 3, 6]), (240, [0, 1, 1, 1, 4, 5]), (240, [0, 1, 1, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-192, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (-96, [1, 1, 1, 1, 1, 2, 2, 3]), (-816, [1, 1, 1, 1, 1, 7]), (-960, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (-480, [1, 1, 1, 1, 4, 4]), (-1920, [1, 1, 1, 9])]

def node83Piece0Output : SectorVector := [(-1, node83Piece0Output_sector0)]

def node83Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node83Piece0UnitInput_sector0 : RawPoly ℕ := [node83Piece0UnitInput_sector0_chunk0].flatten

def node83Piece0UnitInput : SectorVector := [(-1, node83Piece0UnitInput_sector0)]

def node83Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (136, [0, 1, 1, 1, 1, 1, 1, 6]), (216, [0, 1, 1, 1, 1, 1, 2, 5]), (226, [0, 1, 1, 1, 1, 1, 3, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 4]), (60, [0, 1, 1, 1, 1, 2, 3, 3]), (270, [0, 1, 1, 1, 1, 8]), (240, [0, 1, 1, 1, 2, 7]), (240, [0, 1, 1, 1, 3, 6]), (240, [0, 1, 1, 1, 4, 5]), (240, [0, 1, 1, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-192, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (-96, [1, 1, 1, 1, 1, 2, 2, 3]), (-816, [1, 1, 1, 1, 1, 7]), (-960, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (-480, [1, 1, 1, 1, 4, 4]), (-1920, [1, 1, 1, 9])]

def node83Piece0UnitOutput_sector0 : RawPoly ℕ := [node83Piece0UnitOutput_sector0_chunk0].flatten

def node83Piece0UnitOutput : SectorVector := [(-1, node83Piece0UnitOutput_sector0)]

theorem node83Piece0_check : neutralDirectS JR (-4) node83Piece0UnitInput = node83Piece0UnitOutput := by decide +kernel

theorem node83Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece0Input) = evaluate node83Piece0Output :=
  mode_of_scaled _ _ (1) node83Piece0UnitInput node83Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece0_check)

def node83Piece1Input_sector0 : RawPoly ℕ := [(10, [0, 1, 1, 3])]

def node83Piece1Input : SectorVector := [(-1, node83Piece1Input_sector0)]
def node83Piece1Output_sector0_chunk0 : RawPoly ℕ := [(40, [0, 1, 1, 1, 1, 1, 3, 4]), (120, [0, 1, 1, 1, 1, 2, 3, 3]), (360, [0, 1, 1, 1, 1, 8]), (40, [0, 1, 1, 1, 2, 2, 2, 3]), (720, [0, 1, 1, 1, 2, 7]), (1720, [0, 1, 1, 1, 3, 6]), (720, [0, 1, 1, 1, 4, 5]), (360, [0, 1, 1, 2, 2, 6]), (2160, [0, 1, 1, 2, 3, 5]), (360, [0, 1, 1, 2, 4, 4]), (1900, [0, 1, 1, 3, 3, 4]), (-1680, [0, 1, 1, 10]), (240, [0, 1, 2, 2, 3, 4]), (240, [0, 1, 2, 3, 3, 3]), (1440, [0, 1, 2, 9]), (1800, [0, 1, 3, 8]), (1440, [0, 1, 4, 7]), (1440, [0, 1, 5, 6]), (240, [0, 2, 3, 7]), (240, [0, 3, 3, 6]), (240, [0, 3, 4, 5]), (720, [0, 12]), (-960, [1, 1, 1, 1, 3, 5]), (-1920, [1, 1, 1, 2, 3, 4])]

def node83Piece1Output_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 3, 3, 3]), (-5760, [1, 1, 1, 9]), (-960, [1, 1, 2, 2, 3, 3]), (-5760, [1, 1, 2, 8]), (-8160, [1, 1, 3, 7]), (-5760, [1, 1, 4, 6]), (-2880, [1, 1, 5, 5]), (-3840, [1, 2, 3, 6]), (-3840, [1, 3, 3, 5]), (-1920, [1, 3, 4, 4]), (-11520, [1, 11]), (-1920, [3, 9])]

def node83Piece1Output_sector0 : RawPoly ℕ := [node83Piece1Output_sector0_chunk0, node83Piece1Output_sector0_chunk1].flatten

def node83Piece1Output : SectorVector := [(-1, node83Piece1Output_sector0)]

def node83Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node83Piece1UnitInput_sector0 : RawPoly ℕ := [node83Piece1UnitInput_sector0_chunk0].flatten

def node83Piece1UnitInput : SectorVector := [(-1, node83Piece1UnitInput_sector0)]

def node83Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 3, 4]), (12, [0, 1, 1, 1, 1, 2, 3, 3]), (36, [0, 1, 1, 1, 1, 8]), (4, [0, 1, 1, 1, 2, 2, 2, 3]), (72, [0, 1, 1, 1, 2, 7]), (172, [0, 1, 1, 1, 3, 6]), (72, [0, 1, 1, 1, 4, 5]), (36, [0, 1, 1, 2, 2, 6]), (216, [0, 1, 1, 2, 3, 5]), (36, [0, 1, 1, 2, 4, 4]), (190, [0, 1, 1, 3, 3, 4]), (-168, [0, 1, 1, 10]), (24, [0, 1, 2, 2, 3, 4]), (24, [0, 1, 2, 3, 3, 3]), (144, [0, 1, 2, 9]), (180, [0, 1, 3, 8]), (144, [0, 1, 4, 7]), (144, [0, 1, 5, 6]), (24, [0, 2, 3, 7]), (24, [0, 3, 3, 6]), (24, [0, 3, 4, 5]), (72, [0, 12]), (-96, [1, 1, 1, 1, 3, 5]), (-192, [1, 1, 1, 2, 3, 4])]

def node83Piece1UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-96, [1, 1, 1, 3, 3, 3]), (-576, [1, 1, 1, 9]), (-96, [1, 1, 2, 2, 3, 3]), (-576, [1, 1, 2, 8]), (-816, [1, 1, 3, 7]), (-576, [1, 1, 4, 6]), (-288, [1, 1, 5, 5]), (-384, [1, 2, 3, 6]), (-384, [1, 3, 3, 5]), (-192, [1, 3, 4, 4]), (-1152, [1, 11]), (-192, [3, 9])]

def node83Piece1UnitOutput_sector0 : RawPoly ℕ := [node83Piece1UnitOutput_sector0_chunk0, node83Piece1UnitOutput_sector0_chunk1].flatten

def node83Piece1UnitOutput : SectorVector := [(-1, node83Piece1UnitOutput_sector0)]

theorem node83Piece1_check : neutralDirectS JR (-4) node83Piece1UnitInput = node83Piece1UnitOutput := by decide +kernel

theorem node83Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece1Input) = evaluate node83Piece1Output :=
  mode_of_scaled _ _ (10) node83Piece1UnitInput node83Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece1_check)

def node83Piece2Input_sector0 : RawPoly ℕ := [(15/2, [0, 1, 2, 2])]

def node83Piece2Input : SectorVector := [(-1, node83Piece2Input_sector0)]
def node83Piece2Output_sector0_chunk0 : RawPoly ℕ := [(30, [0, 1, 1, 1, 1, 2, 2, 4]), (90, [0, 1, 1, 1, 2, 2, 2, 3]), (360, [0, 1, 1, 1, 2, 7]), (30, [0, 1, 1, 2, 2, 2, 2, 2]), (1380, [0, 1, 1, 2, 2, 6]), (720, [0, 1, 1, 2, 3, 5]), (360, [0, 1, 1, 2, 4, 4]), (720, [0, 1, 1, 10]), (1260, [0, 1, 2, 2, 2, 5]), (1695, [0, 1, 2, 2, 3, 4]), (120, [0, 1, 2, 3, 3, 3]), (120, [0, 1, 2, 9]), (720, [0, 1, 3, 8]), (720, [0, 1, 4, 7]), (720, [0, 1, 5, 6]), (90, [0, 2, 2, 2, 2, 4]), (90, [0, 2, 2, 2, 3, 3]), (765, [0, 2, 2, 8]), (720, [0, 2, 3, 7]), (720, [0, 2, 4, 6]), (360, [0, 2, 5, 5]), (720, [0, 12]), (-720, [1, 1, 1, 2, 2, 5]), (-1440, [1, 1, 2, 2, 2, 4])]

def node83Piece2Output_sector0_chunk1 : RawPoly ℕ := [(-720, [1, 1, 2, 2, 3, 3]), (-5760, [1, 1, 2, 8]), (-720, [1, 2, 2, 2, 2, 3]), (-6120, [1, 2, 2, 7]), (-5760, [1, 2, 3, 6]), (-5760, [1, 2, 4, 5]), (-5760, [1, 11]), (-1440, [2, 2, 2, 6]), (-1440, [2, 2, 3, 5]), (-720, [2, 2, 4, 4]), (-5760, [2, 10])]

def node83Piece2Output_sector0 : RawPoly ℕ := [node83Piece2Output_sector0_chunk0, node83Piece2Output_sector0_chunk1].flatten

def node83Piece2Output : SectorVector := [(-1, node83Piece2Output_sector0)]

def node83Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node83Piece2UnitInput_sector0 : RawPoly ℕ := [node83Piece2UnitInput_sector0_chunk0].flatten

def node83Piece2UnitInput : SectorVector := [(-1, node83Piece2UnitInput_sector0)]

def node83Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 4]), (12, [0, 1, 1, 1, 2, 2, 2, 3]), (48, [0, 1, 1, 1, 2, 7]), (4, [0, 1, 1, 2, 2, 2, 2, 2]), (184, [0, 1, 1, 2, 2, 6]), (96, [0, 1, 1, 2, 3, 5]), (48, [0, 1, 1, 2, 4, 4]), (96, [0, 1, 1, 10]), (168, [0, 1, 2, 2, 2, 5]), (226, [0, 1, 2, 2, 3, 4]), (16, [0, 1, 2, 3, 3, 3]), (16, [0, 1, 2, 9]), (96, [0, 1, 3, 8]), (96, [0, 1, 4, 7]), (96, [0, 1, 5, 6]), (12, [0, 2, 2, 2, 2, 4]), (12, [0, 2, 2, 2, 3, 3]), (102, [0, 2, 2, 8]), (96, [0, 2, 3, 7]), (96, [0, 2, 4, 6]), (48, [0, 2, 5, 5]), (96, [0, 12]), (-96, [1, 1, 1, 2, 2, 5]), (-192, [1, 1, 2, 2, 2, 4])]

def node83Piece2UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-96, [1, 1, 2, 2, 3, 3]), (-768, [1, 1, 2, 8]), (-96, [1, 2, 2, 2, 2, 3]), (-816, [1, 2, 2, 7]), (-768, [1, 2, 3, 6]), (-768, [1, 2, 4, 5]), (-768, [1, 11]), (-192, [2, 2, 2, 6]), (-192, [2, 2, 3, 5]), (-96, [2, 2, 4, 4]), (-768, [2, 10])]

def node83Piece2UnitOutput_sector0 : RawPoly ℕ := [node83Piece2UnitOutput_sector0_chunk0, node83Piece2UnitOutput_sector0_chunk1].flatten

def node83Piece2UnitOutput : SectorVector := [(-1, node83Piece2UnitOutput_sector0)]

theorem node83Piece2_check : neutralDirectS JR (-4) node83Piece2UnitInput = node83Piece2UnitOutput := by decide +kernel

theorem node83Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece2Input) = evaluate node83Piece2Output :=
  mode_of_scaled _ _ (15/2) node83Piece2UnitInput node83Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece2_check)

def node83Piece3Input_sector0 : RawPoly ℕ := [(6, [0, 5])]

def node83Piece3Input : SectorVector := [(-1, node83Piece3Input_sector0)]
def node83Piece3Output_sector0_chunk0 : RawPoly ℕ := [(24, [0, 1, 1, 1, 4, 5]), (72, [0, 1, 1, 2, 3, 5]), (360, [0, 1, 1, 10]), (24, [0, 1, 2, 2, 2, 5]), (720, [0, 1, 2, 9]), (720, [0, 1, 3, 8]), (720, [0, 1, 4, 7]), (1176, [0, 1, 5, 6]), (360, [0, 2, 2, 8]), (720, [0, 2, 3, 7]), (720, [0, 2, 4, 6]), (936, [0, 2, 5, 5]), (360, [0, 3, 3, 6]), (1356, [0, 3, 4, 5]), (120, [0, 4, 4, 4]), (-7620, [0, 12]), (-576, [1, 1, 5, 5]), (-1152, [1, 2, 4, 5]), (-576, [1, 3, 3, 5]), (-5760, [1, 11]), (-576, [2, 2, 3, 5]), (-5760, [2, 10]), (-5760, [3, 9]), (-5760, [4, 8])]

def node83Piece3Output_sector0_chunk1 : RawPoly ℕ := [(-4896, [5, 7]), (-2880, [6, 6])]

def node83Piece3Output_sector0 : RawPoly ℕ := [node83Piece3Output_sector0_chunk0, node83Piece3Output_sector0_chunk1].flatten

def node83Piece3Output : SectorVector := [(-1, node83Piece3Output_sector0)]

def node83Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node83Piece3UnitInput_sector0 : RawPoly ℕ := [node83Piece3UnitInput_sector0_chunk0].flatten

def node83Piece3UnitInput : SectorVector := [(-1, node83Piece3UnitInput_sector0)]

def node83Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 4, 5]), (12, [0, 1, 1, 2, 3, 5]), (60, [0, 1, 1, 10]), (4, [0, 1, 2, 2, 2, 5]), (120, [0, 1, 2, 9]), (120, [0, 1, 3, 8]), (120, [0, 1, 4, 7]), (196, [0, 1, 5, 6]), (60, [0, 2, 2, 8]), (120, [0, 2, 3, 7]), (120, [0, 2, 4, 6]), (156, [0, 2, 5, 5]), (60, [0, 3, 3, 6]), (226, [0, 3, 4, 5]), (20, [0, 4, 4, 4]), (-1270, [0, 12]), (-96, [1, 1, 5, 5]), (-192, [1, 2, 4, 5]), (-96, [1, 3, 3, 5]), (-960, [1, 11]), (-96, [2, 2, 3, 5]), (-960, [2, 10]), (-960, [3, 9]), (-960, [4, 8])]

def node83Piece3UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-816, [5, 7]), (-480, [6, 6])]

def node83Piece3UnitOutput_sector0 : RawPoly ℕ := [node83Piece3UnitOutput_sector0_chunk0, node83Piece3UnitOutput_sector0_chunk1].flatten

def node83Piece3UnitOutput : SectorVector := [(-1, node83Piece3UnitOutput_sector0)]

theorem node83Piece3_check : neutralDirectS JR (-4) node83Piece3UnitInput = node83Piece3UnitOutput := by decide +kernel

theorem node83Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece3Input) = evaluate node83Piece3Output :=
  mode_of_scaled _ _ (6) node83Piece3UnitInput node83Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece3_check)

def node83Piece4Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node83Piece4Input : SectorVector := [(-1, node83Piece4Input_sector0)]
def node83Piece4Output_sector0_chunk0 : RawPoly ℕ := [(-240, [0, 1, 1, 1, 1, 1, 2, 5]), (-480, [0, 1, 1, 1, 1, 2, 2, 4]), (-240, [0, 1, 1, 1, 1, 2, 3, 3]), (-960, [0, 1, 1, 1, 1, 8]), (-240, [0, 1, 1, 1, 2, 2, 2, 3]), (-2040, [0, 1, 1, 1, 2, 7]), (-960, [0, 1, 1, 1, 3, 6]), (-960, [0, 1, 1, 1, 4, 5]), (-1440, [0, 1, 1, 2, 2, 6]), (-1440, [0, 1, 1, 2, 3, 5]), (-720, [0, 1, 1, 2, 4, 4]), (-2880, [0, 1, 1, 10]), (-1440, [0, 1, 2, 9]), (80, [1, 1, 1, 1, 1, 1, 2, 4]), (240, [1, 1, 1, 1, 1, 2, 2, 3]), (480, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (3200, [1, 1, 1, 1, 2, 6]), (960, [1, 1, 1, 1, 3, 5]), (480, [1, 1, 1, 1, 4, 4]), (3840, [1, 1, 1, 2, 2, 5]), (4520, [1, 1, 1, 2, 3, 4]), (160, [1, 1, 1, 3, 3, 3]), (1120, [1, 1, 1, 9])]

def node83Piece4Output_sector0_chunk1 : RawPoly ℕ := [(720, [1, 1, 2, 2, 2, 4]), (720, [1, 1, 2, 2, 3, 3]), (4680, [1, 1, 2, 8]), (2880, [1, 1, 3, 7]), (2880, [1, 1, 4, 6]), (1440, [1, 1, 5, 5]), (1440, [1, 2, 2, 7]), (1440, [1, 2, 3, 6]), (1440, [1, 2, 4, 5]), (2880, [1, 11]), (480, [2, 10])]

def node83Piece4Output_sector0 : RawPoly ℕ := [node83Piece4Output_sector0_chunk0, node83Piece4Output_sector0_chunk1].flatten

def node83Piece4Output : SectorVector := [(-1, node83Piece4Output_sector0)]

def node83Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node83Piece4UnitInput_sector0 : RawPoly ℕ := [node83Piece4UnitInput_sector0_chunk0].flatten

def node83Piece4UnitInput : SectorVector := [(-1, node83Piece4UnitInput_sector0)]

def node83Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 1, 1, 2, 5]), (-24, [0, 1, 1, 1, 1, 2, 2, 4]), (-12, [0, 1, 1, 1, 1, 2, 3, 3]), (-48, [0, 1, 1, 1, 1, 8]), (-12, [0, 1, 1, 1, 2, 2, 2, 3]), (-102, [0, 1, 1, 1, 2, 7]), (-48, [0, 1, 1, 1, 3, 6]), (-48, [0, 1, 1, 1, 4, 5]), (-72, [0, 1, 1, 2, 2, 6]), (-72, [0, 1, 1, 2, 3, 5]), (-36, [0, 1, 1, 2, 4, 4]), (-144, [0, 1, 1, 10]), (-72, [0, 1, 2, 9]), (4, [1, 1, 1, 1, 1, 1, 2, 4]), (12, [1, 1, 1, 1, 1, 2, 2, 3]), (24, [1, 1, 1, 1, 1, 7]), (4, [1, 1, 1, 1, 2, 2, 2, 2]), (160, [1, 1, 1, 1, 2, 6]), (48, [1, 1, 1, 1, 3, 5]), (24, [1, 1, 1, 1, 4, 4]), (192, [1, 1, 1, 2, 2, 5]), (226, [1, 1, 1, 2, 3, 4]), (8, [1, 1, 1, 3, 3, 3]), (56, [1, 1, 1, 9])]

def node83Piece4UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [1, 1, 2, 2, 2, 4]), (36, [1, 1, 2, 2, 3, 3]), (234, [1, 1, 2, 8]), (144, [1, 1, 3, 7]), (144, [1, 1, 4, 6]), (72, [1, 1, 5, 5]), (72, [1, 2, 2, 7]), (72, [1, 2, 3, 6]), (72, [1, 2, 4, 5]), (144, [1, 11]), (24, [2, 10])]

def node83Piece4UnitOutput_sector0 : RawPoly ℕ := [node83Piece4UnitOutput_sector0_chunk0, node83Piece4UnitOutput_sector0_chunk1].flatten

def node83Piece4UnitOutput : SectorVector := [(-1, node83Piece4UnitOutput_sector0)]

theorem node83Piece4_check : neutralDirectS JR (-4) node83Piece4UnitInput = node83Piece4UnitOutput := by decide +kernel

theorem node83Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece4Input) = evaluate node83Piece4Output :=
  mode_of_scaled _ _ (20) node83Piece4UnitInput node83Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece4_check)

def node83Piece5Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node83Piece5Input : SectorVector := [(-1, node83Piece5Input_sector0)]
def node83Piece5Output_sector0_chunk0 : RawPoly ℕ := [(-360, [0, 1, 1, 1, 4, 5]), (-720, [0, 1, 1, 2, 4, 4]), (-360, [0, 1, 1, 3, 3, 4]), (-2880, [0, 1, 1, 10]), (-360, [0, 1, 2, 2, 3, 4]), (-2880, [0, 1, 2, 9]), (-2880, [0, 1, 3, 8]), (-3060, [0, 1, 4, 7]), (-2880, [0, 1, 5, 6]), (-720, [0, 2, 4, 6]), (-720, [0, 3, 4, 5]), (-360, [0, 4, 4, 4]), (-2880, [0, 12]), (120, [1, 1, 1, 1, 4, 4]), (360, [1, 1, 1, 2, 3, 4]), (1440, [1, 1, 1, 9]), (120, [1, 1, 2, 2, 2, 4]), (2880, [1, 1, 2, 8]), (2880, [1, 1, 3, 7]), (5520, [1, 1, 4, 6]), (1440, [1, 1, 5, 5]), (1440, [1, 2, 2, 7]), (2880, [1, 2, 3, 6]), (6480, [1, 2, 4, 5])]

def node83Piece5Output_sector0_chunk1 : RawPoly ℕ := [(1440, [1, 3, 3, 5]), (5340, [1, 3, 4, 4]), (-18000, [1, 11]), (360, [2, 2, 4, 4]), (360, [2, 3, 3, 4]), (2880, [2, 10]), (2880, [3, 9]), (3060, [4, 8]), (2880, [5, 7]), (1440, [6, 6])]

def node83Piece5Output_sector0 : RawPoly ℕ := [node83Piece5Output_sector0_chunk0, node83Piece5Output_sector0_chunk1].flatten

def node83Piece5Output : SectorVector := [(-1, node83Piece5Output_sector0)]

def node83Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node83Piece5UnitInput_sector0 : RawPoly ℕ := [node83Piece5UnitInput_sector0_chunk0].flatten

def node83Piece5UnitInput : SectorVector := [(-1, node83Piece5UnitInput_sector0)]

def node83Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 4, 5]), (-24, [0, 1, 1, 2, 4, 4]), (-12, [0, 1, 1, 3, 3, 4]), (-96, [0, 1, 1, 10]), (-12, [0, 1, 2, 2, 3, 4]), (-96, [0, 1, 2, 9]), (-96, [0, 1, 3, 8]), (-102, [0, 1, 4, 7]), (-96, [0, 1, 5, 6]), (-24, [0, 2, 4, 6]), (-24, [0, 3, 4, 5]), (-12, [0, 4, 4, 4]), (-96, [0, 12]), (4, [1, 1, 1, 1, 4, 4]), (12, [1, 1, 1, 2, 3, 4]), (48, [1, 1, 1, 9]), (4, [1, 1, 2, 2, 2, 4]), (96, [1, 1, 2, 8]), (96, [1, 1, 3, 7]), (184, [1, 1, 4, 6]), (48, [1, 1, 5, 5]), (48, [1, 2, 2, 7]), (96, [1, 2, 3, 6]), (216, [1, 2, 4, 5])]

def node83Piece5UnitOutput_sector0_chunk1 : RawPoly ℕ := [(48, [1, 3, 3, 5]), (178, [1, 3, 4, 4]), (-600, [1, 11]), (12, [2, 2, 4, 4]), (12, [2, 3, 3, 4]), (96, [2, 10]), (96, [3, 9]), (102, [4, 8]), (96, [5, 7]), (48, [6, 6])]

def node83Piece5UnitOutput_sector0 : RawPoly ℕ := [node83Piece5UnitOutput_sector0_chunk0, node83Piece5UnitOutput_sector0_chunk1].flatten

def node83Piece5UnitOutput : SectorVector := [(-1, node83Piece5UnitOutput_sector0)]

theorem node83Piece5_check : neutralDirectS JR (-4) node83Piece5UnitInput = node83Piece5UnitOutput := by decide +kernel

theorem node83Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece5Input) = evaluate node83Piece5Output :=
  mode_of_scaled _ _ (30) node83Piece5UnitInput node83Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece5_check)

def node83Piece6Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node83Piece6Input : SectorVector := [(-1, node83Piece6Input_sector0)]
def node83Piece6Output_sector0_chunk0 : RawPoly ℕ := [(-240, [0, 1, 1, 2, 3, 5]), (-480, [0, 1, 2, 2, 3, 4]), (-240, [0, 1, 2, 3, 3, 3]), (-1440, [0, 1, 2, 9]), (-960, [0, 1, 3, 8]), (-240, [0, 2, 2, 2, 3, 3]), (-1440, [0, 2, 2, 8]), (-2040, [0, 2, 3, 7]), (-1440, [0, 2, 4, 6]), (-720, [0, 2, 5, 5]), (-960, [0, 3, 3, 6]), (-960, [0, 3, 4, 5]), (-2880, [0, 12]), (80, [1, 1, 1, 2, 3, 4]), (240, [1, 1, 2, 2, 3, 3]), (720, [1, 1, 2, 8]), (480, [1, 1, 3, 7]), (80, [1, 2, 2, 2, 2, 3]), (1440, [1, 2, 2, 7]), (3920, [1, 2, 3, 6]), (1440, [1, 2, 4, 5]), (960, [1, 3, 3, 5]), (480, [1, 3, 4, 4]), (2880, [1, 11])]

def node83Piece6Output_sector0_chunk1 : RawPoly ℕ := [(720, [2, 2, 2, 6]), (3840, [2, 2, 3, 5]), (720, [2, 2, 4, 4]), (3800, [2, 3, 3, 4]), (-3360, [2, 10]), (160, [3, 3, 3, 3]), (1120, [3, 9]), (2880, [4, 8]), (2880, [5, 7]), (1440, [6, 6])]

def node83Piece6Output_sector0 : RawPoly ℕ := [node83Piece6Output_sector0_chunk0, node83Piece6Output_sector0_chunk1].flatten

def node83Piece6Output : SectorVector := [(-1, node83Piece6Output_sector0)]

def node83Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node83Piece6UnitInput_sector0 : RawPoly ℕ := [node83Piece6UnitInput_sector0_chunk0].flatten

def node83Piece6UnitInput : SectorVector := [(-1, node83Piece6UnitInput_sector0)]

def node83Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 2, 3, 5]), (-24, [0, 1, 2, 2, 3, 4]), (-12, [0, 1, 2, 3, 3, 3]), (-72, [0, 1, 2, 9]), (-48, [0, 1, 3, 8]), (-12, [0, 2, 2, 2, 3, 3]), (-72, [0, 2, 2, 8]), (-102, [0, 2, 3, 7]), (-72, [0, 2, 4, 6]), (-36, [0, 2, 5, 5]), (-48, [0, 3, 3, 6]), (-48, [0, 3, 4, 5]), (-144, [0, 12]), (4, [1, 1, 1, 2, 3, 4]), (12, [1, 1, 2, 2, 3, 3]), (36, [1, 1, 2, 8]), (24, [1, 1, 3, 7]), (4, [1, 2, 2, 2, 2, 3]), (72, [1, 2, 2, 7]), (196, [1, 2, 3, 6]), (72, [1, 2, 4, 5]), (48, [1, 3, 3, 5]), (24, [1, 3, 4, 4]), (144, [1, 11])]

def node83Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 2, 6]), (192, [2, 2, 3, 5]), (36, [2, 2, 4, 4]), (190, [2, 3, 3, 4]), (-168, [2, 10]), (8, [3, 3, 3, 3]), (56, [3, 9]), (144, [4, 8]), (144, [5, 7]), (72, [6, 6])]

def node83Piece6UnitOutput_sector0 : RawPoly ℕ := [node83Piece6UnitOutput_sector0_chunk0, node83Piece6UnitOutput_sector0_chunk1].flatten

def node83Piece6UnitOutput : SectorVector := [(-1, node83Piece6UnitOutput_sector0)]

theorem node83Piece6_check : neutralDirectS JR (-4) node83Piece6UnitInput = node83Piece6UnitOutput := by decide +kernel

theorem node83Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece6Input) = evaluate node83Piece6Output :=
  mode_of_scaled _ _ (20) node83Piece6UnitInput node83Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece6_check)

def node83Piece7Input_sector0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1])]

def node83Piece7Input : SectorVector := [(1, node83Piece7Input_sector0)]
def node83Piece7Output_sector0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (-4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (-136, [0, 1, 1, 1, 1, 1, 1, 6]), (-216, [0, 1, 1, 1, 1, 1, 2, 5]), (-226, [0, 1, 1, 1, 1, 1, 3, 4]), (-60, [0, 1, 1, 1, 1, 2, 2, 4]), (-60, [0, 1, 1, 1, 1, 2, 3, 3]), (-270, [0, 1, 1, 1, 1, 8]), (-240, [0, 1, 1, 1, 2, 7]), (-240, [0, 1, 1, 1, 3, 6]), (-240, [0, 1, 1, 1, 4, 5]), (-240, [0, 1, 1, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-192, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (-96, [1, 1, 1, 1, 1, 2, 2, 3]), (-816, [1, 1, 1, 1, 1, 7]), (-960, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (-480, [1, 1, 1, 1, 4, 4]), (-1920, [1, 1, 1, 9])]

def node83Piece7Output : SectorVector := [(1, node83Piece7Output_sector0)]

def node83Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node83Piece7UnitInput_sector0 : RawPoly ℕ := [node83Piece7UnitInput_sector0_chunk0].flatten

def node83Piece7UnitInput : SectorVector := [(1, node83Piece7UnitInput_sector0)]

def node83Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (136, [0, 1, 1, 1, 1, 1, 1, 6]), (216, [0, 1, 1, 1, 1, 1, 2, 5]), (226, [0, 1, 1, 1, 1, 1, 3, 4]), (60, [0, 1, 1, 1, 1, 2, 2, 4]), (60, [0, 1, 1, 1, 1, 2, 3, 3]), (270, [0, 1, 1, 1, 1, 8]), (240, [0, 1, 1, 1, 2, 7]), (240, [0, 1, 1, 1, 3, 6]), (240, [0, 1, 1, 1, 4, 5]), (240, [0, 1, 1, 10]), (96, [1, 1, 1, 1, 1, 1, 1, 5]), (192, [1, 1, 1, 1, 1, 1, 2, 4]), (96, [1, 1, 1, 1, 1, 1, 3, 3]), (96, [1, 1, 1, 1, 1, 2, 2, 3]), (816, [1, 1, 1, 1, 1, 7]), (960, [1, 1, 1, 1, 2, 6]), (960, [1, 1, 1, 1, 3, 5]), (480, [1, 1, 1, 1, 4, 4]), (1920, [1, 1, 1, 9])]

def node83Piece7UnitOutput_sector0 : RawPoly ℕ := [node83Piece7UnitOutput_sector0_chunk0].flatten

def node83Piece7UnitOutput : SectorVector := [(1, node83Piece7UnitOutput_sector0)]

theorem node83Piece7_check : neutralDirectS JR (-4) node83Piece7UnitInput = node83Piece7UnitOutput := by decide +kernel

theorem node83Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece7Input) = evaluate node83Piece7Output :=
  mode_of_scaled _ _ (-1) node83Piece7UnitInput node83Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece7_check)

def node83Piece8Input_sector0 : RawPoly ℕ := [(-10, [0, 1, 1, 3])]

def node83Piece8Input : SectorVector := [(1, node83Piece8Input_sector0)]
def node83Piece8Output_sector0_chunk0 : RawPoly ℕ := [(-40, [0, 1, 1, 1, 1, 1, 3, 4]), (-120, [0, 1, 1, 1, 1, 2, 3, 3]), (-360, [0, 1, 1, 1, 1, 8]), (-40, [0, 1, 1, 1, 2, 2, 2, 3]), (-720, [0, 1, 1, 1, 2, 7]), (-1720, [0, 1, 1, 1, 3, 6]), (-720, [0, 1, 1, 1, 4, 5]), (-360, [0, 1, 1, 2, 2, 6]), (-2160, [0, 1, 1, 2, 3, 5]), (-360, [0, 1, 1, 2, 4, 4]), (-1900, [0, 1, 1, 3, 3, 4]), (1680, [0, 1, 1, 10]), (-240, [0, 1, 2, 2, 3, 4]), (-240, [0, 1, 2, 3, 3, 3]), (-1440, [0, 1, 2, 9]), (-1800, [0, 1, 3, 8]), (-1440, [0, 1, 4, 7]), (-1440, [0, 1, 5, 6]), (-240, [0, 2, 3, 7]), (-240, [0, 3, 3, 6]), (-240, [0, 3, 4, 5]), (-720, [0, 12]), (-960, [1, 1, 1, 1, 3, 5]), (-1920, [1, 1, 1, 2, 3, 4])]

def node83Piece8Output_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 3, 3, 3]), (-5760, [1, 1, 1, 9]), (-960, [1, 1, 2, 2, 3, 3]), (-5760, [1, 1, 2, 8]), (-8160, [1, 1, 3, 7]), (-5760, [1, 1, 4, 6]), (-2880, [1, 1, 5, 5]), (-3840, [1, 2, 3, 6]), (-3840, [1, 3, 3, 5]), (-1920, [1, 3, 4, 4]), (-11520, [1, 11]), (-1920, [3, 9])]

def node83Piece8Output_sector0 : RawPoly ℕ := [node83Piece8Output_sector0_chunk0, node83Piece8Output_sector0_chunk1].flatten

def node83Piece8Output : SectorVector := [(1, node83Piece8Output_sector0)]

def node83Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node83Piece8UnitInput_sector0 : RawPoly ℕ := [node83Piece8UnitInput_sector0_chunk0].flatten

def node83Piece8UnitInput : SectorVector := [(1, node83Piece8UnitInput_sector0)]

def node83Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 3, 4]), (12, [0, 1, 1, 1, 1, 2, 3, 3]), (36, [0, 1, 1, 1, 1, 8]), (4, [0, 1, 1, 1, 2, 2, 2, 3]), (72, [0, 1, 1, 1, 2, 7]), (172, [0, 1, 1, 1, 3, 6]), (72, [0, 1, 1, 1, 4, 5]), (36, [0, 1, 1, 2, 2, 6]), (216, [0, 1, 1, 2, 3, 5]), (36, [0, 1, 1, 2, 4, 4]), (190, [0, 1, 1, 3, 3, 4]), (-168, [0, 1, 1, 10]), (24, [0, 1, 2, 2, 3, 4]), (24, [0, 1, 2, 3, 3, 3]), (144, [0, 1, 2, 9]), (180, [0, 1, 3, 8]), (144, [0, 1, 4, 7]), (144, [0, 1, 5, 6]), (24, [0, 2, 3, 7]), (24, [0, 3, 3, 6]), (24, [0, 3, 4, 5]), (72, [0, 12]), (96, [1, 1, 1, 1, 3, 5]), (192, [1, 1, 1, 2, 3, 4])]

def node83Piece8UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [1, 1, 1, 3, 3, 3]), (576, [1, 1, 1, 9]), (96, [1, 1, 2, 2, 3, 3]), (576, [1, 1, 2, 8]), (816, [1, 1, 3, 7]), (576, [1, 1, 4, 6]), (288, [1, 1, 5, 5]), (384, [1, 2, 3, 6]), (384, [1, 3, 3, 5]), (192, [1, 3, 4, 4]), (1152, [1, 11]), (192, [3, 9])]

def node83Piece8UnitOutput_sector0 : RawPoly ℕ := [node83Piece8UnitOutput_sector0_chunk0, node83Piece8UnitOutput_sector0_chunk1].flatten

def node83Piece8UnitOutput : SectorVector := [(1, node83Piece8UnitOutput_sector0)]

theorem node83Piece8_check : neutralDirectS JR (-4) node83Piece8UnitInput = node83Piece8UnitOutput := by decide +kernel

theorem node83Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece8Input) = evaluate node83Piece8Output :=
  mode_of_scaled _ _ (-10) node83Piece8UnitInput node83Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece8_check)

def node83Piece9Input_sector0 : RawPoly ℕ := [(-15/2, [0, 1, 2, 2])]

def node83Piece9Input : SectorVector := [(1, node83Piece9Input_sector0)]
def node83Piece9Output_sector0_chunk0 : RawPoly ℕ := [(-30, [0, 1, 1, 1, 1, 2, 2, 4]), (-90, [0, 1, 1, 1, 2, 2, 2, 3]), (-360, [0, 1, 1, 1, 2, 7]), (-30, [0, 1, 1, 2, 2, 2, 2, 2]), (-1380, [0, 1, 1, 2, 2, 6]), (-720, [0, 1, 1, 2, 3, 5]), (-360, [0, 1, 1, 2, 4, 4]), (-720, [0, 1, 1, 10]), (-1260, [0, 1, 2, 2, 2, 5]), (-1695, [0, 1, 2, 2, 3, 4]), (-120, [0, 1, 2, 3, 3, 3]), (-120, [0, 1, 2, 9]), (-720, [0, 1, 3, 8]), (-720, [0, 1, 4, 7]), (-720, [0, 1, 5, 6]), (-90, [0, 2, 2, 2, 2, 4]), (-90, [0, 2, 2, 2, 3, 3]), (-765, [0, 2, 2, 8]), (-720, [0, 2, 3, 7]), (-720, [0, 2, 4, 6]), (-360, [0, 2, 5, 5]), (-720, [0, 12]), (-720, [1, 1, 1, 2, 2, 5]), (-1440, [1, 1, 2, 2, 2, 4])]

def node83Piece9Output_sector0_chunk1 : RawPoly ℕ := [(-720, [1, 1, 2, 2, 3, 3]), (-5760, [1, 1, 2, 8]), (-720, [1, 2, 2, 2, 2, 3]), (-6120, [1, 2, 2, 7]), (-5760, [1, 2, 3, 6]), (-5760, [1, 2, 4, 5]), (-5760, [1, 11]), (-1440, [2, 2, 2, 6]), (-1440, [2, 2, 3, 5]), (-720, [2, 2, 4, 4]), (-5760, [2, 10])]

def node83Piece9Output_sector0 : RawPoly ℕ := [node83Piece9Output_sector0_chunk0, node83Piece9Output_sector0_chunk1].flatten

def node83Piece9Output : SectorVector := [(1, node83Piece9Output_sector0)]

def node83Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node83Piece9UnitInput_sector0 : RawPoly ℕ := [node83Piece9UnitInput_sector0_chunk0].flatten

def node83Piece9UnitInput : SectorVector := [(1, node83Piece9UnitInput_sector0)]

def node83Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 4]), (12, [0, 1, 1, 1, 2, 2, 2, 3]), (48, [0, 1, 1, 1, 2, 7]), (4, [0, 1, 1, 2, 2, 2, 2, 2]), (184, [0, 1, 1, 2, 2, 6]), (96, [0, 1, 1, 2, 3, 5]), (48, [0, 1, 1, 2, 4, 4]), (96, [0, 1, 1, 10]), (168, [0, 1, 2, 2, 2, 5]), (226, [0, 1, 2, 2, 3, 4]), (16, [0, 1, 2, 3, 3, 3]), (16, [0, 1, 2, 9]), (96, [0, 1, 3, 8]), (96, [0, 1, 4, 7]), (96, [0, 1, 5, 6]), (12, [0, 2, 2, 2, 2, 4]), (12, [0, 2, 2, 2, 3, 3]), (102, [0, 2, 2, 8]), (96, [0, 2, 3, 7]), (96, [0, 2, 4, 6]), (48, [0, 2, 5, 5]), (96, [0, 12]), (96, [1, 1, 1, 2, 2, 5]), (192, [1, 1, 2, 2, 2, 4])]

def node83Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [1, 1, 2, 2, 3, 3]), (768, [1, 1, 2, 8]), (96, [1, 2, 2, 2, 2, 3]), (816, [1, 2, 2, 7]), (768, [1, 2, 3, 6]), (768, [1, 2, 4, 5]), (768, [1, 11]), (192, [2, 2, 2, 6]), (192, [2, 2, 3, 5]), (96, [2, 2, 4, 4]), (768, [2, 10])]

def node83Piece9UnitOutput_sector0 : RawPoly ℕ := [node83Piece9UnitOutput_sector0_chunk0, node83Piece9UnitOutput_sector0_chunk1].flatten

def node83Piece9UnitOutput : SectorVector := [(1, node83Piece9UnitOutput_sector0)]

theorem node83Piece9_check : neutralDirectS JR (-4) node83Piece9UnitInput = node83Piece9UnitOutput := by decide +kernel

theorem node83Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece9Input) = evaluate node83Piece9Output :=
  mode_of_scaled _ _ (-15/2) node83Piece9UnitInput node83Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece9_check)

def node83Piece10Input_sector0 : RawPoly ℕ := [(-6, [0, 5])]

def node83Piece10Input : SectorVector := [(1, node83Piece10Input_sector0)]
def node83Piece10Output_sector0_chunk0 : RawPoly ℕ := [(-24, [0, 1, 1, 1, 4, 5]), (-72, [0, 1, 1, 2, 3, 5]), (-360, [0, 1, 1, 10]), (-24, [0, 1, 2, 2, 2, 5]), (-720, [0, 1, 2, 9]), (-720, [0, 1, 3, 8]), (-720, [0, 1, 4, 7]), (-1176, [0, 1, 5, 6]), (-360, [0, 2, 2, 8]), (-720, [0, 2, 3, 7]), (-720, [0, 2, 4, 6]), (-936, [0, 2, 5, 5]), (-360, [0, 3, 3, 6]), (-1356, [0, 3, 4, 5]), (-120, [0, 4, 4, 4]), (7620, [0, 12]), (-576, [1, 1, 5, 5]), (-1152, [1, 2, 4, 5]), (-576, [1, 3, 3, 5]), (-5760, [1, 11]), (-576, [2, 2, 3, 5]), (-5760, [2, 10]), (-5760, [3, 9]), (-5760, [4, 8])]

def node83Piece10Output_sector0_chunk1 : RawPoly ℕ := [(-4896, [5, 7]), (-2880, [6, 6])]

def node83Piece10Output_sector0 : RawPoly ℕ := [node83Piece10Output_sector0_chunk0, node83Piece10Output_sector0_chunk1].flatten

def node83Piece10Output : SectorVector := [(1, node83Piece10Output_sector0)]

def node83Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node83Piece10UnitInput_sector0 : RawPoly ℕ := [node83Piece10UnitInput_sector0_chunk0].flatten

def node83Piece10UnitInput : SectorVector := [(1, node83Piece10UnitInput_sector0)]

def node83Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 4, 5]), (12, [0, 1, 1, 2, 3, 5]), (60, [0, 1, 1, 10]), (4, [0, 1, 2, 2, 2, 5]), (120, [0, 1, 2, 9]), (120, [0, 1, 3, 8]), (120, [0, 1, 4, 7]), (196, [0, 1, 5, 6]), (60, [0, 2, 2, 8]), (120, [0, 2, 3, 7]), (120, [0, 2, 4, 6]), (156, [0, 2, 5, 5]), (60, [0, 3, 3, 6]), (226, [0, 3, 4, 5]), (20, [0, 4, 4, 4]), (-1270, [0, 12]), (96, [1, 1, 5, 5]), (192, [1, 2, 4, 5]), (96, [1, 3, 3, 5]), (960, [1, 11]), (96, [2, 2, 3, 5]), (960, [2, 10]), (960, [3, 9]), (960, [4, 8])]

def node83Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(816, [5, 7]), (480, [6, 6])]

def node83Piece10UnitOutput_sector0 : RawPoly ℕ := [node83Piece10UnitOutput_sector0_chunk0, node83Piece10UnitOutput_sector0_chunk1].flatten

def node83Piece10UnitOutput : SectorVector := [(1, node83Piece10UnitOutput_sector0)]

theorem node83Piece10_check : neutralDirectS JR (-4) node83Piece10UnitInput = node83Piece10UnitOutput := by decide +kernel

theorem node83Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece10Input) = evaluate node83Piece10Output :=
  mode_of_scaled _ _ (-6) node83Piece10UnitInput node83Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece10_check)

def node83Piece11Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node83Piece11Input : SectorVector := [(1, node83Piece11Input_sector0)]
def node83Piece11Output_sector0_chunk0 : RawPoly ℕ := [(240, [0, 1, 1, 1, 1, 1, 2, 5]), (480, [0, 1, 1, 1, 1, 2, 2, 4]), (240, [0, 1, 1, 1, 1, 2, 3, 3]), (960, [0, 1, 1, 1, 1, 8]), (240, [0, 1, 1, 1, 2, 2, 2, 3]), (2040, [0, 1, 1, 1, 2, 7]), (960, [0, 1, 1, 1, 3, 6]), (960, [0, 1, 1, 1, 4, 5]), (1440, [0, 1, 1, 2, 2, 6]), (1440, [0, 1, 1, 2, 3, 5]), (720, [0, 1, 1, 2, 4, 4]), (2880, [0, 1, 1, 10]), (1440, [0, 1, 2, 9]), (80, [1, 1, 1, 1, 1, 1, 2, 4]), (240, [1, 1, 1, 1, 1, 2, 2, 3]), (480, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (3200, [1, 1, 1, 1, 2, 6]), (960, [1, 1, 1, 1, 3, 5]), (480, [1, 1, 1, 1, 4, 4]), (3840, [1, 1, 1, 2, 2, 5]), (4520, [1, 1, 1, 2, 3, 4]), (160, [1, 1, 1, 3, 3, 3]), (1120, [1, 1, 1, 9])]

def node83Piece11Output_sector0_chunk1 : RawPoly ℕ := [(720, [1, 1, 2, 2, 2, 4]), (720, [1, 1, 2, 2, 3, 3]), (4680, [1, 1, 2, 8]), (2880, [1, 1, 3, 7]), (2880, [1, 1, 4, 6]), (1440, [1, 1, 5, 5]), (1440, [1, 2, 2, 7]), (1440, [1, 2, 3, 6]), (1440, [1, 2, 4, 5]), (2880, [1, 11]), (480, [2, 10])]

def node83Piece11Output_sector0 : RawPoly ℕ := [node83Piece11Output_sector0_chunk0, node83Piece11Output_sector0_chunk1].flatten

def node83Piece11Output : SectorVector := [(1, node83Piece11Output_sector0)]

def node83Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node83Piece11UnitInput_sector0 : RawPoly ℕ := [node83Piece11UnitInput_sector0_chunk0].flatten

def node83Piece11UnitInput : SectorVector := [(1, node83Piece11UnitInput_sector0)]

def node83Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 1, 1, 2, 5]), (24, [0, 1, 1, 1, 1, 2, 2, 4]), (12, [0, 1, 1, 1, 1, 2, 3, 3]), (48, [0, 1, 1, 1, 1, 8]), (12, [0, 1, 1, 1, 2, 2, 2, 3]), (102, [0, 1, 1, 1, 2, 7]), (48, [0, 1, 1, 1, 3, 6]), (48, [0, 1, 1, 1, 4, 5]), (72, [0, 1, 1, 2, 2, 6]), (72, [0, 1, 1, 2, 3, 5]), (36, [0, 1, 1, 2, 4, 4]), (144, [0, 1, 1, 10]), (72, [0, 1, 2, 9]), (4, [1, 1, 1, 1, 1, 1, 2, 4]), (12, [1, 1, 1, 1, 1, 2, 2, 3]), (24, [1, 1, 1, 1, 1, 7]), (4, [1, 1, 1, 1, 2, 2, 2, 2]), (160, [1, 1, 1, 1, 2, 6]), (48, [1, 1, 1, 1, 3, 5]), (24, [1, 1, 1, 1, 4, 4]), (192, [1, 1, 1, 2, 2, 5]), (226, [1, 1, 1, 2, 3, 4]), (8, [1, 1, 1, 3, 3, 3]), (56, [1, 1, 1, 9])]

def node83Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [1, 1, 2, 2, 2, 4]), (36, [1, 1, 2, 2, 3, 3]), (234, [1, 1, 2, 8]), (144, [1, 1, 3, 7]), (144, [1, 1, 4, 6]), (72, [1, 1, 5, 5]), (72, [1, 2, 2, 7]), (72, [1, 2, 3, 6]), (72, [1, 2, 4, 5]), (144, [1, 11]), (24, [2, 10])]

def node83Piece11UnitOutput_sector0 : RawPoly ℕ := [node83Piece11UnitOutput_sector0_chunk0, node83Piece11UnitOutput_sector0_chunk1].flatten

def node83Piece11UnitOutput : SectorVector := [(1, node83Piece11UnitOutput_sector0)]

theorem node83Piece11_check : neutralDirectS JR (-4) node83Piece11UnitInput = node83Piece11UnitOutput := by decide +kernel

theorem node83Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece11Input) = evaluate node83Piece11Output :=
  mode_of_scaled _ _ (20) node83Piece11UnitInput node83Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece11_check)

def node83Piece12Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node83Piece12Input : SectorVector := [(1, node83Piece12Input_sector0)]
def node83Piece12Output_sector0_chunk0 : RawPoly ℕ := [(360, [0, 1, 1, 1, 4, 5]), (720, [0, 1, 1, 2, 4, 4]), (360, [0, 1, 1, 3, 3, 4]), (2880, [0, 1, 1, 10]), (360, [0, 1, 2, 2, 3, 4]), (2880, [0, 1, 2, 9]), (2880, [0, 1, 3, 8]), (3060, [0, 1, 4, 7]), (2880, [0, 1, 5, 6]), (720, [0, 2, 4, 6]), (720, [0, 3, 4, 5]), (360, [0, 4, 4, 4]), (2880, [0, 12]), (120, [1, 1, 1, 1, 4, 4]), (360, [1, 1, 1, 2, 3, 4]), (1440, [1, 1, 1, 9]), (120, [1, 1, 2, 2, 2, 4]), (2880, [1, 1, 2, 8]), (2880, [1, 1, 3, 7]), (5520, [1, 1, 4, 6]), (1440, [1, 1, 5, 5]), (1440, [1, 2, 2, 7]), (2880, [1, 2, 3, 6]), (6480, [1, 2, 4, 5])]

def node83Piece12Output_sector0_chunk1 : RawPoly ℕ := [(1440, [1, 3, 3, 5]), (5340, [1, 3, 4, 4]), (-18000, [1, 11]), (360, [2, 2, 4, 4]), (360, [2, 3, 3, 4]), (2880, [2, 10]), (2880, [3, 9]), (3060, [4, 8]), (2880, [5, 7]), (1440, [6, 6])]

def node83Piece12Output_sector0 : RawPoly ℕ := [node83Piece12Output_sector0_chunk0, node83Piece12Output_sector0_chunk1].flatten

def node83Piece12Output : SectorVector := [(1, node83Piece12Output_sector0)]

def node83Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node83Piece12UnitInput_sector0 : RawPoly ℕ := [node83Piece12UnitInput_sector0_chunk0].flatten

def node83Piece12UnitInput : SectorVector := [(1, node83Piece12UnitInput_sector0)]

def node83Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 4, 5]), (24, [0, 1, 1, 2, 4, 4]), (12, [0, 1, 1, 3, 3, 4]), (96, [0, 1, 1, 10]), (12, [0, 1, 2, 2, 3, 4]), (96, [0, 1, 2, 9]), (96, [0, 1, 3, 8]), (102, [0, 1, 4, 7]), (96, [0, 1, 5, 6]), (24, [0, 2, 4, 6]), (24, [0, 3, 4, 5]), (12, [0, 4, 4, 4]), (96, [0, 12]), (4, [1, 1, 1, 1, 4, 4]), (12, [1, 1, 1, 2, 3, 4]), (48, [1, 1, 1, 9]), (4, [1, 1, 2, 2, 2, 4]), (96, [1, 1, 2, 8]), (96, [1, 1, 3, 7]), (184, [1, 1, 4, 6]), (48, [1, 1, 5, 5]), (48, [1, 2, 2, 7]), (96, [1, 2, 3, 6]), (216, [1, 2, 4, 5])]

def node83Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(48, [1, 3, 3, 5]), (178, [1, 3, 4, 4]), (-600, [1, 11]), (12, [2, 2, 4, 4]), (12, [2, 3, 3, 4]), (96, [2, 10]), (96, [3, 9]), (102, [4, 8]), (96, [5, 7]), (48, [6, 6])]

def node83Piece12UnitOutput_sector0 : RawPoly ℕ := [node83Piece12UnitOutput_sector0_chunk0, node83Piece12UnitOutput_sector0_chunk1].flatten

def node83Piece12UnitOutput : SectorVector := [(1, node83Piece12UnitOutput_sector0)]

theorem node83Piece12_check : neutralDirectS JR (-4) node83Piece12UnitInput = node83Piece12UnitOutput := by decide +kernel

theorem node83Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece12Input) = evaluate node83Piece12Output :=
  mode_of_scaled _ _ (30) node83Piece12UnitInput node83Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece12_check)

def node83Piece13Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node83Piece13Input : SectorVector := [(1, node83Piece13Input_sector0)]
def node83Piece13Output_sector0_chunk0 : RawPoly ℕ := [(240, [0, 1, 1, 2, 3, 5]), (480, [0, 1, 2, 2, 3, 4]), (240, [0, 1, 2, 3, 3, 3]), (1440, [0, 1, 2, 9]), (960, [0, 1, 3, 8]), (240, [0, 2, 2, 2, 3, 3]), (1440, [0, 2, 2, 8]), (2040, [0, 2, 3, 7]), (1440, [0, 2, 4, 6]), (720, [0, 2, 5, 5]), (960, [0, 3, 3, 6]), (960, [0, 3, 4, 5]), (2880, [0, 12]), (80, [1, 1, 1, 2, 3, 4]), (240, [1, 1, 2, 2, 3, 3]), (720, [1, 1, 2, 8]), (480, [1, 1, 3, 7]), (80, [1, 2, 2, 2, 2, 3]), (1440, [1, 2, 2, 7]), (3920, [1, 2, 3, 6]), (1440, [1, 2, 4, 5]), (960, [1, 3, 3, 5]), (480, [1, 3, 4, 4]), (2880, [1, 11])]

def node83Piece13Output_sector0_chunk1 : RawPoly ℕ := [(720, [2, 2, 2, 6]), (3840, [2, 2, 3, 5]), (720, [2, 2, 4, 4]), (3800, [2, 3, 3, 4]), (-3360, [2, 10]), (160, [3, 3, 3, 3]), (1120, [3, 9]), (2880, [4, 8]), (2880, [5, 7]), (1440, [6, 6])]

def node83Piece13Output_sector0 : RawPoly ℕ := [node83Piece13Output_sector0_chunk0, node83Piece13Output_sector0_chunk1].flatten

def node83Piece13Output : SectorVector := [(1, node83Piece13Output_sector0)]

def node83Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node83Piece13UnitInput_sector0 : RawPoly ℕ := [node83Piece13UnitInput_sector0_chunk0].flatten

def node83Piece13UnitInput : SectorVector := [(1, node83Piece13UnitInput_sector0)]

def node83Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 2, 3, 5]), (24, [0, 1, 2, 2, 3, 4]), (12, [0, 1, 2, 3, 3, 3]), (72, [0, 1, 2, 9]), (48, [0, 1, 3, 8]), (12, [0, 2, 2, 2, 3, 3]), (72, [0, 2, 2, 8]), (102, [0, 2, 3, 7]), (72, [0, 2, 4, 6]), (36, [0, 2, 5, 5]), (48, [0, 3, 3, 6]), (48, [0, 3, 4, 5]), (144, [0, 12]), (4, [1, 1, 1, 2, 3, 4]), (12, [1, 1, 2, 2, 3, 3]), (36, [1, 1, 2, 8]), (24, [1, 1, 3, 7]), (4, [1, 2, 2, 2, 2, 3]), (72, [1, 2, 2, 7]), (196, [1, 2, 3, 6]), (72, [1, 2, 4, 5]), (48, [1, 3, 3, 5]), (24, [1, 3, 4, 4]), (144, [1, 11])]

def node83Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 2, 6]), (192, [2, 2, 3, 5]), (36, [2, 2, 4, 4]), (190, [2, 3, 3, 4]), (-168, [2, 10]), (8, [3, 3, 3, 3]), (56, [3, 9]), (144, [4, 8]), (144, [5, 7]), (72, [6, 6])]

def node83Piece13UnitOutput_sector0 : RawPoly ℕ := [node83Piece13UnitOutput_sector0_chunk0, node83Piece13UnitOutput_sector0_chunk1].flatten

def node83Piece13UnitOutput : SectorVector := [(1, node83Piece13UnitOutput_sector0)]

theorem node83Piece13_check : neutralDirectS JR (-4) node83Piece13UnitInput = node83Piece13UnitOutput := by decide +kernel

theorem node83Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node83Piece13Input) = evaluate node83Piece13Output :=
  mode_of_scaled _ _ (20) node83Piece13UnitInput node83Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node83Piece13_check)

def node83Pieces : List (SectorVector × SectorVector) := [(node83Piece0Input, node83Piece0Output), (node83Piece1Input, node83Piece1Output), (node83Piece2Input, node83Piece2Output), (node83Piece3Input, node83Piece3Output), (node83Piece4Input, node83Piece4Output), (node83Piece5Input, node83Piece5Output), (node83Piece6Input, node83Piece6Output), (node83Piece7Input, node83Piece7Output), (node83Piece8Input, node83Piece8Output), (node83Piece9Input, node83Piece9Output), (node83Piece10Input, node83Piece10Output), (node83Piece11Input, node83Piece11Output), (node83Piece12Input, node83Piece12Output), (node83Piece13Input, node83Piece13Output)]

theorem node83Pieces_input : VectorCertificate (node83Pieces.flatMap Prod.fst) nineData := by decide +kernel

theorem node83Pieces_each : ∀ p ∈ node83Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-4) (evaluate p.1) = evaluate p.2 := by
  simp only [node83Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node83Piece0_value, node83Piece1_value, node83Piece2_value, node83Piece3_value, node83Piece4_value, node83Piece5_value, node83Piece6_value, node83Piece7_value, node83Piece8_value, node83Piece9_value, node83Piece10_value, node83Piece11_value, node83Piece12_value, node83Piece13_value, by simp⟩
end VOA.Classification.COne.OrbC2h
