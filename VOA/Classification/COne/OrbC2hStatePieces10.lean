import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hNine
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

def node10Piece0Input_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node10Piece0Input : SectorVector := [(-1, node10Piece0Input_sector0)]
def node10Piece0Output_sector0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (220, [0, 1, 1, 1, 1, 1, 2, 3]), (20, [0, 1, 1, 1, 1, 2, 2, 2]), (440, [0, 1, 1, 1, 1, 6]), (240, [0, 1, 1, 1, 2, 5]), (240, [0, 1, 1, 1, 3, 4]), (240, [0, 1, 1, 8]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-96, [1, 1, 1, 1, 1, 1, 2, 2]), (-1008, [1, 1, 1, 1, 1, 5]), (-960, [1, 1, 1, 1, 2, 4]), (-480, [1, 1, 1, 1, 3, 3]), (-1920, [1, 1, 1, 7])]

def node10Piece0Output : SectorVector := [(-1, node10Piece0Output_sector0)]

def node10Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node10Piece0UnitInput_sector0 : RawPoly ℕ := [node10Piece0UnitInput_sector0_chunk0].flatten

def node10Piece0UnitInput : SectorVector := [(-1, node10Piece0UnitInput_sector0)]

def node10Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (220, [0, 1, 1, 1, 1, 1, 2, 3]), (20, [0, 1, 1, 1, 1, 2, 2, 2]), (440, [0, 1, 1, 1, 1, 6]), (240, [0, 1, 1, 1, 2, 5]), (240, [0, 1, 1, 1, 3, 4]), (240, [0, 1, 1, 8]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-96, [1, 1, 1, 1, 1, 1, 2, 2]), (-1008, [1, 1, 1, 1, 1, 5]), (-960, [1, 1, 1, 1, 2, 4]), (-480, [1, 1, 1, 1, 3, 3]), (-1920, [1, 1, 1, 7])]

def node10Piece0UnitOutput_sector0 : RawPoly ℕ := [node10Piece0UnitOutput_sector0_chunk0].flatten

def node10Piece0UnitOutput : SectorVector := [(-1, node10Piece0UnitOutput_sector0)]

theorem node10Piece0_check : VectorCertificate (neutralBoundS JR (-2) node10Piece0UnitInput) node10Piece0UnitOutput := by decide +kernel

theorem node10Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece0Input) = evaluate node10Piece0Output :=
  mode_of_scaled _ _ (1) node10Piece0UnitInput node10Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece0_check)

def node10Piece1Input_sector0 : RawPoly ℕ := [(10, [0, 1, 1, 3])]

def node10Piece1Input : SectorVector := [(-1, node10Piece1Input_sector0)]
def node10Piece1Output_sector0 : RawPoly ℕ := [(40, [0, 1, 1, 1, 1, 1, 2, 3]), (360, [0, 1, 1, 1, 1, 6]), (720, [0, 1, 1, 1, 2, 5]), (1860, [0, 1, 1, 1, 3, 4]), (360, [0, 1, 1, 2, 2, 4]), (1840, [0, 1, 1, 2, 3, 3]), (-60, [0, 1, 1, 8]), (80, [0, 1, 2, 2, 2, 3]), (1440, [0, 1, 2, 7]), (2480, [0, 1, 3, 6]), (1440, [0, 1, 4, 5]), (240, [0, 2, 3, 5]), (240, [0, 3, 3, 4]), (720, [0, 10]), (-960, [1, 1, 1, 1, 3, 3]), (-960, [1, 1, 1, 2, 2, 3]), (-5760, [1, 1, 1, 7]), (-5760, [1, 1, 2, 6]), (-10080, [1, 1, 3, 5]), (-2880, [1, 1, 4, 4]), (-3840, [1, 2, 3, 4]), (-1920, [1, 3, 3, 3]), (-11520, [1, 9]), (-1920, [3, 7])]

def node10Piece1Output : SectorVector := [(-1, node10Piece1Output_sector0)]

def node10Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node10Piece1UnitInput_sector0 : RawPoly ℕ := [node10Piece1UnitInput_sector0_chunk0].flatten

def node10Piece1UnitInput : SectorVector := [(-1, node10Piece1UnitInput_sector0)]

def node10Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 2, 3]), (36, [0, 1, 1, 1, 1, 6]), (72, [0, 1, 1, 1, 2, 5]), (186, [0, 1, 1, 1, 3, 4]), (36, [0, 1, 1, 2, 2, 4]), (184, [0, 1, 1, 2, 3, 3]), (-6, [0, 1, 1, 8]), (8, [0, 1, 2, 2, 2, 3]), (144, [0, 1, 2, 7]), (248, [0, 1, 3, 6]), (144, [0, 1, 4, 5]), (24, [0, 2, 3, 5]), (24, [0, 3, 3, 4]), (72, [0, 10]), (-96, [1, 1, 1, 1, 3, 3]), (-96, [1, 1, 1, 2, 2, 3]), (-576, [1, 1, 1, 7]), (-576, [1, 1, 2, 6]), (-1008, [1, 1, 3, 5]), (-288, [1, 1, 4, 4]), (-384, [1, 2, 3, 4]), (-192, [1, 3, 3, 3]), (-1152, [1, 9]), (-192, [3, 7])]

def node10Piece1UnitOutput_sector0 : RawPoly ℕ := [node10Piece1UnitOutput_sector0_chunk0].flatten

def node10Piece1UnitOutput : SectorVector := [(-1, node10Piece1UnitOutput_sector0)]

theorem node10Piece1_check : VectorCertificate (neutralBoundS JR (-2) node10Piece1UnitInput) node10Piece1UnitOutput := by decide +kernel

theorem node10Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece1Input) = evaluate node10Piece1Output :=
  mode_of_scaled _ _ (10) node10Piece1UnitInput node10Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece1_check)

def node10Piece2Input_sector0 : RawPoly ℕ := [(15/2, [0, 1, 2, 2])]

def node10Piece2Input : SectorVector := [(-1, node10Piece2Input_sector0)]
def node10Piece2Output_sector0 : RawPoly ℕ := [(30, [0, 1, 1, 1, 1, 2, 2, 2]), (360, [0, 1, 1, 1, 2, 5]), (1485, [0, 1, 1, 2, 2, 4]), (360, [0, 1, 1, 2, 3, 3]), (720, [0, 1, 1, 8]), (1290, [0, 1, 2, 2, 2, 3]), (1440, [0, 1, 2, 7]), (720, [0, 1, 3, 6]), (720, [0, 1, 4, 5]), (30, [0, 2, 2, 2, 2, 2]), (1020, [0, 2, 2, 6]), (720, [0, 2, 3, 5]), (360, [0, 2, 4, 4]), (720, [0, 10]), (-720, [1, 1, 1, 2, 2, 3]), (-720, [1, 1, 2, 2, 2, 2]), (-5760, [1, 1, 2, 6]), (-7560, [1, 2, 2, 5]), (-5760, [1, 2, 3, 4]), (-5760, [1, 9]), (-1440, [2, 2, 2, 4]), (-720, [2, 2, 3, 3]), (-5760, [2, 8])]

def node10Piece2Output : SectorVector := [(-1, node10Piece2Output_sector0)]

def node10Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node10Piece2UnitInput_sector0 : RawPoly ℕ := [node10Piece2UnitInput_sector0_chunk0].flatten

def node10Piece2UnitInput : SectorVector := [(-1, node10Piece2UnitInput_sector0)]

def node10Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 2]), (48, [0, 1, 1, 1, 2, 5]), (198, [0, 1, 1, 2, 2, 4]), (48, [0, 1, 1, 2, 3, 3]), (96, [0, 1, 1, 8]), (172, [0, 1, 2, 2, 2, 3]), (192, [0, 1, 2, 7]), (96, [0, 1, 3, 6]), (96, [0, 1, 4, 5]), (4, [0, 2, 2, 2, 2, 2]), (136, [0, 2, 2, 6]), (96, [0, 2, 3, 5]), (48, [0, 2, 4, 4]), (96, [0, 10]), (-96, [1, 1, 1, 2, 2, 3]), (-96, [1, 1, 2, 2, 2, 2]), (-768, [1, 1, 2, 6]), (-1008, [1, 2, 2, 5]), (-768, [1, 2, 3, 4]), (-768, [1, 9]), (-192, [2, 2, 2, 4]), (-96, [2, 2, 3, 3]), (-768, [2, 8])]

def node10Piece2UnitOutput_sector0 : RawPoly ℕ := [node10Piece2UnitOutput_sector0_chunk0].flatten

def node10Piece2UnitOutput : SectorVector := [(-1, node10Piece2UnitOutput_sector0)]

theorem node10Piece2_check : VectorCertificate (neutralBoundS JR (-2) node10Piece2UnitInput) node10Piece2UnitOutput := by decide +kernel

theorem node10Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece2Input) = evaluate node10Piece2Output :=
  mode_of_scaled _ _ (15/2) node10Piece2UnitInput node10Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece2_check)

def node10Piece3Input_sector0 : RawPoly ℕ := [(6, [0, 5])]

def node10Piece3Input : SectorVector := [(-1, node10Piece3Input_sector0)]
def node10Piece3Output_sector0 : RawPoly ℕ := [(24, [0, 1, 1, 1, 2, 5]), (360, [0, 1, 1, 8]), (720, [0, 1, 2, 7]), (720, [0, 1, 3, 6]), (1260, [0, 1, 4, 5]), (360, [0, 2, 2, 6]), (1320, [0, 2, 3, 5]), (360, [0, 2, 4, 4]), (360, [0, 3, 3, 4]), (-5400, [0, 10]), (-576, [1, 1, 3, 5]), (-576, [1, 2, 2, 5]), (-5760, [1, 9]), (-5760, [2, 8]), (-5760, [3, 7]), (-5760, [4, 6]), (-3168, [5, 5])]

def node10Piece3Output : SectorVector := [(-1, node10Piece3Output_sector0)]

def node10Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node10Piece3UnitInput_sector0 : RawPoly ℕ := [node10Piece3UnitInput_sector0_chunk0].flatten

def node10Piece3UnitInput : SectorVector := [(-1, node10Piece3UnitInput_sector0)]

def node10Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 2, 5]), (60, [0, 1, 1, 8]), (120, [0, 1, 2, 7]), (120, [0, 1, 3, 6]), (210, [0, 1, 4, 5]), (60, [0, 2, 2, 6]), (220, [0, 2, 3, 5]), (60, [0, 2, 4, 4]), (60, [0, 3, 3, 4]), (-900, [0, 10]), (-96, [1, 1, 3, 5]), (-96, [1, 2, 2, 5]), (-960, [1, 9]), (-960, [2, 8]), (-960, [3, 7]), (-960, [4, 6]), (-528, [5, 5])]

def node10Piece3UnitOutput_sector0 : RawPoly ℕ := [node10Piece3UnitOutput_sector0_chunk0].flatten

def node10Piece3UnitOutput : SectorVector := [(-1, node10Piece3UnitOutput_sector0)]

theorem node10Piece3_check : VectorCertificate (neutralBoundS JR (-2) node10Piece3UnitInput) node10Piece3UnitOutput := by decide +kernel

theorem node10Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece3Input) = evaluate node10Piece3Output :=
  mode_of_scaled _ _ (6) node10Piece3UnitInput node10Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece3_check)

def node10Piece4Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node10Piece4Input : SectorVector := [(-1, node10Piece4Input_sector0)]
def node10Piece4Output_sector0 : RawPoly ℕ := [(-240, [0, 1, 1, 1, 1, 1, 2, 3]), (-240, [0, 1, 1, 1, 1, 2, 2, 2]), (-960, [0, 1, 1, 1, 1, 6]), (-2520, [0, 1, 1, 1, 2, 5]), (-960, [0, 1, 1, 1, 3, 4]), (-1440, [0, 1, 1, 2, 2, 4]), (-720, [0, 1, 1, 2, 3, 3]), (-2880, [0, 1, 1, 8]), (-1440, [0, 1, 2, 7]), (80, [1, 1, 1, 1, 1, 1, 2, 2]), (480, [1, 1, 1, 1, 1, 5]), (3480, [1, 1, 1, 1, 2, 4]), (480, [1, 1, 1, 1, 3, 3]), (3920, [1, 1, 1, 2, 2, 3]), (2880, [1, 1, 1, 7]), (240, [1, 1, 2, 2, 2, 2]), (6720, [1, 1, 2, 6]), (2880, [1, 1, 3, 5]), (1440, [1, 1, 4, 4]), (1440, [1, 2, 2, 5]), (1440, [1, 2, 3, 4]), (2880, [1, 9]), (480, [2, 8])]

def node10Piece4Output : SectorVector := [(-1, node10Piece4Output_sector0)]

def node10Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node10Piece4UnitInput_sector0 : RawPoly ℕ := [node10Piece4UnitInput_sector0_chunk0].flatten

def node10Piece4UnitInput : SectorVector := [(-1, node10Piece4UnitInput_sector0)]

def node10Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 1, 1, 2, 3]), (-12, [0, 1, 1, 1, 1, 2, 2, 2]), (-48, [0, 1, 1, 1, 1, 6]), (-126, [0, 1, 1, 1, 2, 5]), (-48, [0, 1, 1, 1, 3, 4]), (-72, [0, 1, 1, 2, 2, 4]), (-36, [0, 1, 1, 2, 3, 3]), (-144, [0, 1, 1, 8]), (-72, [0, 1, 2, 7]), (4, [1, 1, 1, 1, 1, 1, 2, 2]), (24, [1, 1, 1, 1, 1, 5]), (174, [1, 1, 1, 1, 2, 4]), (24, [1, 1, 1, 1, 3, 3]), (196, [1, 1, 1, 2, 2, 3]), (144, [1, 1, 1, 7]), (12, [1, 1, 2, 2, 2, 2]), (336, [1, 1, 2, 6]), (144, [1, 1, 3, 5]), (72, [1, 1, 4, 4]), (72, [1, 2, 2, 5]), (72, [1, 2, 3, 4]), (144, [1, 9]), (24, [2, 8])]

def node10Piece4UnitOutput_sector0 : RawPoly ℕ := [node10Piece4UnitOutput_sector0_chunk0].flatten

def node10Piece4UnitOutput : SectorVector := [(-1, node10Piece4UnitOutput_sector0)]

theorem node10Piece4_check : VectorCertificate (neutralBoundS JR (-2) node10Piece4UnitInput) node10Piece4UnitOutput := by decide +kernel

theorem node10Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece4Input) = evaluate node10Piece4Output :=
  mode_of_scaled _ _ (20) node10Piece4UnitInput node10Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece4_check)

def node10Piece5Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node10Piece5Input : SectorVector := [(-1, node10Piece5Input_sector0)]
def node10Piece5Output_sector0 : RawPoly ℕ := [(-360, [0, 1, 1, 1, 3, 4]), (-360, [0, 1, 1, 2, 2, 4]), (-2880, [0, 1, 1, 8]), (-2880, [0, 1, 2, 7]), (-2880, [0, 1, 3, 6]), (-3780, [0, 1, 4, 5]), (-720, [0, 2, 4, 4]), (-360, [0, 3, 3, 4]), (-2880, [0, 10]), (120, [1, 1, 1, 1, 2, 4]), (1440, [1, 1, 1, 7]), (2880, [1, 1, 2, 6]), (2880, [1, 1, 3, 5]), (4500, [1, 1, 4, 4]), (1440, [1, 2, 2, 5]), (6600, [1, 2, 3, 4]), (480, [1, 3, 3, 3]), (-10320, [1, 9]), (120, [2, 2, 2, 4]), (2880, [2, 8]), (2880, [3, 7]), (4080, [4, 6]), (1440, [5, 5])]

def node10Piece5Output : SectorVector := [(-1, node10Piece5Output_sector0)]

def node10Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node10Piece5UnitInput_sector0 : RawPoly ℕ := [node10Piece5UnitInput_sector0_chunk0].flatten

def node10Piece5UnitInput : SectorVector := [(-1, node10Piece5UnitInput_sector0)]

def node10Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 3, 4]), (-12, [0, 1, 1, 2, 2, 4]), (-96, [0, 1, 1, 8]), (-96, [0, 1, 2, 7]), (-96, [0, 1, 3, 6]), (-126, [0, 1, 4, 5]), (-24, [0, 2, 4, 4]), (-12, [0, 3, 3, 4]), (-96, [0, 10]), (4, [1, 1, 1, 1, 2, 4]), (48, [1, 1, 1, 7]), (96, [1, 1, 2, 6]), (96, [1, 1, 3, 5]), (150, [1, 1, 4, 4]), (48, [1, 2, 2, 5]), (220, [1, 2, 3, 4]), (16, [1, 3, 3, 3]), (-344, [1, 9]), (4, [2, 2, 2, 4]), (96, [2, 8]), (96, [3, 7]), (136, [4, 6]), (48, [5, 5])]

def node10Piece5UnitOutput_sector0 : RawPoly ℕ := [node10Piece5UnitOutput_sector0_chunk0].flatten

def node10Piece5UnitOutput : SectorVector := [(-1, node10Piece5UnitOutput_sector0)]

theorem node10Piece5_check : VectorCertificate (neutralBoundS JR (-2) node10Piece5UnitInput) node10Piece5UnitOutput := by decide +kernel

theorem node10Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece5Input) = evaluate node10Piece5Output :=
  mode_of_scaled _ _ (30) node10Piece5UnitInput node10Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece5_check)

def node10Piece6Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node10Piece6Input : SectorVector := [(-1, node10Piece6Input_sector0)]
def node10Piece6Output_sector0 : RawPoly ℕ := [(-240, [0, 1, 1, 2, 3, 3]), (-240, [0, 1, 2, 2, 2, 3]), (-1440, [0, 1, 2, 7]), (-960, [0, 1, 3, 6]), (-1440, [0, 2, 2, 6]), (-2520, [0, 2, 3, 5]), (-720, [0, 2, 4, 4]), (-960, [0, 3, 3, 4]), (-2880, [0, 10]), (80, [1, 1, 1, 2, 2, 3]), (720, [1, 1, 2, 6]), (480, [1, 1, 3, 5]), (1440, [1, 2, 2, 5]), (4200, [1, 2, 3, 4]), (480, [1, 3, 3, 3]), (2880, [1, 9]), (720, [2, 2, 2, 4]), (3200, [2, 2, 3, 3]), (-120, [2, 8]), (2880, [3, 7]), (2880, [4, 6]), (1440, [5, 5])]

def node10Piece6Output : SectorVector := [(-1, node10Piece6Output_sector0)]

def node10Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node10Piece6UnitInput_sector0 : RawPoly ℕ := [node10Piece6UnitInput_sector0_chunk0].flatten

def node10Piece6UnitInput : SectorVector := [(-1, node10Piece6UnitInput_sector0)]

def node10Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 2, 3, 3]), (-12, [0, 1, 2, 2, 2, 3]), (-72, [0, 1, 2, 7]), (-48, [0, 1, 3, 6]), (-72, [0, 2, 2, 6]), (-126, [0, 2, 3, 5]), (-36, [0, 2, 4, 4]), (-48, [0, 3, 3, 4]), (-144, [0, 10]), (4, [1, 1, 1, 2, 2, 3]), (36, [1, 1, 2, 6]), (24, [1, 1, 3, 5]), (72, [1, 2, 2, 5]), (210, [1, 2, 3, 4]), (24, [1, 3, 3, 3]), (144, [1, 9]), (36, [2, 2, 2, 4]), (160, [2, 2, 3, 3]), (-6, [2, 8]), (144, [3, 7]), (144, [4, 6]), (72, [5, 5])]

def node10Piece6UnitOutput_sector0 : RawPoly ℕ := [node10Piece6UnitOutput_sector0_chunk0].flatten

def node10Piece6UnitOutput : SectorVector := [(-1, node10Piece6UnitOutput_sector0)]

theorem node10Piece6_check : VectorCertificate (neutralBoundS JR (-2) node10Piece6UnitInput) node10Piece6UnitOutput := by decide +kernel

theorem node10Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece6Input) = evaluate node10Piece6Output :=
  mode_of_scaled _ _ (20) node10Piece6UnitInput node10Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece6_check)

def node10Piece7Input_sector0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1])]

def node10Piece7Input : SectorVector := [(1, node10Piece7Input_sector0)]
def node10Piece7Output_sector0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (-150, [0, 1, 1, 1, 1, 1, 1, 4]), (-220, [0, 1, 1, 1, 1, 1, 2, 3]), (-20, [0, 1, 1, 1, 1, 2, 2, 2]), (-440, [0, 1, 1, 1, 1, 6]), (-240, [0, 1, 1, 1, 2, 5]), (-240, [0, 1, 1, 1, 3, 4]), (-240, [0, 1, 1, 8]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-96, [1, 1, 1, 1, 1, 1, 2, 2]), (-1008, [1, 1, 1, 1, 1, 5]), (-960, [1, 1, 1, 1, 2, 4]), (-480, [1, 1, 1, 1, 3, 3]), (-1920, [1, 1, 1, 7])]

def node10Piece7Output : SectorVector := [(1, node10Piece7Output_sector0)]

def node10Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node10Piece7UnitInput_sector0 : RawPoly ℕ := [node10Piece7UnitInput_sector0_chunk0].flatten

def node10Piece7UnitInput : SectorVector := [(1, node10Piece7UnitInput_sector0)]

def node10Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (220, [0, 1, 1, 1, 1, 1, 2, 3]), (20, [0, 1, 1, 1, 1, 2, 2, 2]), (440, [0, 1, 1, 1, 1, 6]), (240, [0, 1, 1, 1, 2, 5]), (240, [0, 1, 1, 1, 3, 4]), (240, [0, 1, 1, 8]), (96, [1, 1, 1, 1, 1, 1, 1, 3]), (96, [1, 1, 1, 1, 1, 1, 2, 2]), (1008, [1, 1, 1, 1, 1, 5]), (960, [1, 1, 1, 1, 2, 4]), (480, [1, 1, 1, 1, 3, 3]), (1920, [1, 1, 1, 7])]

def node10Piece7UnitOutput_sector0 : RawPoly ℕ := [node10Piece7UnitOutput_sector0_chunk0].flatten

def node10Piece7UnitOutput : SectorVector := [(1, node10Piece7UnitOutput_sector0)]

theorem node10Piece7_check : VectorCertificate (neutralBoundS JR (-2) node10Piece7UnitInput) node10Piece7UnitOutput := by decide +kernel

theorem node10Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece7Input) = evaluate node10Piece7Output :=
  mode_of_scaled _ _ (-1) node10Piece7UnitInput node10Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece7_check)

def node10Piece8Input_sector0 : RawPoly ℕ := [(-10, [0, 1, 1, 3])]

def node10Piece8Input : SectorVector := [(1, node10Piece8Input_sector0)]
def node10Piece8Output_sector0 : RawPoly ℕ := [(-40, [0, 1, 1, 1, 1, 1, 2, 3]), (-360, [0, 1, 1, 1, 1, 6]), (-720, [0, 1, 1, 1, 2, 5]), (-1860, [0, 1, 1, 1, 3, 4]), (-360, [0, 1, 1, 2, 2, 4]), (-1840, [0, 1, 1, 2, 3, 3]), (60, [0, 1, 1, 8]), (-80, [0, 1, 2, 2, 2, 3]), (-1440, [0, 1, 2, 7]), (-2480, [0, 1, 3, 6]), (-1440, [0, 1, 4, 5]), (-240, [0, 2, 3, 5]), (-240, [0, 3, 3, 4]), (-720, [0, 10]), (-960, [1, 1, 1, 1, 3, 3]), (-960, [1, 1, 1, 2, 2, 3]), (-5760, [1, 1, 1, 7]), (-5760, [1, 1, 2, 6]), (-10080, [1, 1, 3, 5]), (-2880, [1, 1, 4, 4]), (-3840, [1, 2, 3, 4]), (-1920, [1, 3, 3, 3]), (-11520, [1, 9]), (-1920, [3, 7])]

def node10Piece8Output : SectorVector := [(1, node10Piece8Output_sector0)]

def node10Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node10Piece8UnitInput_sector0 : RawPoly ℕ := [node10Piece8UnitInput_sector0_chunk0].flatten

def node10Piece8UnitInput : SectorVector := [(1, node10Piece8UnitInput_sector0)]

def node10Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 2, 3]), (36, [0, 1, 1, 1, 1, 6]), (72, [0, 1, 1, 1, 2, 5]), (186, [0, 1, 1, 1, 3, 4]), (36, [0, 1, 1, 2, 2, 4]), (184, [0, 1, 1, 2, 3, 3]), (-6, [0, 1, 1, 8]), (8, [0, 1, 2, 2, 2, 3]), (144, [0, 1, 2, 7]), (248, [0, 1, 3, 6]), (144, [0, 1, 4, 5]), (24, [0, 2, 3, 5]), (24, [0, 3, 3, 4]), (72, [0, 10]), (96, [1, 1, 1, 1, 3, 3]), (96, [1, 1, 1, 2, 2, 3]), (576, [1, 1, 1, 7]), (576, [1, 1, 2, 6]), (1008, [1, 1, 3, 5]), (288, [1, 1, 4, 4]), (384, [1, 2, 3, 4]), (192, [1, 3, 3, 3]), (1152, [1, 9]), (192, [3, 7])]

def node10Piece8UnitOutput_sector0 : RawPoly ℕ := [node10Piece8UnitOutput_sector0_chunk0].flatten

def node10Piece8UnitOutput : SectorVector := [(1, node10Piece8UnitOutput_sector0)]

theorem node10Piece8_check : VectorCertificate (neutralBoundS JR (-2) node10Piece8UnitInput) node10Piece8UnitOutput := by decide +kernel

theorem node10Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece8Input) = evaluate node10Piece8Output :=
  mode_of_scaled _ _ (-10) node10Piece8UnitInput node10Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece8_check)

def node10Piece9Input_sector0 : RawPoly ℕ := [(-15/2, [0, 1, 2, 2])]

def node10Piece9Input : SectorVector := [(1, node10Piece9Input_sector0)]
def node10Piece9Output_sector0 : RawPoly ℕ := [(-30, [0, 1, 1, 1, 1, 2, 2, 2]), (-360, [0, 1, 1, 1, 2, 5]), (-1485, [0, 1, 1, 2, 2, 4]), (-360, [0, 1, 1, 2, 3, 3]), (-720, [0, 1, 1, 8]), (-1290, [0, 1, 2, 2, 2, 3]), (-1440, [0, 1, 2, 7]), (-720, [0, 1, 3, 6]), (-720, [0, 1, 4, 5]), (-30, [0, 2, 2, 2, 2, 2]), (-1020, [0, 2, 2, 6]), (-720, [0, 2, 3, 5]), (-360, [0, 2, 4, 4]), (-720, [0, 10]), (-720, [1, 1, 1, 2, 2, 3]), (-720, [1, 1, 2, 2, 2, 2]), (-5760, [1, 1, 2, 6]), (-7560, [1, 2, 2, 5]), (-5760, [1, 2, 3, 4]), (-5760, [1, 9]), (-1440, [2, 2, 2, 4]), (-720, [2, 2, 3, 3]), (-5760, [2, 8])]

def node10Piece9Output : SectorVector := [(1, node10Piece9Output_sector0)]

def node10Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node10Piece9UnitInput_sector0 : RawPoly ℕ := [node10Piece9UnitInput_sector0_chunk0].flatten

def node10Piece9UnitInput : SectorVector := [(1, node10Piece9UnitInput_sector0)]

def node10Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 2, 2, 2]), (48, [0, 1, 1, 1, 2, 5]), (198, [0, 1, 1, 2, 2, 4]), (48, [0, 1, 1, 2, 3, 3]), (96, [0, 1, 1, 8]), (172, [0, 1, 2, 2, 2, 3]), (192, [0, 1, 2, 7]), (96, [0, 1, 3, 6]), (96, [0, 1, 4, 5]), (4, [0, 2, 2, 2, 2, 2]), (136, [0, 2, 2, 6]), (96, [0, 2, 3, 5]), (48, [0, 2, 4, 4]), (96, [0, 10]), (96, [1, 1, 1, 2, 2, 3]), (96, [1, 1, 2, 2, 2, 2]), (768, [1, 1, 2, 6]), (1008, [1, 2, 2, 5]), (768, [1, 2, 3, 4]), (768, [1, 9]), (192, [2, 2, 2, 4]), (96, [2, 2, 3, 3]), (768, [2, 8])]

def node10Piece9UnitOutput_sector0 : RawPoly ℕ := [node10Piece9UnitOutput_sector0_chunk0].flatten

def node10Piece9UnitOutput : SectorVector := [(1, node10Piece9UnitOutput_sector0)]

theorem node10Piece9_check : VectorCertificate (neutralBoundS JR (-2) node10Piece9UnitInput) node10Piece9UnitOutput := by decide +kernel

theorem node10Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece9Input) = evaluate node10Piece9Output :=
  mode_of_scaled _ _ (-15/2) node10Piece9UnitInput node10Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece9_check)

def node10Piece10Input_sector0 : RawPoly ℕ := [(-6, [0, 5])]

def node10Piece10Input : SectorVector := [(1, node10Piece10Input_sector0)]
def node10Piece10Output_sector0 : RawPoly ℕ := [(-24, [0, 1, 1, 1, 2, 5]), (-360, [0, 1, 1, 8]), (-720, [0, 1, 2, 7]), (-720, [0, 1, 3, 6]), (-1260, [0, 1, 4, 5]), (-360, [0, 2, 2, 6]), (-1320, [0, 2, 3, 5]), (-360, [0, 2, 4, 4]), (-360, [0, 3, 3, 4]), (5400, [0, 10]), (-576, [1, 1, 3, 5]), (-576, [1, 2, 2, 5]), (-5760, [1, 9]), (-5760, [2, 8]), (-5760, [3, 7]), (-5760, [4, 6]), (-3168, [5, 5])]

def node10Piece10Output : SectorVector := [(1, node10Piece10Output_sector0)]

def node10Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node10Piece10UnitInput_sector0 : RawPoly ℕ := [node10Piece10UnitInput_sector0_chunk0].flatten

def node10Piece10UnitInput : SectorVector := [(1, node10Piece10UnitInput_sector0)]

def node10Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 2, 5]), (60, [0, 1, 1, 8]), (120, [0, 1, 2, 7]), (120, [0, 1, 3, 6]), (210, [0, 1, 4, 5]), (60, [0, 2, 2, 6]), (220, [0, 2, 3, 5]), (60, [0, 2, 4, 4]), (60, [0, 3, 3, 4]), (-900, [0, 10]), (96, [1, 1, 3, 5]), (96, [1, 2, 2, 5]), (960, [1, 9]), (960, [2, 8]), (960, [3, 7]), (960, [4, 6]), (528, [5, 5])]

def node10Piece10UnitOutput_sector0 : RawPoly ℕ := [node10Piece10UnitOutput_sector0_chunk0].flatten

def node10Piece10UnitOutput : SectorVector := [(1, node10Piece10UnitOutput_sector0)]

theorem node10Piece10_check : VectorCertificate (neutralBoundS JR (-2) node10Piece10UnitInput) node10Piece10UnitOutput := by decide +kernel

theorem node10Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece10Input) = evaluate node10Piece10Output :=
  mode_of_scaled _ _ (-6) node10Piece10UnitInput node10Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece10_check)

def node10Piece11Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node10Piece11Input : SectorVector := [(1, node10Piece11Input_sector0)]
def node10Piece11Output_sector0 : RawPoly ℕ := [(240, [0, 1, 1, 1, 1, 1, 2, 3]), (240, [0, 1, 1, 1, 1, 2, 2, 2]), (960, [0, 1, 1, 1, 1, 6]), (2520, [0, 1, 1, 1, 2, 5]), (960, [0, 1, 1, 1, 3, 4]), (1440, [0, 1, 1, 2, 2, 4]), (720, [0, 1, 1, 2, 3, 3]), (2880, [0, 1, 1, 8]), (1440, [0, 1, 2, 7]), (80, [1, 1, 1, 1, 1, 1, 2, 2]), (480, [1, 1, 1, 1, 1, 5]), (3480, [1, 1, 1, 1, 2, 4]), (480, [1, 1, 1, 1, 3, 3]), (3920, [1, 1, 1, 2, 2, 3]), (2880, [1, 1, 1, 7]), (240, [1, 1, 2, 2, 2, 2]), (6720, [1, 1, 2, 6]), (2880, [1, 1, 3, 5]), (1440, [1, 1, 4, 4]), (1440, [1, 2, 2, 5]), (1440, [1, 2, 3, 4]), (2880, [1, 9]), (480, [2, 8])]

def node10Piece11Output : SectorVector := [(1, node10Piece11Output_sector0)]

def node10Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node10Piece11UnitInput_sector0 : RawPoly ℕ := [node10Piece11UnitInput_sector0_chunk0].flatten

def node10Piece11UnitInput : SectorVector := [(1, node10Piece11UnitInput_sector0)]

def node10Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 1, 1, 2, 3]), (12, [0, 1, 1, 1, 1, 2, 2, 2]), (48, [0, 1, 1, 1, 1, 6]), (126, [0, 1, 1, 1, 2, 5]), (48, [0, 1, 1, 1, 3, 4]), (72, [0, 1, 1, 2, 2, 4]), (36, [0, 1, 1, 2, 3, 3]), (144, [0, 1, 1, 8]), (72, [0, 1, 2, 7]), (4, [1, 1, 1, 1, 1, 1, 2, 2]), (24, [1, 1, 1, 1, 1, 5]), (174, [1, 1, 1, 1, 2, 4]), (24, [1, 1, 1, 1, 3, 3]), (196, [1, 1, 1, 2, 2, 3]), (144, [1, 1, 1, 7]), (12, [1, 1, 2, 2, 2, 2]), (336, [1, 1, 2, 6]), (144, [1, 1, 3, 5]), (72, [1, 1, 4, 4]), (72, [1, 2, 2, 5]), (72, [1, 2, 3, 4]), (144, [1, 9]), (24, [2, 8])]

def node10Piece11UnitOutput_sector0 : RawPoly ℕ := [node10Piece11UnitOutput_sector0_chunk0].flatten

def node10Piece11UnitOutput : SectorVector := [(1, node10Piece11UnitOutput_sector0)]

theorem node10Piece11_check : VectorCertificate (neutralBoundS JR (-2) node10Piece11UnitInput) node10Piece11UnitOutput := by decide +kernel

theorem node10Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece11Input) = evaluate node10Piece11Output :=
  mode_of_scaled _ _ (20) node10Piece11UnitInput node10Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece11_check)

def node10Piece12Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node10Piece12Input : SectorVector := [(1, node10Piece12Input_sector0)]
def node10Piece12Output_sector0 : RawPoly ℕ := [(360, [0, 1, 1, 1, 3, 4]), (360, [0, 1, 1, 2, 2, 4]), (2880, [0, 1, 1, 8]), (2880, [0, 1, 2, 7]), (2880, [0, 1, 3, 6]), (3780, [0, 1, 4, 5]), (720, [0, 2, 4, 4]), (360, [0, 3, 3, 4]), (2880, [0, 10]), (120, [1, 1, 1, 1, 2, 4]), (1440, [1, 1, 1, 7]), (2880, [1, 1, 2, 6]), (2880, [1, 1, 3, 5]), (4500, [1, 1, 4, 4]), (1440, [1, 2, 2, 5]), (6600, [1, 2, 3, 4]), (480, [1, 3, 3, 3]), (-10320, [1, 9]), (120, [2, 2, 2, 4]), (2880, [2, 8]), (2880, [3, 7]), (4080, [4, 6]), (1440, [5, 5])]

def node10Piece12Output : SectorVector := [(1, node10Piece12Output_sector0)]

def node10Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node10Piece12UnitInput_sector0 : RawPoly ℕ := [node10Piece12UnitInput_sector0_chunk0].flatten

def node10Piece12UnitInput : SectorVector := [(1, node10Piece12UnitInput_sector0)]

def node10Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 3, 4]), (12, [0, 1, 1, 2, 2, 4]), (96, [0, 1, 1, 8]), (96, [0, 1, 2, 7]), (96, [0, 1, 3, 6]), (126, [0, 1, 4, 5]), (24, [0, 2, 4, 4]), (12, [0, 3, 3, 4]), (96, [0, 10]), (4, [1, 1, 1, 1, 2, 4]), (48, [1, 1, 1, 7]), (96, [1, 1, 2, 6]), (96, [1, 1, 3, 5]), (150, [1, 1, 4, 4]), (48, [1, 2, 2, 5]), (220, [1, 2, 3, 4]), (16, [1, 3, 3, 3]), (-344, [1, 9]), (4, [2, 2, 2, 4]), (96, [2, 8]), (96, [3, 7]), (136, [4, 6]), (48, [5, 5])]

def node10Piece12UnitOutput_sector0 : RawPoly ℕ := [node10Piece12UnitOutput_sector0_chunk0].flatten

def node10Piece12UnitOutput : SectorVector := [(1, node10Piece12UnitOutput_sector0)]

theorem node10Piece12_check : VectorCertificate (neutralBoundS JR (-2) node10Piece12UnitInput) node10Piece12UnitOutput := by decide +kernel

theorem node10Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece12Input) = evaluate node10Piece12Output :=
  mode_of_scaled _ _ (30) node10Piece12UnitInput node10Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece12_check)

def node10Piece13Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node10Piece13Input : SectorVector := [(1, node10Piece13Input_sector0)]
def node10Piece13Output_sector0 : RawPoly ℕ := [(240, [0, 1, 1, 2, 3, 3]), (240, [0, 1, 2, 2, 2, 3]), (1440, [0, 1, 2, 7]), (960, [0, 1, 3, 6]), (1440, [0, 2, 2, 6]), (2520, [0, 2, 3, 5]), (720, [0, 2, 4, 4]), (960, [0, 3, 3, 4]), (2880, [0, 10]), (80, [1, 1, 1, 2, 2, 3]), (720, [1, 1, 2, 6]), (480, [1, 1, 3, 5]), (1440, [1, 2, 2, 5]), (4200, [1, 2, 3, 4]), (480, [1, 3, 3, 3]), (2880, [1, 9]), (720, [2, 2, 2, 4]), (3200, [2, 2, 3, 3]), (-120, [2, 8]), (2880, [3, 7]), (2880, [4, 6]), (1440, [5, 5])]

def node10Piece13Output : SectorVector := [(1, node10Piece13Output_sector0)]

def node10Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node10Piece13UnitInput_sector0 : RawPoly ℕ := [node10Piece13UnitInput_sector0_chunk0].flatten

def node10Piece13UnitInput : SectorVector := [(1, node10Piece13UnitInput_sector0)]

def node10Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 2, 3, 3]), (12, [0, 1, 2, 2, 2, 3]), (72, [0, 1, 2, 7]), (48, [0, 1, 3, 6]), (72, [0, 2, 2, 6]), (126, [0, 2, 3, 5]), (36, [0, 2, 4, 4]), (48, [0, 3, 3, 4]), (144, [0, 10]), (4, [1, 1, 1, 2, 2, 3]), (36, [1, 1, 2, 6]), (24, [1, 1, 3, 5]), (72, [1, 2, 2, 5]), (210, [1, 2, 3, 4]), (24, [1, 3, 3, 3]), (144, [1, 9]), (36, [2, 2, 2, 4]), (160, [2, 2, 3, 3]), (-6, [2, 8]), (144, [3, 7]), (144, [4, 6]), (72, [5, 5])]

def node10Piece13UnitOutput_sector0 : RawPoly ℕ := [node10Piece13UnitOutput_sector0_chunk0].flatten

def node10Piece13UnitOutput : SectorVector := [(1, node10Piece13UnitOutput_sector0)]

theorem node10Piece13_check : VectorCertificate (neutralBoundS JR (-2) node10Piece13UnitInput) node10Piece13UnitOutput := by decide +kernel

theorem node10Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node10Piece13Input) = evaluate node10Piece13Output :=
  mode_of_scaled _ _ (20) node10Piece13UnitInput node10Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node10Piece13_check)

def node10Pieces : List (SectorVector × SectorVector) := [(node10Piece0Input, node10Piece0Output), (node10Piece1Input, node10Piece1Output), (node10Piece2Input, node10Piece2Output), (node10Piece3Input, node10Piece3Output), (node10Piece4Input, node10Piece4Output), (node10Piece5Input, node10Piece5Output), (node10Piece6Input, node10Piece6Output), (node10Piece7Input, node10Piece7Output), (node10Piece8Input, node10Piece8Output), (node10Piece9Input, node10Piece9Output), (node10Piece10Input, node10Piece10Output), (node10Piece11Input, node10Piece11Output), (node10Piece12Input, node10Piece12Output), (node10Piece13Input, node10Piece13Output)]

theorem node10Pieces_input : VectorCertificate (node10Pieces.flatMap Prod.fst) nineData := by decide +kernel

theorem node10Pieces_each : ∀ p ∈ node10Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-2) (evaluate p.1) = evaluate p.2 := by
  simp only [node10Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node10Piece0_value, node10Piece1_value, node10Piece2_value, node10Piece3_value, node10Piece4_value, node10Piece5_value, node10Piece6_value, node10Piece7_value, node10Piece8_value, node10Piece9_value, node10Piece10_value, node10Piece11_value, node10Piece12_value, node10Piece13_value, by simp⟩
end VOA.Classification.COne.OrbC2h
