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

def node18Piece0Input_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node18Piece0Input : SectorVector := [(-1, node18Piece0Input_sector0)]
def node18Piece0Output_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (154, [0, 1, 1, 1, 1, 1, 1, 3]), (219/2, [0, 1, 1, 1, 1, 1, 2, 2]), (510, [0, 1, 1, 1, 1, 5]), (240, [0, 1, 1, 1, 2, 4]), (120, [0, 1, 1, 1, 3, 3]), (240, [0, 1, 1, 7]), (-96, [1, 1, 1, 1, 1, 1, 1, 2]), (-1080, [1, 1, 1, 1, 1, 4]), (-960, [1, 1, 1, 1, 2, 3]), (-1920, [1, 1, 1, 6])]

def node18Piece0Output : SectorVector := [(-1, node18Piece0Output_sector0)]

def node18Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node18Piece0UnitInput_sector0 : RawPoly ℕ := [node18Piece0UnitInput_sector0_chunk0].flatten

def node18Piece0UnitInput : SectorVector := [(-1, node18Piece0UnitInput_sector0)]

def node18Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (154, [0, 1, 1, 1, 1, 1, 1, 3]), (219/2, [0, 1, 1, 1, 1, 1, 2, 2]), (510, [0, 1, 1, 1, 1, 5]), (240, [0, 1, 1, 1, 2, 4]), (120, [0, 1, 1, 1, 3, 3]), (240, [0, 1, 1, 7]), (-96, [1, 1, 1, 1, 1, 1, 1, 2]), (-1080, [1, 1, 1, 1, 1, 4]), (-960, [1, 1, 1, 1, 2, 3]), (-1920, [1, 1, 1, 6])]

def node18Piece0UnitOutput_sector0 : RawPoly ℕ := [node18Piece0UnitOutput_sector0_chunk0].flatten

def node18Piece0UnitOutput : SectorVector := [(-1, node18Piece0UnitOutput_sector0)]

theorem node18Piece0_check : VectorCertificate (neutralBoundS JR (-1) node18Piece0UnitInput) node18Piece0UnitOutput := by decide +kernel

theorem node18Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece0Input) = evaluate node18Piece0Output :=
  mode_of_scaled _ _ (1) node18Piece0UnitInput node18Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece0_check)

def node18Piece1Input_sector0 : RawPoly ℕ := [(10, [0, 1, 1, 3])]

def node18Piece1Input : SectorVector := [(-1, node18Piece1Input_sector0)]
def node18Piece1Output_sector0 : RawPoly ℕ := [(10, [0, 1, 1, 1, 1, 1, 1, 3]), (360, [0, 1, 1, 1, 1, 5]), (720, [0, 1, 1, 1, 2, 4]), (1540, [0, 1, 1, 1, 3, 3]), (1095, [0, 1, 1, 2, 2, 3]), (660, [0, 1, 1, 7]), (1440, [0, 1, 2, 6]), (2760, [0, 1, 3, 5]), (720, [0, 1, 4, 4]), (240, [0, 2, 3, 4]), (120, [0, 3, 3, 3]), (720, [0, 9]), (-960, [1, 1, 1, 1, 2, 3]), (-5760, [1, 1, 1, 6]), (-5760, [1, 1, 2, 5]), (-10800, [1, 1, 3, 4]), (-3840, [1, 2, 3, 3]), (-11520, [1, 8]), (-1920, [3, 6])]

def node18Piece1Output : SectorVector := [(-1, node18Piece1Output_sector0)]

def node18Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node18Piece1UnitInput_sector0 : RawPoly ℕ := [node18Piece1UnitInput_sector0_chunk0].flatten

def node18Piece1UnitInput : SectorVector := [(-1, node18Piece1UnitInput_sector0)]

def node18Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 3]), (36, [0, 1, 1, 1, 1, 5]), (72, [0, 1, 1, 1, 2, 4]), (154, [0, 1, 1, 1, 3, 3]), (219/2, [0, 1, 1, 2, 2, 3]), (66, [0, 1, 1, 7]), (144, [0, 1, 2, 6]), (276, [0, 1, 3, 5]), (72, [0, 1, 4, 4]), (24, [0, 2, 3, 4]), (12, [0, 3, 3, 3]), (72, [0, 9]), (-96, [1, 1, 1, 1, 2, 3]), (-576, [1, 1, 1, 6]), (-576, [1, 1, 2, 5]), (-1080, [1, 1, 3, 4]), (-384, [1, 2, 3, 3]), (-1152, [1, 8]), (-192, [3, 6])]

def node18Piece1UnitOutput_sector0 : RawPoly ℕ := [node18Piece1UnitOutput_sector0_chunk0].flatten

def node18Piece1UnitOutput : SectorVector := [(-1, node18Piece1UnitOutput_sector0)]

theorem node18Piece1_check : VectorCertificate (neutralBoundS JR (-1) node18Piece1UnitInput) node18Piece1UnitOutput := by decide +kernel

theorem node18Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece1Input) = evaluate node18Piece1Output :=
  mode_of_scaled _ _ (10) node18Piece1UnitInput node18Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece1_check)

def node18Piece2Input_sector0 : RawPoly ℕ := [(15/2, [0, 1, 2, 2])]

def node18Piece2Input : SectorVector := [(-1, node18Piece2Input_sector0)]
def node18Piece2Output_sector0 : RawPoly ℕ := [(15/2, [0, 1, 1, 1, 1, 1, 2, 2]), (360, [0, 1, 1, 1, 2, 4]), (1515, [0, 1, 1, 2, 2, 3]), (720, [0, 1, 1, 7]), (2325/4, [0, 1, 2, 2, 2, 2]), (2010, [0, 1, 2, 6]), (720, [0, 1, 3, 5]), (360, [0, 1, 4, 4]), (1125, [0, 2, 2, 5]), (720, [0, 2, 3, 4]), (720, [0, 9]), (-720, [1, 1, 1, 2, 2, 2]), (-5760, [1, 1, 2, 5]), (-8100, [1, 2, 2, 4]), (-2880, [1, 2, 3, 3]), (-5760, [1, 8]), (-1440, [2, 2, 2, 3]), (-5760, [2, 7])]

def node18Piece2Output : SectorVector := [(-1, node18Piece2Output_sector0)]

def node18Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node18Piece2UnitInput_sector0 : RawPoly ℕ := [node18Piece2UnitInput_sector0_chunk0].flatten

def node18Piece2UnitInput : SectorVector := [(-1, node18Piece2UnitInput_sector0)]

def node18Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 2, 2]), (48, [0, 1, 1, 1, 2, 4]), (202, [0, 1, 1, 2, 2, 3]), (96, [0, 1, 1, 7]), (155/2, [0, 1, 2, 2, 2, 2]), (268, [0, 1, 2, 6]), (96, [0, 1, 3, 5]), (48, [0, 1, 4, 4]), (150, [0, 2, 2, 5]), (96, [0, 2, 3, 4]), (96, [0, 9]), (-96, [1, 1, 1, 2, 2, 2]), (-768, [1, 1, 2, 5]), (-1080, [1, 2, 2, 4]), (-384, [1, 2, 3, 3]), (-768, [1, 8]), (-192, [2, 2, 2, 3]), (-768, [2, 7])]

def node18Piece2UnitOutput_sector0 : RawPoly ℕ := [node18Piece2UnitOutput_sector0_chunk0].flatten

def node18Piece2UnitOutput : SectorVector := [(-1, node18Piece2UnitOutput_sector0)]

theorem node18Piece2_check : VectorCertificate (neutralBoundS JR (-1) node18Piece2UnitInput) node18Piece2UnitOutput := by decide +kernel

theorem node18Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece2Input) = evaluate node18Piece2Output :=
  mode_of_scaled _ _ (15/2) node18Piece2UnitInput node18Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece2_check)

def node18Piece3Input_sector0 : RawPoly ℕ := [(6, [0, 5])]

def node18Piece3Input : SectorVector := [(-1, node18Piece3Input_sector0)]
def node18Piece3Output_sector0 : RawPoly ℕ := [(6, [0, 1, 1, 1, 1, 5]), (360, [0, 1, 1, 7]), (720, [0, 1, 2, 6]), (1284, [0, 1, 3, 5]), (360, [0, 1, 4, 4]), (657, [0, 2, 2, 5]), (720, [0, 2, 3, 4]), (120, [0, 3, 3, 3]), (-4380, [0, 9]), (-576, [1, 1, 2, 5]), (-5760, [1, 8]), (-5760, [2, 7]), (-5760, [3, 6]), (-6480, [4, 5])]

def node18Piece3Output : SectorVector := [(-1, node18Piece3Output_sector0)]

def node18Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node18Piece3UnitInput_sector0 : RawPoly ℕ := [node18Piece3UnitInput_sector0_chunk0].flatten

def node18Piece3UnitInput : SectorVector := [(-1, node18Piece3UnitInput_sector0)]

def node18Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 5]), (60, [0, 1, 1, 7]), (120, [0, 1, 2, 6]), (214, [0, 1, 3, 5]), (60, [0, 1, 4, 4]), (219/2, [0, 2, 2, 5]), (120, [0, 2, 3, 4]), (20, [0, 3, 3, 3]), (-730, [0, 9]), (-96, [1, 1, 2, 5]), (-960, [1, 8]), (-960, [2, 7]), (-960, [3, 6]), (-1080, [4, 5])]

def node18Piece3UnitOutput_sector0 : RawPoly ℕ := [node18Piece3UnitOutput_sector0_chunk0].flatten

def node18Piece3UnitOutput : SectorVector := [(-1, node18Piece3UnitOutput_sector0)]

theorem node18Piece3_check : VectorCertificate (neutralBoundS JR (-1) node18Piece3UnitInput) node18Piece3UnitOutput := by decide +kernel

theorem node18Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece3Input) = evaluate node18Piece3Output :=
  mode_of_scaled _ _ (6) node18Piece3UnitInput node18Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece3_check)

def node18Piece4Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node18Piece4Input : SectorVector := [(-1, node18Piece4Input_sector0)]
def node18Piece4Output_sector0 : RawPoly ℕ := [(-240, [0, 1, 1, 1, 1, 1, 2, 2]), (-960, [0, 1, 1, 1, 1, 5]), (-2700, [0, 1, 1, 1, 2, 4]), (-480, [0, 1, 1, 1, 3, 3]), (-1440, [0, 1, 1, 2, 2, 3]), (-2880, [0, 1, 1, 7]), (-1440, [0, 1, 2, 6]), (20, [1, 1, 1, 1, 1, 1, 1, 2]), (480, [1, 1, 1, 1, 1, 4]), (3560, [1, 1, 1, 1, 2, 3]), (1870, [1, 1, 1, 2, 2, 2]), (3640, [1, 1, 1, 6]), (7560, [1, 1, 2, 5]), (2880, [1, 1, 3, 4]), (1440, [1, 2, 2, 4]), (720, [1, 2, 3, 3]), (2880, [1, 8]), (480, [2, 7])]

def node18Piece4Output : SectorVector := [(-1, node18Piece4Output_sector0)]

def node18Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node18Piece4UnitInput_sector0 : RawPoly ℕ := [node18Piece4UnitInput_sector0_chunk0].flatten

def node18Piece4UnitInput : SectorVector := [(-1, node18Piece4UnitInput_sector0)]

def node18Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 1, 1, 2, 2]), (-48, [0, 1, 1, 1, 1, 5]), (-135, [0, 1, 1, 1, 2, 4]), (-24, [0, 1, 1, 1, 3, 3]), (-72, [0, 1, 1, 2, 2, 3]), (-144, [0, 1, 1, 7]), (-72, [0, 1, 2, 6]), (1, [1, 1, 1, 1, 1, 1, 1, 2]), (24, [1, 1, 1, 1, 1, 4]), (178, [1, 1, 1, 1, 2, 3]), (187/2, [1, 1, 1, 2, 2, 2]), (182, [1, 1, 1, 6]), (378, [1, 1, 2, 5]), (144, [1, 1, 3, 4]), (72, [1, 2, 2, 4]), (36, [1, 2, 3, 3]), (144, [1, 8]), (24, [2, 7])]

def node18Piece4UnitOutput_sector0 : RawPoly ℕ := [node18Piece4UnitOutput_sector0_chunk0].flatten

def node18Piece4UnitOutput : SectorVector := [(-1, node18Piece4UnitOutput_sector0)]

theorem node18Piece4_check : VectorCertificate (neutralBoundS JR (-1) node18Piece4UnitInput) node18Piece4UnitOutput := by decide +kernel

theorem node18Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece4Input) = evaluate node18Piece4Output :=
  mode_of_scaled _ _ (20) node18Piece4UnitInput node18Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece4_check)

def node18Piece5Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node18Piece5Input : SectorVector := [(-1, node18Piece5Input_sector0)]
def node18Piece5Output_sector0 : RawPoly ℕ := [(-360, [0, 1, 1, 1, 2, 4]), (-2880, [0, 1, 1, 7]), (-2880, [0, 1, 2, 6]), (-2880, [0, 1, 3, 5]), (-2610, [0, 1, 4, 4]), (-720, [0, 2, 3, 4]), (-2880, [0, 9]), (30, [1, 1, 1, 1, 1, 4]), (1440, [1, 1, 1, 6]), (2880, [1, 1, 2, 5]), (6060, [1, 1, 3, 4]), (3285, [1, 2, 2, 4]), (1440, [1, 2, 3, 3]), (-6840, [1, 8]), (2880, [2, 7]), (2880, [3, 6]), (4500, [4, 5])]

def node18Piece5Output : SectorVector := [(-1, node18Piece5Output_sector0)]

def node18Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node18Piece5UnitInput_sector0 : RawPoly ℕ := [node18Piece5UnitInput_sector0_chunk0].flatten

def node18Piece5UnitInput : SectorVector := [(-1, node18Piece5UnitInput_sector0)]

def node18Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 1, 2, 4]), (-96, [0, 1, 1, 7]), (-96, [0, 1, 2, 6]), (-96, [0, 1, 3, 5]), (-87, [0, 1, 4, 4]), (-24, [0, 2, 3, 4]), (-96, [0, 9]), (1, [1, 1, 1, 1, 1, 4]), (48, [1, 1, 1, 6]), (96, [1, 1, 2, 5]), (202, [1, 1, 3, 4]), (219/2, [1, 2, 2, 4]), (48, [1, 2, 3, 3]), (-228, [1, 8]), (96, [2, 7]), (96, [3, 6]), (150, [4, 5])]

def node18Piece5UnitOutput_sector0 : RawPoly ℕ := [node18Piece5UnitOutput_sector0_chunk0].flatten

def node18Piece5UnitOutput : SectorVector := [(-1, node18Piece5UnitOutput_sector0)]

theorem node18Piece5_check : VectorCertificate (neutralBoundS JR (-1) node18Piece5UnitInput) node18Piece5UnitOutput := by decide +kernel

theorem node18Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece5Input) = evaluate node18Piece5Output :=
  mode_of_scaled _ _ (30) node18Piece5UnitInput node18Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece5_check)

def node18Piece6Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node18Piece6Input : SectorVector := [(-1, node18Piece6Input_sector0)]
def node18Piece6Output_sector0 : RawPoly ℕ := [(-240, [0, 1, 1, 2, 2, 3]), (-1440, [0, 1, 2, 6]), (-960, [0, 1, 3, 5]), (-1440, [0, 2, 2, 5]), (-2700, [0, 2, 3, 4]), (-480, [0, 3, 3, 3]), (-2880, [0, 9]), (20, [1, 1, 1, 1, 2, 3]), (720, [1, 1, 2, 5]), (480, [1, 1, 3, 4]), (1440, [1, 2, 2, 4]), (3560, [1, 2, 3, 3]), (2880, [1, 8]), (1870, [2, 2, 2, 3]), (1320, [2, 7]), (3640, [3, 6]), (2880, [4, 5])]

def node18Piece6Output : SectorVector := [(-1, node18Piece6Output_sector0)]

def node18Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node18Piece6UnitInput_sector0 : RawPoly ℕ := [node18Piece6UnitInput_sector0_chunk0].flatten

def node18Piece6UnitInput : SectorVector := [(-1, node18Piece6UnitInput_sector0)]

def node18Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(-12, [0, 1, 1, 2, 2, 3]), (-72, [0, 1, 2, 6]), (-48, [0, 1, 3, 5]), (-72, [0, 2, 2, 5]), (-135, [0, 2, 3, 4]), (-24, [0, 3, 3, 3]), (-144, [0, 9]), (1, [1, 1, 1, 1, 2, 3]), (36, [1, 1, 2, 5]), (24, [1, 1, 3, 4]), (72, [1, 2, 2, 4]), (178, [1, 2, 3, 3]), (144, [1, 8]), (187/2, [2, 2, 2, 3]), (66, [2, 7]), (182, [3, 6]), (144, [4, 5])]

def node18Piece6UnitOutput_sector0 : RawPoly ℕ := [node18Piece6UnitOutput_sector0_chunk0].flatten

def node18Piece6UnitOutput : SectorVector := [(-1, node18Piece6UnitOutput_sector0)]

theorem node18Piece6_check : VectorCertificate (neutralBoundS JR (-1) node18Piece6UnitInput) node18Piece6UnitOutput := by decide +kernel

theorem node18Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece6Input) = evaluate node18Piece6Output :=
  mode_of_scaled _ _ (20) node18Piece6UnitInput node18Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece6_check)

def node18Piece7Input_sector0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1])]

def node18Piece7Input : SectorVector := [(1, node18Piece7Input_sector0)]
def node18Piece7Output_sector0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (-154, [0, 1, 1, 1, 1, 1, 1, 3]), (-219/2, [0, 1, 1, 1, 1, 1, 2, 2]), (-510, [0, 1, 1, 1, 1, 5]), (-240, [0, 1, 1, 1, 2, 4]), (-120, [0, 1, 1, 1, 3, 3]), (-240, [0, 1, 1, 7]), (-96, [1, 1, 1, 1, 1, 1, 1, 2]), (-1080, [1, 1, 1, 1, 1, 4]), (-960, [1, 1, 1, 1, 2, 3]), (-1920, [1, 1, 1, 6])]

def node18Piece7Output : SectorVector := [(1, node18Piece7Output_sector0)]

def node18Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1])]

def node18Piece7UnitInput_sector0 : RawPoly ℕ := [node18Piece7UnitInput_sector0_chunk0].flatten

def node18Piece7UnitInput : SectorVector := [(1, node18Piece7UnitInput_sector0)]

def node18Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (154, [0, 1, 1, 1, 1, 1, 1, 3]), (219/2, [0, 1, 1, 1, 1, 1, 2, 2]), (510, [0, 1, 1, 1, 1, 5]), (240, [0, 1, 1, 1, 2, 4]), (120, [0, 1, 1, 1, 3, 3]), (240, [0, 1, 1, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 2]), (1080, [1, 1, 1, 1, 1, 4]), (960, [1, 1, 1, 1, 2, 3]), (1920, [1, 1, 1, 6])]

def node18Piece7UnitOutput_sector0 : RawPoly ℕ := [node18Piece7UnitOutput_sector0_chunk0].flatten

def node18Piece7UnitOutput : SectorVector := [(1, node18Piece7UnitOutput_sector0)]

theorem node18Piece7_check : VectorCertificate (neutralBoundS JR (-1) node18Piece7UnitInput) node18Piece7UnitOutput := by decide +kernel

theorem node18Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece7Input) = evaluate node18Piece7Output :=
  mode_of_scaled _ _ (-1) node18Piece7UnitInput node18Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece7_check)

def node18Piece8Input_sector0 : RawPoly ℕ := [(-10, [0, 1, 1, 3])]

def node18Piece8Input : SectorVector := [(1, node18Piece8Input_sector0)]
def node18Piece8Output_sector0 : RawPoly ℕ := [(-10, [0, 1, 1, 1, 1, 1, 1, 3]), (-360, [0, 1, 1, 1, 1, 5]), (-720, [0, 1, 1, 1, 2, 4]), (-1540, [0, 1, 1, 1, 3, 3]), (-1095, [0, 1, 1, 2, 2, 3]), (-660, [0, 1, 1, 7]), (-1440, [0, 1, 2, 6]), (-2760, [0, 1, 3, 5]), (-720, [0, 1, 4, 4]), (-240, [0, 2, 3, 4]), (-120, [0, 3, 3, 3]), (-720, [0, 9]), (-960, [1, 1, 1, 1, 2, 3]), (-5760, [1, 1, 1, 6]), (-5760, [1, 1, 2, 5]), (-10800, [1, 1, 3, 4]), (-3840, [1, 2, 3, 3]), (-11520, [1, 8]), (-1920, [3, 6])]

def node18Piece8Output : SectorVector := [(1, node18Piece8Output_sector0)]

def node18Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 3])]

def node18Piece8UnitInput_sector0 : RawPoly ℕ := [node18Piece8UnitInput_sector0_chunk0].flatten

def node18Piece8UnitInput : SectorVector := [(1, node18Piece8UnitInput_sector0)]

def node18Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 3]), (36, [0, 1, 1, 1, 1, 5]), (72, [0, 1, 1, 1, 2, 4]), (154, [0, 1, 1, 1, 3, 3]), (219/2, [0, 1, 1, 2, 2, 3]), (66, [0, 1, 1, 7]), (144, [0, 1, 2, 6]), (276, [0, 1, 3, 5]), (72, [0, 1, 4, 4]), (24, [0, 2, 3, 4]), (12, [0, 3, 3, 3]), (72, [0, 9]), (96, [1, 1, 1, 1, 2, 3]), (576, [1, 1, 1, 6]), (576, [1, 1, 2, 5]), (1080, [1, 1, 3, 4]), (384, [1, 2, 3, 3]), (1152, [1, 8]), (192, [3, 6])]

def node18Piece8UnitOutput_sector0 : RawPoly ℕ := [node18Piece8UnitOutput_sector0_chunk0].flatten

def node18Piece8UnitOutput : SectorVector := [(1, node18Piece8UnitOutput_sector0)]

theorem node18Piece8_check : VectorCertificate (neutralBoundS JR (-1) node18Piece8UnitInput) node18Piece8UnitOutput := by decide +kernel

theorem node18Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece8Input) = evaluate node18Piece8Output :=
  mode_of_scaled _ _ (-10) node18Piece8UnitInput node18Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece8_check)

def node18Piece9Input_sector0 : RawPoly ℕ := [(-15/2, [0, 1, 2, 2])]

def node18Piece9Input : SectorVector := [(1, node18Piece9Input_sector0)]
def node18Piece9Output_sector0 : RawPoly ℕ := [(-15/2, [0, 1, 1, 1, 1, 1, 2, 2]), (-360, [0, 1, 1, 1, 2, 4]), (-1515, [0, 1, 1, 2, 2, 3]), (-720, [0, 1, 1, 7]), (-2325/4, [0, 1, 2, 2, 2, 2]), (-2010, [0, 1, 2, 6]), (-720, [0, 1, 3, 5]), (-360, [0, 1, 4, 4]), (-1125, [0, 2, 2, 5]), (-720, [0, 2, 3, 4]), (-720, [0, 9]), (-720, [1, 1, 1, 2, 2, 2]), (-5760, [1, 1, 2, 5]), (-8100, [1, 2, 2, 4]), (-2880, [1, 2, 3, 3]), (-5760, [1, 8]), (-1440, [2, 2, 2, 3]), (-5760, [2, 7])]

def node18Piece9Output : SectorVector := [(1, node18Piece9Output_sector0)]

def node18Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 2, 2])]

def node18Piece9UnitInput_sector0 : RawPoly ℕ := [node18Piece9UnitInput_sector0_chunk0].flatten

def node18Piece9UnitInput : SectorVector := [(1, node18Piece9UnitInput_sector0)]

def node18Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 2, 2]), (48, [0, 1, 1, 1, 2, 4]), (202, [0, 1, 1, 2, 2, 3]), (96, [0, 1, 1, 7]), (155/2, [0, 1, 2, 2, 2, 2]), (268, [0, 1, 2, 6]), (96, [0, 1, 3, 5]), (48, [0, 1, 4, 4]), (150, [0, 2, 2, 5]), (96, [0, 2, 3, 4]), (96, [0, 9]), (96, [1, 1, 1, 2, 2, 2]), (768, [1, 1, 2, 5]), (1080, [1, 2, 2, 4]), (384, [1, 2, 3, 3]), (768, [1, 8]), (192, [2, 2, 2, 3]), (768, [2, 7])]

def node18Piece9UnitOutput_sector0 : RawPoly ℕ := [node18Piece9UnitOutput_sector0_chunk0].flatten

def node18Piece9UnitOutput : SectorVector := [(1, node18Piece9UnitOutput_sector0)]

theorem node18Piece9_check : VectorCertificate (neutralBoundS JR (-1) node18Piece9UnitInput) node18Piece9UnitOutput := by decide +kernel

theorem node18Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece9Input) = evaluate node18Piece9Output :=
  mode_of_scaled _ _ (-15/2) node18Piece9UnitInput node18Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece9_check)

def node18Piece10Input_sector0 : RawPoly ℕ := [(-6, [0, 5])]

def node18Piece10Input : SectorVector := [(1, node18Piece10Input_sector0)]
def node18Piece10Output_sector0 : RawPoly ℕ := [(-6, [0, 1, 1, 1, 1, 5]), (-360, [0, 1, 1, 7]), (-720, [0, 1, 2, 6]), (-1284, [0, 1, 3, 5]), (-360, [0, 1, 4, 4]), (-657, [0, 2, 2, 5]), (-720, [0, 2, 3, 4]), (-120, [0, 3, 3, 3]), (4380, [0, 9]), (-576, [1, 1, 2, 5]), (-5760, [1, 8]), (-5760, [2, 7]), (-5760, [3, 6]), (-6480, [4, 5])]

def node18Piece10Output : SectorVector := [(1, node18Piece10Output_sector0)]

def node18Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 5])]

def node18Piece10UnitInput_sector0 : RawPoly ℕ := [node18Piece10UnitInput_sector0_chunk0].flatten

def node18Piece10UnitInput : SectorVector := [(1, node18Piece10UnitInput_sector0)]

def node18Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 5]), (60, [0, 1, 1, 7]), (120, [0, 1, 2, 6]), (214, [0, 1, 3, 5]), (60, [0, 1, 4, 4]), (219/2, [0, 2, 2, 5]), (120, [0, 2, 3, 4]), (20, [0, 3, 3, 3]), (-730, [0, 9]), (96, [1, 1, 2, 5]), (960, [1, 8]), (960, [2, 7]), (960, [3, 6]), (1080, [4, 5])]

def node18Piece10UnitOutput_sector0 : RawPoly ℕ := [node18Piece10UnitOutput_sector0_chunk0].flatten

def node18Piece10UnitOutput : SectorVector := [(1, node18Piece10UnitOutput_sector0)]

theorem node18Piece10_check : VectorCertificate (neutralBoundS JR (-1) node18Piece10UnitInput) node18Piece10UnitOutput := by decide +kernel

theorem node18Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece10Input) = evaluate node18Piece10Output :=
  mode_of_scaled _ _ (-6) node18Piece10UnitInput node18Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece10_check)

def node18Piece11Input_sector0 : RawPoly ℕ := [(20, [1, 1, 1, 2])]

def node18Piece11Input : SectorVector := [(1, node18Piece11Input_sector0)]
def node18Piece11Output_sector0 : RawPoly ℕ := [(240, [0, 1, 1, 1, 1, 1, 2, 2]), (960, [0, 1, 1, 1, 1, 5]), (2700, [0, 1, 1, 1, 2, 4]), (480, [0, 1, 1, 1, 3, 3]), (1440, [0, 1, 1, 2, 2, 3]), (2880, [0, 1, 1, 7]), (1440, [0, 1, 2, 6]), (20, [1, 1, 1, 1, 1, 1, 1, 2]), (480, [1, 1, 1, 1, 1, 4]), (3560, [1, 1, 1, 1, 2, 3]), (1870, [1, 1, 1, 2, 2, 2]), (3640, [1, 1, 1, 6]), (7560, [1, 1, 2, 5]), (2880, [1, 1, 3, 4]), (1440, [1, 2, 2, 4]), (720, [1, 2, 3, 3]), (2880, [1, 8]), (480, [2, 7])]

def node18Piece11Output : SectorVector := [(1, node18Piece11Output_sector0)]

def node18Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2])]

def node18Piece11UnitInput_sector0 : RawPoly ℕ := [node18Piece11UnitInput_sector0_chunk0].flatten

def node18Piece11UnitInput : SectorVector := [(1, node18Piece11UnitInput_sector0)]

def node18Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 1, 1, 2, 2]), (48, [0, 1, 1, 1, 1, 5]), (135, [0, 1, 1, 1, 2, 4]), (24, [0, 1, 1, 1, 3, 3]), (72, [0, 1, 1, 2, 2, 3]), (144, [0, 1, 1, 7]), (72, [0, 1, 2, 6]), (1, [1, 1, 1, 1, 1, 1, 1, 2]), (24, [1, 1, 1, 1, 1, 4]), (178, [1, 1, 1, 1, 2, 3]), (187/2, [1, 1, 1, 2, 2, 2]), (182, [1, 1, 1, 6]), (378, [1, 1, 2, 5]), (144, [1, 1, 3, 4]), (72, [1, 2, 2, 4]), (36, [1, 2, 3, 3]), (144, [1, 8]), (24, [2, 7])]

def node18Piece11UnitOutput_sector0 : RawPoly ℕ := [node18Piece11UnitOutput_sector0_chunk0].flatten

def node18Piece11UnitOutput : SectorVector := [(1, node18Piece11UnitOutput_sector0)]

theorem node18Piece11_check : VectorCertificate (neutralBoundS JR (-1) node18Piece11UnitInput) node18Piece11UnitOutput := by decide +kernel

theorem node18Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece11Input) = evaluate node18Piece11Output :=
  mode_of_scaled _ _ (20) node18Piece11UnitInput node18Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece11_check)

def node18Piece12Input_sector0 : RawPoly ℕ := [(30, [1, 4])]

def node18Piece12Input : SectorVector := [(1, node18Piece12Input_sector0)]
def node18Piece12Output_sector0 : RawPoly ℕ := [(360, [0, 1, 1, 1, 2, 4]), (2880, [0, 1, 1, 7]), (2880, [0, 1, 2, 6]), (2880, [0, 1, 3, 5]), (2610, [0, 1, 4, 4]), (720, [0, 2, 3, 4]), (2880, [0, 9]), (30, [1, 1, 1, 1, 1, 4]), (1440, [1, 1, 1, 6]), (2880, [1, 1, 2, 5]), (6060, [1, 1, 3, 4]), (3285, [1, 2, 2, 4]), (1440, [1, 2, 3, 3]), (-6840, [1, 8]), (2880, [2, 7]), (2880, [3, 6]), (4500, [4, 5])]

def node18Piece12Output : SectorVector := [(1, node18Piece12Output_sector0)]

def node18Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4])]

def node18Piece12UnitInput_sector0 : RawPoly ℕ := [node18Piece12UnitInput_sector0_chunk0].flatten

def node18Piece12UnitInput : SectorVector := [(1, node18Piece12UnitInput_sector0)]

def node18Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 1, 2, 4]), (96, [0, 1, 1, 7]), (96, [0, 1, 2, 6]), (96, [0, 1, 3, 5]), (87, [0, 1, 4, 4]), (24, [0, 2, 3, 4]), (96, [0, 9]), (1, [1, 1, 1, 1, 1, 4]), (48, [1, 1, 1, 6]), (96, [1, 1, 2, 5]), (202, [1, 1, 3, 4]), (219/2, [1, 2, 2, 4]), (48, [1, 2, 3, 3]), (-228, [1, 8]), (96, [2, 7]), (96, [3, 6]), (150, [4, 5])]

def node18Piece12UnitOutput_sector0 : RawPoly ℕ := [node18Piece12UnitOutput_sector0_chunk0].flatten

def node18Piece12UnitOutput : SectorVector := [(1, node18Piece12UnitOutput_sector0)]

theorem node18Piece12_check : VectorCertificate (neutralBoundS JR (-1) node18Piece12UnitInput) node18Piece12UnitOutput := by decide +kernel

theorem node18Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece12Input) = evaluate node18Piece12Output :=
  mode_of_scaled _ _ (30) node18Piece12UnitInput node18Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece12_check)

def node18Piece13Input_sector0 : RawPoly ℕ := [(20, [2, 3])]

def node18Piece13Input : SectorVector := [(1, node18Piece13Input_sector0)]
def node18Piece13Output_sector0 : RawPoly ℕ := [(240, [0, 1, 1, 2, 2, 3]), (1440, [0, 1, 2, 6]), (960, [0, 1, 3, 5]), (1440, [0, 2, 2, 5]), (2700, [0, 2, 3, 4]), (480, [0, 3, 3, 3]), (2880, [0, 9]), (20, [1, 1, 1, 1, 2, 3]), (720, [1, 1, 2, 5]), (480, [1, 1, 3, 4]), (1440, [1, 2, 2, 4]), (3560, [1, 2, 3, 3]), (2880, [1, 8]), (1870, [2, 2, 2, 3]), (1320, [2, 7]), (3640, [3, 6]), (2880, [4, 5])]

def node18Piece13Output : SectorVector := [(1, node18Piece13Output_sector0)]

def node18Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3])]

def node18Piece13UnitInput_sector0 : RawPoly ℕ := [node18Piece13UnitInput_sector0_chunk0].flatten

def node18Piece13UnitInput : SectorVector := [(1, node18Piece13UnitInput_sector0)]

def node18Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(12, [0, 1, 1, 2, 2, 3]), (72, [0, 1, 2, 6]), (48, [0, 1, 3, 5]), (72, [0, 2, 2, 5]), (135, [0, 2, 3, 4]), (24, [0, 3, 3, 3]), (144, [0, 9]), (1, [1, 1, 1, 1, 2, 3]), (36, [1, 1, 2, 5]), (24, [1, 1, 3, 4]), (72, [1, 2, 2, 4]), (178, [1, 2, 3, 3]), (144, [1, 8]), (187/2, [2, 2, 2, 3]), (66, [2, 7]), (182, [3, 6]), (144, [4, 5])]

def node18Piece13UnitOutput_sector0 : RawPoly ℕ := [node18Piece13UnitOutput_sector0_chunk0].flatten

def node18Piece13UnitOutput : SectorVector := [(1, node18Piece13UnitOutput_sector0)]

theorem node18Piece13_check : VectorCertificate (neutralBoundS JR (-1) node18Piece13UnitInput) node18Piece13UnitOutput := by decide +kernel

theorem node18Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-1)
    (evaluate node18Piece13Input) = evaluate node18Piece13Output :=
  mode_of_scaled _ _ (20) node18Piece13UnitInput node18Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node18Piece13_check)

def node18Pieces : List (SectorVector × SectorVector) := [(node18Piece0Input, node18Piece0Output), (node18Piece1Input, node18Piece1Output), (node18Piece2Input, node18Piece2Output), (node18Piece3Input, node18Piece3Output), (node18Piece4Input, node18Piece4Output), (node18Piece5Input, node18Piece5Output), (node18Piece6Input, node18Piece6Output), (node18Piece7Input, node18Piece7Output), (node18Piece8Input, node18Piece8Output), (node18Piece9Input, node18Piece9Output), (node18Piece10Input, node18Piece10Output), (node18Piece11Input, node18Piece11Output), (node18Piece12Input, node18Piece12Output), (node18Piece13Input, node18Piece13Output)]

theorem node18Pieces_input : VectorCertificate (node18Pieces.flatMap Prod.fst) nineData := by decide +kernel

theorem node18Pieces_each : ∀ p ∈ node18Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-1) (evaluate p.1) = evaluate p.2 := by
  simp only [node18Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node18Piece0_value, node18Piece1_value, node18Piece2_value, node18Piece3_value, node18Piece4_value, node18Piece5_value, node18Piece6_value, node18Piece7_value, node18Piece8_value, node18Piece9_value, node18Piece10_value, node18Piece11_value, node18Piece12_value, node18Piece13_value, by simp⟩
end VOA.Classification.COne.OrbC2h
