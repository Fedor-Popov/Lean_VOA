import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
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

def node12Piece0Input_sector0 : RawPoly ℕ := [(512/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node12Piece0Input : SectorVector := [(0, node12Piece0Input_sector0)]
def node12Piece0Output_sector0 : RawPoly ℕ := [(2048/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1024/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (2048/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (57856/45045, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (88064/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (4096/6435, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (28672/6435, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (4096/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (4096/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (2048/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9])]

def node12Piece0Output : SectorVector := [(0, node12Piece0Output_sector0)]

def node12Piece0UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def node12Piece0UnitInput_sector0 : RawPoly ℕ := [node12Piece0UnitInput_sector0_chunk0].flatten

def node12Piece0UnitInput : SectorVector := [(0, node12Piece0UnitInput_sector0)]

def node12Piece0UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (156, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (339, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (1176, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (2184, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (2184, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (1092, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (8736, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9])]

def node12Piece0UnitOutput_sector0 : RawPoly ℕ := [node12Piece0UnitOutput_sector0_chunk0].flatten

def node12Piece0UnitOutput : SectorVector := [(0, node12Piece0UnitOutput_sector0)]

theorem node12Piece0_check : VectorCertificate (neutralBoundS JR (-3) node12Piece0UnitInput) node12Piece0UnitOutput := by decide +kernel

theorem node12Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece0Input) = evaluate node12Piece0Output :=
  mode_of_scaled _ _ (512/135135) node12Piece0UnitInput node12Piece0UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece0_check)

def node12Piece1Input_sector0 : RawPoly ℕ := [(512/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node12Piece1Input : SectorVector := [(0, node12Piece1Input_sector0)]
def node12Piece1Output_sector0 : RawPoly ℕ := [(2048/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (3072/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (18432/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (36864/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (98304/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (18432/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (18432/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (173568/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (75776/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (141312/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (6144/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (36864/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (36864/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (18432/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node12Piece1Output : SectorVector := [(0, node12Piece1Output_sector0)]

def node12Piece1UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])]

def node12Piece1UnitInput_sector0 : RawPoly ℕ := [node12Piece1UnitInput_sector0_chunk0].flatten

def node12Piece1UnitInput : SectorVector := [(0, node12Piece1UnitInput_sector0)]

def node12Piece1UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (339, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (148, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (276, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (132, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (792, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (792, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (396, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (3960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (3960, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node12Piece1UnitOutput_sector0 : RawPoly ℕ := [node12Piece1UnitOutput_sector0_chunk0].flatten

def node12Piece1UnitOutput : SectorVector := [(0, node12Piece1UnitOutput_sector0)]

theorem node12Piece1_check : VectorCertificate (neutralBoundS JR (-3) node12Piece1UnitInput) node12Piece1UnitOutput := by decide +kernel

theorem node12Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece1Input) = evaluate node12Piece1Output :=
  mode_of_scaled _ _ (512/385) node12Piece1UnitInput node12Piece1UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece1_check)

def node12Piece2Input_sector0 : RawPoly ℕ := [(1664/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2])]

def node12Piece2Input : SectorVector := [(0, node12Piece2Input_sector0)]
def node12Piece2Output_sector0 : RawPoly ℕ := [(6656/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (3328/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (26624/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (113152/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (53248/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (53248/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (161408/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (286208/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (46592/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (53248/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (53248/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (26624/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (13312/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (146432/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (106496/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (106496/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (106496/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (13312/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (13312/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (6656/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (53248/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (106496/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9])]

def node12Piece2Output : SectorVector := [(0, node12Piece2Output_sector0)]

def node12Piece2UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2])]

def node12Piece2UnitInput_sector0 : RawPoly ℕ := [node12Piece2UnitInput_sector0_chunk0].flatten

def node12Piece2UnitInput : SectorVector := [(0, node12Piece2UnitInput_sector0)]

def node12Piece2UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (204, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (291, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (588, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (1320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (960, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (540, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (4320, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (2880, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9])]

def node12Piece2UnitOutput_sector0 : RawPoly ℕ := [node12Piece2UnitOutput_sector0_chunk0].flatten

def node12Piece2UnitOutput : SectorVector := [(0, node12Piece2UnitOutput_sector0)]

theorem node12Piece2_check : VectorCertificate (neutralBoundS JR (-3) node12Piece2UnitInput) node12Piece2UnitOutput := by decide +kernel

theorem node12Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece2Input) = evaluate node12Piece2Output :=
  mode_of_scaled _ _ (1664/945) node12Piece2UnitInput node12Piece2UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece2_check)

def node12Piece3Input_sector0 : RawPoly ℕ := [(9088/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5])]

def node12Piece3Input : SectorVector := [(0, node12Piece3Input_sector0)]
def node12Piece3Output_sector0 : RawPoly ℕ := [(36352/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (18176/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (36352/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (72704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (72704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (72704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (472576/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (36352/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (72704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1026944/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (1563136/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (36352/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-290816/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (36352/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (72704/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (72704/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (72704/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (436224/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (36352/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (290816/35, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (290816/35, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (145408/35, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (290816/7, [1, 1, 1, 1, 1, 1, 1, 13]), (290816/15, [1, 1, 1, 1, 1, 1, 5, 9])]

def node12Piece3Output : SectorVector := [(0, node12Piece3Output_sector0)]

def node12Piece3UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5])]

def node12Piece3UnitInput_sector0 : RawPoly ℕ := [node12Piece3UnitInput_sector0_chunk0].flatten

def node12Piece3UnitInput : SectorVector := [(0, node12Piece3UnitInput_sector0)]

def node12Piece3UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (156, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (339, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1080, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (1296, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (540, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (864, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (864, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (432, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (4320, [1, 1, 1, 1, 1, 1, 1, 13]), (2016, [1, 1, 1, 1, 1, 1, 5, 9])]

def node12Piece3UnitOutput_sector0 : RawPoly ℕ := [node12Piece3UnitOutput_sector0_chunk0].flatten

def node12Piece3UnitOutput : SectorVector := [(0, node12Piece3UnitOutput_sector0)]

theorem node12Piece3_check : VectorCertificate (neutralBoundS JR (-3) node12Piece3UnitInput) node12Piece3UnitOutput := by decide +kernel

theorem node12Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece3Input) = evaluate node12Piece3Output :=
  mode_of_scaled _ _ (9088/945) node12Piece3UnitInput node12Piece3UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece3_check)

def node12Piece4Input_sector0 : RawPoly ℕ := [(64/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4])]

def node12Piece4Input : SectorVector := [(0, node12Piece4Input_sector0)]
def node12Piece4Output_sector0_chunk0 : RawPoly ℕ := [(256/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (128, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (4864, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (5696, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (11008/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (256, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (7296, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (4096, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (2048, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (2048, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (26624, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (16384, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (8192, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6])]

def node12Piece4Output_sector0_chunk1 : RawPoly ℕ := [(8192, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (32768, [1, 1, 1, 1, 1, 1, 1, 13]), (14336, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (14336, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (7168, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (57344, [1, 1, 1, 1, 1, 1, 2, 12]), (28672, [1, 1, 1, 1, 1, 1, 4, 10]), (28672, [1, 1, 1, 1, 1, 2, 4, 9])]

def node12Piece4Output_sector0 : RawPoly ℕ := [node12Piece4Output_sector0_chunk0, node12Piece4Output_sector0_chunk1].flatten

def node12Piece4Output : SectorVector := [(0, node12Piece4Output_sector0)]

def node12Piece4UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4])]

def node12Piece4UnitInput_sector0 : RawPoly ℕ := [node12Piece4UnitInput_sector0_chunk0].flatten

def node12Piece4UnitInput : SectorVector := [(0, node12Piece4UnitInput_sector0)]

def node12Piece4UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (228, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (267, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (172, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (12, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (342, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1248, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (384, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6])]

def node12Piece4UnitOutput_sector0_chunk1 : RawPoly ℕ := [(384, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (1536, [1, 1, 1, 1, 1, 1, 1, 13]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (336, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (2688, [1, 1, 1, 1, 1, 1, 2, 12]), (1344, [1, 1, 1, 1, 1, 1, 4, 10]), (1344, [1, 1, 1, 1, 1, 2, 4, 9])]

def node12Piece4UnitOutput_sector0 : RawPoly ℕ := [node12Piece4UnitOutput_sector0_chunk0, node12Piece4UnitOutput_sector0_chunk1].flatten

def node12Piece4UnitOutput : SectorVector := [(0, node12Piece4UnitOutput_sector0)]

theorem node12Piece4_check : VectorCertificate (neutralBoundS JR (-3) node12Piece4UnitInput) node12Piece4UnitOutput := by decide +kernel

theorem node12Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece4Input) = evaluate node12Piece4Output :=
  mode_of_scaled _ _ (64/3) node12Piece4UnitInput node12Piece4UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece4_check)

def node12Piece5Input_sector0 : RawPoly ℕ := [(-256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3])]

def node12Piece5Input : SectorVector := [(0, node12Piece5Input_sector0)]
def node12Piece5Output_sector0_chunk0 : RawPoly ℕ := [(-1024/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (-512/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (-2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (-4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (-19456/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (-2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (-2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (-28928/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (-31744/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (-4096/3, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (-6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (-3072/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (-8192/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (-32768/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-106496/21, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-16384/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-49152/7, [1, 1, 1, 1, 1, 1, 1, 13]), (-8192/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-8192/3, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-4096/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4])]

def node12Piece5Output_sector0_chunk1 : RawPoly ℕ := [(-16384, [1, 1, 1, 1, 1, 1, 3, 11]), (-16384/3, [1, 1, 1, 1, 1, 3, 3, 9])]

def node12Piece5Output_sector0 : RawPoly ℕ := [node12Piece5Output_sector0_chunk0, node12Piece5Output_sector0_chunk1].flatten

def node12Piece5Output : SectorVector := [(0, node12Piece5Output_sector0)]

def node12Piece5UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3])]

def node12Piece5UnitInput_sector0 : RawPoly ℕ := [node12Piece5UnitInput_sector0_chunk0].flatten

def node12Piece5UnitInput : SectorVector := [(0, node12Piece5UnitInput_sector0)]

def node12Piece5UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (144, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (228, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (339, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (124, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (336, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (216, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (108, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (1152, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1248, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1152, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (576, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (1728, [1, 1, 1, 1, 1, 1, 1, 13]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (672, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (336, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4])]

def node12Piece5UnitOutput_sector0_chunk1 : RawPoly ℕ := [(4032, [1, 1, 1, 1, 1, 1, 3, 11]), (1344, [1, 1, 1, 1, 1, 3, 3, 9])]

def node12Piece5UnitOutput_sector0 : RawPoly ℕ := [node12Piece5UnitOutput_sector0_chunk0, node12Piece5UnitOutput_sector0_chunk1].flatten

def node12Piece5UnitOutput : SectorVector := [(0, node12Piece5UnitOutput_sector0)]

theorem node12Piece5_check : VectorCertificate (neutralBoundS JR (-3) node12Piece5UnitInput) node12Piece5UnitOutput := by decide +kernel

theorem node12Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece5Input) = evaluate node12Piece5Output :=
  mode_of_scaled _ _ (-256/63) node12Piece5UnitInput node12Piece5UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece5_check)

def node12Piece6Input_sector0 : RawPoly ℕ := [(64/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3])]

def node12Piece6Input : SectorVector := [(0, node12Piece6Input_sector0)]
def node12Piece6Output_sector0_chunk0 : RawPoly ℕ := [(256/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (128/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (256/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (1024/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (5120/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (256/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (256/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (6208/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (9472/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (5888/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1792/3, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (1024/21, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 13]), (256/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (512, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (3584/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7])]

def node12Piece6Output_sector0_chunk1 : RawPoly ℕ := [(512, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (256, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (2048/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (2048/3, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (2048, [1, 1, 1, 1, 1, 1, 2, 12]), (2048/3, [1, 1, 1, 1, 1, 1, 3, 11]), (512, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (512, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (256, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (1536, [1, 1, 1, 1, 1, 2, 2, 11]), (2048, [1, 1, 1, 1, 1, 2, 3, 10]), (2560/3, [1, 1, 1, 1, 2, 2, 3, 9])]

def node12Piece6Output_sector0 : RawPoly ℕ := [node12Piece6Output_sector0_chunk0, node12Piece6Output_sector0_chunk1].flatten

def node12Piece6Output : SectorVector := [(0, node12Piece6Output_sector0)]

def node12Piece6UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3])]

def node12Piece6UnitInput_sector0 : RawPoly ℕ := [node12Piece6UnitInput_sector0_chunk0].flatten

def node12Piece6UnitInput : SectorVector := [(0, node12Piece6UnitInput_sector0)]

def node12Piece6UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (48, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (288, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (291, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (148, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (276, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (588, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (288, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (288, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (96, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (96, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (288, [1, 1, 1, 1, 1, 1, 1, 13]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (504, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (1176, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7])]

def node12Piece6UnitOutput_sector0_chunk1 : RawPoly ℕ := [(504, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (252, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (672, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (2016, [1, 1, 1, 1, 1, 1, 2, 12]), (672, [1, 1, 1, 1, 1, 1, 3, 11]), (504, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (504, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (252, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (1512, [1, 1, 1, 1, 1, 2, 2, 11]), (2016, [1, 1, 1, 1, 1, 2, 3, 10]), (840, [1, 1, 1, 1, 2, 2, 3, 9])]

def node12Piece6UnitOutput_sector0 : RawPoly ℕ := [node12Piece6UnitOutput_sector0_chunk0, node12Piece6UnitOutput_sector0_chunk1].flatten

def node12Piece6UnitOutput : SectorVector := [(0, node12Piece6UnitOutput_sector0)]

theorem node12Piece6_check : VectorCertificate (neutralBoundS JR (-3) node12Piece6UnitInput) node12Piece6UnitOutput := by decide +kernel

theorem node12Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece6Input) = evaluate node12Piece6Output :=
  mode_of_scaled _ _ (64/63) node12Piece6UnitInput node12Piece6UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece6_check)

def node12Piece7Input_sector0 : RawPoly ℕ := [(64/7, [1, 1, 1, 1, 1, 1, 1, 7])]

def node12Piece7Input : SectorVector := [(0, node12Piece7Input_sector0)]
def node12Piece7Output_sector0_chunk0 : RawPoly ℕ := [(256/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (384/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (15360/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (21696/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (11008/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (768, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-20736, [1, 1, 1, 1, 1, 1, 1, 13]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (10752, [1, 1, 1, 1, 1, 1, 2, 12]), (10752, [1, 1, 1, 1, 1, 1, 3, 11]), (10752, [1, 1, 1, 1, 1, 1, 4, 10]), (10752, [1, 1, 1, 1, 1, 1, 5, 9]), (10752, [1, 1, 1, 1, 1, 1, 6, 8]), (5376, [1, 1, 1, 1, 1, 1, 7, 7])]

def node12Piece7Output_sector0_chunk1 : RawPoly ℕ := [(4608, [1, 1, 1, 1, 1, 2, 6, 7]), (4608, [1, 1, 1, 1, 1, 3, 5, 7]), (2304, [1, 1, 1, 1, 1, 4, 4, 7]), (32256, [1, 1, 1, 1, 1, 15]), (7680, [1, 1, 1, 1, 7, 9])]

def node12Piece7Output_sector0 : RawPoly ℕ := [node12Piece7Output_sector0_chunk0, node12Piece7Output_sector0_chunk1].flatten

def node12Piece7Output : SectorVector := [(0, node12Piece7Output_sector0)]

def node12Piece7UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 1, 7])]

def node12Piece7UnitInput_sector0 : RawPoly ℕ := [node12Piece7UnitInput_sector0_chunk0].flatten

def node12Piece7UnitInput : SectorVector := [(0, node12Piece7UnitInput_sector0)]

def node12Piece7UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (168, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (240, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (84, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (84, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (168, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (339, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (172, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (168, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (84, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (84, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-2268, [1, 1, 1, 1, 1, 1, 1, 13]), (84, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (1176, [1, 1, 1, 1, 1, 1, 2, 12]), (1176, [1, 1, 1, 1, 1, 1, 3, 11]), (1176, [1, 1, 1, 1, 1, 1, 4, 10]), (1176, [1, 1, 1, 1, 1, 1, 5, 9]), (1176, [1, 1, 1, 1, 1, 1, 6, 8]), (588, [1, 1, 1, 1, 1, 1, 7, 7])]

def node12Piece7UnitOutput_sector0_chunk1 : RawPoly ℕ := [(504, [1, 1, 1, 1, 1, 2, 6, 7]), (504, [1, 1, 1, 1, 1, 3, 5, 7]), (252, [1, 1, 1, 1, 1, 4, 4, 7]), (3528, [1, 1, 1, 1, 1, 15]), (840, [1, 1, 1, 1, 7, 9])]

def node12Piece7UnitOutput_sector0 : RawPoly ℕ := [node12Piece7UnitOutput_sector0_chunk0, node12Piece7UnitOutput_sector0_chunk1].flatten

def node12Piece7UnitOutput : SectorVector := [(0, node12Piece7UnitOutput_sector0)]

theorem node12Piece7_check : VectorCertificate (neutralBoundS JR (-3) node12Piece7UnitInput) node12Piece7UnitOutput := by decide +kernel

theorem node12Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece7Input) = evaluate node12Piece7Output :=
  mode_of_scaled _ _ (64/7) node12Piece7UnitInput node12Piece7UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece7_check)

def node12Piece8Input_sector0 : RawPoly ℕ := [(40/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2])]

def node12Piece8Input : SectorVector := [(0, node12Piece8Input_sector0)]
def node12Piece8Output_sector0 : RawPoly ℕ := [(160/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (80, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (1280, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (2560, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (7680, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (3240, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (6880/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (10560, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (7680, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (7680, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (3840, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (10240, [1, 1, 1, 1, 1, 1, 2, 12]), (960, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (14400, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (15360, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (15360, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (46080, [1, 1, 1, 1, 1, 2, 2, 11]), (4800, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (4800, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (2400, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (38400, [1, 1, 1, 1, 2, 2, 2, 10]), (6400, [1, 1, 1, 2, 2, 2, 2, 9])]

def node12Piece8Output : SectorVector := [(0, node12Piece8Output_sector0)]

def node12Piece8UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2])]

def node12Piece8UnitInput_sector0 : RawPoly ℕ := [node12Piece8UnitInput_sector0_chunk0].flatten

def node12Piece8UnitInput : SectorVector := [(0, node12Piece8UnitInput_sector0)]

def node12Piece8UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (252, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (192, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (576, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (243, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (172, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (792, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (576, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (576, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (288, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (768, [1, 1, 1, 1, 1, 1, 2, 12]), (72, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (1080, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (1152, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (1152, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (3456, [1, 1, 1, 1, 1, 2, 2, 11]), (360, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (360, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (180, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (2880, [1, 1, 1, 1, 2, 2, 2, 10]), (480, [1, 1, 1, 2, 2, 2, 2, 9])]

def node12Piece8UnitOutput_sector0 : RawPoly ℕ := [node12Piece8UnitOutput_sector0_chunk0].flatten

def node12Piece8UnitOutput : SectorVector := [(0, node12Piece8UnitOutput_sector0)]

theorem node12Piece8_check : VectorCertificate (neutralBoundS JR (-3) node12Piece8UnitInput) node12Piece8UnitOutput := by decide +kernel

theorem node12Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece8Input) = evaluate node12Piece8Output :=
  mode_of_scaled _ _ (40/3) node12Piece8UnitInput node12Piece8UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece8_check)

def node12Piece9Input_sector0 : RawPoly ℕ := [(32/3, [1, 1, 1, 1, 1, 1, 2, 6])]

def node12Piece9Input : SectorVector := [(0, node12Piece9Input_sector0)]
def node12Piece9Output_sector0_chunk0 : RawPoly ℕ := [(128/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (64, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (256, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (2688, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (3072, [1, 1, 1, 1, 1, 1, 1, 13]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (1536, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (3360, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (5504/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (1536, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (256, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-13120, [1, 1, 1, 1, 1, 1, 2, 12]), (3072, [1, 1, 1, 1, 1, 1, 3, 11]), (3072, [1, 1, 1, 1, 1, 1, 4, 10]), (3072, [1, 1, 1, 1, 1, 1, 5, 9]), (3648, [1, 1, 1, 1, 1, 1, 6, 8]), (1536, [1, 1, 1, 1, 1, 1, 7, 7]), (768, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6])]

def node12Piece9Output_sector0_chunk1 : RawPoly ℕ := [(9216, [1, 1, 1, 1, 1, 2, 2, 11]), (9216, [1, 1, 1, 1, 1, 2, 3, 10]), (9216, [1, 1, 1, 1, 1, 2, 4, 9]), (9216, [1, 1, 1, 1, 1, 2, 5, 8]), (11520, [1, 1, 1, 1, 1, 2, 6, 7]), (3072, [1, 1, 1, 1, 1, 3, 6, 6]), (3072, [1, 1, 1, 1, 1, 4, 5, 6]), (18432, [1, 1, 1, 1, 1, 15]), (3840, [1, 1, 1, 1, 2, 2, 6, 6]), (3840, [1, 1, 1, 1, 2, 3, 5, 6]), (1920, [1, 1, 1, 1, 2, 4, 4, 6]), (23040, [1, 1, 1, 1, 2, 14]), (7680, [1, 1, 1, 1, 6, 10]), (5120, [1, 1, 1, 2, 6, 9])]

def node12Piece9Output_sector0 : RawPoly ℕ := [node12Piece9Output_sector0_chunk0, node12Piece9Output_sector0_chunk1].flatten

def node12Piece9Output : SectorVector := [(0, node12Piece9Output_sector0)]

def node12Piece9UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 2, 6])]

def node12Piece9UnitInput_sector0 : RawPoly ℕ := [node12Piece9UnitInput_sector0_chunk0].flatten

def node12Piece9UnitInput : SectorVector := [(0, node12Piece9UnitInput_sector0)]

def node12Piece9UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (72, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (24, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (144, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (144, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (144, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (252, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (48, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (288, [1, 1, 1, 1, 1, 1, 1, 13]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (144, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (315, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (172, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (144, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (24, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-1230, [1, 1, 1, 1, 1, 1, 2, 12]), (288, [1, 1, 1, 1, 1, 1, 3, 11]), (288, [1, 1, 1, 1, 1, 1, 4, 10]), (288, [1, 1, 1, 1, 1, 1, 5, 9]), (342, [1, 1, 1, 1, 1, 1, 6, 8]), (144, [1, 1, 1, 1, 1, 1, 7, 7]), (72, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6])]

def node12Piece9UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [1, 1, 1, 1, 1, 2, 2, 11]), (864, [1, 1, 1, 1, 1, 2, 3, 10]), (864, [1, 1, 1, 1, 1, 2, 4, 9]), (864, [1, 1, 1, 1, 1, 2, 5, 8]), (1080, [1, 1, 1, 1, 1, 2, 6, 7]), (288, [1, 1, 1, 1, 1, 3, 6, 6]), (288, [1, 1, 1, 1, 1, 4, 5, 6]), (1728, [1, 1, 1, 1, 1, 15]), (360, [1, 1, 1, 1, 2, 2, 6, 6]), (360, [1, 1, 1, 1, 2, 3, 5, 6]), (180, [1, 1, 1, 1, 2, 4, 4, 6]), (2160, [1, 1, 1, 1, 2, 14]), (720, [1, 1, 1, 1, 6, 10]), (480, [1, 1, 1, 2, 6, 9])]

def node12Piece9UnitOutput_sector0 : RawPoly ℕ := [node12Piece9UnitOutput_sector0_chunk0, node12Piece9UnitOutput_sector0_chunk1].flatten

def node12Piece9UnitOutput : SectorVector := [(0, node12Piece9UnitOutput_sector0)]

theorem node12Piece9_check : VectorCertificate (neutralBoundS JR (-3) node12Piece9UnitInput) node12Piece9UnitOutput := by decide +kernel

theorem node12Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece9Input) = evaluate node12Piece9Output :=
  mode_of_scaled _ _ (32/3) node12Piece9UnitInput node12Piece9UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece9_check)

def node12Piece10Input_sector0 : RawPoly ℕ := [(-2432/45, [1, 1, 1, 1, 1, 1, 3, 5])]

def node12Piece10Input : SectorVector := [(0, node12Piece10Input_sector0)]
def node12Piece10Output_sector0_chunk0 : RawPoly ℕ := [(-9728/45, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (-4864/15, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (-9728/3, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-9728/5, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (-19456/3, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-19456/5, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-19456/3, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-19456/3, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-155648/15, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-9728/5, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-19456, [1, 1, 1, 1, 1, 1, 1, 13]), (-9728/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-9728/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (-19456/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-274816/15, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-19456, [1, 1, 1, 1, 1, 1, 2, 12]), (-359936/45, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-9728/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (77824/3, [1, 1, 1, 1, 1, 1, 3, 11]), (-19456, [1, 1, 1, 1, 1, 1, 4, 10]), (-223744/15, [1, 1, 1, 1, 1, 1, 5, 9]), (-19456, [1, 1, 1, 1, 1, 1, 6, 8]), (-9728, [1, 1, 1, 1, 1, 1, 7, 7]), (-19456/5, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5])]

def node12Piece10Output_sector0_chunk1 : RawPoly ℕ := [(-38912, [1, 1, 1, 1, 1, 2, 3, 10]), (-116736/5, [1, 1, 1, 1, 1, 2, 5, 8]), (-38912, [1, 1, 1, 1, 1, 3, 3, 9]), (-38912, [1, 1, 1, 1, 1, 3, 4, 8]), (-58368, [1, 1, 1, 1, 1, 3, 5, 7]), (-19456, [1, 1, 1, 1, 1, 3, 6, 6]), (-116736/5, [1, 1, 1, 1, 1, 4, 5, 6]), (-58368/5, [1, 1, 1, 1, 1, 5, 5, 5]), (-116736, [1, 1, 1, 1, 1, 15]), (-19456, [1, 1, 1, 1, 2, 3, 5, 6]), (-19456, [1, 1, 1, 1, 3, 3, 5, 5]), (-9728, [1, 1, 1, 1, 3, 4, 4, 5]), (-97280, [1, 1, 1, 1, 3, 13]), (-58368, [1, 1, 1, 1, 5, 11]), (-77824/3, [1, 1, 1, 3, 5, 9])]

def node12Piece10Output_sector0 : RawPoly ℕ := [node12Piece10Output_sector0_chunk0, node12Piece10Output_sector0_chunk1].flatten

def node12Piece10Output : SectorVector := [(0, node12Piece10Output_sector0)]

def node12Piece10UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 3, 5])]

def node12Piece10UnitInput_sector0 : RawPoly ℕ := [node12Piece10UnitInput_sector0_chunk0].flatten

def node12Piece10UnitInput : SectorVector := [(0, node12Piece10UnitInput_sector0)]

def node12Piece10UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (72, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (120, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (192, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (36, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (360, [1, 1, 1, 1, 1, 1, 1, 13]), (60, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (36, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (120, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (339, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (360, [1, 1, 1, 1, 1, 1, 2, 12]), (148, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-480, [1, 1, 1, 1, 1, 1, 3, 11]), (360, [1, 1, 1, 1, 1, 1, 4, 10]), (276, [1, 1, 1, 1, 1, 1, 5, 9]), (360, [1, 1, 1, 1, 1, 1, 6, 8]), (180, [1, 1, 1, 1, 1, 1, 7, 7]), (72, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5])]

def node12Piece10UnitOutput_sector0_chunk1 : RawPoly ℕ := [(720, [1, 1, 1, 1, 1, 2, 3, 10]), (432, [1, 1, 1, 1, 1, 2, 5, 8]), (720, [1, 1, 1, 1, 1, 3, 3, 9]), (720, [1, 1, 1, 1, 1, 3, 4, 8]), (1080, [1, 1, 1, 1, 1, 3, 5, 7]), (360, [1, 1, 1, 1, 1, 3, 6, 6]), (432, [1, 1, 1, 1, 1, 4, 5, 6]), (216, [1, 1, 1, 1, 1, 5, 5, 5]), (2160, [1, 1, 1, 1, 1, 15]), (360, [1, 1, 1, 1, 2, 3, 5, 6]), (360, [1, 1, 1, 1, 3, 3, 5, 5]), (180, [1, 1, 1, 1, 3, 4, 4, 5]), (1800, [1, 1, 1, 1, 3, 13]), (1080, [1, 1, 1, 1, 5, 11]), (480, [1, 1, 1, 3, 5, 9])]

def node12Piece10UnitOutput_sector0 : RawPoly ℕ := [node12Piece10UnitOutput_sector0_chunk0, node12Piece10UnitOutput_sector0_chunk1].flatten

def node12Piece10UnitOutput : SectorVector := [(0, node12Piece10UnitOutput_sector0)]

theorem node12Piece10_check : VectorCertificate (neutralBoundS JR (-3) node12Piece10UnitInput) node12Piece10UnitOutput := by decide +kernel

theorem node12Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece10Input) = evaluate node12Piece10Output :=
  mode_of_scaled _ _ (-2432/45) node12Piece10UnitInput node12Piece10UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece10_check)

def node12Piece11Input_sector0 : RawPoly ℕ := [(-100/3, [1, 1, 1, 1, 1, 1, 4, 4])]

def node12Piece11Input : SectorVector := [(0, node12Piece11Input_sector0)]
def node12Piece11Output_sector0_chunk0 : RawPoly ℕ := [(-400/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-200, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (-3200, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (-6400, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-6400, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-8400, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-12800, [1, 1, 1, 1, 1, 1, 1, 13]), (-3200, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-6400, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-8100, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-12800, [1, 1, 1, 1, 1, 1, 2, 12]), (-17200/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-12800, [1, 1, 1, 1, 1, 1, 3, 11]), (12000, [1, 1, 1, 1, 1, 1, 4, 10]), (-12800, [1, 1, 1, 1, 1, 1, 5, 9]), (-12800, [1, 1, 1, 1, 1, 1, 6, 8]), (-6400, [1, 1, 1, 1, 1, 1, 7, 7]), (-2400, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-38400, [1, 1, 1, 1, 1, 2, 4, 9]), (-38400, [1, 1, 1, 1, 1, 3, 4, 8]), (-36000, [1, 1, 1, 1, 1, 4, 4, 7]), (-38400, [1, 1, 1, 1, 1, 4, 5, 6]), (-76800, [1, 1, 1, 1, 1, 15]), (-12000, [1, 1, 1, 1, 2, 4, 4, 6])]

def node12Piece11Output_sector0_chunk1 : RawPoly ℕ := [(-12000, [1, 1, 1, 1, 3, 4, 4, 5]), (-6000, [1, 1, 1, 1, 4, 4, 4, 4]), (-96000, [1, 1, 1, 1, 4, 12]), (-16000, [1, 1, 1, 4, 4, 9])]

def node12Piece11Output_sector0 : RawPoly ℕ := [node12Piece11Output_sector0_chunk0, node12Piece11Output_sector0_chunk1].flatten

def node12Piece11Output : SectorVector := [(0, node12Piece11Output_sector0)]

def node12Piece11UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 1, 4, 4])]

def node12Piece11UnitInput_sector0 : RawPoly ℕ := [node12Piece11UnitInput_sector0_chunk0].flatten

def node12Piece11UnitInput : SectorVector := [(0, node12Piece11UnitInput_sector0)]

def node12Piece11UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (96, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (192, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (192, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (252, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (384, [1, 1, 1, 1, 1, 1, 1, 13]), (96, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (192, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (243, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (384, [1, 1, 1, 1, 1, 1, 2, 12]), (172, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (384, [1, 1, 1, 1, 1, 1, 3, 11]), (-360, [1, 1, 1, 1, 1, 1, 4, 10]), (384, [1, 1, 1, 1, 1, 1, 5, 9]), (384, [1, 1, 1, 1, 1, 1, 6, 8]), (192, [1, 1, 1, 1, 1, 1, 7, 7]), (72, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (1152, [1, 1, 1, 1, 1, 2, 4, 9]), (1152, [1, 1, 1, 1, 1, 3, 4, 8]), (1080, [1, 1, 1, 1, 1, 4, 4, 7]), (1152, [1, 1, 1, 1, 1, 4, 5, 6]), (2304, [1, 1, 1, 1, 1, 15]), (360, [1, 1, 1, 1, 2, 4, 4, 6])]

def node12Piece11UnitOutput_sector0_chunk1 : RawPoly ℕ := [(360, [1, 1, 1, 1, 3, 4, 4, 5]), (180, [1, 1, 1, 1, 4, 4, 4, 4]), (2880, [1, 1, 1, 1, 4, 12]), (480, [1, 1, 1, 4, 4, 9])]

def node12Piece11UnitOutput_sector0 : RawPoly ℕ := [node12Piece11UnitOutput_sector0_chunk0, node12Piece11UnitOutput_sector0_chunk1].flatten

def node12Piece11UnitOutput : SectorVector := [(0, node12Piece11UnitOutput_sector0)]

theorem node12Piece11_check : VectorCertificate (neutralBoundS JR (-3) node12Piece11UnitInput) node12Piece11UnitOutput := by decide +kernel

theorem node12Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece11Input) = evaluate node12Piece11Output :=
  mode_of_scaled _ _ (-100/3) node12Piece11UnitInput node12Piece11UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece11_check)

def node12Piece12Input_sector0 : RawPoly ℕ := [(592/5, [1, 1, 1, 1, 1, 2, 2, 5])]

def node12Piece12Input : SectorVector := [(0, node12Piece12Input_sector0)]
def node12Piece12Output_sector0_chunk0 : RawPoly ℕ := [(2368/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (3552/5, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (7104, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (28416/5, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (14208, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (14208, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (14208, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (120768/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (56832/5, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (56832, [1, 1, 1, 1, 1, 1, 2, 12]), (56832/5, [1, 1, 1, 1, 1, 1, 5, 9]), (7104, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (14208, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (172272/5, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (101824/5, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (7104, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-56832, [1, 1, 1, 1, 1, 2, 2, 11]), (56832, [1, 1, 1, 1, 1, 2, 3, 10]), (56832, [1, 1, 1, 1, 1, 2, 4, 9]), (348096/5, [1, 1, 1, 1, 1, 2, 5, 8]), (56832, [1, 1, 1, 1, 1, 2, 6, 7]), (56832/5, [1, 1, 1, 1, 1, 3, 5, 7]), (56832/5, [1, 1, 1, 1, 1, 4, 5, 6]), (28416/5, [1, 1, 1, 1, 1, 5, 5, 5])]

def node12Piece12Output_sector0_chunk1 : RawPoly ℕ := [(56832, [1, 1, 1, 1, 1, 15]), (7104, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (71040, [1, 1, 1, 1, 2, 2, 2, 10]), (71040, [1, 1, 1, 1, 2, 2, 3, 9]), (71040, [1, 1, 1, 1, 2, 2, 4, 8]), (113664, [1, 1, 1, 1, 2, 2, 5, 7]), (35520, [1, 1, 1, 1, 2, 2, 6, 6]), (56832, [1, 1, 1, 1, 2, 3, 5, 6]), (56832, [1, 1, 1, 1, 2, 4, 5, 5]), (284160, [1, 1, 1, 1, 2, 14]), (56832, [1, 1, 1, 1, 5, 11]), (28416, [1, 1, 1, 2, 2, 2, 5, 6]), (28416, [1, 1, 1, 2, 2, 3, 5, 5]), (14208, [1, 1, 1, 2, 2, 4, 4, 5]), (142080, [1, 1, 1, 2, 2, 13]), (113664, [1, 1, 1, 2, 5, 10]), (28416, [1, 1, 2, 2, 5, 9])]

def node12Piece12Output_sector0 : RawPoly ℕ := [node12Piece12Output_sector0_chunk0, node12Piece12Output_sector0_chunk1].flatten

def node12Piece12Output : SectorVector := [(0, node12Piece12Output_sector0)]

def node12Piece12UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 2, 2, 5])]

def node12Piece12UnitInput_sector0 : RawPoly ℕ := [node12Piece12UnitInput_sector0_chunk0].flatten

def node12Piece12UnitInput : SectorVector := [(0, node12Piece12UnitInput_sector0)]

def node12Piece12UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (6, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (60, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (48, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (120, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (120, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (120, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (204, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (96, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (480, [1, 1, 1, 1, 1, 1, 2, 12]), (96, [1, 1, 1, 1, 1, 1, 5, 9]), (60, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (120, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (291, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (172, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (60, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-480, [1, 1, 1, 1, 1, 2, 2, 11]), (480, [1, 1, 1, 1, 1, 2, 3, 10]), (480, [1, 1, 1, 1, 1, 2, 4, 9]), (588, [1, 1, 1, 1, 1, 2, 5, 8]), (480, [1, 1, 1, 1, 1, 2, 6, 7]), (96, [1, 1, 1, 1, 1, 3, 5, 7]), (96, [1, 1, 1, 1, 1, 4, 5, 6]), (48, [1, 1, 1, 1, 1, 5, 5, 5])]

def node12Piece12UnitOutput_sector0_chunk1 : RawPoly ℕ := [(480, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (600, [1, 1, 1, 1, 2, 2, 2, 10]), (600, [1, 1, 1, 1, 2, 2, 3, 9]), (600, [1, 1, 1, 1, 2, 2, 4, 8]), (960, [1, 1, 1, 1, 2, 2, 5, 7]), (300, [1, 1, 1, 1, 2, 2, 6, 6]), (480, [1, 1, 1, 1, 2, 3, 5, 6]), (480, [1, 1, 1, 1, 2, 4, 5, 5]), (2400, [1, 1, 1, 1, 2, 14]), (480, [1, 1, 1, 1, 5, 11]), (240, [1, 1, 1, 2, 2, 2, 5, 6]), (240, [1, 1, 1, 2, 2, 3, 5, 5]), (120, [1, 1, 1, 2, 2, 4, 4, 5]), (1200, [1, 1, 1, 2, 2, 13]), (960, [1, 1, 1, 2, 5, 10]), (240, [1, 1, 2, 2, 5, 9])]

def node12Piece12UnitOutput_sector0 : RawPoly ℕ := [node12Piece12UnitOutput_sector0_chunk0, node12Piece12UnitOutput_sector0_chunk1].flatten

def node12Piece12UnitOutput : SectorVector := [(0, node12Piece12UnitOutput_sector0)]

theorem node12Piece12_check : VectorCertificate (neutralBoundS JR (-3) node12Piece12UnitInput) node12Piece12UnitOutput := by decide +kernel

theorem node12Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece12Input) = evaluate node12Piece12Output :=
  mode_of_scaled _ _ (592/5) node12Piece12UnitInput node12Piece12UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece12_check)

def node12Piece13Input_sector0 : RawPoly ℕ := [(-688/3, [1, 1, 1, 1, 1, 2, 3, 4])]

def node12Piece13Input : SectorVector := [(0, node12Piece13Input_sector0)]
def node12Piece13Output_sector0_chunk0 : RawPoly ℕ := [(-2752/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-1376, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (-11008, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-8256, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-5504, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-22016, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-16512, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-22016, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-60544, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-8256, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-66048, [1, 1, 1, 1, 1, 1, 2, 12]), (-11008, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-44032, [1, 1, 1, 1, 1, 1, 3, 11]), (-33024, [1, 1, 1, 1, 1, 1, 4, 10]), (-11008, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (-8256, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-22016, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-61232, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-66048, [1, 1, 1, 1, 1, 2, 2, 11]), (-101824/3, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-2752, [1, 1, 1, 1, 1, 2, 3, 10]), (-63296, [1, 1, 1, 1, 1, 2, 4, 9]), (-66048, [1, 1, 1, 1, 1, 2, 5, 8]), (-66048, [1, 1, 1, 1, 1, 2, 6, 7])]

def node12Piece13Output_sector0_chunk1 : RawPoly ℕ := [(-44032, [1, 1, 1, 1, 1, 3, 3, 9]), (-78432, [1, 1, 1, 1, 1, 3, 4, 8]), (-44032, [1, 1, 1, 1, 1, 3, 5, 7]), (-22016, [1, 1, 1, 1, 1, 3, 6, 6]), (-33024, [1, 1, 1, 1, 1, 4, 4, 7]), (-33024, [1, 1, 1, 1, 1, 4, 5, 6]), (-132096, [1, 1, 1, 1, 1, 15]), (-13760, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-110080, [1, 1, 1, 1, 2, 2, 3, 9]), (-82560, [1, 1, 1, 1, 2, 2, 4, 8]), (-110080, [1, 1, 1, 1, 2, 3, 3, 8]), (-220160, [1, 1, 1, 1, 2, 3, 4, 7]), (-110080, [1, 1, 1, 1, 2, 3, 5, 6]), (-82560, [1, 1, 1, 1, 2, 4, 4, 6]), (-41280, [1, 1, 1, 1, 2, 4, 5, 5]), (-330240, [1, 1, 1, 1, 2, 14]), (-55040, [1, 1, 1, 1, 3, 3, 4, 6]), (-55040, [1, 1, 1, 1, 3, 4, 4, 5]), (-220160, [1, 1, 1, 1, 3, 13]), (-165120, [1, 1, 1, 1, 4, 12]), (-55040, [1, 1, 1, 2, 2, 3, 4, 6]), (-55040, [1, 1, 1, 2, 3, 3, 4, 5]), (-27520, [1, 1, 1, 2, 3, 4, 4, 4]), (-220160, [1, 1, 1, 2, 3, 12])]

def node12Piece13Output_sector0_chunk2 : RawPoly ℕ := [(-165120, [1, 1, 1, 2, 4, 11]), (-110080, [1, 1, 1, 3, 4, 10]), (-55040, [1, 1, 2, 3, 4, 9])]

def node12Piece13Output_sector0 : RawPoly ℕ := [node12Piece13Output_sector0_chunk0, node12Piece13Output_sector0_chunk1, node12Piece13Output_sector0_chunk2].flatten

def node12Piece13Output : SectorVector := [(0, node12Piece13Output_sector0)]

def node12Piece13UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 2, 3, 4])]

def node12Piece13UnitInput_sector0 : RawPoly ℕ := [node12Piece13UnitInput_sector0_chunk0].flatten

def node12Piece13UnitInput : SectorVector := [(0, node12Piece13UnitInput_sector0)]

def node12Piece13UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (6, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (48, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (36, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (24, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (72, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (96, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (264, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (36, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (288, [1, 1, 1, 1, 1, 1, 2, 12]), (48, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (192, [1, 1, 1, 1, 1, 1, 3, 11]), (144, [1, 1, 1, 1, 1, 1, 4, 10]), (48, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (36, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (96, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (267, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (288, [1, 1, 1, 1, 1, 2, 2, 11]), (148, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (12, [1, 1, 1, 1, 1, 2, 3, 10]), (276, [1, 1, 1, 1, 1, 2, 4, 9]), (288, [1, 1, 1, 1, 1, 2, 5, 8]), (288, [1, 1, 1, 1, 1, 2, 6, 7])]

def node12Piece13UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [1, 1, 1, 1, 1, 3, 3, 9]), (342, [1, 1, 1, 1, 1, 3, 4, 8]), (192, [1, 1, 1, 1, 1, 3, 5, 7]), (96, [1, 1, 1, 1, 1, 3, 6, 6]), (144, [1, 1, 1, 1, 1, 4, 4, 7]), (144, [1, 1, 1, 1, 1, 4, 5, 6]), (576, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (480, [1, 1, 1, 1, 2, 2, 3, 9]), (360, [1, 1, 1, 1, 2, 2, 4, 8]), (480, [1, 1, 1, 1, 2, 3, 3, 8]), (960, [1, 1, 1, 1, 2, 3, 4, 7]), (480, [1, 1, 1, 1, 2, 3, 5, 6]), (360, [1, 1, 1, 1, 2, 4, 4, 6]), (180, [1, 1, 1, 1, 2, 4, 5, 5]), (1440, [1, 1, 1, 1, 2, 14]), (240, [1, 1, 1, 1, 3, 3, 4, 6]), (240, [1, 1, 1, 1, 3, 4, 4, 5]), (960, [1, 1, 1, 1, 3, 13]), (720, [1, 1, 1, 1, 4, 12]), (240, [1, 1, 1, 2, 2, 3, 4, 6]), (240, [1, 1, 1, 2, 3, 3, 4, 5]), (120, [1, 1, 1, 2, 3, 4, 4, 4]), (960, [1, 1, 1, 2, 3, 12])]

def node12Piece13UnitOutput_sector0_chunk2 : RawPoly ℕ := [(720, [1, 1, 1, 2, 4, 11]), (480, [1, 1, 1, 3, 4, 10]), (240, [1, 1, 2, 3, 4, 9])]

def node12Piece13UnitOutput_sector0 : RawPoly ℕ := [node12Piece13UnitOutput_sector0_chunk0, node12Piece13UnitOutput_sector0_chunk1, node12Piece13UnitOutput_sector0_chunk2].flatten

def node12Piece13UnitOutput : SectorVector := [(0, node12Piece13UnitOutput_sector0)]

theorem node12Piece13_check : VectorCertificate (neutralBoundS JR (-3) node12Piece13UnitInput) node12Piece13UnitOutput := by decide +kernel

theorem node12Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece13Input) = evaluate node12Piece13Output :=
  mode_of_scaled _ _ (-688/3) node12Piece13UnitInput node12Piece13UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece13_check)

def node12Piece14Input_sector0 : RawPoly ℕ := [(-2368/27, [1, 1, 1, 1, 1, 3, 3, 3])]

def node12Piece14Input : SectorVector := [(0, node12Piece14Input_sector0)]
def node12Piece14Output_sector0_chunk0 : RawPoly ℕ := [(-9472/27, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (-4736/9, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (-9472, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-18944, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-208384/9, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-9472, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-56832, [1, 1, 1, 1, 1, 1, 3, 11]), (-9472, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-267584/9, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-56832, [1, 1, 1, 1, 1, 2, 3, 10]), (-236800/27, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (-47360/3, [1, 1, 1, 1, 1, 3, 3, 9]), (-56832, [1, 1, 1, 1, 1, 3, 4, 8]), (-56832, [1, 1, 1, 1, 1, 3, 5, 7]), (-28416, [1, 1, 1, 1, 1, 3, 6, 6]), (-56832, [1, 1, 1, 1, 1, 15]), (-47360/9, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (-94720, [1, 1, 1, 1, 2, 3, 3, 8]), (-757760/9, [1, 1, 1, 1, 3, 3, 3, 7]), (-94720, [1, 1, 1, 1, 3, 3, 4, 6]), (-47360, [1, 1, 1, 1, 3, 3, 5, 5]), (-284160, [1, 1, 1, 1, 3, 13]), (-189440/9, [1, 1, 1, 2, 3, 3, 3, 6]), (-189440/9, [1, 1, 1, 3, 3, 3, 3, 5])]

def node12Piece14Output_sector0_chunk1 : RawPoly ℕ := [(-94720/9, [1, 1, 1, 3, 3, 3, 4, 4]), (-189440, [1, 1, 1, 3, 3, 11]), (-189440/9, [1, 1, 3, 3, 3, 9])]

def node12Piece14Output_sector0 : RawPoly ℕ := [node12Piece14Output_sector0_chunk0, node12Piece14Output_sector0_chunk1].flatten

def node12Piece14Output : SectorVector := [(0, node12Piece14Output_sector0)]

def node12Piece14UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 3, 3, 3])]

def node12Piece14UnitInput_sector0 : RawPoly ℕ := [node12Piece14UnitInput_sector0_chunk0].flatten

def node12Piece14UnitInput : SectorVector := [(0, node12Piece14UnitInput_sector0)]

def node12Piece14UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (6, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (108, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (216, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (264, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (108, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (648, [1, 1, 1, 1, 1, 1, 3, 11]), (108, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (339, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (648, [1, 1, 1, 1, 1, 2, 3, 10]), (100, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (180, [1, 1, 1, 1, 1, 3, 3, 9]), (648, [1, 1, 1, 1, 1, 3, 4, 8]), (648, [1, 1, 1, 1, 1, 3, 5, 7]), (324, [1, 1, 1, 1, 1, 3, 6, 6]), (648, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (1080, [1, 1, 1, 1, 2, 3, 3, 8]), (960, [1, 1, 1, 1, 3, 3, 3, 7]), (1080, [1, 1, 1, 1, 3, 3, 4, 6]), (540, [1, 1, 1, 1, 3, 3, 5, 5]), (3240, [1, 1, 1, 1, 3, 13]), (240, [1, 1, 1, 2, 3, 3, 3, 6]), (240, [1, 1, 1, 3, 3, 3, 3, 5])]

def node12Piece14UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 1, 1, 3, 3, 3, 4, 4]), (2160, [1, 1, 1, 3, 3, 11]), (240, [1, 1, 3, 3, 3, 9])]

def node12Piece14UnitOutput_sector0 : RawPoly ℕ := [node12Piece14UnitOutput_sector0_chunk0, node12Piece14UnitOutput_sector0_chunk1].flatten

def node12Piece14UnitOutput : SectorVector := [(0, node12Piece14UnitOutput_sector0)]

theorem node12Piece14_check : VectorCertificate (neutralBoundS JR (-3) node12Piece14UnitInput) node12Piece14UnitOutput := by decide +kernel

theorem node12Piece14_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece14Input) = evaluate node12Piece14Output :=
  mode_of_scaled _ _ (-2368/27) node12Piece14UnitInput node12Piece14UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece14_check)

def node12Piece15Input_sector0 : RawPoly ℕ := [(-208/3, [1, 1, 1, 1, 1, 9])]

def node12Piece15Input : SectorVector := [(0, node12Piece15Input_sector0)]
def node12Piece15Output_sector0_chunk0 : RawPoly ℕ := [(-832/3, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-416, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (-7488, [1, 1, 1, 1, 1, 1, 1, 13]), (-14976, [1, 1, 1, 1, 1, 1, 2, 12]), (-14976, [1, 1, 1, 1, 1, 1, 3, 11]), (-14976, [1, 1, 1, 1, 1, 1, 4, 10]), (-18304, [1, 1, 1, 1, 1, 1, 5, 9]), (-14976, [1, 1, 1, 1, 1, 1, 6, 8]), (-7488, [1, 1, 1, 1, 1, 1, 7, 7]), (-7488, [1, 1, 1, 1, 1, 2, 2, 11]), (-14976, [1, 1, 1, 1, 1, 2, 3, 10]), (-23504, [1, 1, 1, 1, 1, 2, 4, 9]), (-14976, [1, 1, 1, 1, 1, 2, 5, 8]), (-14976, [1, 1, 1, 1, 1, 2, 6, 7]), (-35776/3, [1, 1, 1, 1, 1, 3, 3, 9]), (-14976, [1, 1, 1, 1, 1, 3, 4, 8]), (-14976, [1, 1, 1, 1, 1, 3, 5, 7]), (-7488, [1, 1, 1, 1, 1, 3, 6, 6]), (-7488, [1, 1, 1, 1, 1, 4, 4, 7]), (-14976, [1, 1, 1, 1, 1, 4, 5, 6]), (-2496, [1, 1, 1, 1, 1, 5, 5, 5]), (369408, [1, 1, 1, 1, 1, 15]), (-4160, [1, 1, 1, 1, 2, 2, 3, 9]), (-74880, [1, 1, 1, 1, 2, 14])]

def node12Piece15Output_sector0_chunk1 : RawPoly ℕ := [(-74880, [1, 1, 1, 1, 3, 13]), (-74880, [1, 1, 1, 1, 4, 12]), (-74880, [1, 1, 1, 1, 5, 11]), (-74880, [1, 1, 1, 1, 6, 10]), (-66560, [1, 1, 1, 1, 7, 9]), (-37440, [1, 1, 1, 1, 8, 8]), (-16640, [1, 1, 1, 2, 6, 9]), (-16640, [1, 1, 1, 3, 5, 9]), (-8320, [1, 1, 1, 4, 4, 9]), (-149760, [1, 1, 1, 17]), (-16640, [1, 1, 9, 9])]

def node12Piece15Output_sector0 : RawPoly ℕ := [node12Piece15Output_sector0_chunk0, node12Piece15Output_sector0_chunk1].flatten

def node12Piece15Output : SectorVector := [(0, node12Piece15Output_sector0)]

def node12Piece15UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 9])]

def node12Piece15UnitInput_sector0 : RawPoly ℕ := [node12Piece15UnitInput_sector0_chunk0].flatten

def node12Piece15UnitInput : SectorVector := [(0, node12Piece15UnitInput_sector0)]

def node12Piece15UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (6, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (108, [1, 1, 1, 1, 1, 1, 1, 13]), (216, [1, 1, 1, 1, 1, 1, 2, 12]), (216, [1, 1, 1, 1, 1, 1, 3, 11]), (216, [1, 1, 1, 1, 1, 1, 4, 10]), (264, [1, 1, 1, 1, 1, 1, 5, 9]), (216, [1, 1, 1, 1, 1, 1, 6, 8]), (108, [1, 1, 1, 1, 1, 1, 7, 7]), (108, [1, 1, 1, 1, 1, 2, 2, 11]), (216, [1, 1, 1, 1, 1, 2, 3, 10]), (339, [1, 1, 1, 1, 1, 2, 4, 9]), (216, [1, 1, 1, 1, 1, 2, 5, 8]), (216, [1, 1, 1, 1, 1, 2, 6, 7]), (172, [1, 1, 1, 1, 1, 3, 3, 9]), (216, [1, 1, 1, 1, 1, 3, 4, 8]), (216, [1, 1, 1, 1, 1, 3, 5, 7]), (108, [1, 1, 1, 1, 1, 3, 6, 6]), (108, [1, 1, 1, 1, 1, 4, 4, 7]), (216, [1, 1, 1, 1, 1, 4, 5, 6]), (36, [1, 1, 1, 1, 1, 5, 5, 5]), (-5328, [1, 1, 1, 1, 1, 15]), (60, [1, 1, 1, 1, 2, 2, 3, 9]), (1080, [1, 1, 1, 1, 2, 14])]

def node12Piece15UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1080, [1, 1, 1, 1, 3, 13]), (1080, [1, 1, 1, 1, 4, 12]), (1080, [1, 1, 1, 1, 5, 11]), (1080, [1, 1, 1, 1, 6, 10]), (960, [1, 1, 1, 1, 7, 9]), (540, [1, 1, 1, 1, 8, 8]), (240, [1, 1, 1, 2, 6, 9]), (240, [1, 1, 1, 3, 5, 9]), (120, [1, 1, 1, 4, 4, 9]), (2160, [1, 1, 1, 17]), (240, [1, 1, 9, 9])]

def node12Piece15UnitOutput_sector0 : RawPoly ℕ := [node12Piece15UnitOutput_sector0_chunk0, node12Piece15UnitOutput_sector0_chunk1].flatten

def node12Piece15UnitOutput : SectorVector := [(0, node12Piece15UnitOutput_sector0)]

theorem node12Piece15_check : VectorCertificate (neutralBoundS JR (-3) node12Piece15UnitInput) node12Piece15UnitOutput := by decide +kernel

theorem node12Piece15_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece15Input) = evaluate node12Piece15Output :=
  mode_of_scaled _ _ (-208/3) node12Piece15UnitInput node12Piece15UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece15_check)

end VOA.Classification.COne.OrbC2h
