import VOA.Classification.COne.OrbC2hStateNode25
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

def node27Piece0Input_sector0 : RawPoly ℕ := [(288/7, [1, 1, 1, 1, 1, 1, 1, 2])]

def node27Piece0Input : SectorVector := [(0, node27Piece0Input_sector0)]
def node27Piece0Output_sector0_chunk0 : RawPoly ℕ := [(1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (6912/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (6912/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (17280/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (13824/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (13824/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (13824/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (6912/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (3456/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (46080/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (61632/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (67392/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (70272/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (6912/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (13824/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (6912/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5])]

def node27Piece0Output_sector0_chunk1 : RawPoly ℕ := [(6912/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-6912, [1, 1, 1, 1, 1, 1, 1, 13]), (3456, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (6912, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (6912, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (3456, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (3456, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (6912, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (1152, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-17856, [1, 1, 1, 1, 1, 1, 2, 12]), (13824, [1, 1, 1, 1, 1, 1, 3, 11]), (13824, [1, 1, 1, 1, 1, 1, 4, 10]), (13824, [1, 1, 1, 1, 1, 1, 5, 9]), (13824, [1, 1, 1, 1, 1, 1, 6, 8]), (6912, [1, 1, 1, 1, 1, 1, 7, 7]), (20736, [1, 1, 1, 1, 1, 2, 2, 11]), (20736, [1, 1, 1, 1, 1, 2, 3, 10]), (20736, [1, 1, 1, 1, 1, 2, 4, 9]), (20736, [1, 1, 1, 1, 1, 2, 5, 8]), (20736, [1, 1, 1, 1, 1, 2, 6, 7]), (41472, [1, 1, 1, 1, 1, 15]), (34560, [1, 1, 1, 1, 2, 14])]

def node27Piece0Output_sector0 : RawPoly ℕ := [node27Piece0Output_sector0_chunk0, node27Piece0Output_sector0_chunk1].flatten

def node27Piece0Output : SectorVector := [(0, node27Piece0Output_sector0)]
theorem node27Piece0_check : VectorCertificate (neutralBoundS JR (-8) node27Piece0Input) node27Piece0Output := by decide +kernel
theorem node27Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece0Input) = evaluate node27Piece0Output :=
  neutralBound_value JR _ _ _ node27Piece0_check

def node27Piece1Input_sector0 : RawPoly ℕ := [(-252, [1, 1, 1, 1, 1, 4])]

def node27Piece1Input : SectorVector := [(0, node27Piece1Input_sector0)]
def node27Piece1Output_sector0_chunk0 : RawPoly ℕ := [(-1008, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (-3024, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-3024, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-3024, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-12096, [1, 1, 1, 1, 1, 1, 1, 13]), (-3024, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-6048, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-3024, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-24192, [1, 1, 1, 1, 1, 1, 2, 12]), (-3024, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-24192, [1, 1, 1, 1, 1, 1, 3, 11]), (-21168, [1, 1, 1, 1, 1, 1, 4, 10]), (-24192, [1, 1, 1, 1, 1, 1, 5, 9]), (-24192, [1, 1, 1, 1, 1, 1, 6, 8]), (-12096, [1, 1, 1, 1, 1, 1, 7, 7]), (-1008, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-3024, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-12096, [1, 1, 1, 1, 1, 2, 2, 11]), (-1008, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-24192, [1, 1, 1, 1, 1, 2, 3, 10]), (-46368, [1, 1, 1, 1, 1, 2, 4, 9]), (-24192, [1, 1, 1, 1, 1, 2, 5, 8]), (-24192, [1, 1, 1, 1, 1, 2, 6, 7]), (-12096, [1, 1, 1, 1, 1, 3, 3, 9])]

def node27Piece1Output_sector0_chunk1 : RawPoly ℕ := [(-53928, [1, 1, 1, 1, 1, 3, 4, 8]), (-24192, [1, 1, 1, 1, 1, 3, 5, 7]), (-12096, [1, 1, 1, 1, 1, 3, 6, 6]), (-46872, [1, 1, 1, 1, 1, 4, 4, 7]), (-61488, [1, 1, 1, 1, 1, 4, 5, 6]), (-4032, [1, 1, 1, 1, 1, 5, 5, 5]), (304416, [1, 1, 1, 1, 1, 15]), (-15120, [1, 1, 1, 1, 2, 2, 4, 8]), (-30240, [1, 1, 1, 1, 2, 3, 4, 7]), (-30240, [1, 1, 1, 1, 2, 4, 4, 6]), (-15120, [1, 1, 1, 1, 2, 4, 5, 5]), (-120960, [1, 1, 1, 1, 2, 14]), (-15120, [1, 1, 1, 1, 3, 3, 4, 6]), (-30240, [1, 1, 1, 1, 3, 4, 4, 5]), (-120960, [1, 1, 1, 1, 3, 13]), (-5040, [1, 1, 1, 1, 4, 4, 4, 4]), (47880, [1, 1, 1, 1, 4, 12]), (-120960, [1, 1, 1, 1, 5, 11]), (-120960, [1, 1, 1, 1, 6, 10]), (-120960, [1, 1, 1, 1, 7, 9]), (-60480, [1, 1, 1, 1, 8, 8]), (-60480, [1, 1, 1, 2, 4, 11]), (-60480, [1, 1, 1, 3, 4, 10]), (-60480, [1, 1, 1, 4, 4, 9])]

def node27Piece1Output_sector0_chunk2 : RawPoly ℕ := [(-60480, [1, 1, 1, 4, 5, 8]), (-60480, [1, 1, 1, 4, 6, 7]), (-241920, [1, 1, 1, 17]), (-60480, [1, 1, 4, 14])]

def node27Piece1Output_sector0 : RawPoly ℕ := [node27Piece1Output_sector0_chunk0, node27Piece1Output_sector0_chunk1, node27Piece1Output_sector0_chunk2].flatten

def node27Piece1Output : SectorVector := [(0, node27Piece1Output_sector0)]
theorem node27Piece1_check : VectorCertificate (neutralBoundS JR (-8) node27Piece1Input) node27Piece1Output := by decide +kernel
theorem node27Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece1Input) = evaluate node27Piece1Output :=
  neutralBound_value JR _ _ _ node27Piece1_check

def node27Piece2Input_sector0 : RawPoly ℕ := [(120, [1, 1, 1, 2, 2, 2])]

def node27Piece2Input : SectorVector := [(0, node27Piece2Input_sector0)]
def node27Piece2Output_sector0_chunk0 : RawPoly ℕ := [(480, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (1440, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (1440, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (1440, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (8640, [1, 1, 1, 1, 1, 2, 2, 11]), (1440, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (2880, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (1440, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (1440, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (12960, [1, 1, 1, 1, 2, 2, 2, 10]), (17280, [1, 1, 1, 1, 2, 2, 3, 9]), (17280, [1, 1, 1, 1, 2, 2, 4, 8]), (17280, [1, 1, 1, 1, 2, 2, 5, 7]), (8640, [1, 1, 1, 1, 2, 2, 6, 6]), (34560, [1, 1, 1, 1, 2, 14]), (480, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (1440, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (480, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (13440, [1, 1, 1, 2, 2, 2, 2, 9]), (25680, [1, 1, 1, 2, 2, 2, 3, 8]), (28080, [1, 1, 1, 2, 2, 2, 4, 7]), (29280, [1, 1, 1, 2, 2, 2, 5, 6]), (8640, [1, 1, 1, 2, 2, 3, 3, 7]), (17280, [1, 1, 1, 2, 2, 3, 4, 6])]

def node27Piece2Output_sector0_chunk1 : RawPoly ℕ := [(8640, [1, 1, 1, 2, 2, 3, 5, 5]), (8640, [1, 1, 1, 2, 2, 4, 4, 5]), (-95040, [1, 1, 1, 2, 2, 13]), (34560, [1, 1, 1, 2, 3, 12]), (34560, [1, 1, 1, 2, 4, 11]), (34560, [1, 1, 1, 2, 5, 10]), (34560, [1, 1, 1, 2, 6, 9]), (34560, [1, 1, 1, 2, 7, 8]), (23040, [1, 1, 1, 17]), (4320, [1, 1, 2, 2, 2, 2, 2, 8]), (8640, [1, 1, 2, 2, 2, 2, 3, 7]), (8640, [1, 1, 2, 2, 2, 2, 4, 6]), (4320, [1, 1, 2, 2, 2, 2, 5, 5]), (4320, [1, 1, 2, 2, 2, 3, 3, 6]), (8640, [1, 1, 2, 2, 2, 3, 4, 5]), (1440, [1, 1, 2, 2, 2, 4, 4, 4]), (-5040, [1, 1, 2, 2, 2, 12]), (51840, [1, 1, 2, 2, 3, 11]), (51840, [1, 1, 2, 2, 4, 10]), (51840, [1, 1, 2, 2, 5, 9]), (51840, [1, 1, 2, 2, 6, 8]), (25920, [1, 1, 2, 2, 7, 7]), (103680, [1, 1, 2, 16]), (8640, [1, 2, 2, 2, 2, 11])]

def node27Piece2Output_sector0_chunk2 : RawPoly ℕ := [(8640, [1, 2, 2, 2, 3, 10]), (8640, [1, 2, 2, 2, 4, 9]), (8640, [1, 2, 2, 2, 5, 8]), (8640, [1, 2, 2, 2, 6, 7]), (51840, [1, 2, 2, 15]), (2880, [2, 2, 2, 14])]

def node27Piece2Output_sector0 : RawPoly ℕ := [node27Piece2Output_sector0_chunk0, node27Piece2Output_sector0_chunk1, node27Piece2Output_sector0_chunk2].flatten

def node27Piece2Output : SectorVector := [(0, node27Piece2Output_sector0)]
theorem node27Piece2_check : VectorCertificate (neutralBoundS JR (-8) node27Piece2Input) node27Piece2Output := by decide +kernel
theorem node27Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece2Input) = evaluate node27Piece2Output :=
  neutralBound_value JR _ _ _ node27Piece2_check

def node27Piece3Input_sector0 : RawPoly ℕ := [(-160, [1, 1, 1, 6])]

def node27Piece3Input : SectorVector := [(0, node27Piece3Input_sector0)]
def node27Piece3Output_sector0_chunk0 : RawPoly ℕ := [(-640, [1, 1, 1, 1, 1, 1, 6, 8]), (-1920, [1, 1, 1, 1, 1, 2, 6, 7]), (-1920, [1, 1, 1, 1, 1, 3, 6, 6]), (-1920, [1, 1, 1, 1, 1, 4, 5, 6]), (-11520, [1, 1, 1, 1, 1, 15]), (-1920, [1, 1, 1, 1, 2, 2, 6, 6]), (-3840, [1, 1, 1, 1, 2, 3, 5, 6]), (-1920, [1, 1, 1, 1, 2, 4, 4, 6]), (-23040, [1, 1, 1, 1, 2, 14]), (-1920, [1, 1, 1, 1, 3, 3, 4, 6]), (-23040, [1, 1, 1, 1, 3, 13]), (-23040, [1, 1, 1, 1, 4, 12]), (-23040, [1, 1, 1, 1, 5, 11]), (-17280, [1, 1, 1, 1, 6, 10]), (-23040, [1, 1, 1, 1, 7, 9]), (-11520, [1, 1, 1, 1, 8, 8]), (-640, [1, 1, 1, 2, 2, 2, 5, 6]), (-1920, [1, 1, 1, 2, 2, 3, 4, 6]), (-11520, [1, 1, 1, 2, 2, 13]), (-640, [1, 1, 1, 2, 3, 3, 3, 6]), (-23040, [1, 1, 1, 2, 3, 12]), (-23040, [1, 1, 1, 2, 4, 11]), (-23040, [1, 1, 1, 2, 5, 10]), (-29440, [1, 1, 1, 2, 6, 9])]

def node27Piece3Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [1, 1, 1, 2, 7, 8]), (-11520, [1, 1, 1, 3, 3, 11]), (-23040, [1, 1, 1, 3, 4, 10]), (-23040, [1, 1, 1, 3, 5, 9]), (-34240, [1, 1, 1, 3, 6, 8]), (-11520, [1, 1, 1, 3, 7, 7]), (-11520, [1, 1, 1, 4, 4, 9]), (-23040, [1, 1, 1, 4, 5, 8]), (-37440, [1, 1, 1, 4, 6, 7]), (-11520, [1, 1, 1, 5, 5, 7]), (-27520, [1, 1, 1, 5, 6, 6]), (537600, [1, 1, 1, 17]), (-5760, [1, 1, 2, 2, 6, 8]), (-11520, [1, 1, 2, 3, 6, 7]), (-11520, [1, 1, 2, 4, 6, 6]), (-5760, [1, 1, 2, 5, 5, 6]), (-69120, [1, 1, 2, 16]), (-5760, [1, 1, 3, 3, 6, 6]), (-11520, [1, 1, 3, 4, 5, 6]), (-69120, [1, 1, 3, 15]), (-1920, [1, 1, 4, 4, 4, 6]), (-69120, [1, 1, 4, 14]), (-69120, [1, 1, 5, 13]), (6720, [1, 1, 6, 12])]

def node27Piece3Output_sector0_chunk2 : RawPoly ℕ := [(-69120, [1, 1, 7, 11]), (-69120, [1, 1, 8, 10]), (-34560, [1, 1, 9, 9]), (-11520, [1, 2, 6, 11]), (-11520, [1, 3, 6, 10]), (-11520, [1, 4, 6, 9]), (-11520, [1, 5, 6, 8]), (-11520, [1, 6, 6, 7]), (-69120, [1, 19]), (-3840, [6, 14])]

def node27Piece3Output_sector0 : RawPoly ℕ := [node27Piece3Output_sector0_chunk0, node27Piece3Output_sector0_chunk1, node27Piece3Output_sector0_chunk2].flatten

def node27Piece3Output : SectorVector := [(0, node27Piece3Output_sector0)]
theorem node27Piece3_check : VectorCertificate (neutralBoundS JR (-8) node27Piece3Input) node27Piece3Output := by decide +kernel
theorem node27Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece3Input) = evaluate node27Piece3Output :=
  neutralBound_value JR _ _ _ node27Piece3_check

def node27Piece4Input_sector0 : RawPoly ℕ := [(384, [1, 1, 2, 5])]

def node27Piece4Input : SectorVector := [(0, node27Piece4Input_sector0)]
def node27Piece4Output_sector0_chunk0 : RawPoly ℕ := [(1536, [1, 1, 1, 1, 1, 2, 5, 8]), (4608, [1, 1, 1, 1, 2, 2, 5, 7]), (4608, [1, 1, 1, 1, 2, 3, 5, 6]), (4608, [1, 1, 1, 1, 2, 4, 5, 5]), (23040, [1, 1, 1, 1, 2, 14]), (9216, [1, 1, 1, 1, 5, 11]), (4608, [1, 1, 1, 2, 2, 2, 5, 6]), (9216, [1, 1, 1, 2, 2, 3, 5, 5]), (4608, [1, 1, 1, 2, 2, 4, 4, 5]), (46080, [1, 1, 1, 2, 2, 13]), (4608, [1, 1, 1, 2, 3, 3, 4, 5]), (46080, [1, 1, 1, 2, 3, 12]), (46080, [1, 1, 1, 2, 4, 11]), (46080, [1, 1, 1, 2, 5, 10]), (46080, [1, 1, 1, 2, 6, 9]), (46080, [1, 1, 1, 2, 7, 8]), (18432, [1, 1, 1, 3, 5, 9]), (18432, [1, 1, 1, 4, 5, 8]), (18432, [1, 1, 1, 5, 5, 7]), (9216, [1, 1, 1, 5, 6, 6]), (92160, [1, 1, 1, 17]), (1536, [1, 1, 2, 2, 2, 2, 5, 5]), (4608, [1, 1, 2, 2, 2, 3, 4, 5]), (23040, [1, 1, 2, 2, 2, 12])]

def node27Piece4Output_sector0_chunk1 : RawPoly ℕ := [(1536, [1, 1, 2, 2, 3, 3, 3, 5]), (46080, [1, 1, 2, 2, 3, 11]), (46080, [1, 1, 2, 2, 4, 10]), (61440, [1, 1, 2, 2, 5, 9]), (46080, [1, 1, 2, 2, 6, 8]), (23040, [1, 1, 2, 2, 7, 7]), (23040, [1, 1, 2, 3, 3, 10]), (46080, [1, 1, 2, 3, 4, 9]), (82176, [1, 1, 2, 3, 5, 8]), (46080, [1, 1, 2, 3, 6, 7]), (23040, [1, 1, 2, 4, 4, 8]), (89856, [1, 1, 2, 4, 5, 7]), (23040, [1, 1, 2, 4, 6, 6]), (70656, [1, 1, 2, 5, 5, 6]), (-817920, [1, 1, 2, 16]), (9216, [1, 1, 3, 3, 5, 7]), (18432, [1, 1, 3, 4, 5, 6]), (9216, [1, 1, 3, 5, 5, 5]), (92160, [1, 1, 3, 15]), (9216, [1, 1, 4, 4, 5, 5]), (92160, [1, 1, 4, 14]), (-64512, [1, 1, 5, 13]), (92160, [1, 1, 6, 12]), (92160, [1, 1, 7, 11])]

def node27Piece4Output_sector0_chunk2 : RawPoly ℕ := [(92160, [1, 1, 8, 10]), (46080, [1, 1, 9, 9]), (9216, [1, 2, 2, 2, 5, 8]), (18432, [1, 2, 2, 3, 5, 7]), (18432, [1, 2, 2, 4, 5, 6]), (9216, [1, 2, 2, 5, 5, 5]), (92160, [1, 2, 2, 15]), (9216, [1, 2, 3, 3, 5, 6]), (18432, [1, 2, 3, 4, 5, 5]), (92160, [1, 2, 3, 14]), (3072, [1, 2, 4, 4, 4, 5]), (92160, [1, 2, 4, 13]), (-1536, [1, 2, 5, 12]), (92160, [1, 2, 6, 11]), (92160, [1, 2, 7, 10]), (92160, [1, 2, 8, 9]), (36864, [1, 3, 5, 11]), (36864, [1, 4, 5, 10]), (36864, [1, 5, 5, 9]), (36864, [1, 5, 6, 8]), (18432, [1, 5, 7, 7]), (184320, [1, 19]), (9216, [2, 2, 5, 11]), (9216, [2, 3, 5, 10])]

def node27Piece4Output_sector0_chunk3 : RawPoly ℕ := [(9216, [2, 4, 5, 9]), (9216, [2, 5, 5, 8]), (9216, [2, 5, 6, 7]), (46080, [2, 18]), (18432, [5, 15])]

def node27Piece4Output_sector0 : RawPoly ℕ := [node27Piece4Output_sector0_chunk0, node27Piece4Output_sector0_chunk1, node27Piece4Output_sector0_chunk2, node27Piece4Output_sector0_chunk3].flatten

def node27Piece4Output : SectorVector := [(0, node27Piece4Output_sector0)]
theorem node27Piece4_check : VectorCertificate (neutralBoundS JR (-8) node27Piece4Input) node27Piece4Output := by decide +kernel
theorem node27Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece4Input) = evaluate node27Piece4Output :=
  neutralBound_value JR _ _ _ node27Piece4_check

def node27Piece5Input_sector0 : RawPoly ℕ := [(-120, [1, 1, 3, 4])]

def node27Piece5Input : SectorVector := [(0, node27Piece5Input_sector0)]
def node27Piece5Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 1, 1, 3, 4, 8]), (-1440, [1, 1, 1, 1, 2, 3, 4, 7]), (-1440, [1, 1, 1, 1, 3, 3, 4, 6]), (-1440, [1, 1, 1, 1, 3, 4, 4, 5]), (-5760, [1, 1, 1, 1, 3, 13]), (-4320, [1, 1, 1, 1, 4, 12]), (-1440, [1, 1, 1, 2, 2, 3, 4, 6]), (-2880, [1, 1, 1, 2, 3, 3, 4, 5]), (-1440, [1, 1, 1, 2, 3, 4, 4, 4]), (-11520, [1, 1, 1, 2, 3, 12]), (-8640, [1, 1, 1, 2, 4, 11]), (-1440, [1, 1, 1, 3, 3, 3, 4, 4]), (-11520, [1, 1, 1, 3, 3, 11]), (-14400, [1, 1, 1, 3, 4, 10]), (-11520, [1, 1, 1, 3, 5, 9]), (-11520, [1, 1, 1, 3, 6, 8]), (-5760, [1, 1, 1, 3, 7, 7]), (-8640, [1, 1, 1, 4, 4, 9]), (-8640, [1, 1, 1, 4, 5, 8]), (-8640, [1, 1, 1, 4, 6, 7]), (-34560, [1, 1, 1, 17]), (-480, [1, 1, 2, 2, 2, 3, 4, 5]), (-1440, [1, 1, 2, 2, 3, 3, 4, 4]), (-5760, [1, 1, 2, 2, 3, 11])]

def node27Piece5Output_sector0_chunk1 : RawPoly ℕ := [(-4320, [1, 1, 2, 2, 4, 10]), (-480, [1, 1, 2, 3, 3, 3, 3, 4]), (-11520, [1, 1, 2, 3, 3, 10]), (-22080, [1, 1, 2, 3, 4, 9]), (-11520, [1, 1, 2, 3, 5, 8]), (-11520, [1, 1, 2, 3, 6, 7]), (-8640, [1, 1, 2, 4, 4, 8]), (-8640, [1, 1, 2, 4, 5, 7]), (-4320, [1, 1, 2, 4, 6, 6]), (-34560, [1, 1, 2, 16]), (-5760, [1, 1, 3, 3, 3, 9]), (-21360, [1, 1, 3, 3, 4, 8]), (-11520, [1, 1, 3, 3, 5, 7]), (-5760, [1, 1, 3, 3, 6, 6]), (-22320, [1, 1, 3, 4, 4, 7]), (-29280, [1, 1, 3, 4, 5, 6]), (-1920, [1, 1, 3, 5, 5, 5]), (144960, [1, 1, 3, 15]), (-4320, [1, 1, 4, 4, 4, 6]), (-4320, [1, 1, 4, 4, 5, 5]), (67680, [1, 1, 4, 14]), (-34560, [1, 1, 5, 13]), (-34560, [1, 1, 6, 12]), (-34560, [1, 1, 7, 11])]

def node27Piece5Output_sector0_chunk2 : RawPoly ℕ := [(-34560, [1, 1, 8, 10]), (-17280, [1, 1, 9, 9]), (-2880, [1, 2, 2, 3, 4, 8]), (-5760, [1, 2, 3, 3, 4, 7]), (-5760, [1, 2, 3, 4, 4, 6]), (-2880, [1, 2, 3, 4, 5, 5]), (-23040, [1, 2, 3, 14]), (-17280, [1, 2, 4, 13]), (-2880, [1, 3, 3, 3, 4, 6]), (-5760, [1, 3, 3, 4, 4, 5]), (-23040, [1, 3, 3, 13]), (-960, [1, 3, 4, 4, 4, 4]), (480, [1, 3, 4, 12]), (-23040, [1, 3, 5, 11]), (-23040, [1, 3, 6, 10]), (-23040, [1, 3, 7, 9]), (-11520, [1, 3, 8, 8]), (-17280, [1, 4, 4, 11]), (-17280, [1, 4, 5, 10]), (-17280, [1, 4, 6, 9]), (-17280, [1, 4, 7, 8]), (-69120, [1, 19]), (-2880, [2, 3, 4, 11]), (-2880, [3, 3, 4, 10])]

def node27Piece5Output_sector0_chunk3 : RawPoly ℕ := [(-2880, [3, 4, 4, 9]), (-2880, [3, 4, 5, 8]), (-2880, [3, 4, 6, 7]), (-11520, [3, 17]), (-8640, [4, 16])]

def node27Piece5Output_sector0 : RawPoly ℕ := [node27Piece5Output_sector0_chunk0, node27Piece5Output_sector0_chunk1, node27Piece5Output_sector0_chunk2, node27Piece5Output_sector0_chunk3].flatten

def node27Piece5Output : SectorVector := [(0, node27Piece5Output_sector0)]
theorem node27Piece5_check : VectorCertificate (neutralBoundS JR (-8) node27Piece5Input) node27Piece5Output := by decide +kernel
theorem node27Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece5Input) = evaluate node27Piece5Output :=
  neutralBound_value JR _ _ _ node27Piece5_check

def node27Piece6Input_sector0 : RawPoly ℕ := [(-750, [1, 2, 2, 4])]

def node27Piece6Input : SectorVector := [(0, node27Piece6Input_sector0)]
def node27Piece6Output_sector0_chunk0 : RawPoly ℕ := [(-3000, [1, 1, 1, 1, 2, 2, 4, 8]), (-9000, [1, 1, 1, 2, 2, 2, 4, 7]), (-9000, [1, 1, 1, 2, 2, 3, 4, 6]), (-9000, [1, 1, 1, 2, 2, 4, 4, 5]), (-36000, [1, 1, 1, 2, 2, 13]), (-36000, [1, 1, 1, 2, 4, 11]), (-9000, [1, 1, 2, 2, 2, 2, 4, 6]), (-18000, [1, 1, 2, 2, 2, 3, 4, 5]), (-9000, [1, 1, 2, 2, 2, 4, 4, 4]), (-72000, [1, 1, 2, 2, 2, 12]), (-9000, [1, 1, 2, 2, 3, 3, 4, 4]), (-72000, [1, 1, 2, 2, 3, 11]), (-99000, [1, 1, 2, 2, 4, 10]), (-72000, [1, 1, 2, 2, 5, 9]), (-72000, [1, 1, 2, 2, 6, 8]), (-36000, [1, 1, 2, 2, 7, 7]), (-72000, [1, 1, 2, 3, 4, 9]), (-72000, [1, 1, 2, 4, 4, 8]), (-72000, [1, 1, 2, 4, 5, 7]), (-36000, [1, 1, 2, 4, 6, 6]), (-288000, [1, 1, 2, 16]), (-72000, [1, 1, 4, 14]), (-3000, [1, 2, 2, 2, 2, 2, 4, 5]), (-9000, [1, 2, 2, 2, 2, 3, 4, 4])]

def node27Piece6Output_sector0_chunk1 : RawPoly ℕ := [(-36000, [1, 2, 2, 2, 2, 11]), (-3000, [1, 2, 2, 2, 3, 3, 3, 4]), (-72000, [1, 2, 2, 2, 3, 10]), (-102000, [1, 2, 2, 2, 4, 9]), (-72000, [1, 2, 2, 2, 5, 8]), (-72000, [1, 2, 2, 2, 6, 7]), (-36000, [1, 2, 2, 3, 3, 9]), (-160500, [1, 2, 2, 3, 4, 8]), (-72000, [1, 2, 2, 3, 5, 7]), (-36000, [1, 2, 2, 3, 6, 6]), (-139500, [1, 2, 2, 4, 4, 7]), (-183000, [1, 2, 2, 4, 5, 6]), (-12000, [1, 2, 2, 5, 5, 5]), (906000, [1, 2, 2, 15]), (-36000, [1, 2, 3, 3, 4, 7]), (-72000, [1, 2, 3, 4, 4, 6]), (-36000, [1, 2, 3, 4, 5, 5]), (-288000, [1, 2, 3, 14]), (-36000, [1, 2, 4, 4, 4, 5]), (324000, [1, 2, 4, 13]), (-288000, [1, 2, 5, 12]), (-288000, [1, 2, 6, 11]), (-288000, [1, 2, 7, 10]), (-288000, [1, 2, 8, 9])]

def node27Piece6Output_sector0_chunk2 : RawPoly ℕ := [(-72000, [1, 3, 4, 12]), (-72000, [1, 4, 4, 11]), (-72000, [1, 4, 5, 10]), (-72000, [1, 4, 6, 9]), (-72000, [1, 4, 7, 8]), (-288000, [1, 19]), (-9000, [2, 2, 2, 2, 4, 8]), (-18000, [2, 2, 2, 3, 4, 7]), (-18000, [2, 2, 2, 4, 4, 6]), (-9000, [2, 2, 2, 4, 5, 5]), (-72000, [2, 2, 2, 14]), (-9000, [2, 2, 3, 3, 4, 6]), (-18000, [2, 2, 3, 4, 4, 5]), (-72000, [2, 2, 3, 13]), (-3000, [2, 2, 4, 4, 4, 4]), (-7500, [2, 2, 4, 12]), (-72000, [2, 2, 5, 11]), (-72000, [2, 2, 6, 10]), (-72000, [2, 2, 7, 9]), (-36000, [2, 2, 8, 8]), (-72000, [2, 3, 4, 11]), (-72000, [2, 4, 4, 10]), (-72000, [2, 4, 5, 9]), (-72000, [2, 4, 6, 8])]

def node27Piece6Output_sector0_chunk3 : RawPoly ℕ := [(-36000, [2, 4, 7, 7]), (-288000, [2, 18]), (-72000, [4, 16])]

def node27Piece6Output_sector0 : RawPoly ℕ := [node27Piece6Output_sector0_chunk0, node27Piece6Output_sector0_chunk1, node27Piece6Output_sector0_chunk2, node27Piece6Output_sector0_chunk3].flatten

def node27Piece6Output : SectorVector := [(0, node27Piece6Output_sector0)]
theorem node27Piece6_check : VectorCertificate (neutralBoundS JR (-8) node27Piece6Input) node27Piece6Output := by decide +kernel
theorem node27Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece6Input) = evaluate node27Piece6Output :=
  neutralBound_value JR _ _ _ node27Piece6_check

def node27Piece7Input_sector0 : RawPoly ℕ := [(960, [1, 2, 3, 3])]

def node27Piece7Input : SectorVector := [(0, node27Piece7Input_sector0)]
def node27Piece7Output_sector0_chunk0 : RawPoly ℕ := [(3840, [1, 1, 1, 1, 2, 3, 3, 8]), (11520, [1, 1, 1, 2, 2, 3, 3, 7]), (11520, [1, 1, 1, 2, 3, 3, 3, 6]), (11520, [1, 1, 1, 2, 3, 3, 4, 5]), (69120, [1, 1, 1, 2, 3, 12]), (23040, [1, 1, 1, 3, 3, 11]), (11520, [1, 1, 2, 2, 2, 3, 3, 6]), (23040, [1, 1, 2, 2, 3, 3, 3, 5]), (11520, [1, 1, 2, 2, 3, 3, 4, 4]), (138240, [1, 1, 2, 2, 3, 11]), (11520, [1, 1, 2, 3, 3, 3, 3, 4]), (126720, [1, 1, 2, 3, 3, 10]), (138240, [1, 1, 2, 3, 4, 9]), (138240, [1, 1, 2, 3, 5, 8]), (138240, [1, 1, 2, 3, 6, 7]), (207360, [1, 1, 2, 16]), (46080, [1, 1, 3, 3, 3, 9]), (46080, [1, 1, 3, 3, 4, 8]), (46080, [1, 1, 3, 3, 5, 7]), (23040, [1, 1, 3, 3, 6, 6]), (276480, [1, 1, 3, 15]), (3840, [1, 2, 2, 2, 2, 3, 3, 5]), (11520, [1, 2, 2, 2, 3, 3, 3, 4]), (69120, [1, 2, 2, 2, 3, 10])]

def node27Piece7Output_sector0_chunk1 : RawPoly ℕ := [(3840, [1, 2, 2, 3, 3, 3, 3, 3]), (153600, [1, 2, 2, 3, 3, 9]), (138240, [1, 2, 2, 3, 4, 8]), (138240, [1, 2, 2, 3, 5, 7]), (69120, [1, 2, 2, 3, 6, 6]), (207360, [1, 2, 2, 15]), (136320, [1, 2, 3, 3, 3, 8]), (224640, [1, 2, 3, 3, 4, 7]), (234240, [1, 2, 3, 3, 5, 6]), (69120, [1, 2, 3, 4, 4, 6]), (69120, [1, 2, 3, 4, 5, 5]), (-1290240, [1, 2, 3, 14]), (207360, [1, 2, 4, 13]), (207360, [1, 2, 5, 12]), (207360, [1, 2, 6, 11]), (207360, [1, 2, 7, 10]), (207360, [1, 2, 8, 9]), (23040, [1, 3, 3, 3, 3, 7]), (46080, [1, 3, 3, 3, 4, 6]), (23040, [1, 3, 3, 3, 5, 5]), (23040, [1, 3, 3, 4, 4, 5]), (-161280, [1, 3, 3, 13]), (276480, [1, 3, 4, 12]), (276480, [1, 3, 5, 11])]

def node27Piece7Output_sector0_chunk2 : RawPoly ℕ := [(276480, [1, 3, 6, 10]), (276480, [1, 3, 7, 9]), (138240, [1, 3, 8, 8]), (414720, [1, 19]), (11520, [2, 2, 2, 3, 3, 8]), (23040, [2, 2, 3, 3, 3, 7]), (23040, [2, 2, 3, 3, 4, 6]), (11520, [2, 2, 3, 3, 5, 5]), (138240, [2, 2, 3, 13]), (11520, [2, 3, 3, 3, 3, 6]), (23040, [2, 3, 3, 3, 4, 5]), (3840, [2, 3, 3, 4, 4, 4]), (9600, [2, 3, 3, 12]), (138240, [2, 3, 4, 11]), (138240, [2, 3, 5, 10]), (138240, [2, 3, 6, 9]), (138240, [2, 3, 7, 8]), (207360, [2, 18]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (46080, [3, 3, 6, 8]), (23040, [3, 3, 7, 7]), (276480, [3, 17])]

def node27Piece7Output_sector0 : RawPoly ℕ := [node27Piece7Output_sector0_chunk0, node27Piece7Output_sector0_chunk1, node27Piece7Output_sector0_chunk2].flatten

def node27Piece7Output : SectorVector := [(0, node27Piece7Output_sector0)]
theorem node27Piece7_check : VectorCertificate (neutralBoundS JR (-8) node27Piece7Input) node27Piece7Output := by decide +kernel
theorem node27Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece7Input) = evaluate node27Piece7Output :=
  neutralBound_value JR _ _ _ node27Piece7_check

def node27Piece8Input_sector0 : RawPoly ℕ := [(60, [1, 8])]

def node27Piece8Input : SectorVector := [(0, node27Piece8Input_sector0)]
def node27Piece8Output_sector0_chunk0 : RawPoly ℕ := [(240, [1, 1, 1, 1, 8, 8]), (720, [1, 1, 1, 2, 7, 8]), (720, [1, 1, 1, 3, 6, 8]), (720, [1, 1, 1, 4, 5, 8]), (5760, [1, 1, 1, 17]), (720, [1, 1, 2, 2, 6, 8]), (1440, [1, 1, 2, 3, 5, 8]), (720, [1, 1, 2, 4, 4, 8]), (11520, [1, 1, 2, 16]), (720, [1, 1, 3, 3, 4, 8]), (11520, [1, 1, 3, 15]), (11520, [1, 1, 4, 14]), (11520, [1, 1, 5, 13]), (11520, [1, 1, 6, 12]), (11520, [1, 1, 7, 11]), (7920, [1, 1, 8, 10]), (5760, [1, 1, 9, 9]), (240, [1, 2, 2, 2, 5, 8]), (720, [1, 2, 2, 3, 4, 8]), (5760, [1, 2, 2, 15]), (240, [1, 2, 3, 3, 3, 8]), (11520, [1, 2, 3, 14]), (11520, [1, 2, 4, 13]), (11520, [1, 2, 5, 12])]

def node27Piece8Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 2, 6, 11]), (11520, [1, 2, 7, 10]), (11040, [1, 2, 8, 9]), (5760, [1, 3, 3, 13]), (11520, [1, 3, 4, 12]), (11520, [1, 3, 5, 11]), (11520, [1, 3, 6, 10]), (11520, [1, 3, 7, 9]), (7080, [1, 3, 8, 8]), (5760, [1, 4, 4, 11]), (11520, [1, 4, 5, 10]), (11520, [1, 4, 6, 9]), (14040, [1, 4, 7, 8]), (5760, [1, 5, 5, 9]), (14640, [1, 5, 6, 8]), (5760, [1, 5, 7, 7]), (5760, [1, 6, 6, 7]), (-411840, [1, 19]), (720, [2, 2, 8, 8]), (1440, [2, 3, 7, 8]), (1440, [2, 4, 6, 8]), (720, [2, 5, 5, 8]), (11520, [2, 18]), (720, [3, 3, 6, 8])]

def node27Piece8Output_sector0_chunk2 : RawPoly ℕ := [(1440, [3, 4, 5, 8]), (11520, [3, 17]), (240, [4, 4, 4, 8]), (11520, [4, 16]), (11520, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (600, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node27Piece8Output_sector0 : RawPoly ℕ := [node27Piece8Output_sector0_chunk0, node27Piece8Output_sector0_chunk1, node27Piece8Output_sector0_chunk2].flatten

def node27Piece8Output : SectorVector := [(0, node27Piece8Output_sector0)]
theorem node27Piece8_check : VectorCertificate (neutralBoundS JR (-8) node27Piece8Input) node27Piece8Output := by decide +kernel
theorem node27Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece8Input) = evaluate node27Piece8Output :=
  neutralBound_value JR _ _ _ node27Piece8_check

def node27Piece9Input_sector0 : RawPoly ℕ := [(-280, [2, 2, 2, 3])]

def node27Piece9Input : SectorVector := [(0, node27Piece9Input_sector0)]
def node27Piece9Output_sector0_chunk0 : RawPoly ℕ := [(-1120, [1, 1, 1, 2, 2, 2, 3, 8]), (-3360, [1, 1, 2, 2, 2, 2, 3, 7]), (-3360, [1, 1, 2, 2, 2, 3, 3, 6]), (-3360, [1, 1, 2, 2, 2, 3, 4, 5]), (-10080, [1, 1, 2, 2, 2, 12]), (-20160, [1, 1, 2, 2, 3, 11]), (-3360, [1, 2, 2, 2, 2, 2, 3, 6]), (-6720, [1, 2, 2, 2, 2, 3, 3, 5]), (-3360, [1, 2, 2, 2, 2, 3, 4, 4]), (-20160, [1, 2, 2, 2, 2, 11]), (-3360, [1, 2, 2, 2, 3, 3, 3, 4]), (-40320, [1, 2, 2, 2, 3, 10]), (-20160, [1, 2, 2, 2, 4, 9]), (-20160, [1, 2, 2, 2, 5, 8]), (-20160, [1, 2, 2, 2, 6, 7]), (-40320, [1, 2, 2, 3, 3, 9]), (-40320, [1, 2, 2, 3, 4, 8]), (-40320, [1, 2, 2, 3, 5, 7]), (-20160, [1, 2, 2, 3, 6, 6]), (-120960, [1, 2, 2, 15]), (-80640, [1, 2, 3, 14]), (-1120, [2, 2, 2, 2, 2, 2, 3, 5]), (-3360, [2, 2, 2, 2, 2, 3, 3, 4]), (-10080, [2, 2, 2, 2, 2, 10])]

def node27Piece9Output_sector0_chunk1 : RawPoly ℕ := [(-1120, [2, 2, 2, 2, 3, 3, 3, 3]), (-31360, [2, 2, 2, 2, 3, 9]), (-20160, [2, 2, 2, 2, 4, 8]), (-20160, [2, 2, 2, 2, 5, 7]), (-10080, [2, 2, 2, 2, 6, 6]), (-49840, [2, 2, 2, 3, 3, 8]), (-65520, [2, 2, 2, 3, 4, 7]), (-68320, [2, 2, 2, 3, 5, 6]), (-10080, [2, 2, 2, 4, 4, 6]), (-10080, [2, 2, 2, 4, 5, 5]), (157920, [2, 2, 2, 14]), (-20160, [2, 2, 3, 3, 3, 7]), (-40320, [2, 2, 3, 3, 4, 6]), (-20160, [2, 2, 3, 3, 5, 5]), (-20160, [2, 2, 3, 4, 4, 5]), (221760, [2, 2, 3, 13]), (-120960, [2, 2, 4, 12]), (-120960, [2, 2, 5, 11]), (-120960, [2, 2, 6, 10]), (-120960, [2, 2, 7, 9]), (-60480, [2, 2, 8, 8]), (-80640, [2, 3, 3, 12]), (-80640, [2, 3, 4, 11]), (-80640, [2, 3, 5, 10])]

def node27Piece9Output_sector0_chunk2 : RawPoly ℕ := [(-80640, [2, 3, 6, 9]), (-80640, [2, 3, 7, 8]), (-241920, [2, 18]), (-53760, [3, 17])]

def node27Piece9Output_sector0 : RawPoly ℕ := [node27Piece9Output_sector0_chunk0, node27Piece9Output_sector0_chunk1, node27Piece9Output_sector0_chunk2].flatten

def node27Piece9Output : SectorVector := [(0, node27Piece9Output_sector0)]
theorem node27Piece9_check : VectorCertificate (neutralBoundS JR (-8) node27Piece9Input) node27Piece9Output := by decide +kernel
theorem node27Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece9Input) = evaluate node27Piece9Output :=
  neutralBound_value JR _ _ _ node27Piece9_check

def node27Piece10Input_sector0 : RawPoly ℕ := [(-960/7, [2, 7])]

def node27Piece10Input : SectorVector := [(0, node27Piece10Input_sector0)]
def node27Piece10Output_sector0_chunk0 : RawPoly ℕ := [(-3840/7, [1, 1, 1, 2, 7, 8]), (-11520/7, [1, 1, 2, 2, 7, 7]), (-11520/7, [1, 1, 2, 3, 6, 7]), (-11520/7, [1, 1, 2, 4, 5, 7]), (-11520, [1, 1, 2, 16]), (-23040/7, [1, 1, 7, 11]), (-11520/7, [1, 2, 2, 2, 6, 7]), (-23040/7, [1, 2, 2, 3, 5, 7]), (-11520/7, [1, 2, 2, 4, 4, 7]), (-23040, [1, 2, 2, 15]), (-11520/7, [1, 2, 3, 3, 4, 7]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-138240/7, [1, 2, 7, 10]), (-23040, [1, 2, 8, 9]), (-46080/7, [1, 3, 7, 9]), (-46080/7, [1, 4, 7, 8]), (-46080/7, [1, 5, 7, 7]), (-23040/7, [1, 6, 6, 7]), (-46080, [1, 19]), (-3840/7, [2, 2, 2, 2, 5, 7]), (-11520/7, [2, 2, 2, 3, 4, 7])]

def node27Piece10Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 2, 2, 14]), (-3840/7, [2, 2, 3, 3, 3, 7]), (-23040, [2, 2, 3, 13]), (-23040, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10]), (-153600/7, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8]), (-11520, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9]), (-205440/7, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-144000/7, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-234240/7, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (675840, [2, 18]), (-23040/7, [3, 3, 7, 7]), (-46080/7, [3, 4, 6, 7]), (-23040/7, [3, 5, 5, 7])]

def node27Piece10Output_sector0_chunk2 : RawPoly ℕ := [(-46080, [3, 17]), (-23040/7, [4, 4, 5, 7]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (23040, [7, 13]), (-46080, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node27Piece10Output_sector0 : RawPoly ℕ := [node27Piece10Output_sector0_chunk0, node27Piece10Output_sector0_chunk1, node27Piece10Output_sector0_chunk2].flatten

def node27Piece10Output : SectorVector := [(0, node27Piece10Output_sector0)]
theorem node27Piece10_check : VectorCertificate (neutralBoundS JR (-8) node27Piece10Input) node27Piece10Output := by decide +kernel
theorem node27Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece10Input) = evaluate node27Piece10Output :=
  neutralBound_value JR _ _ _ node27Piece10_check

def node27Piece11Input_sector0 : RawPoly ℕ := [(160, [3, 6])]

def node27Piece11Input : SectorVector := [(0, node27Piece11Input_sector0)]
def node27Piece11Output_sector0_chunk0 : RawPoly ℕ := [(640, [1, 1, 1, 3, 6, 8]), (1920, [1, 1, 2, 3, 6, 7]), (1920, [1, 1, 3, 3, 6, 6]), (1920, [1, 1, 3, 4, 5, 6]), (11520, [1, 1, 3, 15]), (5760, [1, 1, 6, 12]), (1920, [1, 2, 2, 3, 6, 6]), (3840, [1, 2, 3, 3, 5, 6]), (1920, [1, 2, 3, 4, 4, 6]), (23040, [1, 2, 3, 14]), (11520, [1, 2, 6, 11]), (1920, [1, 3, 3, 3, 4, 6]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (23040, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (11520, [1, 4, 6, 9]), (11520, [1, 5, 6, 8]), (11520, [1, 6, 6, 7]), (69120, [1, 19]), (640, [2, 2, 2, 3, 5, 6]), (1920, [2, 2, 3, 3, 4, 6])]

def node27Piece11Output_sector0_chunk1 : RawPoly ℕ := [(11520, [2, 2, 3, 13]), (5760, [2, 2, 6, 10]), (640, [2, 3, 3, 3, 3, 6]), (23040, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (23040, [2, 3, 5, 10]), (29440, [2, 3, 6, 9]), (23040, [2, 3, 7, 8]), (11520, [2, 4, 6, 8]), (11520, [2, 5, 6, 7]), (5760, [2, 6, 6, 6]), (69120, [2, 18]), (11520, [3, 3, 3, 11]), (23040, [3, 3, 4, 10]), (23040, [3, 3, 5, 9]), (28480, [3, 3, 6, 8]), (11520, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (37440, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (27520, [3, 5, 6, 6]), (-537600, [3, 17]), (5760, [4, 4, 6, 6])]

def node27Piece11Output_sector0_chunk2 : RawPoly ℕ := [(5760, [4, 5, 5, 6]), (69120, [4, 16]), (69120, [5, 15]), (-90240, [6, 14]), (69120, [7, 13]), (69120, [8, 12]), (69120, [9, 11]), (34560, [10, 10])]

def node27Piece11Output_sector0 : RawPoly ℕ := [node27Piece11Output_sector0_chunk0, node27Piece11Output_sector0_chunk1, node27Piece11Output_sector0_chunk2].flatten

def node27Piece11Output : SectorVector := [(0, node27Piece11Output_sector0)]
theorem node27Piece11_check : VectorCertificate (neutralBoundS JR (-8) node27Piece11Input) node27Piece11Output := by decide +kernel
theorem node27Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece11Input) = evaluate node27Piece11Output :=
  neutralBound_value JR _ _ _ node27Piece11_check

def node27Piece12Input_sector0 : RawPoly ℕ := [(-72, [4, 5])]

def node27Piece12Input : SectorVector := [(0, node27Piece12Input_sector0)]
def node27Piece12Output_sector0_chunk0 : RawPoly ℕ := [(-288, [1, 1, 1, 4, 5, 8]), (-864, [1, 1, 2, 4, 5, 7]), (-864, [1, 1, 3, 4, 5, 6]), (-864, [1, 1, 4, 4, 5, 5]), (-4320, [1, 1, 4, 14]), (-3456, [1, 1, 5, 13]), (-864, [1, 2, 2, 4, 5, 6]), (-1728, [1, 2, 3, 4, 5, 5]), (-864, [1, 2, 4, 4, 4, 5]), (-8640, [1, 2, 4, 13]), (-6912, [1, 2, 5, 12]), (-864, [1, 3, 3, 4, 4, 5]), (-8640, [1, 3, 4, 12]), (-6912, [1, 3, 5, 11]), (-8640, [1, 4, 4, 11]), (-10368, [1, 4, 5, 10]), (-8640, [1, 4, 6, 9]), (-8640, [1, 4, 7, 8]), (-6912, [1, 5, 5, 9]), (-6912, [1, 5, 6, 8]), (-3456, [1, 5, 7, 7]), (-34560, [1, 19]), (-288, [2, 2, 2, 4, 5, 5]), (-864, [2, 2, 3, 4, 4, 5])]

def node27Piece12Output_sector0_chunk1 : RawPoly ℕ := [(-4320, [2, 2, 4, 12]), (-3456, [2, 2, 5, 11]), (-288, [2, 3, 3, 3, 4, 5]), (-8640, [2, 3, 4, 11]), (-6912, [2, 3, 5, 10]), (-8640, [2, 4, 4, 10]), (-13248, [2, 4, 5, 9]), (-8640, [2, 4, 6, 8]), (-4320, [2, 4, 7, 7]), (-6912, [2, 5, 5, 8]), (-6912, [2, 5, 6, 7]), (-34560, [2, 18]), (-4320, [3, 3, 4, 10]), (-3456, [3, 3, 5, 9]), (-8640, [3, 4, 4, 9]), (-15408, [3, 4, 5, 8]), (-8640, [3, 4, 6, 7]), (-6912, [3, 5, 5, 7]), (-3456, [3, 5, 6, 6]), (-34560, [3, 17]), (-4320, [4, 4, 4, 8]), (-13392, [4, 4, 5, 7]), (-4320, [4, 4, 6, 6]), (-13248, [4, 5, 5, 6])]

def node27Piece12Output_sector0_chunk2 : RawPoly ℕ := [(153360, [4, 16]), (-1152, [5, 5, 5, 5]), (86976, [5, 15]), (-34560, [6, 14]), (-34560, [7, 13]), (-34560, [8, 12]), (-34560, [9, 11]), (-17280, [10, 10])]

def node27Piece12Output_sector0 : RawPoly ℕ := [node27Piece12Output_sector0_chunk0, node27Piece12Output_sector0_chunk1, node27Piece12Output_sector0_chunk2].flatten

def node27Piece12Output : SectorVector := [(0, node27Piece12Output_sector0)]
theorem node27Piece12_check : VectorCertificate (neutralBoundS JR (-8) node27Piece12Input) node27Piece12Output := by decide +kernel
theorem node27Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-8)
    (evaluate node27Piece12Input) = evaluate node27Piece12Output :=
  neutralBound_value JR _ _ _ node27Piece12_check

def node27Pieces : List (SectorVector × SectorVector) := [(node27Piece0Input, node27Piece0Output), (node27Piece1Input, node27Piece1Output), (node27Piece2Input, node27Piece2Output), (node27Piece3Input, node27Piece3Output), (node27Piece4Input, node27Piece4Output), (node27Piece5Input, node27Piece5Output), (node27Piece6Input, node27Piece6Output), (node27Piece7Input, node27Piece7Output), (node27Piece8Input, node27Piece8Output), (node27Piece9Input, node27Piece9Output), (node27Piece10Input, node27Piece10Output), (node27Piece11Input, node27Piece11Output), (node27Piece12Input, node27Piece12Output)]

theorem node27Pieces_input : VectorCertificate (node27Pieces.flatMap Prod.fst) node25 := by decide +kernel

theorem node27Pieces_each : ∀ p ∈ node27Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-8) (evaluate p.1) = evaluate p.2 := by
  simp only [node27Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node27Piece0_value, node27Piece1_value, node27Piece2_value, node27Piece3_value, node27Piece4_value, node27Piece5_value, node27Piece6_value, node27Piece7_value, node27Piece8_value, node27Piece9_value, node27Piece10_value, node27Piece11_value, node27Piece12_value, by simp⟩
end VOA.Classification.COne.OrbC2h
