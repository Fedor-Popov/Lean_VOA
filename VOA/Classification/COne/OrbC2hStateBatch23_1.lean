import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode19
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node23Piece16Input_sector0 : RawPoly ℕ := [(-440, [2, 2, 2, 4])]

def node23Piece16Input : SectorVector := [(0, node23Piece16Input_sector0)]
def node23Piece16Output_sector0_chunk0 : RawPoly ℕ := [(-1760, [1, 1, 1, 2, 2, 2, 4, 7]), (-5280, [1, 1, 2, 2, 2, 2, 4, 6]), (-5280, [1, 1, 2, 2, 2, 3, 4, 5]), (-2640, [1, 1, 2, 2, 2, 4, 4, 4]), (-21120, [1, 1, 2, 2, 2, 12]), (-31680, [1, 1, 2, 2, 4, 10]), (-5280, [1, 2, 2, 2, 2, 2, 4, 5]), (-10560, [1, 2, 2, 2, 2, 3, 4, 4]), (-42240, [1, 2, 2, 2, 2, 11]), (-1760, [1, 2, 2, 2, 3, 3, 3, 4]), (-42240, [1, 2, 2, 2, 3, 10]), (-80960, [1, 2, 2, 2, 4, 9]), (-42240, [1, 2, 2, 2, 5, 8]), (-42240, [1, 2, 2, 2, 6, 7]), (-63360, [1, 2, 2, 3, 4, 8]), (-63360, [1, 2, 2, 4, 4, 7]), (-63360, [1, 2, 2, 4, 5, 6]), (-253440, [1, 2, 2, 15]), (-126720, [1, 2, 4, 13]), (-1760, [2, 2, 2, 2, 2, 2, 4, 4]), (-2640, [2, 2, 2, 2, 2, 3, 3, 4]), (-21120, [2, 2, 2, 2, 2, 10]), (-42240, [2, 2, 2, 2, 3, 9]), (-64680, [2, 2, 2, 2, 4, 8])]

def node23Piece16Output_sector0_chunk1 : RawPoly ℕ := [(-42240, [2, 2, 2, 2, 5, 7]), (-21120, [2, 2, 2, 2, 6, 6]), (-21120, [2, 2, 2, 3, 3, 8]), (-107360, [2, 2, 2, 3, 4, 7]), (-42240, [2, 2, 2, 3, 5, 6]), (-92840, [2, 2, 2, 4, 4, 6]), (-58080, [2, 2, 2, 4, 5, 5]), (417120, [2, 2, 2, 14]), (-31680, [2, 2, 3, 3, 4, 6]), (-63360, [2, 2, 3, 4, 4, 5]), (-253440, [2, 2, 3, 13]), (-10560, [2, 2, 4, 4, 4, 4]), (203280, [2, 2, 4, 12]), (-253440, [2, 2, 5, 11]), (-253440, [2, 2, 6, 10]), (-253440, [2, 2, 7, 9]), (-126720, [2, 2, 8, 8]), (-126720, [2, 3, 4, 11]), (-126720, [2, 4, 4, 10]), (-126720, [2, 4, 5, 9]), (-126720, [2, 4, 6, 8]), (-63360, [2, 4, 7, 7]), (-506880, [2, 18]), (-84480, [4, 16])]

def node23Piece16Output_sector0 : RawPoly ℕ := [node23Piece16Output_sector0_chunk0, node23Piece16Output_sector0_chunk1].flatten

def node23Piece16Output : SectorVector := [(0, node23Piece16Output_sector0)]
theorem node23Piece16_check : VectorCertificate (neutralBoundS JR (-7) node23Piece16Input) node23Piece16Output := by decide +kernel
theorem node23Piece16_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece16Input) = evaluate node23Piece16Output :=
  neutralBound_value JR _ _ _ node23Piece16_check

def node23Piece17Input_sector0 : RawPoly ℕ := [(320/3, [2, 2, 3, 3])]

def node23Piece17Input : SectorVector := [(0, node23Piece17Input_sector0)]
def node23Piece17Output_sector0_chunk0 : RawPoly ℕ := [(1280/3, [1, 1, 1, 2, 2, 3, 3, 7]), (1280, [1, 1, 2, 2, 2, 3, 3, 6]), (1280, [1, 1, 2, 2, 3, 3, 3, 5]), (640, [1, 1, 2, 2, 3, 3, 4, 4]), (7680, [1, 1, 2, 2, 3, 11]), (5120, [1, 1, 2, 3, 3, 10]), (1280, [1, 2, 2, 2, 2, 3, 3, 5]), (2560, [1, 2, 2, 2, 3, 3, 3, 4]), (15360, [1, 2, 2, 2, 3, 10]), (1280/3, [1, 2, 2, 3, 3, 3, 3, 3]), (58880/3, [1, 2, 2, 3, 3, 9]), (15360, [1, 2, 2, 3, 4, 8]), (15360, [1, 2, 2, 3, 5, 7]), (7680, [1, 2, 2, 3, 6, 6]), (23040, [1, 2, 2, 15]), (10240, [1, 2, 3, 3, 3, 8]), (10240, [1, 2, 3, 3, 4, 7]), (10240, [1, 2, 3, 3, 5, 6]), (61440, [1, 2, 3, 14]), (10240, [1, 3, 3, 13]), (1280/3, [2, 2, 2, 2, 2, 3, 3, 4]), (640, [2, 2, 2, 2, 3, 3, 3, 3]), (7680, [2, 2, 2, 2, 3, 9]), (18240, [2, 2, 2, 3, 3, 8])]

def node23Piece17Output_sector0_chunk1 : RawPoly ℕ := [(15360, [2, 2, 2, 3, 4, 7]), (15360, [2, 2, 2, 3, 5, 6]), (23040, [2, 2, 2, 14]), (55040/3, [2, 2, 3, 3, 3, 7]), (82880/3, [2, 2, 3, 3, 4, 6]), (14080, [2, 2, 3, 3, 5, 5]), (7680, [2, 2, 3, 4, 4, 5]), (-104960, [2, 2, 3, 13]), (23040, [2, 2, 4, 12]), (23040, [2, 2, 5, 11]), (23040, [2, 2, 6, 10]), (23040, [2, 2, 7, 9]), (11520, [2, 2, 8, 8]), (5120, [2, 3, 3, 3, 3, 6]), (10240, [2, 3, 3, 3, 4, 5]), (5120/3, [2, 3, 3, 4, 4, 4]), (-67840/3, [2, 3, 3, 12]), (61440, [2, 3, 4, 11]), (61440, [2, 3, 5, 10]), (61440, [2, 3, 6, 9]), (61440, [2, 3, 7, 8]), (92160, [2, 18]), (10240, [3, 3, 3, 11]), (10240, [3, 3, 4, 10])]

def node23Piece17Output_sector0_chunk2 : RawPoly ℕ := [(10240, [3, 3, 5, 9]), (10240, [3, 3, 6, 8]), (5120, [3, 3, 7, 7]), (61440, [3, 17])]

def node23Piece17Output_sector0 : RawPoly ℕ := [node23Piece17Output_sector0_chunk0, node23Piece17Output_sector0_chunk1, node23Piece17Output_sector0_chunk2].flatten

def node23Piece17Output : SectorVector := [(0, node23Piece17Output_sector0)]
theorem node23Piece17_check : VectorCertificate (neutralBoundS JR (-7) node23Piece17Input) node23Piece17Output := by decide +kernel
theorem node23Piece17_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece17Input) = evaluate node23Piece17Output :=
  neutralBound_value JR _ _ _ node23Piece17_check

def node23Piece18Input_sector0 : RawPoly ℕ := [(-120, [2, 8])]

def node23Piece18Input : SectorVector := [(0, node23Piece18Input_sector0)]
def node23Piece18Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 2, 7, 8]), (-1440, [1, 1, 2, 2, 6, 8]), (-1440, [1, 1, 2, 3, 5, 8]), (-720, [1, 1, 2, 4, 4, 8]), (-11520, [1, 1, 2, 16]), (-2880, [1, 1, 8, 10]), (-1440, [1, 2, 2, 2, 5, 8]), (-2880, [1, 2, 2, 3, 4, 8]), (-23040, [1, 2, 2, 15]), (-480, [1, 2, 3, 3, 3, 8]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-23040, [1, 2, 7, 10]), (-22080, [1, 2, 8, 9]), (-5760, [1, 3, 8, 8]), (-5760, [1, 4, 7, 8]), (-5760, [1, 5, 6, 8]), (-46080, [1, 19]), (-480, [2, 2, 2, 2, 4, 8]), (-720, [2, 2, 2, 3, 3, 8]), (-11520, [2, 2, 2, 14]), (-23040, [2, 2, 3, 13])]

def node23Piece18Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10]), (-23040, [2, 2, 7, 9]), (-11880, [2, 2, 8, 8]), (-11520, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9]), (-29280, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-31080, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-15840, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (742080, [2, 18]), (-2880, [3, 3, 6, 8]), (-5760, [3, 4, 5, 8]), (-46080, [3, 17]), (-960, [4, 4, 4, 8]), (-46080, [4, 16]), (-46080, [5, 15])]

def node23Piece18Output_sector0_chunk2 : RawPoly ℕ := [(-46080, [6, 14]), (-46080, [7, 13]), (6960, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node23Piece18Output_sector0 : RawPoly ℕ := [node23Piece18Output_sector0_chunk0, node23Piece18Output_sector0_chunk1, node23Piece18Output_sector0_chunk2].flatten

def node23Piece18Output : SectorVector := [(0, node23Piece18Output_sector0)]
theorem node23Piece18_check : VectorCertificate (neutralBoundS JR (-7) node23Piece18Input) node23Piece18Output := by decide +kernel
theorem node23Piece18_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece18Input) = evaluate node23Piece18Output :=
  neutralBound_value JR _ _ _ node23Piece18_check

def node23Piece19Input_sector0 : RawPoly ℕ := [(960/7, [3, 7])]

def node23Piece19Input : SectorVector := [(0, node23Piece19Input_sector0)]
def node23Piece19Output_sector0_chunk0 : RawPoly ℕ := [(3840/7, [1, 1, 1, 3, 7, 7]), (11520/7, [1, 1, 2, 3, 6, 7]), (11520/7, [1, 1, 3, 3, 5, 7]), (5760/7, [1, 1, 3, 4, 4, 7]), (11520, [1, 1, 3, 15]), (34560/7, [1, 1, 7, 11]), (11520/7, [1, 2, 2, 3, 5, 7]), (23040/7, [1, 2, 3, 3, 4, 7]), (23040, [1, 2, 3, 14]), (69120/7, [1, 2, 7, 10]), (3840/7, [1, 3, 3, 3, 3, 7]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (176640/7, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (69120/7, [1, 4, 7, 8]), (69120/7, [1, 5, 7, 7]), (34560/7, [1, 6, 6, 7]), (69120, [1, 19]), (3840/7, [2, 2, 2, 3, 4, 7]), (5760/7, [2, 2, 3, 3, 3, 7]), (11520, [2, 2, 3, 13])]

def node23Piece19Output_sector0_chunk1 : RawPoly ℕ := [(34560/7, [2, 2, 7, 9]), (23040, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (23040, [2, 3, 5, 10]), (23040, [2, 3, 6, 9]), (210240/7, [2, 3, 7, 8]), (69120/7, [2, 4, 7, 7]), (69120/7, [2, 5, 6, 7]), (69120, [2, 18]), (11520, [3, 3, 3, 11]), (23040, [3, 3, 4, 10]), (23040, [3, 3, 5, 9]), (23040, [3, 3, 6, 8]), (119040/7, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (35520, [3, 4, 6, 7]), (126720/7, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-599040, [3, 17]), (34560/7, [4, 4, 5, 7]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14])]

def node23Piece19Output_sector0_chunk2 : RawPoly ℕ := [(-368640/7, [7, 13]), (69120, [8, 12]), (69120, [9, 11]), (34560, [10, 10])]

def node23Piece19Output_sector0 : RawPoly ℕ := [node23Piece19Output_sector0_chunk0, node23Piece19Output_sector0_chunk1, node23Piece19Output_sector0_chunk2].flatten

def node23Piece19Output : SectorVector := [(0, node23Piece19Output_sector0)]
theorem node23Piece19_check : VectorCertificate (neutralBoundS JR (-7) node23Piece19Input) node23Piece19Output := by decide +kernel
theorem node23Piece19_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece19Input) = evaluate node23Piece19Output :=
  neutralBound_value JR _ _ _ node23Piece19_check

def node23Piece20Input_sector0 : RawPoly ℕ := [(-80, [4, 6])]

def node23Piece20Input : SectorVector := [(0, node23Piece20Input_sector0)]
def node23Piece20Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 4, 6, 7]), (-960, [1, 1, 2, 4, 6, 6]), (-960, [1, 1, 3, 4, 5, 6]), (-480, [1, 1, 4, 4, 4, 6]), (-5760, [1, 1, 4, 14]), (-3840, [1, 1, 6, 12]), (-960, [1, 2, 2, 4, 5, 6]), (-1920, [1, 2, 3, 4, 4, 6]), (-11520, [1, 2, 4, 13]), (-7680, [1, 2, 6, 11]), (-320, [1, 3, 3, 3, 4, 6]), (-11520, [1, 3, 4, 12]), (-7680, [1, 3, 6, 10]), (-11520, [1, 4, 4, 11]), (-11520, [1, 4, 5, 10]), (-14720, [1, 4, 6, 9]), (-11520, [1, 4, 7, 8]), (-7680, [1, 5, 6, 8]), (-7680, [1, 6, 6, 7]), (-46080, [1, 19]), (-320, [2, 2, 2, 4, 4, 6]), (-480, [2, 2, 3, 3, 4, 6]), (-5760, [2, 2, 4, 12]), (-3840, [2, 2, 6, 10])]

def node23Piece20Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 3, 4, 11]), (-7680, [2, 3, 6, 9]), (-11520, [2, 4, 4, 10]), (-11520, [2, 4, 5, 9]), (-17520, [2, 4, 6, 8]), (-5760, [2, 4, 7, 7]), (-7680, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (-46080, [2, 18]), (-5760, [3, 3, 4, 10]), (-3840, [3, 3, 6, 8]), (-11520, [3, 4, 4, 9]), (-11520, [3, 4, 5, 8]), (-19520, [3, 4, 6, 7]), (-7680, [3, 5, 6, 6]), (-46080, [3, 17]), (-5760, [4, 4, 4, 8]), (-11520, [4, 4, 5, 7]), (-11120, [4, 4, 6, 6]), (-10560, [4, 5, 5, 6]), (232800, [4, 16]), (-46080, [5, 15]), (75840, [6, 14]), (-46080, [7, 13])]

def node23Piece20Output_sector0_chunk2 : RawPoly ℕ := [(-46080, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node23Piece20Output_sector0 : RawPoly ℕ := [node23Piece20Output_sector0_chunk0, node23Piece20Output_sector0_chunk1, node23Piece20Output_sector0_chunk2].flatten

def node23Piece20Output : SectorVector := [(0, node23Piece20Output_sector0)]
theorem node23Piece20_check : VectorCertificate (neutralBoundS JR (-7) node23Piece20Input) node23Piece20Output := by decide +kernel
theorem node23Piece20_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece20Input) = evaluate node23Piece20Output :=
  neutralBound_value JR _ _ _ node23Piece20_check

def node23Piece21Input_sector0 : RawPoly ℕ := [(96/5, [5, 5])]

def node23Piece21Input : SectorVector := [(0, node23Piece21Input_sector0)]
def node23Piece21Output_sector0_chunk0 : RawPoly ℕ := [(384/5, [1, 1, 1, 5, 5, 7]), (1152/5, [1, 1, 2, 5, 5, 6]), (1152/5, [1, 1, 3, 5, 5, 5]), (576/5, [1, 1, 4, 4, 5, 5]), (2304, [1, 1, 5, 13]), (1152/5, [1, 2, 2, 5, 5, 5]), (2304/5, [1, 2, 3, 4, 5, 5]), (4608, [1, 2, 5, 12]), (384/5, [1, 3, 3, 3, 5, 5]), (4608, [1, 3, 5, 11]), (4608, [1, 4, 5, 10]), (17664/5, [1, 5, 5, 9]), (4608, [1, 5, 6, 8]), (2304, [1, 5, 7, 7]), (11520, [1, 19]), (384/5, [2, 2, 2, 4, 5, 5]), (576/5, [2, 2, 3, 3, 5, 5]), (2304, [2, 2, 5, 11]), (4608, [2, 3, 5, 10]), (4608, [2, 4, 5, 9]), (21024/5, [2, 5, 5, 8]), (4608, [2, 5, 6, 7]), (11520, [2, 18]), (2304, [3, 3, 5, 9])]

def node23Piece21Output_sector0_chunk1 : RawPoly ℕ := [(4608, [3, 4, 5, 8]), (23424/5, [3, 5, 5, 7]), (2304, [3, 5, 6, 6]), (11520, [3, 17]), (2304, [4, 4, 5, 7]), (24864/5, [4, 5, 5, 6]), (11520, [4, 16]), (4992/5, [5, 5, 5, 5]), (-79872, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node23Piece21Output_sector0 : RawPoly ℕ := [node23Piece21Output_sector0_chunk0, node23Piece21Output_sector0_chunk1].flatten

def node23Piece21Output : SectorVector := [(0, node23Piece21Output_sector0)]
theorem node23Piece21_check : VectorCertificate (neutralBoundS JR (-7) node23Piece21Input) node23Piece21Output := by decide +kernel
theorem node23Piece21_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-7)
    (evaluate node23Piece21Input) = evaluate node23Piece21Output :=
  neutralBound_value JR _ _ _ node23Piece21_check

end VOA.Classification.COne.OrbC2h
