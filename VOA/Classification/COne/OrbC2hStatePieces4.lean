import VOA.Classification.COne.OrbC2hStateNode3
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node4Piece0Input_sector0 : RawPoly ℕ := [(256/15015, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2])]

def node4Piece0Input : SectorVector := [(0, node4Piece0Input_sector0)]
def node4Piece0Output_sector0 : RawPoly ℕ := [(1024/15015, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (2048/5005, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (1536/455, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (2048/5005, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (17408/3003, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (36864/5005, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (1024/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (34816/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (4096/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (2048/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (12288/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (12288/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (24576/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8])]

def node4Piece0Output : SectorVector := [(0, node4Piece0Output_sector0)]
theorem node4Piece0_check : VectorCertificate (neutralBoundS JR (-2) node4Piece0Input) node4Piece0Output := by decide +kernel
theorem node4Piece0_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece0Input) = evaluate node4Piece0Output :=
  neutralBound_value JR _ _ _ node4Piece0_check

def node4Piece1Input_sector0 : RawPoly ℕ := [(4736/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4])]

def node4Piece1Input : SectorVector := [(0, node4Piece1Input_sector0)]
def node4Piece1Output_sector0 : RawPoly ℕ := [(18944/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (75776/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (151552/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (151552/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (274688/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (75776/1155, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (246272/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (75776/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (1098752/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (18944/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (151552/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (151552/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (151552/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (75776/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (37888/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (37888/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (151552/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (37888/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8])]

def node4Piece1Output : SectorVector := [(0, node4Piece1Output_sector0)]
theorem node4Piece1_check : VectorCertificate (neutralBoundS JR (-2) node4Piece1Input) node4Piece1Output := by decide +kernel
theorem node4Piece1_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece1Input) = evaluate node4Piece1Output :=
  neutralBound_value JR _ _ _ node4Piece1_check

def node4Piece2Input_sector0 : RawPoly ℕ := [(1024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3])]

def node4Piece2Input : SectorVector := [(0, node4Piece2Input_sector0)]
def node4Piece2Output_sector0_chunk0 : RawPoly ℕ := [(4096/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (8192/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (8192/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (26624/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (8192/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (16384/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (4096/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (311296/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (145408/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (49152/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (16384/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (8192/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (8192/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (352256/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (32768/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (16384/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (73728/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (49152/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9])]

def node4Piece2Output_sector0_chunk1 : RawPoly ℕ := [(65536/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8])]

def node4Piece2Output_sector0 : RawPoly ℕ := [node4Piece2Output_sector0_chunk0, node4Piece2Output_sector0_chunk1].flatten

def node4Piece2Output : SectorVector := [(0, node4Piece2Output_sector0)]
theorem node4Piece2_check : VectorCertificate (neutralBoundS JR (-2) node4Piece2Input) node4Piece2Output := by decide +kernel
theorem node4Piece2_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece2Input) = evaluate node4Piece2Output :=
  neutralBound_value JR _ _ _ node4Piece2_check

def node4Piece3Input_sector0 : RawPoly ℕ := [(64/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2])]

def node4Piece3Input : SectorVector := [(0, node4Piece3Input_sector0)]
def node4Piece3Output_sector0 : RawPoly ℕ := [(256/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (5248/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (512/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (18688/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (256/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (11776/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (4608/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (2048, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8])]

def node4Piece3Output : SectorVector := [(0, node4Piece3Output_sector0)]
theorem node4Piece3_check : VectorCertificate (neutralBoundS JR (-2) node4Piece3Input) node4Piece3Output := by decide +kernel
theorem node4Piece3_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece3Input) = evaluate node4Piece3Output :=
  neutralBound_value JR _ _ _ node4Piece3_check

def node4Piece4Input_sector0 : RawPoly ℕ := [(64/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 6])]

def node4Piece4Input : SectorVector := [(0, node4Piece4Input_sector0)]
def node4Piece4Output_sector0 : RawPoly ℕ := [(256/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (5248/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (23296/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (1024, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (512, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (-17920/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (256, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (9216, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (7168, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (6144, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (6144, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (36864, [1, 1, 1, 1, 1, 1, 1, 13]), (14336, [1, 1, 1, 1, 1, 1, 6, 8])]

def node4Piece4Output : SectorVector := [(0, node4Piece4Output_sector0)]
theorem node4Piece4_check : VectorCertificate (neutralBoundS JR (-2) node4Piece4Input) node4Piece4Output := by decide +kernel
theorem node4Piece4_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece4Input) = evaluate node4Piece4Output :=
  neutralBound_value JR _ _ _ node4Piece4_check

def node4Piece5Input_sector0 : RawPoly ℕ := [(768/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 5])]

def node4Piece5Input : SectorVector := [(0, node4Piece5Input_sector0)]
def node4Piece5Output_sector0_chunk0 : RawPoly ℕ := [(3072/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (18432/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (198144/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (18432/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (52224/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (9216/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-27648/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (36864/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (331776/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (18432/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (24576/35, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (147456/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (147456/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (147456/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (172032/5, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (294912/35, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (147456/35, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node4Piece5Output_sector0_chunk1 : RawPoly ℕ := [(294912/7, [1, 1, 1, 1, 1, 1, 1, 13]), (73728/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (73728/5, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (73728, [1, 1, 1, 1, 1, 1, 2, 12]), (147456/5, [1, 1, 1, 1, 1, 1, 5, 9]), (147456/5, [1, 1, 1, 1, 1, 2, 5, 8])]

def node4Piece5Output_sector0 : RawPoly ℕ := [node4Piece5Output_sector0_chunk0, node4Piece5Output_sector0_chunk1].flatten

def node4Piece5Output : SectorVector := [(0, node4Piece5Output_sector0)]
theorem node4Piece5_check : VectorCertificate (neutralBoundS JR (-2) node4Piece5Input) node4Piece5Output := by decide +kernel
theorem node4Piece5_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece5Input) = evaluate node4Piece5Output :=
  neutralBound_value JR _ _ _ node4Piece5_check

def node4Piece6Input_sector0 : RawPoly ℕ := [(128/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 4])]

def node4Piece6Input : SectorVector := [(0, node4Piece6Input_sector0)]
def node4Piece6Output_sector0_chunk0 : RawPoly ℕ := [(512/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (3072/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (4096/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (1280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (2048/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (41984/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (29696/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (18176/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (12288/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (6144/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (4096/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (32768/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (28672/3, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (16384/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (24576/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5])]

def node4Piece6Output_sector0_chunk1 : RawPoly ℕ := [(98304/7, [1, 1, 1, 1, 1, 1, 1, 13]), (4096, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (4096, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (16384, [1, 1, 1, 1, 1, 1, 3, 11]), (12288, [1, 1, 1, 1, 1, 1, 4, 10]), (8192, [1, 1, 1, 1, 1, 3, 4, 8])]

def node4Piece6Output_sector0 : RawPoly ℕ := [node4Piece6Output_sector0_chunk0, node4Piece6Output_sector0_chunk1].flatten

def node4Piece6Output : SectorVector := [(0, node4Piece6Output_sector0)]
theorem node4Piece6_check : VectorCertificate (neutralBoundS JR (-2) node4Piece6Input) node4Piece6Output := by decide +kernel
theorem node4Piece6_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece6Input) = evaluate node4Piece6Output :=
  neutralBound_value JR _ _ _ node4Piece6_check

def node4Piece7Input_sector0 : RawPoly ℕ := [(16, [1, 1, 1, 1, 1, 1, 1, 2, 2, 4])]

def node4Piece7Input : SectorVector := [(0, node4Piece7Input_sector0)]
def node4Piece7Output_sector0_chunk0 : RawPoly ℕ := [(64, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (3552, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (6144, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (5056, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (256, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (3712, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (6144, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (12288, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (6144, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (6144, [1, 1, 1, 1, 1, 1, 1, 13]), (448, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (10752, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (10752, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (23296, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (5376, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5])]

def node4Piece7Output_sector0_chunk1 : RawPoly ℕ := [(10752, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (5376, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (43008, [1, 1, 1, 1, 1, 1, 2, 12]), (10752, [1, 1, 1, 1, 1, 1, 4, 10]), (8064, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (8064, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (32256, [1, 1, 1, 1, 1, 2, 2, 11]), (32256, [1, 1, 1, 1, 1, 2, 4, 9]), (13440, [1, 1, 1, 1, 2, 2, 4, 8])]

def node4Piece7Output_sector0 : RawPoly ℕ := [node4Piece7Output_sector0_chunk0, node4Piece7Output_sector0_chunk1].flatten

def node4Piece7Output : SectorVector := [(0, node4Piece7Output_sector0)]
theorem node4Piece7_check : VectorCertificate (neutralBoundS JR (-2) node4Piece7Input) node4Piece7Output := by decide +kernel
theorem node4Piece7_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece7Input) = evaluate node4Piece7Output :=
  neutralBound_value JR _ _ _ node4Piece7_check

def node4Piece8Input_sector0 : RawPoly ℕ := [(-640/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3])]

def node4Piece8Input : SectorVector := [(0, node4Piece8Input_sector0)]
def node4Piece8Output_sector0_chunk0 : RawPoly ℕ := [(-2560/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (-15360/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (-5120/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (-30720/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (-57600/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-46080/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (-5120/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]), (-61440/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-15360/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (-171520/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (-46080/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (-135680/7, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-46080/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-46080/7, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-92160/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-61440/7, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-30720/7, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-92160/7, [1, 1, 1, 1, 1, 1, 1, 13]), (-2560/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (-30720, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-133120/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-30720, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-46080, [1, 1, 1, 1, 1, 1, 2, 12]), (-10240, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5])]

def node4Piece8Output_sector0_chunk1 : RawPoly ℕ := [(-5120, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-61440, [1, 1, 1, 1, 1, 1, 3, 11]), (-15360, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-15360, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-92160, [1, 1, 1, 1, 1, 2, 3, 10]), (-30720, [1, 1, 1, 1, 1, 3, 3, 9]), (-25600, [1, 1, 1, 1, 2, 3, 3, 8])]

def node4Piece8Output_sector0 : RawPoly ℕ := [node4Piece8Output_sector0_chunk0, node4Piece8Output_sector0_chunk1].flatten

def node4Piece8Output : SectorVector := [(0, node4Piece8Output_sector0)]
theorem node4Piece8_check : VectorCertificate (neutralBoundS JR (-2) node4Piece8Input) node4Piece8Output := by decide +kernel
theorem node4Piece8_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece8Input) = evaluate node4Piece8Output :=
  neutralBound_value JR _ _ _ node4Piece8_check

def node4Piece9Input_sector0 : RawPoly ℕ := [(8, [1, 1, 1, 1, 1, 1, 1, 8])]

def node4Piece9Input : SectorVector := [(0, node4Piece9Input_sector0)]
def node4Piece9Output_sector0_chunk0 : RawPoly ℕ := [(32, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (2160, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (2912, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (768, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (768, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-24192, [1, 1, 1, 1, 1, 1, 1, 13]), (224, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (10752, [1, 1, 1, 1, 1, 1, 2, 12]), (10752, [1, 1, 1, 1, 1, 1, 3, 11]), (10752, [1, 1, 1, 1, 1, 1, 4, 10]), (10752, [1, 1, 1, 1, 1, 1, 5, 9]), (11648, [1, 1, 1, 1, 1, 1, 6, 8]), (5376, [1, 1, 1, 1, 1, 1, 7, 7]), (4032, [1, 1, 1, 1, 1, 2, 5, 8])]

def node4Piece9Output_sector0_chunk1 : RawPoly ℕ := [(4032, [1, 1, 1, 1, 1, 3, 4, 8]), (32256, [1, 1, 1, 1, 1, 15]), (6720, [1, 1, 1, 1, 8, 8])]

def node4Piece9Output_sector0 : RawPoly ℕ := [node4Piece9Output_sector0_chunk0, node4Piece9Output_sector0_chunk1].flatten

def node4Piece9Output : SectorVector := [(0, node4Piece9Output_sector0)]
theorem node4Piece9_check : VectorCertificate (neutralBoundS JR (-2) node4Piece9Input) node4Piece9Output := by decide +kernel
theorem node4Piece9_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece9Input) = evaluate node4Piece9Output :=
  neutralBound_value JR _ _ _ node4Piece9_check

def node4Piece10Input_sector0 : RawPoly ℕ := [(64/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 3])]

def node4Piece10Input : SectorVector := [(0, node4Piece10Input_sector0)]
def node4Piece10Output_sector0_chunk0 : RawPoly ℕ := [(256/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (1536, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (6016, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (9216, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (6144, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (16384/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (9088, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (21504, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (9216, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (4608, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (6144, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (6144, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (18432, [1, 1, 1, 1, 1, 1, 2, 12]), (4096, [1, 1, 1, 1, 1, 1, 3, 11]), (512, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (9216, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (28160, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (9216, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (18432, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (9216, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4])]

def node4Piece10Output_sector0_chunk1 : RawPoly ℕ := [(55296, [1, 1, 1, 1, 1, 2, 2, 11]), (36864, [1, 1, 1, 1, 1, 2, 3, 10]), (7680, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (7680, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (23040, [1, 1, 1, 1, 2, 2, 2, 10]), (46080, [1, 1, 1, 1, 2, 2, 3, 9]), (10240, [1, 1, 1, 2, 2, 2, 3, 8])]

def node4Piece10Output_sector0 : RawPoly ℕ := [node4Piece10Output_sector0_chunk0, node4Piece10Output_sector0_chunk1].flatten

def node4Piece10Output : SectorVector := [(0, node4Piece10Output_sector0)]
theorem node4Piece10_check : VectorCertificate (neutralBoundS JR (-2) node4Piece10Input) node4Piece10Output := by decide +kernel
theorem node4Piece10_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece10Input) = evaluate node4Piece10Output :=
  neutralBound_value JR _ _ _ node4Piece10_check

def node4Piece11Input_sector0 : RawPoly ℕ := [(64/7, [1, 1, 1, 1, 1, 1, 2, 7])]

def node4Piece11Input : SectorVector := [(0, node4Piece11Input_sector0)]
def node4Piece11Output_sector0_chunk0 : RawPoly ℕ := [(256/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (768, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (18048/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1536, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (1536/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (3072, [1, 1, 1, 1, 1, 1, 1, 13]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (21760/7, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (1536, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (768, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (768, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (1536, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (256, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-16256, [1, 1, 1, 1, 1, 1, 2, 12]), (3072, [1, 1, 1, 1, 1, 1, 3, 11]), (3072, [1, 1, 1, 1, 1, 1, 4, 10]), (3072, [1, 1, 1, 1, 1, 1, 5, 9]), (3072, [1, 1, 1, 1, 1, 1, 6, 8]), (16896/7, [1, 1, 1, 1, 1, 1, 7, 7]), (1536/7, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (9216, [1, 1, 1, 1, 1, 2, 2, 11])]

def node4Piece11Output_sector0_chunk1 : RawPoly ℕ := [(9216, [1, 1, 1, 1, 1, 2, 3, 10]), (9216, [1, 1, 1, 1, 1, 2, 4, 9]), (9216, [1, 1, 1, 1, 1, 2, 5, 8]), (84480/7, [1, 1, 1, 1, 1, 2, 6, 7]), (18432/7, [1, 1, 1, 1, 1, 3, 5, 7]), (9216/7, [1, 1, 1, 1, 1, 4, 4, 7]), (18432, [1, 1, 1, 1, 1, 15]), (23040/7, [1, 1, 1, 1, 2, 2, 5, 7]), (23040/7, [1, 1, 1, 1, 2, 3, 4, 7]), (23040, [1, 1, 1, 1, 2, 14]), (46080/7, [1, 1, 1, 1, 7, 9]), (30720/7, [1, 1, 1, 2, 7, 8])]

def node4Piece11Output_sector0 : RawPoly ℕ := [node4Piece11Output_sector0_chunk0, node4Piece11Output_sector0_chunk1].flatten

def node4Piece11Output : SectorVector := [(0, node4Piece11Output_sector0)]
theorem node4Piece11_check : VectorCertificate (neutralBoundS JR (-2) node4Piece11Input) node4Piece11Output := by decide +kernel
theorem node4Piece11_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece11Input) = evaluate node4Piece11Output :=
  neutralBound_value JR _ _ _ node4Piece11_check

def node4Piece12Input_sector0 : RawPoly ℕ := [(-64, [1, 1, 1, 1, 1, 1, 3, 6])]

def node4Piece12Input : SectorVector := [(0, node4Piece12Input_sector0)]
def node4Piece12Output_sector0_chunk0 : RawPoly ℕ := [(-256, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (-4608, [1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (-2304, [1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (-9216, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-4608, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-9216, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-18048, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-4608, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-27648, [1, 1, 1, 1, 1, 1, 1, 13]), (-4608, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-2304, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-20992, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-9216, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-27648, [1, 1, 1, 1, 1, 1, 2, 12]), (-4608, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-4608, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (53760, [1, 1, 1, 1, 1, 1, 3, 11]), (-27648, [1, 1, 1, 1, 1, 1, 4, 10]), (-27648, [1, 1, 1, 1, 1, 1, 5, 9]), (-27264, [1, 1, 1, 1, 1, 1, 6, 8]), (-13824, [1, 1, 1, 1, 1, 1, 7, 7]), (-1536, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (-55296, [1, 1, 1, 1, 1, 2, 3, 10]), (-27648, [1, 1, 1, 1, 1, 2, 6, 7])]

def node4Piece12Output_sector0_chunk1 : RawPoly ℕ := [(-55296, [1, 1, 1, 1, 1, 3, 3, 9]), (-55296, [1, 1, 1, 1, 1, 3, 4, 8]), (-55296, [1, 1, 1, 1, 1, 3, 5, 7]), (-56832, [1, 1, 1, 1, 1, 3, 6, 6]), (-27648, [1, 1, 1, 1, 1, 4, 5, 6]), (-165888, [1, 1, 1, 1, 1, 15]), (-23040, [1, 1, 1, 1, 2, 3, 5, 6]), (-23040, [1, 1, 1, 1, 3, 3, 4, 6]), (-138240, [1, 1, 1, 1, 3, 13]), (-69120, [1, 1, 1, 1, 6, 10]), (-30720, [1, 1, 1, 3, 6, 8])]

def node4Piece12Output_sector0 : RawPoly ℕ := [node4Piece12Output_sector0_chunk0, node4Piece12Output_sector0_chunk1].flatten

def node4Piece12Output : SectorVector := [(0, node4Piece12Output_sector0)]
theorem node4Piece12_check : VectorCertificate (neutralBoundS JR (-2) node4Piece12Input) node4Piece12Output := by decide +kernel
theorem node4Piece12_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece12Input) = evaluate node4Piece12Output :=
  neutralBound_value JR _ _ _ node4Piece12_check

def node4Piece13Input_sector0 : RawPoly ℕ := [(-96/5, [1, 1, 1, 1, 1, 1, 4, 5])]

def node4Piece13Input : SectorVector := [(0, node4Piece13Input_sector0)]
def node4Piece13Output_sector0_chunk0 : RawPoly ℕ := [(-384/5, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (-1152, [1, 1, 1, 1, 1, 1, 1, 1, 4, 8]), (-4608/5, [1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (-2304, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-9216/5, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-2304, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-9216/5, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-22464/5, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-9216, [1, 1, 1, 1, 1, 1, 1, 13]), (-1152, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-4608/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (-34944/5, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-1152, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-9216, [1, 1, 1, 1, 1, 1, 2, 12]), (-1536/5, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-1152, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-9216, [1, 1, 1, 1, 1, 1, 3, 11]), (3456, [1, 1, 1, 1, 1, 1, 4, 10]), (-22272/5, [1, 1, 1, 1, 1, 1, 5, 9]), (-9216, [1, 1, 1, 1, 1, 1, 6, 8]), (-4608, [1, 1, 1, 1, 1, 1, 7, 7]), (-2304/5, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-13824, [1, 1, 1, 1, 1, 2, 4, 9]), (-55296/5, [1, 1, 1, 1, 1, 2, 5, 8])]

def node4Piece13Output_sector0_chunk1 : RawPoly ℕ := [(-13824, [1, 1, 1, 1, 1, 3, 4, 8]), (-55296/5, [1, 1, 1, 1, 1, 3, 5, 7]), (-13824, [1, 1, 1, 1, 1, 4, 4, 7]), (-25344, [1, 1, 1, 1, 1, 4, 5, 6]), (-27648/5, [1, 1, 1, 1, 1, 5, 5, 5]), (-55296, [1, 1, 1, 1, 1, 15]), (-6912, [1, 1, 1, 1, 2, 4, 5, 5]), (-6912, [1, 1, 1, 1, 3, 4, 4, 5]), (-34560, [1, 1, 1, 1, 4, 12]), (-27648, [1, 1, 1, 1, 5, 11]), (-9216, [1, 1, 1, 4, 5, 8])]

def node4Piece13Output_sector0 : RawPoly ℕ := [node4Piece13Output_sector0_chunk0, node4Piece13Output_sector0_chunk1].flatten

def node4Piece13Output : SectorVector := [(0, node4Piece13Output_sector0)]
theorem node4Piece13_check : VectorCertificate (neutralBoundS JR (-2) node4Piece13Input) node4Piece13Output := by decide +kernel
theorem node4Piece13_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece13Input) = evaluate node4Piece13Output :=
  neutralBound_value JR _ _ _ node4Piece13_check

def node4Piece14Input_sector0 : RawPoly ℕ := [(28/5, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2])]

def node4Piece14Input : SectorVector := [(0, node4Piece14Input_sector0)]
def node4Piece14Output_sector0 : RawPoly ℕ := [(112/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (672, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (8232/5, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (672, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (5376, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (6832/5, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (6720, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (5376, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (5376, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (10752, [1, 1, 1, 1, 1, 2, 2, 11]), (112, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (6496, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (6720, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (3360, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (26880, [1, 1, 1, 1, 2, 2, 2, 10]), (1344, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (1344, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (13440, [1, 1, 1, 2, 2, 2, 2, 9]), (1344, [1, 1, 2, 2, 2, 2, 2, 8])]

def node4Piece14Output : SectorVector := [(0, node4Piece14Output_sector0)]
theorem node4Piece14_check : VectorCertificate (neutralBoundS JR (-2) node4Piece14Input) node4Piece14Output := by decide +kernel
theorem node4Piece14_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece14Input) = evaluate node4Piece14Output :=
  neutralBound_value JR _ _ _ node4Piece14_check

def node4Piece15Input_sector0 : RawPoly ℕ := [(56, [1, 1, 1, 1, 1, 2, 2, 6])]

def node4Piece15Input : SectorVector := [(0, node4Piece15Input_sector0)]
def node4Piece15Output_sector0_chunk0 : RawPoly ℕ := [(224, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (4032, [1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (2688, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (8064, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (8064, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (16464, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (4032, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (2688, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (32256, [1, 1, 1, 1, 1, 1, 2, 12]), (5376, [1, 1, 1, 1, 1, 1, 6, 8]), (4032, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (17696, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (8064, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (4032, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (4032, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-47040, [1, 1, 1, 1, 1, 2, 2, 11]), (32256, [1, 1, 1, 1, 1, 2, 3, 10]), (32256, [1, 1, 1, 1, 1, 2, 4, 9]), (32256, [1, 1, 1, 1, 1, 2, 5, 8]), (43008, [1, 1, 1, 1, 1, 2, 6, 7]), (5376, [1, 1, 1, 1, 1, 3, 6, 6]), (5376, [1, 1, 1, 1, 1, 4, 5, 6]), (32256, [1, 1, 1, 1, 1, 15]), (1120, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6])]

def node4Piece15Output_sector0_chunk1 : RawPoly ℕ := [(40320, [1, 1, 1, 1, 2, 2, 2, 10]), (40320, [1, 1, 1, 1, 2, 2, 3, 9]), (40320, [1, 1, 1, 1, 2, 2, 4, 8]), (40320, [1, 1, 1, 1, 2, 2, 5, 7]), (44800, [1, 1, 1, 1, 2, 2, 6, 6]), (26880, [1, 1, 1, 1, 2, 3, 5, 6]), (13440, [1, 1, 1, 1, 2, 4, 4, 6]), (161280, [1, 1, 1, 1, 2, 14]), (26880, [1, 1, 1, 1, 6, 10]), (13440, [1, 1, 1, 2, 2, 2, 5, 6]), (13440, [1, 1, 1, 2, 2, 3, 4, 6]), (80640, [1, 1, 1, 2, 2, 13]), (53760, [1, 1, 1, 2, 6, 9]), (13440, [1, 1, 2, 2, 6, 8])]

def node4Piece15Output_sector0 : RawPoly ℕ := [node4Piece15Output_sector0_chunk0, node4Piece15Output_sector0_chunk1].flatten

def node4Piece15Output : SectorVector := [(0, node4Piece15Output_sector0)]
theorem node4Piece15_check : VectorCertificate (neutralBoundS JR (-2) node4Piece15Input) node4Piece15Output := by decide +kernel
theorem node4Piece15_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece15Input) = evaluate node4Piece15Output :=
  neutralBound_value JR _ _ _ node4Piece15_check

def node4Piece16Input_sector0 : RawPoly ℕ := [(-64/5, [1, 1, 1, 1, 1, 2, 3, 5])]

def node4Piece16Input : SectorVector := [(0, node4Piece16Input_sector0)]
def node4Piece16Output_sector0_chunk0 : RawPoly ℕ := [(-256/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (-768, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-2304/5, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-1536/5, [1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (-1536, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (-4608/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (-1536, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-18816/5, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-4608, [1, 1, 1, 1, 1, 1, 2, 12]), (-1536/5, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-3072, [1, 1, 1, 1, 1, 1, 3, 11]), (-9216/5, [1, 1, 1, 1, 1, 1, 5, 9]), (-768, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (-2304/5, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-19456/5, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-768, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-4608, [1, 1, 1, 1, 1, 2, 2, 11]), (-768, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (2304, [1, 1, 1, 1, 1, 2, 3, 10]), (-4608, [1, 1, 1, 1, 1, 2, 4, 9]), (-27264/5, [1, 1, 1, 1, 1, 2, 5, 8]), (-4608, [1, 1, 1, 1, 1, 2, 6, 7]), (-3072, [1, 1, 1, 1, 1, 3, 3, 9]), (-3072, [1, 1, 1, 1, 1, 3, 4, 8])]

def node4Piece16Output_sector0_chunk1 : RawPoly ℕ := [(-27648/5, [1, 1, 1, 1, 1, 3, 5, 7]), (-1536, [1, 1, 1, 1, 1, 3, 6, 6]), (-9216/5, [1, 1, 1, 1, 1, 4, 5, 6]), (-4608/5, [1, 1, 1, 1, 1, 5, 5, 5]), (-9216, [1, 1, 1, 1, 1, 15]), (-256, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-7680, [1, 1, 1, 1, 2, 2, 3, 9]), (-4608, [1, 1, 1, 1, 2, 2, 5, 7]), (-7680, [1, 1, 1, 1, 2, 3, 3, 8]), (-7680, [1, 1, 1, 1, 2, 3, 4, 7]), (-14848, [1, 1, 1, 1, 2, 3, 5, 6]), (-4608, [1, 1, 1, 1, 2, 4, 5, 5]), (-23040, [1, 1, 1, 1, 2, 14]), (-3072, [1, 1, 1, 1, 3, 3, 5, 5]), (-1536, [1, 1, 1, 1, 3, 4, 4, 5]), (-15360, [1, 1, 1, 1, 3, 13]), (-9216, [1, 1, 1, 1, 5, 11]), (-3072, [1, 1, 1, 2, 2, 3, 5, 5]), (-3072, [1, 1, 1, 2, 3, 3, 4, 5]), (-15360, [1, 1, 1, 2, 3, 12]), (-9216, [1, 1, 1, 2, 5, 10]), (-6144, [1, 1, 1, 3, 5, 9]), (-3072, [1, 1, 2, 3, 5, 8])]

def node4Piece16Output_sector0 : RawPoly ℕ := [node4Piece16Output_sector0_chunk0, node4Piece16Output_sector0_chunk1].flatten

def node4Piece16Output : SectorVector := [(0, node4Piece16Output_sector0)]
theorem node4Piece16_check : VectorCertificate (neutralBoundS JR (-2) node4Piece16Input) node4Piece16Output := by decide +kernel
theorem node4Piece16_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece16Input) = evaluate node4Piece16Output :=
  neutralBound_value JR _ _ _ node4Piece16_check

def node4Piece17Input_sector0 : RawPoly ℕ := [(-102, [1, 1, 1, 1, 1, 2, 4, 4])]

def node4Piece17Input : SectorVector := [(0, node4Piece17Input_sector0)]
def node4Piece17Output_sector0_chunk0 : RawPoly ℕ := [(-408, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (-9792, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-2448, [1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-19584, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-19584, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-20196, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-39168, [1, 1, 1, 1, 1, 1, 2, 12]), (-2448, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-39168, [1, 1, 1, 1, 1, 1, 4, 10]), (-9792, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-34680, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-39168, [1, 1, 1, 1, 1, 2, 2, 11]), (-3264, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-39168, [1, 1, 1, 1, 1, 2, 3, 10]), (-8160, [1, 1, 1, 1, 1, 2, 4, 9]), (-39168, [1, 1, 1, 1, 1, 2, 5, 8]), (-39168, [1, 1, 1, 1, 1, 2, 6, 7]), (-39168, [1, 1, 1, 1, 1, 3, 4, 8]), (-44064, [1, 1, 1, 1, 1, 4, 4, 7]), (-39168, [1, 1, 1, 1, 1, 4, 5, 6]), (-78336, [1, 1, 1, 1, 1, 15]), (-2040, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (-97920, [1, 1, 1, 1, 2, 2, 4, 8]), (-97920, [1, 1, 1, 1, 2, 3, 4, 7])]

def node4Piece17Output_sector0_chunk1 : RawPoly ℕ := [(-118320, [1, 1, 1, 1, 2, 4, 4, 6]), (-48960, [1, 1, 1, 1, 2, 4, 5, 5]), (-195840, [1, 1, 1, 1, 2, 14]), (-24480, [1, 1, 1, 1, 3, 4, 4, 5]), (-12240, [1, 1, 1, 1, 4, 4, 4, 4]), (-195840, [1, 1, 1, 1, 4, 12]), (-24480, [1, 1, 1, 2, 2, 4, 4, 5]), (-24480, [1, 1, 1, 2, 3, 4, 4, 4]), (-195840, [1, 1, 1, 2, 4, 11]), (-48960, [1, 1, 1, 4, 4, 9]), (-24480, [1, 1, 2, 4, 4, 8])]

def node4Piece17Output_sector0 : RawPoly ℕ := [node4Piece17Output_sector0_chunk0, node4Piece17Output_sector0_chunk1].flatten

def node4Piece17Output : SectorVector := [(0, node4Piece17Output_sector0)]
theorem node4Piece17_check : VectorCertificate (neutralBoundS JR (-2) node4Piece17Input) node4Piece17Output := by decide +kernel
theorem node4Piece17_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece17Input) = evaluate node4Piece17Output :=
  neutralBound_value JR _ _ _ node4Piece17_check

def node4Piece18Input_sector0 : RawPoly ℕ := [(-592/3, [1, 1, 1, 1, 1, 3, 3, 4])]

def node4Piece18Input : SectorVector := [(0, node4Piece18Input_sector0)]
def node4Piece18Output_sector0_chunk0 : RawPoly ℕ := [(-2368/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (-9472, [1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (-14208, [1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (-18944, [1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (-28416, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-18944, [1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-48544, [1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (-113664, [1, 1, 1, 1, 1, 1, 3, 11]), (-42624, [1, 1, 1, 1, 1, 1, 4, 10]), (-9472, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (-14208, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-172864/3, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-113664, [1, 1, 1, 1, 1, 2, 3, 10]), (-42624, [1, 1, 1, 1, 1, 2, 4, 9]), (-9472/3, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (-137344/3, [1, 1, 1, 1, 1, 3, 3, 9]), (-125504, [1, 1, 1, 1, 1, 3, 4, 8]), (-113664, [1, 1, 1, 1, 1, 3, 5, 7]), (-56832, [1, 1, 1, 1, 1, 3, 6, 6]), (-42624, [1, 1, 1, 1, 1, 4, 4, 7]), (-42624, [1, 1, 1, 1, 1, 4, 5, 6]), (-170496, [1, 1, 1, 1, 1, 15]), (-11840/3, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-94720, [1, 1, 1, 1, 2, 3, 3, 8])]

def node4Piece18Output_sector0_chunk1 : RawPoly ℕ := [(-142080, [1, 1, 1, 1, 2, 3, 4, 7]), (-94720, [1, 1, 1, 1, 3, 3, 3, 7]), (-686720/3, [1, 1, 1, 1, 3, 3, 4, 6]), (-47360, [1, 1, 1, 1, 3, 3, 5, 5]), (-142080, [1, 1, 1, 1, 3, 4, 4, 5]), (-568320, [1, 1, 1, 1, 3, 13]), (-213120, [1, 1, 1, 1, 4, 12]), (-47360, [1, 1, 1, 2, 3, 3, 4, 5]), (-47360, [1, 1, 1, 3, 3, 3, 4, 4]), (-189440, [1, 1, 1, 3, 3, 11]), (-284160, [1, 1, 1, 3, 4, 10]), (-47360, [1, 1, 3, 3, 4, 8])]

def node4Piece18Output_sector0 : RawPoly ℕ := [node4Piece18Output_sector0_chunk0, node4Piece18Output_sector0_chunk1].flatten

def node4Piece18Output : SectorVector := [(0, node4Piece18Output_sector0)]
theorem node4Piece18_check : VectorCertificate (neutralBoundS JR (-2) node4Piece18Input) node4Piece18Output := by decide +kernel
theorem node4Piece18_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece18Input) = evaluate node4Piece18Output :=
  neutralBound_value JR _ _ _ node4Piece18_check

def node4Piece19Input_sector0 : RawPoly ℕ := [(-312/5, [1, 1, 1, 1, 1, 10])]

def node4Piece19Input : SectorVector := [(0, node4Piece19Input_sector0)]
def node4Piece19Output_sector0_chunk0 : RawPoly ℕ := [(-1248/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (-7488, [1, 1, 1, 1, 1, 1, 1, 13]), (-14976, [1, 1, 1, 1, 1, 1, 2, 12]), (-14976, [1, 1, 1, 1, 1, 1, 3, 11]), (-91728/5, [1, 1, 1, 1, 1, 1, 4, 10]), (-14976, [1, 1, 1, 1, 1, 1, 5, 9]), (-14976, [1, 1, 1, 1, 1, 1, 6, 8]), (-7488, [1, 1, 1, 1, 1, 1, 7, 7]), (-7488, [1, 1, 1, 1, 1, 2, 2, 11]), (-113568/5, [1, 1, 1, 1, 1, 2, 3, 10]), (-14976, [1, 1, 1, 1, 1, 2, 4, 9]), (-14976, [1, 1, 1, 1, 1, 2, 5, 8]), (-14976, [1, 1, 1, 1, 1, 2, 6, 7]), (-7488, [1, 1, 1, 1, 1, 3, 3, 9]), (-14976, [1, 1, 1, 1, 1, 3, 4, 8]), (-14976, [1, 1, 1, 1, 1, 3, 5, 7]), (-7488, [1, 1, 1, 1, 1, 3, 6, 6]), (-7488, [1, 1, 1, 1, 1, 4, 4, 7]), (-14976, [1, 1, 1, 1, 1, 4, 5, 6]), (-2496, [1, 1, 1, 1, 1, 5, 5, 5]), (409344, [1, 1, 1, 1, 1, 15]), (-1248, [1, 1, 1, 1, 2, 2, 2, 10]), (-74880, [1, 1, 1, 1, 2, 14]), (-74880, [1, 1, 1, 1, 3, 13])]

def node4Piece19Output_sector0_chunk1 : RawPoly ℕ := [(-74880, [1, 1, 1, 1, 4, 12]), (-74880, [1, 1, 1, 1, 5, 11]), (-72384, [1, 1, 1, 1, 6, 10]), (-74880, [1, 1, 1, 1, 7, 9]), (-37440, [1, 1, 1, 1, 8, 8]), (-14976, [1, 1, 1, 2, 5, 10]), (-14976, [1, 1, 1, 3, 4, 10]), (-149760, [1, 1, 1, 17]), (-14976, [1, 1, 8, 10])]

def node4Piece19Output_sector0 : RawPoly ℕ := [node4Piece19Output_sector0_chunk0, node4Piece19Output_sector0_chunk1].flatten

def node4Piece19Output : SectorVector := [(0, node4Piece19Output_sector0)]
theorem node4Piece19_check : VectorCertificate (neutralBoundS JR (-2) node4Piece19Input) node4Piece19Output := by decide +kernel
theorem node4Piece19_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece19Input) = evaluate node4Piece19Output :=
  neutralBound_value JR _ _ _ node4Piece19_check

def node4Piece20Input_sector0 : RawPoly ℕ := [(128, [1, 1, 1, 1, 2, 2, 2, 5])]

def node4Piece20Input : SectorVector := [(0, node4Piece20Input_sector0)]
def node4Piece20Output_sector0_chunk0 : RawPoly ℕ := [(512, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (7680, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (9216, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (15360, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (15360, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (39168, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (9216, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (92160, [1, 1, 1, 1, 1, 2, 2, 11]), (36864, [1, 1, 1, 1, 1, 2, 5, 8]), (7680, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (37376, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (7680, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (7680, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-23040, [1, 1, 1, 1, 2, 2, 2, 10]), (92160, [1, 1, 1, 1, 2, 2, 3, 9]), (92160, [1, 1, 1, 1, 2, 2, 4, 8]), (129024, [1, 1, 1, 1, 2, 2, 5, 7]), (46080, [1, 1, 1, 1, 2, 2, 6, 6]), (36864, [1, 1, 1, 1, 2, 3, 5, 6]), (36864, [1, 1, 1, 1, 2, 4, 5, 5]), (184320, [1, 1, 1, 1, 2, 14]), (24576, [1, 1, 1, 1, 5, 11]), (2048, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (61440, [1, 1, 1, 2, 2, 2, 2, 9])]

def node4Piece20Output_sector0_chunk1 : RawPoly ℕ := [(61440, [1, 1, 1, 2, 2, 2, 3, 8]), (61440, [1, 1, 1, 2, 2, 2, 4, 7]), (124928, [1, 1, 1, 2, 2, 2, 5, 6]), (73728, [1, 1, 1, 2, 2, 3, 5, 5]), (36864, [1, 1, 1, 2, 2, 4, 4, 5]), (368640, [1, 1, 1, 2, 2, 13]), (147456, [1, 1, 1, 2, 5, 10]), (18432, [1, 1, 2, 2, 2, 2, 5, 5]), (18432, [1, 1, 2, 2, 2, 3, 4, 5]), (92160, [1, 1, 2, 2, 2, 12]), (110592, [1, 1, 2, 2, 5, 9]), (12288, [1, 2, 2, 2, 5, 8])]

def node4Piece20Output_sector0 : RawPoly ℕ := [node4Piece20Output_sector0_chunk0, node4Piece20Output_sector0_chunk1].flatten

def node4Piece20Output : SectorVector := [(0, node4Piece20Output_sector0)]
theorem node4Piece20_check : VectorCertificate (neutralBoundS JR (-2) node4Piece20Input) node4Piece20Output := by decide +kernel
theorem node4Piece20_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece20Input) = evaluate node4Piece20Output :=
  neutralBound_value JR _ _ _ node4Piece20_check

def node4Piece21Input_sector0 : RawPoly ℕ := [(-160, [1, 1, 1, 1, 3, 8])]

def node4Piece21Input : SectorVector := [(0, node4Piece21Input_sector0)]
def node4Piece21Output_sector0_chunk0 : RawPoly ℕ := [(-640, [1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (-15360, [1, 1, 1, 1, 1, 1, 3, 11]), (-5760, [1, 1, 1, 1, 1, 1, 6, 8]), (-30720, [1, 1, 1, 1, 1, 2, 3, 10]), (-11520, [1, 1, 1, 1, 1, 2, 5, 8]), (-30720, [1, 1, 1, 1, 1, 3, 3, 9]), (-48960, [1, 1, 1, 1, 1, 3, 4, 8]), (-30720, [1, 1, 1, 1, 1, 3, 5, 7]), (-15360, [1, 1, 1, 1, 1, 3, 6, 6]), (-92160, [1, 1, 1, 1, 1, 15]), (-15360, [1, 1, 1, 1, 2, 2, 3, 9]), (-5760, [1, 1, 1, 1, 2, 2, 4, 8]), (-52480, [1, 1, 1, 1, 2, 3, 3, 8]), (-30720, [1, 1, 1, 1, 2, 3, 4, 7]), (-30720, [1, 1, 1, 1, 2, 3, 5, 6]), (-92160, [1, 1, 1, 1, 2, 14]), (-15360, [1, 1, 1, 1, 3, 3, 3, 7]), (-30720, [1, 1, 1, 1, 3, 3, 4, 6]), (-15360, [1, 1, 1, 1, 3, 3, 5, 5]), (-15360, [1, 1, 1, 1, 3, 4, 4, 5]), (483840, [1, 1, 1, 1, 3, 13]), (-92160, [1, 1, 1, 1, 4, 12]), (-92160, [1, 1, 1, 1, 5, 11]), (-92160, [1, 1, 1, 1, 6, 10])]

def node4Piece21Output_sector0_chunk1 : RawPoly ℕ := [(-92160, [1, 1, 1, 1, 7, 9]), (-22080, [1, 1, 1, 1, 8, 8]), (-2560, [1, 1, 1, 2, 2, 2, 3, 8]), (-122880, [1, 1, 1, 2, 3, 12]), (-46080, [1, 1, 1, 2, 7, 8]), (-122880, [1, 1, 1, 3, 3, 11]), (-122880, [1, 1, 1, 3, 4, 10]), (-122880, [1, 1, 1, 3, 5, 9]), (-156160, [1, 1, 1, 3, 6, 8]), (-61440, [1, 1, 1, 3, 7, 7]), (-46080, [1, 1, 1, 4, 5, 8]), (-368640, [1, 1, 1, 17]), (-23040, [1, 1, 2, 3, 5, 8]), (-23040, [1, 1, 3, 3, 4, 8]), (-184320, [1, 1, 3, 15]), (-69120, [1, 1, 8, 10]), (-15360, [1, 3, 8, 8])]

def node4Piece21Output_sector0 : RawPoly ℕ := [node4Piece21Output_sector0_chunk0, node4Piece21Output_sector0_chunk1].flatten

def node4Piece21Output : SectorVector := [(0, node4Piece21Output_sector0)]
theorem node4Piece21_check : VectorCertificate (neutralBoundS JR (-2) node4Piece21Input) node4Piece21Output := by decide +kernel
theorem node4Piece21_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece21Input) = evaluate node4Piece21Output :=
  neutralBound_value JR _ _ _ node4Piece21_check

def node4Piece22Input_sector0 : RawPoly ℕ := [(-1440/7, [1, 1, 1, 1, 4, 7])]

def node4Piece22Input : SectorVector := [(0, node4Piece22Input_sector0)]
def node4Piece22Output_sector0_chunk0 : RawPoly ℕ := [(-5760/7, [1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (-17280, [1, 1, 1, 1, 1, 1, 4, 10]), (-69120/7, [1, 1, 1, 1, 1, 1, 7, 7]), (-34560, [1, 1, 1, 1, 1, 2, 4, 9]), (-138240/7, [1, 1, 1, 1, 1, 2, 6, 7]), (-34560, [1, 1, 1, 1, 1, 3, 4, 8]), (-138240/7, [1, 1, 1, 1, 1, 3, 5, 7]), (-371520/7, [1, 1, 1, 1, 1, 4, 4, 7]), (-34560, [1, 1, 1, 1, 1, 4, 5, 6]), (-138240, [1, 1, 1, 1, 1, 15]), (-17280, [1, 1, 1, 1, 2, 2, 4, 8]), (-69120/7, [1, 1, 1, 1, 2, 2, 5, 7]), (-74880, [1, 1, 1, 1, 2, 3, 4, 7]), (-34560, [1, 1, 1, 1, 2, 4, 4, 6]), (-17280, [1, 1, 1, 1, 2, 4, 5, 5]), (-138240, [1, 1, 1, 1, 2, 14]), (-23040/7, [1, 1, 1, 1, 3, 3, 3, 7]), (-17280, [1, 1, 1, 1, 3, 3, 4, 6]), (-34560, [1, 1, 1, 1, 3, 4, 4, 5]), (-138240, [1, 1, 1, 1, 3, 13]), (-5760, [1, 1, 1, 1, 4, 4, 4, 4]), (365760, [1, 1, 1, 1, 4, 12]), (-138240, [1, 1, 1, 1, 5, 11]), (-138240, [1, 1, 1, 1, 6, 10])]

def node4Piece22Output_sector0_chunk1 : RawPoly ℕ := [(-334080/7, [1, 1, 1, 1, 7, 9]), (-69120, [1, 1, 1, 1, 8, 8]), (-23040/7, [1, 1, 1, 2, 2, 2, 4, 7]), (-138240, [1, 1, 1, 2, 4, 11]), (-552960/7, [1, 1, 1, 2, 7, 8]), (-138240, [1, 1, 1, 3, 4, 10]), (-552960/7, [1, 1, 1, 3, 7, 7]), (-138240, [1, 1, 1, 4, 4, 9]), (-138240, [1, 1, 1, 4, 5, 8]), (-1405440/7, [1, 1, 1, 4, 6, 7]), (-276480/7, [1, 1, 1, 5, 5, 7]), (-552960, [1, 1, 1, 17]), (-207360/7, [1, 1, 2, 4, 5, 7]), (-207360/7, [1, 1, 3, 4, 4, 7]), (-207360, [1, 1, 4, 14]), (-829440/7, [1, 1, 7, 11]), (-138240/7, [1, 4, 7, 8])]

def node4Piece22Output_sector0 : RawPoly ℕ := [node4Piece22Output_sector0_chunk0, node4Piece22Output_sector0_chunk1].flatten

def node4Piece22Output : SectorVector := [(0, node4Piece22Output_sector0)]
theorem node4Piece22_check : VectorCertificate (neutralBoundS JR (-2) node4Piece22Input) node4Piece22Output := by decide +kernel
theorem node4Piece22_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece22Input) = evaluate node4Piece22Output :=
  neutralBound_value JR _ _ _ node4Piece22_check

def node4Piece23Input_sector0 : RawPoly ℕ := [(-64, [1, 1, 1, 1, 5, 6])]

def node4Piece23Input : SectorVector := [(0, node4Piece23Input_sector0)]
def node4Piece23Output_sector0_chunk0 : RawPoly ℕ := [(-256, [1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (-4608, [1, 1, 1, 1, 1, 1, 5, 9]), (-3840, [1, 1, 1, 1, 1, 1, 6, 8]), (-9216, [1, 1, 1, 1, 1, 2, 5, 8]), (-7680, [1, 1, 1, 1, 1, 2, 6, 7]), (-9216, [1, 1, 1, 1, 1, 3, 5, 7]), (-7680, [1, 1, 1, 1, 1, 3, 6, 6]), (-19584, [1, 1, 1, 1, 1, 4, 5, 6]), (-4608, [1, 1, 1, 1, 1, 5, 5, 5]), (-46080, [1, 1, 1, 1, 1, 15]), (-4608, [1, 1, 1, 1, 2, 2, 5, 7]), (-3840, [1, 1, 1, 1, 2, 2, 6, 6]), (-23296, [1, 1, 1, 1, 2, 3, 5, 6]), (-3840, [1, 1, 1, 1, 2, 4, 4, 6]), (-9216, [1, 1, 1, 1, 2, 4, 5, 5]), (-46080, [1, 1, 1, 1, 2, 14]), (-3840, [1, 1, 1, 1, 3, 3, 4, 6]), (-4608, [1, 1, 1, 1, 3, 3, 5, 5]), (-4608, [1, 1, 1, 1, 3, 4, 4, 5]), (-46080, [1, 1, 1, 1, 3, 13]), (-46080, [1, 1, 1, 1, 4, 12]), (53760, [1, 1, 1, 1, 5, 11]), (11520, [1, 1, 1, 1, 6, 10]), (-46080, [1, 1, 1, 1, 7, 9])]

def node4Piece23Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [1, 1, 1, 1, 8, 8]), (-1024, [1, 1, 1, 2, 2, 2, 5, 6]), (-36864, [1, 1, 1, 2, 5, 10]), (-30720, [1, 1, 1, 2, 6, 9]), (-36864, [1, 1, 1, 3, 5, 9]), (-30720, [1, 1, 1, 3, 6, 8]), (-36864, [1, 1, 1, 4, 5, 8]), (-30720, [1, 1, 1, 4, 6, 7]), (-36864, [1, 1, 1, 5, 5, 7]), (-44032, [1, 1, 1, 5, 6, 6]), (-184320, [1, 1, 1, 17]), (-9216, [1, 1, 2, 5, 5, 6]), (-9216, [1, 1, 3, 4, 5, 6]), (-55296, [1, 1, 5, 13]), (-46080, [1, 1, 6, 12]), (-6144, [1, 5, 6, 8])]

def node4Piece23Output_sector0 : RawPoly ℕ := [node4Piece23Output_sector0_chunk0, node4Piece23Output_sector0_chunk1].flatten

def node4Piece23Output : SectorVector := [(0, node4Piece23Output_sector0)]
theorem node4Piece23_check : VectorCertificate (neutralBoundS JR (-2) node4Piece23Input) node4Piece23Output := by decide +kernel
theorem node4Piece23_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece23Input) = evaluate node4Piece23Output :=
  neutralBound_value JR _ _ _ node4Piece23_check

def node4Piece24Input_sector0 : RawPoly ℕ := [(-80, [1, 1, 1, 2, 2, 2, 2, 4])]

def node4Piece24Input : SectorVector := [(0, node4Piece24Input_sector0)]
def node4Piece24Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (-3840, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (-7680, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-7680, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (-7680, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-21600, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (-7680, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-61440, [1, 1, 1, 1, 2, 2, 2, 10]), (-46080, [1, 1, 1, 1, 2, 2, 4, 8]), (-3840, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (-21440, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-1280, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (-18560, [1, 1, 1, 2, 2, 2, 2, 9]), (-61440, [1, 1, 1, 2, 2, 2, 3, 8]), (-92160, [1, 1, 1, 2, 2, 2, 4, 7]), (-61440, [1, 1, 1, 2, 2, 2, 5, 6]), (-46080, [1, 1, 1, 2, 2, 3, 4, 6]), (-46080, [1, 1, 1, 2, 2, 4, 4, 5]), (-184320, [1, 1, 1, 2, 2, 13]), (-61440, [1, 1, 1, 2, 4, 11]), (-960, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-23040, [1, 1, 2, 2, 2, 2, 2, 8]), (-23040, [1, 1, 2, 2, 2, 2, 3, 7]), (-61440, [1, 1, 2, 2, 2, 2, 4, 6])]

def node4Piece24Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [1, 1, 2, 2, 2, 2, 5, 5]), (-46080, [1, 1, 2, 2, 2, 3, 4, 5]), (-23040, [1, 1, 2, 2, 2, 4, 4, 4]), (-184320, [1, 1, 2, 2, 2, 12]), (-138240, [1, 1, 2, 2, 4, 10]), (-5760, [1, 2, 2, 2, 2, 2, 4, 5]), (-5760, [1, 2, 2, 2, 2, 3, 4, 4]), (-23040, [1, 2, 2, 2, 2, 11]), (-46080, [1, 2, 2, 2, 4, 9]), (-1920, [2, 2, 2, 2, 4, 8])]

def node4Piece24Output_sector0 : RawPoly ℕ := [node4Piece24Output_sector0_chunk0, node4Piece24Output_sector0_chunk1].flatten

def node4Piece24Output : SectorVector := [(0, node4Piece24Output_sector0)]
theorem node4Piece24_check : VectorCertificate (neutralBoundS JR (-2) node4Piece24Input) node4Piece24Output := by decide +kernel
theorem node4Piece24_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece24Input) = evaluate node4Piece24Output :=
  neutralBound_value JR _ _ _ node4Piece24_check

def node4Piece25Input_sector0 : RawPoly ℕ := [(800/3, [1, 1, 1, 2, 2, 2, 3, 3])]

def node4Piece25Input : SectorVector := [(0, node4Piece25Input_sector0)]
def node4Piece25Output_sector0_chunk0 : RawPoly ℕ := [(3200/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (19200, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (19200, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (38400, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (84800, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (57600, [1, 1, 1, 1, 2, 2, 2, 10]), (19200, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (230400, [1, 1, 1, 1, 2, 2, 3, 9]), (76800, [1, 1, 1, 1, 2, 3, 3, 8]), (19200, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (176000/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (57600, [1, 1, 1, 2, 2, 2, 2, 9]), (169600, [1, 1, 1, 2, 2, 2, 3, 8]), (57600, [1, 1, 1, 2, 2, 2, 4, 7]), (57600, [1, 1, 1, 2, 2, 2, 5, 6]), (268800, [1, 1, 1, 2, 2, 3, 3, 7]), (230400, [1, 1, 1, 2, 2, 3, 4, 6]), (115200, [1, 1, 1, 2, 2, 3, 5, 5]), (345600, [1, 1, 1, 2, 2, 13]), (76800, [1, 1, 1, 2, 3, 3, 3, 6]), (76800, [1, 1, 1, 2, 3, 3, 4, 5]), (460800, [1, 1, 1, 2, 3, 12]), (51200, [1, 1, 1, 3, 3, 11]), (3200, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3])]

def node4Piece25Output_sector0_chunk1 : RawPoly ℕ := [(115200, [1, 1, 2, 2, 2, 2, 3, 7]), (204800, [1, 1, 2, 2, 2, 3, 3, 6]), (115200, [1, 1, 2, 2, 2, 3, 4, 5]), (172800, [1, 1, 2, 2, 2, 12]), (115200, [1, 1, 2, 2, 3, 3, 3, 5]), (57600, [1, 1, 2, 2, 3, 3, 4, 4]), (691200, [1, 1, 2, 2, 3, 11]), (230400, [1, 1, 2, 3, 3, 10]), (19200, [1, 2, 2, 2, 2, 3, 3, 5]), (19200, [1, 2, 2, 2, 3, 3, 3, 4]), (115200, [1, 2, 2, 2, 3, 10]), (115200, [1, 2, 2, 3, 3, 9]), (6400, [2, 2, 2, 3, 3, 8])]

def node4Piece25Output_sector0 : RawPoly ℕ := [node4Piece25Output_sector0_chunk0, node4Piece25Output_sector0_chunk1].flatten

def node4Piece25Output : SectorVector := [(0, node4Piece25Output_sector0)]
theorem node4Piece25_check : VectorCertificate (neutralBoundS JR (-2) node4Piece25Input) node4Piece25Output := by decide +kernel
theorem node4Piece25_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece25Input) = evaluate node4Piece25Output :=
  neutralBound_value JR _ _ _ node4Piece25_check

def node4Piece26Input_sector0 : RawPoly ℕ := [(120, [1, 1, 1, 2, 2, 8])]

def node4Piece26Input : SectorVector := [(0, node4Piece26Input_sector0)]
def node4Piece26Output_sector0_chunk0 : RawPoly ℕ := [(480, [1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (11520, [1, 1, 1, 1, 1, 2, 2, 11]), (5760, [1, 1, 1, 1, 1, 2, 5, 8]), (23040, [1, 1, 1, 1, 2, 2, 2, 10]), (23040, [1, 1, 1, 1, 2, 2, 3, 9]), (38160, [1, 1, 1, 1, 2, 2, 4, 8]), (23040, [1, 1, 1, 1, 2, 2, 5, 7]), (11520, [1, 1, 1, 1, 2, 2, 6, 6]), (5760, [1, 1, 1, 1, 2, 3, 3, 8]), (92160, [1, 1, 1, 1, 2, 14]), (11520, [1, 1, 1, 1, 8, 8]), (11520, [1, 1, 1, 2, 2, 2, 2, 9]), (37920, [1, 1, 1, 2, 2, 2, 3, 8]), (23040, [1, 1, 1, 2, 2, 2, 4, 7]), (23040, [1, 1, 1, 2, 2, 2, 5, 6]), (11520, [1, 1, 1, 2, 2, 3, 3, 7]), (23040, [1, 1, 1, 2, 2, 3, 4, 6]), (11520, [1, 1, 1, 2, 2, 3, 5, 5]), (11520, [1, 1, 1, 2, 2, 4, 4, 5]), (-362880, [1, 1, 1, 2, 2, 13]), (92160, [1, 1, 1, 2, 3, 12]), (92160, [1, 1, 1, 2, 4, 11]), (92160, [1, 1, 1, 2, 5, 10]), (92160, [1, 1, 1, 2, 6, 9])]

def node4Piece26Output_sector0_chunk1 : RawPoly ℕ := [(92160, [1, 1, 1, 2, 7, 8]), (11520, [1, 1, 1, 3, 6, 8]), (11520, [1, 1, 1, 4, 5, 8]), (92160, [1, 1, 1, 17]), (1440, [1, 1, 2, 2, 2, 2, 2, 8]), (69120, [1, 1, 2, 2, 2, 12]), (69120, [1, 1, 2, 2, 3, 11]), (69120, [1, 1, 2, 2, 4, 10]), (69120, [1, 1, 2, 2, 5, 9]), (92160, [1, 1, 2, 2, 6, 8]), (34560, [1, 1, 2, 2, 7, 7]), (34560, [1, 1, 2, 3, 5, 8]), (17280, [1, 1, 2, 4, 4, 8]), (276480, [1, 1, 2, 16]), (34560, [1, 1, 8, 10]), (8640, [1, 2, 2, 2, 5, 8]), (8640, [1, 2, 2, 3, 4, 8]), (69120, [1, 2, 2, 15]), (34560, [1, 2, 8, 9]), (2880, [2, 2, 8, 8])]

def node4Piece26Output_sector0 : RawPoly ℕ := [node4Piece26Output_sector0_chunk0, node4Piece26Output_sector0_chunk1].flatten

def node4Piece26Output : SectorVector := [(0, node4Piece26Output_sector0)]
theorem node4Piece26_check : VectorCertificate (neutralBoundS JR (-2) node4Piece26Input) node4Piece26Output := by decide +kernel
theorem node4Piece26_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece26Input) = evaluate node4Piece26Output :=
  neutralBound_value JR _ _ _ node4Piece26_check

def node4Piece27Input_sector0 : RawPoly ℕ := [(1600/7, [1, 1, 1, 2, 3, 7])]

def node4Piece27Input : SectorVector := [(0, node4Piece27Input_sector0)]
def node4Piece27Output_sector0_chunk0 : RawPoly ℕ := [(6400/7, [1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (19200, [1, 1, 1, 1, 1, 2, 3, 10]), (57600/7, [1, 1, 1, 1, 1, 2, 6, 7]), (38400/7, [1, 1, 1, 1, 1, 3, 5, 7]), (38400, [1, 1, 1, 1, 2, 2, 3, 9]), (115200/7, [1, 1, 1, 1, 2, 2, 5, 7]), (38400, [1, 1, 1, 1, 2, 3, 3, 8]), (508800/7, [1, 1, 1, 1, 2, 3, 4, 7]), (38400, [1, 1, 1, 1, 2, 3, 5, 6]), (115200, [1, 1, 1, 1, 2, 14]), (38400/7, [1, 1, 1, 1, 3, 3, 3, 7]), (76800, [1, 1, 1, 1, 3, 13]), (230400/7, [1, 1, 1, 1, 7, 9]), (19200, [1, 1, 1, 2, 2, 2, 3, 8]), (57600/7, [1, 1, 1, 2, 2, 2, 4, 7]), (486400/7, [1, 1, 1, 2, 2, 3, 3, 7]), (38400, [1, 1, 1, 2, 2, 3, 4, 6]), (19200, [1, 1, 1, 2, 2, 3, 5, 5]), (115200, [1, 1, 1, 2, 2, 13]), (19200, [1, 1, 1, 2, 3, 3, 3, 6]), (38400, [1, 1, 1, 2, 3, 3, 4, 5]), (6400, [1, 1, 1, 2, 3, 4, 4, 4]), (-406400, [1, 1, 1, 2, 3, 12]), (115200, [1, 1, 1, 2, 4, 11])]

def node4Piece27Output_sector0_chunk1 : RawPoly ℕ := [(115200, [1, 1, 1, 2, 5, 10]), (115200, [1, 1, 1, 2, 6, 9]), (681600/7, [1, 1, 1, 2, 7, 8]), (76800, [1, 1, 1, 3, 3, 11]), (76800, [1, 1, 1, 3, 4, 10]), (76800, [1, 1, 1, 3, 5, 9]), (76800, [1, 1, 1, 3, 6, 8]), (422400/7, [1, 1, 1, 3, 7, 7]), (230400/7, [1, 1, 1, 4, 6, 7]), (115200/7, [1, 1, 1, 5, 5, 7]), (230400, [1, 1, 1, 17]), (19200/7, [1, 1, 2, 2, 2, 2, 3, 7]), (115200, [1, 1, 2, 2, 3, 11]), (345600/7, [1, 1, 2, 2, 7, 7]), (115200, [1, 1, 2, 3, 3, 10]), (115200, [1, 1, 2, 3, 4, 9]), (115200, [1, 1, 2, 3, 5, 8]), (1228800/7, [1, 1, 2, 3, 6, 7]), (345600/7, [1, 1, 2, 4, 5, 7]), (345600, [1, 1, 2, 16]), (230400/7, [1, 1, 3, 3, 5, 7]), (115200/7, [1, 1, 3, 4, 4, 7]), (230400, [1, 1, 3, 15]), (691200/7, [1, 1, 7, 11])]

def node4Piece27Output_sector0_chunk2 : RawPoly ℕ := [(115200/7, [1, 2, 2, 3, 5, 7]), (115200/7, [1, 2, 3, 3, 4, 7]), (115200, [1, 2, 3, 14]), (345600/7, [1, 2, 7, 10]), (230400/7, [1, 3, 7, 9]), (38400/7, [2, 3, 7, 8])]

def node4Piece27Output_sector0 : RawPoly ℕ := [node4Piece27Output_sector0_chunk0, node4Piece27Output_sector0_chunk1, node4Piece27Output_sector0_chunk2].flatten

def node4Piece27Output : SectorVector := [(0, node4Piece27Output_sector0)]
theorem node4Piece27_check : VectorCertificate (neutralBoundS JR (-2) node4Piece27Input) node4Piece27Output := by decide +kernel
theorem node4Piece27_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece27Input) = evaluate node4Piece27Output :=
  neutralBound_value JR _ _ _ node4Piece27_check

def node4Piece28Input_sector0 : RawPoly ℕ := [(-200, [1, 1, 1, 2, 4, 6])]

def node4Piece28Input : SectorVector := [(0, node4Piece28Input_sector0)]
def node4Piece28Output_sector0_chunk0 : RawPoly ℕ := [(-800, [1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (-14400, [1, 1, 1, 1, 1, 2, 4, 9]), (-9600, [1, 1, 1, 1, 1, 2, 6, 7]), (-4800, [1, 1, 1, 1, 1, 4, 5, 6]), (-28800, [1, 1, 1, 1, 2, 2, 4, 8]), (-19200, [1, 1, 1, 1, 2, 2, 6, 6]), (-28800, [1, 1, 1, 1, 2, 3, 4, 7]), (-19200, [1, 1, 1, 1, 2, 3, 5, 6]), (-54000, [1, 1, 1, 1, 2, 4, 4, 6]), (-14400, [1, 1, 1, 1, 2, 4, 5, 5]), (-115200, [1, 1, 1, 1, 2, 14]), (-4800, [1, 1, 1, 1, 3, 3, 4, 6]), (-57600, [1, 1, 1, 1, 4, 12]), (-38400, [1, 1, 1, 1, 6, 10]), (-14400, [1, 1, 1, 2, 2, 2, 4, 7]), (-9600, [1, 1, 1, 2, 2, 2, 5, 6]), (-68000, [1, 1, 1, 2, 2, 3, 4, 6]), (-28800, [1, 1, 1, 2, 2, 4, 4, 5]), (-115200, [1, 1, 1, 2, 2, 13]), (-3200, [1, 1, 1, 2, 3, 3, 3, 6]), (-14400, [1, 1, 1, 2, 3, 3, 4, 5]), (-14400, [1, 1, 1, 2, 3, 4, 4, 4]), (-115200, [1, 1, 1, 2, 3, 12]), (168000, [1, 1, 1, 2, 4, 11])]

def node4Piece28Output_sector0_chunk1 : RawPoly ℕ := [(-115200, [1, 1, 1, 2, 5, 10]), (-46400, [1, 1, 1, 2, 6, 9]), (-115200, [1, 1, 1, 2, 7, 8]), (-57600, [1, 1, 1, 3, 4, 10]), (-38400, [1, 1, 1, 3, 6, 8]), (-57600, [1, 1, 1, 4, 4, 9]), (-57600, [1, 1, 1, 4, 5, 8]), (-86400, [1, 1, 1, 4, 6, 7]), (-38400, [1, 1, 1, 5, 6, 6]), (-230400, [1, 1, 1, 17]), (-2400, [1, 1, 2, 2, 2, 2, 4, 6]), (-86400, [1, 1, 2, 2, 4, 10]), (-57600, [1, 1, 2, 2, 6, 8]), (-86400, [1, 1, 2, 3, 4, 9]), (-57600, [1, 1, 2, 3, 6, 7]), (-86400, [1, 1, 2, 4, 4, 8]), (-86400, [1, 1, 2, 4, 5, 7]), (-110400, [1, 1, 2, 4, 6, 6]), (-28800, [1, 1, 2, 5, 5, 6]), (-345600, [1, 1, 2, 16]), (-28800, [1, 1, 3, 4, 5, 6]), (-14400, [1, 1, 4, 4, 4, 6]), (-172800, [1, 1, 4, 14]), (-115200, [1, 1, 6, 12])]

def node4Piece28Output_sector0_chunk2 : RawPoly ℕ := [(-14400, [1, 2, 2, 4, 5, 6]), (-14400, [1, 2, 3, 4, 4, 6]), (-86400, [1, 2, 4, 13]), (-57600, [1, 2, 6, 11]), (-28800, [1, 4, 6, 9]), (-4800, [2, 4, 6, 8])]

def node4Piece28Output_sector0 : RawPoly ℕ := [node4Piece28Output_sector0_chunk0, node4Piece28Output_sector0_chunk1, node4Piece28Output_sector0_chunk2].flatten

def node4Piece28Output : SectorVector := [(0, node4Piece28Output_sector0)]
theorem node4Piece28_check : VectorCertificate (neutralBoundS JR (-2) node4Piece28Input) node4Piece28Output := by decide +kernel
theorem node4Piece28_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece28Input) = evaluate node4Piece28Output :=
  neutralBound_value JR _ _ _ node4Piece28_check

def node4Piece29Input_sector0 : RawPoly ℕ := [(672/5, [1, 1, 1, 2, 5, 5])]

def node4Piece29Input : SectorVector := [(0, node4Piece29Input_sector0)]
def node4Piece29Output_sector0_chunk0 : RawPoly ℕ := [(2688/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (16128, [1, 1, 1, 1, 1, 2, 5, 8]), (16128/5, [1, 1, 1, 1, 1, 5, 5, 5]), (32256, [1, 1, 1, 1, 2, 2, 5, 7]), (32256, [1, 1, 1, 1, 2, 3, 5, 6]), (213696/5, [1, 1, 1, 1, 2, 4, 5, 5]), (80640, [1, 1, 1, 1, 2, 14]), (16128/5, [1, 1, 1, 1, 3, 3, 5, 5]), (64512, [1, 1, 1, 1, 5, 11]), (16128, [1, 1, 1, 2, 2, 2, 5, 6]), (45696, [1, 1, 1, 2, 2, 3, 5, 5]), (16128, [1, 1, 1, 2, 2, 4, 4, 5]), (80640, [1, 1, 1, 2, 2, 13]), (16128, [1, 1, 1, 2, 3, 3, 4, 5]), (80640, [1, 1, 1, 2, 3, 12]), (80640, [1, 1, 1, 2, 4, 11]), (-129024, [1, 1, 1, 2, 5, 10]), (80640, [1, 1, 1, 2, 6, 9]), (80640, [1, 1, 1, 2, 7, 8]), (64512, [1, 1, 1, 3, 5, 9]), (64512, [1, 1, 1, 4, 5, 8]), (290304/5, [1, 1, 1, 5, 5, 7]), (32256, [1, 1, 1, 5, 6, 6]), (161280, [1, 1, 1, 17])]

def node4Piece29Output_sector0_chunk1 : RawPoly ℕ := [(8064/5, [1, 1, 2, 2, 2, 2, 5, 5]), (96768, [1, 1, 2, 2, 5, 9]), (96768, [1, 1, 2, 3, 5, 8]), (96768, [1, 1, 2, 4, 5, 7]), (516096/5, [1, 1, 2, 5, 5, 6]), (241920, [1, 1, 2, 16]), (96768/5, [1, 1, 3, 5, 5, 5]), (48384/5, [1, 1, 4, 4, 5, 5]), (193536, [1, 1, 5, 13]), (48384/5, [1, 2, 2, 5, 5, 5]), (48384/5, [1, 2, 3, 4, 5, 5]), (96768, [1, 2, 5, 12]), (96768/5, [1, 5, 5, 9]), (16128/5, [2, 5, 5, 8])]

def node4Piece29Output_sector0 : RawPoly ℕ := [node4Piece29Output_sector0_chunk0, node4Piece29Output_sector0_chunk1].flatten

def node4Piece29Output : SectorVector := [(0, node4Piece29Output_sector0)]
theorem node4Piece29_check : VectorCertificate (neutralBoundS JR (-2) node4Piece29Input) node4Piece29Output := by decide +kernel
theorem node4Piece29_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece29Input) = evaluate node4Piece29Output :=
  neutralBound_value JR _ _ _ node4Piece29_check

def node4Piece30Input_sector0 : RawPoly ℕ := [(-192, [1, 1, 1, 3, 4, 5])]

def node4Piece30Input : SectorVector := [(0, node4Piece30Input_sector0)]
def node4Piece30Output_sector0_chunk0 : RawPoly ℕ := [(-768, [1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (-11520, [1, 1, 1, 1, 1, 3, 4, 8]), (-9216, [1, 1, 1, 1, 1, 3, 5, 7]), (-6912, [1, 1, 1, 1, 1, 4, 5, 6]), (-23040, [1, 1, 1, 1, 2, 3, 4, 7]), (-18432, [1, 1, 1, 1, 2, 3, 5, 6]), (-13824, [1, 1, 1, 1, 2, 4, 5, 5]), (-23040, [1, 1, 1, 1, 3, 3, 4, 6]), (-18432, [1, 1, 1, 1, 3, 3, 5, 5]), (-51840, [1, 1, 1, 1, 3, 4, 4, 5]), (-92160, [1, 1, 1, 1, 3, 13]), (-69120, [1, 1, 1, 1, 4, 12]), (-55296, [1, 1, 1, 1, 5, 11]), (-11520, [1, 1, 1, 2, 2, 3, 4, 6]), (-9216, [1, 1, 1, 2, 2, 3, 5, 5]), (-6912, [1, 1, 1, 2, 2, 4, 4, 5]), (-62976, [1, 1, 1, 2, 3, 3, 4, 5]), (-11520, [1, 1, 1, 2, 3, 4, 4, 4]), (-92160, [1, 1, 1, 2, 3, 12]), (-69120, [1, 1, 1, 2, 4, 11]), (-55296, [1, 1, 1, 2, 5, 10]), (-3072, [1, 1, 1, 3, 3, 3, 3, 5]), (-11520, [1, 1, 1, 3, 3, 3, 4, 4]), (-92160, [1, 1, 1, 3, 3, 11])]

def node4Piece30Output_sector0_chunk1 : RawPoly ℕ := [(34560, [1, 1, 1, 3, 4, 10]), (-44544, [1, 1, 1, 3, 5, 9]), (-92160, [1, 1, 1, 3, 6, 8]), (-46080, [1, 1, 1, 3, 7, 7]), (-69120, [1, 1, 1, 4, 4, 9]), (-81792, [1, 1, 1, 4, 5, 8]), (-69120, [1, 1, 1, 4, 6, 7]), (-55296, [1, 1, 1, 5, 5, 7]), (-27648, [1, 1, 1, 5, 6, 6]), (-276480, [1, 1, 1, 17]), (-2304, [1, 1, 2, 2, 2, 3, 4, 5]), (-69120, [1, 1, 2, 3, 4, 9]), (-55296, [1, 1, 2, 3, 5, 8]), (-41472, [1, 1, 2, 4, 5, 7]), (-69120, [1, 1, 3, 3, 4, 8]), (-55296, [1, 1, 3, 3, 5, 7]), (-69120, [1, 1, 3, 4, 4, 7]), (-147456, [1, 1, 3, 4, 5, 6]), (-27648, [1, 1, 3, 5, 5, 5]), (-276480, [1, 1, 3, 15]), (-41472, [1, 1, 4, 4, 5, 5]), (-207360, [1, 1, 4, 14]), (-165888, [1, 1, 5, 13]), (-13824, [1, 2, 3, 4, 5, 5])]

def node4Piece30Output_sector0_chunk2 : RawPoly ℕ := [(-13824, [1, 3, 3, 4, 4, 5]), (-69120, [1, 3, 4, 12]), (-55296, [1, 3, 5, 11]), (-41472, [1, 4, 5, 10]), (-4608, [3, 4, 5, 8])]

def node4Piece30Output_sector0 : RawPoly ℕ := [node4Piece30Output_sector0_chunk0, node4Piece30Output_sector0_chunk1, node4Piece30Output_sector0_chunk2].flatten

def node4Piece30Output : SectorVector := [(0, node4Piece30Output_sector0)]
theorem node4Piece30_check : VectorCertificate (neutralBoundS JR (-2) node4Piece30Input) node4Piece30Output := by decide +kernel
theorem node4Piece30_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece30Input) = evaluate node4Piece30Output :=
  neutralBound_value JR _ _ _ node4Piece30_check

def node4Piece31Input_sector0 : RawPoly ℕ := [(-120, [1, 1, 1, 4, 4, 4])]

def node4Piece31Input : SectorVector := [(0, node4Piece31Input_sector0)]
def node4Piece31Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (-17280, [1, 1, 1, 1, 1, 4, 4, 7]), (-34560, [1, 1, 1, 1, 2, 4, 4, 6]), (-34560, [1, 1, 1, 1, 3, 4, 4, 5]), (-20880, [1, 1, 1, 1, 4, 4, 4, 4]), (-138240, [1, 1, 1, 1, 4, 12]), (-17280, [1, 1, 1, 2, 2, 4, 4, 5]), (-43680, [1, 1, 1, 2, 3, 4, 4, 4]), (-138240, [1, 1, 1, 2, 4, 11]), (-5760, [1, 1, 1, 3, 3, 3, 4, 4]), (-138240, [1, 1, 1, 3, 4, 10]), (54720, [1, 1, 1, 4, 4, 9]), (-138240, [1, 1, 1, 4, 5, 8]), (-138240, [1, 1, 1, 4, 6, 7]), (-184320, [1, 1, 1, 17]), (-1440, [1, 1, 2, 2, 2, 4, 4, 4]), (-103680, [1, 1, 2, 4, 4, 8]), (-103680, [1, 1, 3, 4, 4, 7]), (-92160, [1, 1, 4, 4, 4, 6]), (-51840, [1, 1, 4, 4, 5, 5]), (-414720, [1, 1, 4, 14]), (-8640, [1, 2, 4, 4, 4, 5]), (-8640, [1, 3, 4, 4, 4, 4]), (-103680, [1, 4, 4, 11])]

def node4Piece31Output_sector0_chunk1 : RawPoly ℕ := [(-2880, [4, 4, 4, 8])]

def node4Piece31Output_sector0 : RawPoly ℕ := [node4Piece31Output_sector0_chunk0, node4Piece31Output_sector0_chunk1].flatten

def node4Piece31Output : SectorVector := [(0, node4Piece31Output_sector0)]
theorem node4Piece31_check : VectorCertificate (neutralBoundS JR (-2) node4Piece31Input) node4Piece31Output := by decide +kernel
theorem node4Piece31_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece31Input) = evaluate node4Piece31Output :=
  neutralBound_value JR _ _ _ node4Piece31_check

def node4Piece32Input_sector0 : RawPoly ℕ := [(-80, [1, 1, 1, 12])]

def node4Piece32Input : SectorVector := [(0, node4Piece32Input_sector0)]
def node4Piece32Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 1, 1, 1, 2, 12]), (-11520, [1, 1, 1, 1, 1, 15]), (-23040, [1, 1, 1, 1, 2, 14]), (-23040, [1, 1, 1, 1, 3, 13]), (-25440, [1, 1, 1, 1, 4, 12]), (-23040, [1, 1, 1, 1, 5, 11]), (-23040, [1, 1, 1, 1, 6, 10]), (-23040, [1, 1, 1, 1, 7, 9]), (-11520, [1, 1, 1, 1, 8, 8]), (-11520, [1, 1, 1, 2, 2, 13]), (-29120, [1, 1, 1, 2, 3, 12]), (-23040, [1, 1, 1, 2, 4, 11]), (-23040, [1, 1, 1, 2, 5, 10]), (-23040, [1, 1, 1, 2, 6, 9]), (-23040, [1, 1, 1, 2, 7, 8]), (-11520, [1, 1, 1, 3, 3, 11]), (-23040, [1, 1, 1, 3, 4, 10]), (-23040, [1, 1, 1, 3, 5, 9]), (-23040, [1, 1, 1, 3, 6, 8]), (-11520, [1, 1, 1, 3, 7, 7]), (-11520, [1, 1, 1, 4, 4, 9]), (-23040, [1, 1, 1, 4, 5, 8]), (-23040, [1, 1, 1, 4, 6, 7]), (-11520, [1, 1, 1, 5, 5, 7])]

def node4Piece32Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [1, 1, 1, 5, 6, 6]), (935040, [1, 1, 1, 17]), (-960, [1, 1, 2, 2, 2, 12]), (-69120, [1, 1, 2, 16]), (-69120, [1, 1, 3, 15]), (-69120, [1, 1, 4, 14]), (-69120, [1, 1, 5, 13]), (-61440, [1, 1, 6, 12]), (-69120, [1, 1, 7, 11]), (-69120, [1, 1, 8, 10]), (-34560, [1, 1, 9, 9]), (-5760, [1, 2, 5, 12]), (-5760, [1, 3, 4, 12]), (-69120, [1, 19]), (-1920, [8, 12])]

def node4Piece32Output_sector0 : RawPoly ℕ := [node4Piece32Output_sector0_chunk0, node4Piece32Output_sector0_chunk1].flatten

def node4Piece32Output : SectorVector := [(0, node4Piece32Output_sector0)]
theorem node4Piece32_check : VectorCertificate (neutralBoundS JR (-2) node4Piece32Input) node4Piece32Output := by decide +kernel
theorem node4Piece32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece32Input) = evaluate node4Piece32Output :=
  neutralBound_value JR _ _ _ node4Piece32_check

def node4Piece33Input_sector0 : RawPoly ℕ := [(-56, [1, 1, 2, 2, 2, 2, 2, 3])]

def node4Piece33Input : SectorVector := [(0, node4Piece33Input_sector0)]
def node4Piece33Output_sector0_chunk0 : RawPoly ℕ := [(-224, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (-2016, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (-6720, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-4032, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (-18480, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-6720, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (-40320, [1, 1, 1, 2, 2, 2, 2, 9]), (-53760, [1, 1, 1, 2, 2, 2, 3, 8]), (-2016, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-11648, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-23856, [1, 1, 2, 2, 2, 2, 2, 8]), (-67200, [1, 1, 2, 2, 2, 2, 3, 7]), (-40320, [1, 1, 2, 2, 2, 2, 4, 6]), (-20160, [1, 1, 2, 2, 2, 2, 5, 5]), (-53760, [1, 1, 2, 2, 2, 3, 3, 6]), (-53760, [1, 1, 2, 2, 2, 3, 4, 5]), (-161280, [1, 1, 2, 2, 2, 12]), (-107520, [1, 1, 2, 2, 3, 11]), (-448, [1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-8064, [1, 2, 2, 2, 2, 2, 2, 7]), (-30016, [1, 2, 2, 2, 2, 2, 3, 6]), (-8064, [1, 2, 2, 2, 2, 2, 4, 5]), (-26880, [1, 2, 2, 2, 2, 3, 3, 5]), (-13440, [1, 2, 2, 2, 2, 3, 4, 4])]

def node4Piece33Output_sector0_chunk1 : RawPoly ℕ := [(-80640, [1, 2, 2, 2, 2, 11]), (-107520, [1, 2, 2, 2, 3, 10]), (-1344, [2, 2, 2, 2, 2, 2, 3, 5]), (-1344, [2, 2, 2, 2, 2, 3, 3, 4]), (-4032, [2, 2, 2, 2, 2, 10]), (-13440, [2, 2, 2, 2, 3, 9])]

def node4Piece33Output_sector0 : RawPoly ℕ := [node4Piece33Output_sector0_chunk0, node4Piece33Output_sector0_chunk1].flatten

def node4Piece33Output : SectorVector := [(0, node4Piece33Output_sector0)]
theorem node4Piece33_check : VectorCertificate (neutralBoundS JR (-2) node4Piece33Input) node4Piece33Output := by decide +kernel
theorem node4Piece33_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece33Input) = evaluate node4Piece33Output :=
  neutralBound_value JR _ _ _ node4Piece33_check

def node4Piece34Input_sector0 : RawPoly ℕ := [(-480/7, [1, 1, 2, 2, 2, 7])]

def node4Piece34Input : SectorVector := [(0, node4Piece34Input_sector0)]
def node4Piece34Output_sector0_chunk0 : RawPoly ℕ := [(-1920/7, [1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (-5760, [1, 1, 1, 1, 2, 2, 2, 10]), (-34560/7, [1, 1, 1, 1, 2, 2, 5, 7]), (-11520, [1, 1, 1, 2, 2, 2, 2, 9]), (-11520, [1, 1, 1, 2, 2, 2, 3, 8]), (-158400/7, [1, 1, 1, 2, 2, 2, 4, 7]), (-11520, [1, 1, 1, 2, 2, 2, 5, 6]), (-34560/7, [1, 1, 1, 2, 2, 3, 3, 7]), (-69120, [1, 1, 1, 2, 2, 13]), (-138240/7, [1, 1, 1, 2, 7, 8]), (-5760, [1, 1, 2, 2, 2, 2, 2, 8]), (-140160/7, [1, 1, 2, 2, 2, 2, 3, 7]), (-11520, [1, 1, 2, 2, 2, 2, 4, 6]), (-5760, [1, 1, 2, 2, 2, 2, 5, 5]), (-5760, [1, 1, 2, 2, 2, 3, 3, 6]), (-11520, [1, 1, 2, 2, 2, 3, 4, 5]), (-1920, [1, 1, 2, 2, 2, 4, 4, 4]), (121920, [1, 1, 2, 2, 2, 12]), (-69120, [1, 1, 2, 2, 3, 11]), (-69120, [1, 1, 2, 2, 4, 10]), (-69120, [1, 1, 2, 2, 5, 9]), (-69120, [1, 1, 2, 2, 6, 8]), (-34560, [1, 1, 2, 2, 7, 7]), (-138240/7, [1, 1, 2, 3, 6, 7])]

def node4Piece34Output_sector0_chunk1 : RawPoly ℕ := [(-138240/7, [1, 1, 2, 4, 5, 7]), (-138240, [1, 1, 2, 16]), (-92160/7, [1, 1, 7, 11]), (-3840/7, [1, 2, 2, 2, 2, 2, 2, 7]), (-23040, [1, 2, 2, 2, 2, 11]), (-23040, [1, 2, 2, 2, 3, 10]), (-23040, [1, 2, 2, 2, 4, 9]), (-23040, [1, 2, 2, 2, 5, 8]), (-257280/7, [1, 2, 2, 2, 6, 7]), (-138240/7, [1, 2, 2, 3, 5, 7]), (-69120/7, [1, 2, 2, 4, 4, 7]), (-138240, [1, 2, 2, 15]), (-276480/7, [1, 2, 7, 10]), (-11520/7, [2, 2, 2, 2, 5, 7]), (-11520/7, [2, 2, 2, 3, 4, 7]), (-11520, [2, 2, 2, 14]), (-69120/7, [2, 2, 7, 9])]

def node4Piece34Output_sector0 : RawPoly ℕ := [node4Piece34Output_sector0_chunk0, node4Piece34Output_sector0_chunk1].flatten

def node4Piece34Output : SectorVector := [(0, node4Piece34Output_sector0)]
theorem node4Piece34_check : VectorCertificate (neutralBoundS JR (-2) node4Piece34Input) node4Piece34Output := by decide +kernel
theorem node4Piece34_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece34Input) = evaluate node4Piece34Output :=
  neutralBound_value JR _ _ _ node4Piece34_check

def node4Piece35Input_sector0 : RawPoly ℕ := [(400, [1, 1, 2, 2, 3, 6])]

def node4Piece35Input : SectorVector := [(0, node4Piece35Input_sector0)]
def node4Piece35Output_sector0_chunk0 : RawPoly ℕ := [(1600, [1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (28800, [1, 1, 1, 1, 2, 2, 3, 9]), (14400, [1, 1, 1, 1, 2, 2, 6, 6]), (19200, [1, 1, 1, 1, 2, 3, 5, 6]), (57600, [1, 1, 1, 2, 2, 2, 3, 8]), (28800, [1, 1, 1, 2, 2, 2, 5, 6]), (57600, [1, 1, 1, 2, 2, 3, 3, 7]), (132000, [1, 1, 1, 2, 2, 3, 4, 6]), (28800, [1, 1, 1, 2, 2, 3, 5, 5]), (172800, [1, 1, 1, 2, 2, 13]), (19200, [1, 1, 1, 2, 3, 3, 3, 6]), (230400, [1, 1, 1, 2, 3, 12]), (115200, [1, 1, 1, 2, 6, 9]), (38400, [1, 1, 1, 3, 6, 8]), (28800, [1, 1, 2, 2, 2, 2, 3, 7]), (14400, [1, 1, 2, 2, 2, 2, 4, 6]), (112000, [1, 1, 2, 2, 2, 3, 3, 6]), (57600, [1, 1, 2, 2, 2, 3, 4, 5]), (172800, [1, 1, 2, 2, 2, 12]), (28800, [1, 1, 2, 2, 3, 3, 3, 5]), (28800, [1, 1, 2, 2, 3, 3, 4, 4]), (-336000, [1, 1, 2, 2, 3, 11]), (172800, [1, 1, 2, 2, 4, 10]), (172800, [1, 1, 2, 2, 5, 9])]

def node4Piece35Output_sector0_chunk1 : RawPoly ℕ := [(170400, [1, 1, 2, 2, 6, 8]), (86400, [1, 1, 2, 2, 7, 7]), (230400, [1, 1, 2, 3, 3, 10]), (230400, [1, 1, 2, 3, 4, 9]), (230400, [1, 1, 2, 3, 5, 8]), (307200, [1, 1, 2, 3, 6, 7]), (115200, [1, 1, 2, 4, 6, 6]), (57600, [1, 1, 2, 5, 5, 6]), (691200, [1, 1, 2, 16]), (38400, [1, 1, 3, 3, 6, 6]), (38400, [1, 1, 3, 4, 5, 6]), (230400, [1, 1, 3, 15]), (115200, [1, 1, 6, 12]), (3200, [1, 2, 2, 2, 2, 2, 3, 6]), (115200, [1, 2, 2, 2, 3, 10]), (57600, [1, 2, 2, 2, 6, 7]), (115200, [1, 2, 2, 3, 3, 9]), (115200, [1, 2, 2, 3, 4, 8]), (115200, [1, 2, 2, 3, 5, 7]), (156800, [1, 2, 2, 3, 6, 6]), (57600, [1, 2, 2, 4, 5, 6]), (345600, [1, 2, 2, 15]), (76800, [1, 2, 3, 3, 5, 6]), (38400, [1, 2, 3, 4, 4, 6])]

def node4Piece35Output_sector0_chunk2 : RawPoly ℕ := [(460800, [1, 2, 3, 14]), (230400, [1, 2, 6, 11]), (76800, [1, 3, 6, 10]), (9600, [2, 2, 2, 3, 5, 6]), (9600, [2, 2, 3, 3, 4, 6]), (57600, [2, 2, 3, 13]), (28800, [2, 2, 6, 10]), (38400, [2, 3, 6, 9])]

def node4Piece35Output_sector0 : RawPoly ℕ := [node4Piece35Output_sector0_chunk0, node4Piece35Output_sector0_chunk1, node4Piece35Output_sector0_chunk2].flatten

def node4Piece35Output : SectorVector := [(0, node4Piece35Output_sector0)]
theorem node4Piece35_check : VectorCertificate (neutralBoundS JR (-2) node4Piece35Input) node4Piece35Output := by decide +kernel
theorem node4Piece35_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece35Input) = evaluate node4Piece35Output :=
  neutralBound_value JR _ _ _ node4Piece35_check

def node4Piece36Input_sector0 : RawPoly ℕ := [(-144, [1, 1, 2, 2, 4, 5])]

def node4Piece36Input : SectorVector := [(0, node4Piece36Input_sector0)]
def node4Piece36Output_sector0_chunk0 : RawPoly ℕ := [(-576, [1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (-8640, [1, 1, 1, 1, 2, 2, 4, 8]), (-6912, [1, 1, 1, 1, 2, 2, 5, 7]), (-6912, [1, 1, 1, 1, 2, 4, 5, 5]), (-17280, [1, 1, 1, 2, 2, 2, 4, 7]), (-13824, [1, 1, 1, 2, 2, 2, 5, 6]), (-17280, [1, 1, 1, 2, 2, 3, 4, 6]), (-13824, [1, 1, 1, 2, 2, 3, 5, 5]), (-40608, [1, 1, 1, 2, 2, 4, 4, 5]), (-69120, [1, 1, 1, 2, 2, 13]), (-6912, [1, 1, 1, 2, 3, 3, 4, 5]), (-69120, [1, 1, 1, 2, 4, 11]), (-55296, [1, 1, 1, 2, 5, 10]), (-13824, [1, 1, 1, 4, 5, 8]), (-8640, [1, 1, 2, 2, 2, 2, 4, 6]), (-6912, [1, 1, 2, 2, 2, 2, 5, 5]), (-45504, [1, 1, 2, 2, 2, 3, 4, 5]), (-8640, [1, 1, 2, 2, 2, 4, 4, 4]), (-69120, [1, 1, 2, 2, 2, 12]), (-2304, [1, 1, 2, 2, 3, 3, 3, 5]), (-8640, [1, 1, 2, 2, 3, 3, 4, 4]), (-69120, [1, 1, 2, 2, 3, 11]), (25920, [1, 1, 2, 2, 4, 10]), (-33408, [1, 1, 2, 2, 5, 9])]

def node4Piece36Output_sector0_chunk1 : RawPoly ℕ := [(-69120, [1, 1, 2, 2, 6, 8]), (-34560, [1, 1, 2, 2, 7, 7]), (-69120, [1, 1, 2, 3, 4, 9]), (-55296, [1, 1, 2, 3, 5, 8]), (-69120, [1, 1, 2, 4, 4, 8]), (-110592, [1, 1, 2, 4, 5, 7]), (-34560, [1, 1, 2, 4, 6, 6]), (-55296, [1, 1, 2, 5, 5, 6]), (-276480, [1, 1, 2, 16]), (-13824, [1, 1, 3, 4, 5, 6]), (-13824, [1, 1, 4, 4, 5, 5]), (-69120, [1, 1, 4, 14]), (-55296, [1, 1, 5, 13]), (-1152, [1, 2, 2, 2, 2, 2, 4, 5]), (-34560, [1, 2, 2, 2, 4, 9]), (-27648, [1, 2, 2, 2, 5, 8]), (-34560, [1, 2, 2, 3, 4, 8]), (-27648, [1, 2, 2, 3, 5, 7]), (-34560, [1, 2, 2, 4, 4, 7]), (-77184, [1, 2, 2, 4, 5, 6]), (-13824, [1, 2, 2, 5, 5, 5]), (-138240, [1, 2, 2, 15]), (-27648, [1, 2, 3, 4, 5, 5]), (-13824, [1, 2, 4, 4, 4, 5])]

def node4Piece36Output_sector0_chunk2 : RawPoly ℕ := [(-138240, [1, 2, 4, 13]), (-110592, [1, 2, 5, 12]), (-27648, [1, 4, 5, 10]), (-3456, [2, 2, 2, 4, 5, 5]), (-3456, [2, 2, 3, 4, 4, 5]), (-17280, [2, 2, 4, 12]), (-13824, [2, 2, 5, 11]), (-13824, [2, 4, 5, 9])]

def node4Piece36Output_sector0 : RawPoly ℕ := [node4Piece36Output_sector0_chunk0, node4Piece36Output_sector0_chunk1, node4Piece36Output_sector0_chunk2].flatten

def node4Piece36Output : SectorVector := [(0, node4Piece36Output_sector0)]
theorem node4Piece36_check : VectorCertificate (neutralBoundS JR (-2) node4Piece36Input) node4Piece36Output := by decide +kernel
theorem node4Piece36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece36Input) = evaluate node4Piece36Output :=
  neutralBound_value JR _ _ _ node4Piece36_check

def node4Piece37Input_sector0 : RawPoly ℕ := [(640, [1, 1, 2, 3, 3, 5])]

def node4Piece37Input : SectorVector := [(0, node4Piece37Input_sector0)]
def node4Piece37Output_sector0_chunk0 : RawPoly ℕ := [(2560, [1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (38400, [1, 1, 1, 1, 2, 3, 3, 8]), (46080, [1, 1, 1, 1, 2, 3, 5, 6]), (15360, [1, 1, 1, 1, 3, 3, 5, 5]), (76800, [1, 1, 1, 2, 2, 3, 3, 7]), (92160, [1, 1, 1, 2, 2, 3, 5, 5]), (76800, [1, 1, 1, 2, 3, 3, 3, 6]), (211200, [1, 1, 1, 2, 3, 3, 4, 5]), (460800, [1, 1, 1, 2, 3, 12]), (138240, [1, 1, 1, 2, 5, 10]), (15360, [1, 1, 1, 3, 3, 3, 3, 5]), (153600, [1, 1, 1, 3, 3, 11]), (184320, [1, 1, 1, 3, 5, 9]), (38400, [1, 1, 2, 2, 2, 3, 3, 6]), (46080, [1, 1, 2, 2, 2, 3, 4, 5]), (171520, [1, 1, 2, 2, 3, 3, 3, 5]), (38400, [1, 1, 2, 2, 3, 3, 4, 4]), (460800, [1, 1, 2, 2, 3, 11]), (138240, [1, 1, 2, 2, 5, 9]), (38400, [1, 1, 2, 3, 3, 3, 3, 4]), (-115200, [1, 1, 2, 3, 3, 10]), (460800, [1, 1, 2, 3, 4, 9]), (407040, [1, 1, 2, 3, 5, 8]), (460800, [1, 1, 2, 3, 6, 7])]

def node4Piece37Output_sector0_chunk1 : RawPoly ℕ := [(138240, [1, 1, 2, 4, 5, 7]), (138240, [1, 1, 2, 5, 5, 6]), (691200, [1, 1, 2, 16]), (153600, [1, 1, 3, 3, 3, 9]), (153600, [1, 1, 3, 3, 4, 8]), (276480, [1, 1, 3, 3, 5, 7]), (76800, [1, 1, 3, 3, 6, 6]), (184320, [1, 1, 3, 4, 5, 6]), (92160, [1, 1, 3, 5, 5, 5]), (921600, [1, 1, 3, 15]), (276480, [1, 1, 5, 13]), (5120, [1, 2, 2, 2, 2, 3, 3, 5]), (153600, [1, 2, 2, 3, 3, 9]), (184320, [1, 2, 2, 3, 5, 7]), (153600, [1, 2, 3, 3, 3, 8]), (153600, [1, 2, 3, 3, 4, 7]), (343040, [1, 2, 3, 3, 5, 6]), (184320, [1, 2, 3, 4, 5, 5]), (921600, [1, 2, 3, 14]), (276480, [1, 2, 5, 12]), (61440, [1, 3, 3, 3, 5, 5]), (30720, [1, 3, 3, 4, 4, 5]), (307200, [1, 3, 3, 13]), (368640, [1, 3, 5, 11])]

def node4Piece37Output_sector0_chunk2 : RawPoly ℕ := [(15360, [2, 2, 3, 3, 5, 5]), (15360, [2, 3, 3, 3, 4, 5]), (76800, [2, 3, 3, 12]), (92160, [2, 3, 5, 10]), (30720, [3, 3, 5, 9])]

def node4Piece37Output_sector0 : RawPoly ℕ := [node4Piece37Output_sector0_chunk0, node4Piece37Output_sector0_chunk1, node4Piece37Output_sector0_chunk2].flatten

def node4Piece37Output : SectorVector := [(0, node4Piece37Output_sector0)]
theorem node4Piece37_check : VectorCertificate (neutralBoundS JR (-2) node4Piece37Input) node4Piece37Output := by decide +kernel
theorem node4Piece37_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece37Input) = evaluate node4Piece37Output :=
  neutralBound_value JR _ _ _ node4Piece37_check

def node4Piece38Input_sector0 : RawPoly ℕ := [(-180, [1, 1, 2, 3, 4, 4])]

def node4Piece38Input : SectorVector := [(0, node4Piece38Input_sector0)]
def node4Piece38Output_sector0_chunk0 : RawPoly ℕ := [(-720, [1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (-17280, [1, 1, 1, 1, 2, 3, 4, 7]), (-6480, [1, 1, 1, 1, 2, 4, 4, 6]), (-4320, [1, 1, 1, 1, 3, 4, 4, 5]), (-34560, [1, 1, 1, 2, 2, 3, 4, 6]), (-12960, [1, 1, 1, 2, 2, 4, 4, 5]), (-34560, [1, 1, 1, 2, 3, 3, 4, 5]), (-42120, [1, 1, 1, 2, 3, 4, 4, 4]), (-69120, [1, 1, 1, 2, 3, 12]), (-103680, [1, 1, 1, 2, 4, 11]), (-4320, [1, 1, 1, 3, 3, 3, 4, 4]), (-69120, [1, 1, 1, 3, 4, 10]), (-25920, [1, 1, 1, 4, 4, 9]), (-17280, [1, 1, 2, 2, 2, 3, 4, 5]), (-6480, [1, 1, 2, 2, 2, 4, 4, 4]), (-54720, [1, 1, 2, 2, 3, 3, 4, 4]), (-69120, [1, 1, 2, 2, 3, 11]), (-103680, [1, 1, 2, 2, 4, 10]), (-5760, [1, 1, 2, 3, 3, 3, 3, 4]), (-69120, [1, 1, 2, 3, 3, 10]), (-14400, [1, 1, 2, 3, 4, 9]), (-69120, [1, 1, 2, 3, 5, 8]), (-69120, [1, 1, 2, 3, 6, 7]), (-76680, [1, 1, 2, 4, 4, 8])]

def node4Piece38Output_sector0_chunk1 : RawPoly ℕ := [(-103680, [1, 1, 2, 4, 5, 7]), (-51840, [1, 1, 2, 4, 6, 6]), (-207360, [1, 1, 2, 16]), (-69120, [1, 1, 3, 3, 4, 8]), (-77760, [1, 1, 3, 4, 4, 7]), (-69120, [1, 1, 3, 4, 5, 6]), (-138240, [1, 1, 3, 15]), (-25920, [1, 1, 4, 4, 4, 6]), (-12960, [1, 1, 4, 4, 5, 5]), (-207360, [1, 1, 4, 14]), (-1440, [1, 2, 2, 2, 2, 3, 4, 4]), (-69120, [1, 2, 2, 3, 4, 8]), (-25920, [1, 2, 2, 4, 4, 7]), (-69120, [1, 2, 3, 3, 4, 7]), (-96480, [1, 2, 3, 4, 4, 6]), (-34560, [1, 2, 3, 4, 5, 5]), (-138240, [1, 2, 3, 14]), (-25920, [1, 2, 4, 4, 4, 5]), (-207360, [1, 2, 4, 13]), (-17280, [1, 3, 3, 4, 4, 5]), (-8640, [1, 3, 4, 4, 4, 4]), (-138240, [1, 3, 4, 12]), (-51840, [1, 4, 4, 11]), (-4320, [2, 2, 3, 4, 4, 5])]

def node4Piece38Output_sector0_chunk2 : RawPoly ℕ := [(-4320, [2, 3, 3, 4, 4, 4]), (-34560, [2, 3, 4, 11]), (-12960, [2, 4, 4, 10]), (-8640, [3, 4, 4, 9])]

def node4Piece38Output_sector0 : RawPoly ℕ := [node4Piece38Output_sector0_chunk0, node4Piece38Output_sector0_chunk1, node4Piece38Output_sector0_chunk2].flatten

def node4Piece38Output : SectorVector := [(0, node4Piece38Output_sector0)]
theorem node4Piece38_check : VectorCertificate (neutralBoundS JR (-2) node4Piece38Input) node4Piece38Output := by decide +kernel
theorem node4Piece38_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece38Input) = evaluate node4Piece38Output :=
  neutralBound_value JR _ _ _ node4Piece38_check

def node4Piece39Input_sector0 : RawPoly ℕ := [(960/11, [1, 1, 2, 11])]

def node4Piece39Input : SectorVector := [(0, node4Piece39Input_sector0)]
def node4Piece39Output_sector0_chunk0 : RawPoly ℕ := [(3840/11, [1, 1, 1, 1, 1, 2, 2, 11]), (11520, [1, 1, 1, 1, 2, 14]), (23040/11, [1, 1, 1, 1, 5, 11]), (23040, [1, 1, 1, 2, 2, 13]), (23040, [1, 1, 1, 2, 3, 12]), (28800, [1, 1, 1, 2, 4, 11]), (23040, [1, 1, 1, 2, 5, 10]), (23040, [1, 1, 1, 2, 6, 9]), (23040, [1, 1, 1, 2, 7, 8]), (23040/11, [1, 1, 1, 3, 3, 11]), (46080, [1, 1, 1, 17]), (11520, [1, 1, 2, 2, 2, 12]), (326400/11, [1, 1, 2, 2, 3, 11]), (23040, [1, 1, 2, 2, 4, 10]), (23040, [1, 1, 2, 2, 5, 9]), (23040, [1, 1, 2, 2, 6, 8]), (11520, [1, 1, 2, 2, 7, 7]), (11520, [1, 1, 2, 3, 3, 10]), (23040, [1, 1, 2, 3, 4, 9]), (23040, [1, 1, 2, 3, 5, 8]), (23040, [1, 1, 2, 3, 6, 7]), (11520, [1, 1, 2, 4, 4, 8]), (23040, [1, 1, 2, 4, 5, 7]), (11520, [1, 1, 2, 4, 6, 6])]

def node4Piece39Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 1, 2, 5, 5, 6]), (-777600, [1, 1, 2, 16]), (46080, [1, 1, 3, 15]), (46080, [1, 1, 4, 14]), (46080, [1, 1, 5, 13]), (46080, [1, 1, 6, 12]), (414720/11, [1, 1, 7, 11]), (46080, [1, 1, 8, 10]), (23040, [1, 1, 9, 9]), (7680/11, [1, 2, 2, 2, 2, 11]), (46080, [1, 2, 2, 15]), (46080, [1, 2, 3, 14]), (46080, [1, 2, 4, 13]), (46080, [1, 2, 5, 12]), (514560/11, [1, 2, 6, 11]), (46080, [1, 2, 7, 10]), (46080, [1, 2, 8, 9]), (92160/11, [1, 3, 5, 11]), (46080/11, [1, 4, 4, 11]), (92160, [1, 19]), (23040/11, [2, 2, 5, 11]), (23040/11, [2, 3, 4, 11]), (23040, [2, 18]), (46080/11, [9, 11])]

def node4Piece39Output_sector0 : RawPoly ℕ := [node4Piece39Output_sector0_chunk0, node4Piece39Output_sector0_chunk1].flatten

def node4Piece39Output : SectorVector := [(0, node4Piece39Output_sector0)]
theorem node4Piece39_check : VectorCertificate (neutralBoundS JR (-2) node4Piece39Input) node4Piece39Output := by decide +kernel
theorem node4Piece39_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece39Input) = evaluate node4Piece39Output :=
  neutralBound_value JR _ _ _ node4Piece39_check

def node4Piece40Input_sector0 : RawPoly ℕ := [(800/9, [1, 1, 3, 3, 3, 4])]

def node4Piece40Input : SectorVector := [(0, node4Piece40Input_sector0)]
def node4Piece40Output_sector0_chunk0 : RawPoly ℕ := [(3200/9, [1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (12800/3, [1, 1, 1, 1, 3, 3, 3, 7]), (9600, [1, 1, 1, 1, 3, 3, 4, 6]), (25600/3, [1, 1, 1, 2, 3, 3, 3, 6]), (19200, [1, 1, 1, 2, 3, 3, 4, 5]), (25600/3, [1, 1, 1, 3, 3, 3, 3, 5]), (75200/3, [1, 1, 1, 3, 3, 3, 4, 4]), (76800, [1, 1, 1, 3, 3, 11]), (57600, [1, 1, 1, 3, 4, 10]), (12800/3, [1, 1, 2, 2, 3, 3, 3, 5]), (9600, [1, 1, 2, 2, 3, 3, 4, 4]), (204800/9, [1, 1, 2, 3, 3, 3, 3, 4]), (76800, [1, 1, 2, 3, 3, 10]), (57600, [1, 1, 2, 3, 4, 9]), (12800/9, [1, 1, 3, 3, 3, 3, 3, 3]), (185600/9, [1, 1, 3, 3, 3, 9]), (56000, [1, 1, 3, 3, 4, 8]), (76800, [1, 1, 3, 3, 5, 7]), (38400, [1, 1, 3, 3, 6, 6]), (57600, [1, 1, 3, 4, 4, 7]), (57600, [1, 1, 3, 4, 5, 6]), (230400, [1, 1, 3, 15]), (57600, [1, 1, 4, 14]), (6400/9, [1, 2, 2, 2, 3, 3, 3, 4])]

def node4Piece40Output_sector0_chunk1 : RawPoly ℕ := [(51200/3, [1, 2, 3, 3, 3, 8]), (38400, [1, 2, 3, 3, 4, 7]), (51200/3, [1, 3, 3, 3, 3, 7]), (428800/9, [1, 3, 3, 3, 4, 6]), (25600/3, [1, 3, 3, 3, 5, 5]), (38400, [1, 3, 3, 4, 4, 5]), (153600, [1, 3, 3, 13]), (115200, [1, 3, 4, 12]), (6400/3, [2, 3, 3, 3, 4, 5]), (6400/3, [3, 3, 3, 3, 4, 4]), (25600/3, [3, 3, 3, 11]), (19200, [3, 3, 4, 10])]

def node4Piece40Output_sector0 : RawPoly ℕ := [node4Piece40Output_sector0_chunk0, node4Piece40Output_sector0_chunk1].flatten

def node4Piece40Output : SectorVector := [(0, node4Piece40Output_sector0)]
theorem node4Piece40_check : VectorCertificate (neutralBoundS JR (-2) node4Piece40Input) node4Piece40Output := by decide +kernel
theorem node4Piece40_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece40Input) = evaluate node4Piece40Output :=
  neutralBound_value JR _ _ _ node4Piece40_check

def node4Piece41Input_sector0 : RawPoly ℕ := [(144, [1, 1, 3, 10])]

def node4Piece41Input : SectorVector := [(0, node4Piece41Input_sector0)]
def node4Piece41Output_sector0_chunk0 : RawPoly ℕ := [(576, [1, 1, 1, 1, 1, 2, 3, 10]), (17280, [1, 1, 1, 1, 3, 13]), (5184, [1, 1, 1, 1, 6, 10]), (34560, [1, 1, 1, 2, 3, 12]), (10368, [1, 1, 1, 2, 5, 10]), (34560, [1, 1, 1, 3, 3, 11]), (47520, [1, 1, 1, 3, 4, 10]), (34560, [1, 1, 1, 3, 5, 9]), (34560, [1, 1, 1, 3, 6, 8]), (17280, [1, 1, 1, 3, 7, 7]), (103680, [1, 1, 1, 17]), (17280, [1, 1, 2, 2, 3, 11]), (5184, [1, 1, 2, 2, 4, 10]), (47232, [1, 1, 2, 3, 3, 10]), (34560, [1, 1, 2, 3, 4, 9]), (34560, [1, 1, 2, 3, 5, 8]), (34560, [1, 1, 2, 3, 6, 7]), (103680, [1, 1, 2, 16]), (17280, [1, 1, 3, 3, 3, 9]), (34560, [1, 1, 3, 3, 4, 8]), (34560, [1, 1, 3, 3, 5, 7]), (17280, [1, 1, 3, 3, 6, 6]), (17280, [1, 1, 3, 4, 4, 7]), (34560, [1, 1, 3, 4, 5, 6])]

def node4Piece41Output_sector0_chunk1 : RawPoly ℕ := [(5760, [1, 1, 3, 5, 5, 5]), (-944640, [1, 1, 3, 15]), (103680, [1, 1, 4, 14]), (103680, [1, 1, 5, 13]), (103680, [1, 1, 6, 12]), (103680, [1, 1, 7, 11]), (61344, [1, 1, 8, 10]), (51840, [1, 1, 9, 9]), (1152, [1, 2, 2, 2, 3, 10]), (69120, [1, 2, 3, 14]), (20736, [1, 2, 7, 10]), (69120, [1, 3, 3, 13]), (69120, [1, 3, 4, 12]), (69120, [1, 3, 5, 11]), (77184, [1, 3, 6, 10]), (69120, [1, 3, 7, 9]), (34560, [1, 3, 8, 8]), (20736, [1, 4, 5, 10]), (207360, [1, 19]), (3456, [2, 3, 5, 10]), (3456, [3, 3, 4, 10]), (34560, [3, 17]), (10368, [10, 10])]

def node4Piece41Output_sector0 : RawPoly ℕ := [node4Piece41Output_sector0_chunk0, node4Piece41Output_sector0_chunk1].flatten

def node4Piece41Output : SectorVector := [(0, node4Piece41Output_sector0)]
theorem node4Piece41_check : VectorCertificate (neutralBoundS JR (-2) node4Piece41Input) node4Piece41Output := by decide +kernel
theorem node4Piece41_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece41Input) = evaluate node4Piece41Output :=
  neutralBound_value JR _ _ _ node4Piece41_check

def node4Piece42Input_sector0 : RawPoly ℕ := [(-160, [1, 1, 4, 9])]

def node4Piece42Input : SectorVector := [(0, node4Piece42Input_sector0)]
def node4Piece42Output_sector0_chunk0 : RawPoly ℕ := [(-640, [1, 1, 1, 1, 1, 2, 4, 9]), (-17280, [1, 1, 1, 1, 4, 12]), (-7680, [1, 1, 1, 1, 7, 9]), (-34560, [1, 1, 1, 2, 4, 11]), (-15360, [1, 1, 1, 2, 6, 9]), (-34560, [1, 1, 1, 3, 4, 10]), (-15360, [1, 1, 1, 3, 5, 9]), (-45120, [1, 1, 1, 4, 4, 9]), (-34560, [1, 1, 1, 4, 5, 8]), (-34560, [1, 1, 1, 4, 6, 7]), (-138240, [1, 1, 1, 17]), (-17280, [1, 1, 2, 2, 4, 10]), (-7680, [1, 1, 2, 2, 5, 9]), (-58240, [1, 1, 2, 3, 4, 9]), (-34560, [1, 1, 2, 4, 4, 8]), (-34560, [1, 1, 2, 4, 5, 7]), (-17280, [1, 1, 2, 4, 6, 6]), (-138240, [1, 1, 2, 16]), (-2560, [1, 1, 3, 3, 3, 9]), (-17280, [1, 1, 3, 3, 4, 8]), (-34560, [1, 1, 3, 4, 4, 7]), (-34560, [1, 1, 3, 4, 5, 6]), (-138240, [1, 1, 3, 15]), (-17280, [1, 1, 4, 4, 4, 6])]

def node4Piece42Output_sector0_chunk1 : RawPoly ℕ := [(-17280, [1, 1, 4, 4, 5, 5]), (737280, [1, 1, 4, 14]), (-138240, [1, 1, 5, 13]), (-138240, [1, 1, 6, 12]), (-138240, [1, 1, 7, 11]), (-138240, [1, 1, 8, 10]), (32000, [1, 1, 9, 9]), (-1280, [1, 2, 2, 2, 4, 9]), (-69120, [1, 2, 4, 13]), (-30720, [1, 2, 8, 9]), (-69120, [1, 3, 4, 12]), (-30720, [1, 3, 7, 9]), (-69120, [1, 4, 4, 11]), (-69120, [1, 4, 5, 10]), (-85760, [1, 4, 6, 9]), (-69120, [1, 4, 7, 8]), (-15360, [1, 5, 5, 9]), (-276480, [1, 19]), (-3840, [2, 4, 5, 9]), (-3840, [3, 4, 4, 9]), (-34560, [4, 16]), (-15360, [9, 11])]

def node4Piece42Output_sector0 : RawPoly ℕ := [node4Piece42Output_sector0_chunk0, node4Piece42Output_sector0_chunk1].flatten

def node4Piece42Output : SectorVector := [(0, node4Piece42Output_sector0)]
theorem node4Piece42_check : VectorCertificate (neutralBoundS JR (-2) node4Piece42Input) node4Piece42Output := by decide +kernel
theorem node4Piece42_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece42Input) = evaluate node4Piece42Output :=
  neutralBound_value JR _ _ _ node4Piece42_check

def node4Piece43Input_sector0 : RawPoly ℕ := [(48, [1, 1, 5, 8])]

def node4Piece43Input : SectorVector := [(0, node4Piece43Input_sector0)]
def node4Piece43Output_sector0_chunk0 : RawPoly ℕ := [(192, [1, 1, 1, 1, 1, 2, 5, 8]), (4608, [1, 1, 1, 1, 5, 11]), (2880, [1, 1, 1, 1, 8, 8]), (9216, [1, 1, 1, 2, 5, 10]), (5760, [1, 1, 1, 2, 7, 8]), (9216, [1, 1, 1, 3, 5, 9]), (5760, [1, 1, 1, 3, 6, 8]), (15840, [1, 1, 1, 4, 5, 8]), (9216, [1, 1, 1, 5, 5, 7]), (4608, [1, 1, 1, 5, 6, 6]), (46080, [1, 1, 1, 17]), (4608, [1, 1, 2, 2, 5, 9]), (2880, [1, 1, 2, 2, 6, 8]), (17472, [1, 1, 2, 3, 5, 8]), (2880, [1, 1, 2, 4, 4, 8]), (9216, [1, 1, 2, 4, 5, 7]), (9216, [1, 1, 2, 5, 5, 6]), (46080, [1, 1, 2, 16]), (2880, [1, 1, 3, 3, 4, 8]), (4608, [1, 1, 3, 3, 5, 7]), (9216, [1, 1, 3, 4, 5, 6]), (4608, [1, 1, 3, 5, 5, 5]), (46080, [1, 1, 3, 15]), (4608, [1, 1, 4, 4, 5, 5])]

def node4Piece43Output_sector0_chunk1 : RawPoly ℕ := [(46080, [1, 1, 4, 14]), (-145152, [1, 1, 5, 13]), (46080, [1, 1, 6, 12]), (46080, [1, 1, 7, 11]), (-8640, [1, 1, 8, 10]), (23040, [1, 1, 9, 9]), (384, [1, 2, 2, 2, 5, 8]), (18432, [1, 2, 5, 12]), (11520, [1, 2, 8, 9]), (18432, [1, 3, 5, 11]), (11520, [1, 3, 8, 8]), (18432, [1, 4, 5, 10]), (11520, [1, 4, 7, 8]), (18432, [1, 5, 5, 9]), (25728, [1, 5, 6, 8]), (9216, [1, 5, 7, 7]), (92160, [1, 19]), (1152, [2, 5, 5, 8]), (1152, [3, 4, 5, 8]), (9216, [5, 15]), (5760, [8, 12])]

def node4Piece43Output_sector0 : RawPoly ℕ := [node4Piece43Output_sector0_chunk0, node4Piece43Output_sector0_chunk1].flatten

def node4Piece43Output : SectorVector := [(0, node4Piece43Output_sector0)]
theorem node4Piece43_check : VectorCertificate (neutralBoundS JR (-2) node4Piece43Input) node4Piece43Output := by decide +kernel
theorem node4Piece43_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece43Input) = evaluate node4Piece43Output :=
  neutralBound_value JR _ _ _ node4Piece43_check

def node4Piece44Input_sector0 : RawPoly ℕ := [(-114/7, [1, 2, 2, 2, 2, 2, 2, 2])]

def node4Piece44Input : SectorVector := [(0, node4Piece44Input_sector0)]
def node4Piece44Output_sector0 : RawPoly ℕ := [(-456/7, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]), (-2736, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (-38988/7, [1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (-2736, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-32832, [1, 1, 2, 2, 2, 2, 2, 8]), (-3192, [1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-16416, [1, 2, 2, 2, 2, 2, 2, 7]), (-32832, [1, 2, 2, 2, 2, 2, 3, 6]), (-32832, [1, 2, 2, 2, 2, 2, 4, 5]), (-109440, [1, 2, 2, 2, 2, 11]), (-456/7, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]), (-4560, [2, 2, 2, 2, 2, 2, 2, 6]), (-5472, [2, 2, 2, 2, 2, 2, 3, 5]), (-2736, [2, 2, 2, 2, 2, 2, 4, 4]), (-32832, [2, 2, 2, 2, 2, 10])]

def node4Piece44Output : SectorVector := [(0, node4Piece44Output_sector0)]
theorem node4Piece44_check : VectorCertificate (neutralBoundS JR (-2) node4Piece44Input) node4Piece44Output := by decide +kernel
theorem node4Piece44_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece44Input) = evaluate node4Piece44Output :=
  neutralBound_value JR _ _ _ node4Piece44_check

def node4Piece45Input_sector0 : RawPoly ℕ := [(-180, [1, 2, 2, 2, 2, 6])]

def node4Piece45Input : SectorVector := [(0, node4Piece45Input_sector0)]
def node4Piece45Output_sector0_chunk0 : RawPoly ℕ := [(-720, [1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (-12960, [1, 1, 1, 2, 2, 2, 2, 9]), (-17280, [1, 1, 1, 2, 2, 2, 5, 6]), (-25920, [1, 1, 2, 2, 2, 2, 2, 8]), (-25920, [1, 1, 2, 2, 2, 2, 3, 7]), (-61560, [1, 1, 2, 2, 2, 2, 4, 6]), (-12960, [1, 1, 2, 2, 2, 2, 5, 5]), (-17280, [1, 1, 2, 2, 2, 3, 3, 6]), (-207360, [1, 1, 2, 2, 2, 12]), (-103680, [1, 1, 2, 2, 6, 8]), (-12960, [1, 2, 2, 2, 2, 2, 2, 7]), (-48240, [1, 2, 2, 2, 2, 2, 3, 6]), (-25920, [1, 2, 2, 2, 2, 2, 4, 5]), (-12960, [1, 2, 2, 2, 2, 3, 3, 5]), (-12960, [1, 2, 2, 2, 2, 3, 4, 4]), (151200, [1, 2, 2, 2, 2, 11]), (-207360, [1, 2, 2, 2, 3, 10]), (-207360, [1, 2, 2, 2, 4, 9]), (-207360, [1, 2, 2, 2, 5, 8]), (-207360, [1, 2, 2, 2, 6, 7]), (-103680, [1, 2, 2, 3, 6, 6]), (-103680, [1, 2, 2, 4, 5, 6]), (-622080, [1, 2, 2, 15]), (-138240, [1, 2, 6, 11])]

def node4Piece45Output_sector0_chunk1 : RawPoly ℕ := [(-720, [2, 2, 2, 2, 2, 2, 2, 6]), (-25920, [2, 2, 2, 2, 2, 10]), (-25920, [2, 2, 2, 2, 3, 9]), (-25920, [2, 2, 2, 2, 4, 8]), (-25920, [2, 2, 2, 2, 5, 7]), (-37440, [2, 2, 2, 2, 6, 6]), (-34560, [2, 2, 2, 3, 5, 6]), (-17280, [2, 2, 2, 4, 4, 6]), (-207360, [2, 2, 2, 14]), (-103680, [2, 2, 6, 10])]

def node4Piece45Output_sector0 : RawPoly ℕ := [node4Piece45Output_sector0_chunk0, node4Piece45Output_sector0_chunk1].flatten

def node4Piece45Output : SectorVector := [(0, node4Piece45Output_sector0)]
theorem node4Piece45_check : VectorCertificate (neutralBoundS JR (-2) node4Piece45Input) node4Piece45Output := by decide +kernel
theorem node4Piece45_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece45Input) = evaluate node4Piece45Output :=
  neutralBound_value JR _ _ _ node4Piece45_check

def node4Piece46Input_sector0 : RawPoly ℕ := [(-32, [1, 2, 2, 2, 3, 5])]

def node4Piece46Input : SectorVector := [(0, node4Piece46Input_sector0)]
def node4Piece46Output_sector0_chunk0 : RawPoly ℕ := [(-128, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-1920, [1, 1, 1, 2, 2, 2, 3, 8]), (-1152, [1, 1, 1, 2, 2, 2, 5, 6]), (-2304, [1, 1, 1, 2, 2, 3, 5, 5]), (-3840, [1, 1, 2, 2, 2, 2, 3, 7]), (-2304, [1, 1, 2, 2, 2, 2, 5, 5]), (-3840, [1, 1, 2, 2, 2, 3, 3, 6]), (-10944, [1, 1, 2, 2, 2, 3, 4, 5]), (-11520, [1, 1, 2, 2, 2, 12]), (-2304, [1, 1, 2, 2, 3, 3, 3, 5]), (-23040, [1, 1, 2, 2, 3, 11]), (-13824, [1, 1, 2, 2, 5, 9]), (-9216, [1, 1, 2, 3, 5, 8]), (-1920, [1, 2, 2, 2, 2, 2, 3, 6]), (-1152, [1, 2, 2, 2, 2, 2, 4, 5]), (-8192, [1, 2, 2, 2, 2, 3, 3, 5]), (-1920, [1, 2, 2, 2, 2, 3, 4, 4]), (-11520, [1, 2, 2, 2, 2, 11]), (-1920, [1, 2, 2, 2, 3, 3, 3, 4]), (5760, [1, 2, 2, 2, 3, 10]), (-11520, [1, 2, 2, 2, 4, 9]), (-13632, [1, 2, 2, 2, 5, 8]), (-11520, [1, 2, 2, 2, 6, 7]), (-23040, [1, 2, 2, 3, 3, 9])]

def node4Piece46Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [1, 2, 2, 3, 4, 8]), (-32256, [1, 2, 2, 3, 5, 7]), (-11520, [1, 2, 2, 3, 6, 6]), (-13824, [1, 2, 2, 4, 5, 6]), (-6912, [1, 2, 2, 5, 5, 5]), (-69120, [1, 2, 2, 15]), (-9216, [1, 2, 3, 3, 5, 6]), (-9216, [1, 2, 3, 4, 5, 5]), (-46080, [1, 2, 3, 14]), (-27648, [1, 2, 5, 12]), (-6144, [1, 3, 5, 11]), (-128, [2, 2, 2, 2, 2, 2, 3, 5]), (-3840, [2, 2, 2, 2, 3, 9]), (-2304, [2, 2, 2, 2, 5, 7]), (-3840, [2, 2, 2, 3, 3, 8]), (-3840, [2, 2, 2, 3, 4, 7]), (-8960, [2, 2, 2, 3, 5, 6]), (-2304, [2, 2, 2, 4, 5, 5]), (-11520, [2, 2, 2, 14]), (-4608, [2, 2, 3, 3, 5, 5]), (-2304, [2, 2, 3, 4, 4, 5]), (-23040, [2, 2, 3, 13]), (-13824, [2, 2, 5, 11]), (-9216, [2, 3, 5, 10])]

def node4Piece46Output_sector0 : RawPoly ℕ := [node4Piece46Output_sector0_chunk0, node4Piece46Output_sector0_chunk1].flatten

def node4Piece46Output : SectorVector := [(0, node4Piece46Output_sector0)]
theorem node4Piece46_check : VectorCertificate (neutralBoundS JR (-2) node4Piece46Input) node4Piece46Output := by decide +kernel
theorem node4Piece46_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece46Input) = evaluate node4Piece46Output :=
  neutralBound_value JR _ _ _ node4Piece46_check

def node4Piece47Input_sector0 : RawPoly ℕ := [(-285, [1, 2, 2, 2, 4, 4])]

def node4Piece47Input : SectorVector := [(0, node4Piece47Input_sector0)]
def node4Piece47Output_sector0_chunk0 : RawPoly ℕ := [(-1140, [1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (-27360, [1, 1, 1, 2, 2, 2, 4, 7]), (-20520, [1, 1, 1, 2, 2, 4, 4, 5]), (-54720, [1, 1, 2, 2, 2, 2, 4, 6]), (-54720, [1, 1, 2, 2, 2, 3, 4, 5]), (-70110, [1, 1, 2, 2, 2, 4, 4, 4]), (-109440, [1, 1, 2, 2, 2, 12]), (-20520, [1, 1, 2, 2, 3, 3, 4, 4]), (-328320, [1, 1, 2, 2, 4, 10]), (-82080, [1, 1, 2, 4, 4, 8]), (-27360, [1, 2, 2, 2, 2, 2, 4, 5]), (-83220, [1, 2, 2, 2, 2, 3, 4, 4]), (-109440, [1, 2, 2, 2, 2, 11]), (-9120, [1, 2, 2, 2, 3, 3, 3, 4]), (-109440, [1, 2, 2, 2, 3, 10]), (-22800, [1, 2, 2, 2, 4, 9]), (-109440, [1, 2, 2, 2, 5, 8]), (-109440, [1, 2, 2, 2, 6, 7]), (-328320, [1, 2, 2, 3, 4, 8]), (-287280, [1, 2, 2, 4, 4, 7]), (-328320, [1, 2, 2, 4, 5, 6]), (-656640, [1, 2, 2, 15]), (-82080, [1, 2, 3, 4, 4, 6]), (-82080, [1, 2, 4, 4, 4, 5])]

def node4Piece47Output_sector0_chunk1 : RawPoly ℕ := [(-656640, [1, 2, 4, 13]), (-54720, [1, 4, 4, 11]), (-1140, [2, 2, 2, 2, 2, 2, 4, 4]), (-54720, [2, 2, 2, 2, 4, 8]), (-54720, [2, 2, 2, 3, 4, 7]), (-79800, [2, 2, 2, 4, 4, 6]), (-27360, [2, 2, 2, 4, 5, 5]), (-109440, [2, 2, 2, 14]), (-41040, [2, 2, 3, 4, 4, 5]), (-20520, [2, 2, 4, 4, 4, 4]), (-328320, [2, 2, 4, 12]), (-82080, [2, 4, 4, 10])]

def node4Piece47Output_sector0 : RawPoly ℕ := [node4Piece47Output_sector0_chunk0, node4Piece47Output_sector0_chunk1].flatten

def node4Piece47Output : SectorVector := [(0, node4Piece47Output_sector0)]
theorem node4Piece47_check : VectorCertificate (neutralBoundS JR (-2) node4Piece47Input) node4Piece47Output := by decide +kernel
theorem node4Piece47_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece47Input) = evaluate node4Piece47Output :=
  neutralBound_value JR _ _ _ node4Piece47_check

def node4Piece48Input_sector0 : RawPoly ℕ := [(200, [1, 2, 2, 3, 3, 4])]

def node4Piece48Input : SectorVector := [(0, node4Piece48Input_sector0)]
def node4Piece48Output_sector0_chunk0 : RawPoly ℕ := [(800, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (9600, [1, 1, 1, 2, 2, 3, 3, 7]), (14400, [1, 1, 1, 2, 2, 3, 4, 6]), (9600, [1, 1, 1, 2, 3, 3, 4, 5]), (19200, [1, 1, 2, 2, 2, 3, 3, 6]), (28800, [1, 1, 2, 2, 2, 3, 4, 5]), (19200, [1, 1, 2, 2, 3, 3, 3, 5]), (58800, [1, 1, 2, 2, 3, 3, 4, 4]), (115200, [1, 1, 2, 2, 3, 11]), (43200, [1, 1, 2, 2, 4, 10]), (9600, [1, 1, 2, 3, 3, 3, 3, 4]), (76800, [1, 1, 2, 3, 3, 10]), (115200, [1, 1, 2, 3, 4, 9]), (19200, [1, 1, 3, 3, 4, 8]), (9600, [1, 2, 2, 2, 2, 3, 3, 5]), (14400, [1, 2, 2, 2, 2, 3, 4, 4]), (48800, [1, 2, 2, 2, 3, 3, 3, 4]), (115200, [1, 2, 2, 2, 3, 10]), (43200, [1, 2, 2, 2, 4, 9]), (3200, [1, 2, 2, 3, 3, 3, 3, 3]), (46400, [1, 2, 2, 3, 3, 9]), (127200, [1, 2, 2, 3, 4, 8]), (115200, [1, 2, 2, 3, 5, 7]), (57600, [1, 2, 2, 3, 6, 6])]

def node4Piece48Output_sector0_chunk1 : RawPoly ℕ := [(43200, [1, 2, 2, 4, 4, 7]), (43200, [1, 2, 2, 4, 5, 6]), (172800, [1, 2, 2, 15]), (76800, [1, 2, 3, 3, 3, 8]), (153600, [1, 2, 3, 3, 4, 7]), (76800, [1, 2, 3, 3, 5, 6]), (115200, [1, 2, 3, 4, 4, 6]), (57600, [1, 2, 3, 4, 5, 5]), (460800, [1, 2, 3, 14]), (172800, [1, 2, 4, 13]), (19200, [1, 3, 3, 3, 4, 6]), (19200, [1, 3, 3, 4, 4, 5]), (76800, [1, 3, 3, 13]), (115200, [1, 3, 4, 12]), (800, [2, 2, 2, 2, 2, 3, 3, 4]), (19200, [2, 2, 2, 3, 3, 8]), (28800, [2, 2, 2, 3, 4, 7]), (19200, [2, 2, 3, 3, 3, 7]), (56000, [2, 2, 3, 3, 4, 6]), (9600, [2, 2, 3, 3, 5, 5]), (28800, [2, 2, 3, 4, 4, 5]), (115200, [2, 2, 3, 13]), (43200, [2, 2, 4, 12]), (19200, [2, 3, 3, 3, 4, 5])]

def node4Piece48Output_sector0_chunk2 : RawPoly ℕ := [(9600, [2, 3, 3, 4, 4, 4]), (76800, [2, 3, 3, 12]), (115200, [2, 3, 4, 11]), (19200, [3, 3, 4, 10])]

def node4Piece48Output_sector0 : RawPoly ℕ := [node4Piece48Output_sector0_chunk0, node4Piece48Output_sector0_chunk1, node4Piece48Output_sector0_chunk2].flatten

def node4Piece48Output : SectorVector := [(0, node4Piece48Output_sector0)]
theorem node4Piece48_check : VectorCertificate (neutralBoundS JR (-2) node4Piece48Input) node4Piece48Output := by decide +kernel
theorem node4Piece48_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece48Input) = evaluate node4Piece48Output :=
  neutralBound_value JR _ _ _ node4Piece48_check

def node4Piece49Input_sector0 : RawPoly ℕ := [(-132, [1, 2, 2, 10])]

def node4Piece49Input : SectorVector := [(0, node4Piece49Input_sector0)]
def node4Piece49Output_sector0_chunk0 : RawPoly ℕ := [(-528, [1, 1, 1, 1, 2, 2, 2, 10]), (-15840, [1, 1, 1, 2, 2, 13]), (-6336, [1, 1, 1, 2, 5, 10]), (-31680, [1, 1, 2, 2, 2, 12]), (-31680, [1, 1, 2, 2, 3, 11]), (-45144, [1, 1, 2, 2, 4, 10]), (-31680, [1, 1, 2, 2, 5, 9]), (-31680, [1, 1, 2, 2, 6, 8]), (-15840, [1, 1, 2, 2, 7, 7]), (-6336, [1, 1, 2, 3, 3, 10]), (-126720, [1, 1, 2, 16]), (-12672, [1, 1, 8, 10]), (-15840, [1, 2, 2, 2, 2, 11]), (-41712, [1, 2, 2, 2, 3, 10]), (-31680, [1, 2, 2, 2, 4, 9]), (-31680, [1, 2, 2, 2, 5, 8]), (-31680, [1, 2, 2, 2, 6, 7]), (-15840, [1, 2, 2, 3, 3, 9]), (-31680, [1, 2, 2, 3, 4, 8]), (-31680, [1, 2, 2, 3, 5, 7]), (-15840, [1, 2, 2, 3, 6, 6]), (-15840, [1, 2, 2, 4, 4, 7]), (-31680, [1, 2, 2, 4, 5, 6]), (-5280, [1, 2, 2, 5, 5, 5])]

def node4Piece49Output_sector0_chunk1 : RawPoly ℕ := [(865920, [1, 2, 2, 15]), (-126720, [1, 2, 3, 14]), (-126720, [1, 2, 4, 13]), (-126720, [1, 2, 5, 12]), (-126720, [1, 2, 6, 11]), (-101376, [1, 2, 7, 10]), (-126720, [1, 2, 8, 9]), (-12672, [1, 3, 6, 10]), (-12672, [1, 4, 5, 10]), (-126720, [1, 19]), (-528, [2, 2, 2, 2, 2, 10]), (-31680, [2, 2, 2, 14]), (-31680, [2, 2, 3, 13]), (-31680, [2, 2, 4, 12]), (-31680, [2, 2, 5, 11]), (-36960, [2, 2, 6, 10]), (-31680, [2, 2, 7, 9]), (-15840, [2, 2, 8, 8]), (-12672, [2, 3, 5, 10]), (-6336, [2, 4, 4, 10]), (-126720, [2, 18]), (-12672, [10, 10])]

def node4Piece49Output_sector0 : RawPoly ℕ := [node4Piece49Output_sector0_chunk0, node4Piece49Output_sector0_chunk1].flatten

def node4Piece49Output : SectorVector := [(0, node4Piece49Output_sector0)]
theorem node4Piece49_check : VectorCertificate (neutralBoundS JR (-2) node4Piece49Input) node4Piece49Output := by decide +kernel
theorem node4Piece49_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece49Input) = evaluate node4Piece49Output :=
  neutralBound_value JR _ _ _ node4Piece49_check

def node4Piece50Input_sector0 : RawPoly ℕ := [(1280/9, [1, 2, 3, 3, 3, 3])]

def node4Piece50Input : SectorVector := [(0, node4Piece50Input_sector0)]
def node4Piece50Output_sector0_chunk0 : RawPoly ℕ := [(5120/9, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (20480, [1, 1, 1, 2, 3, 3, 3, 6]), (10240/3, [1, 1, 1, 3, 3, 3, 3, 5]), (40960, [1, 1, 2, 2, 3, 3, 3, 5]), (48640, [1, 1, 2, 3, 3, 3, 3, 4]), (184320, [1, 1, 2, 3, 3, 10]), (10240/3, [1, 1, 3, 3, 3, 3, 3, 3]), (81920, [1, 1, 3, 3, 3, 9]), (20480, [1, 2, 2, 2, 3, 3, 3, 4]), (250880/9, [1, 2, 2, 3, 3, 3, 3, 3]), (184320, [1, 2, 2, 3, 3, 9]), (174080/3, [1, 2, 3, 3, 3, 8]), (184320, [1, 2, 3, 3, 4, 7]), (184320, [1, 2, 3, 3, 5, 6]), (368640, [1, 2, 3, 14]), (61440, [1, 3, 3, 3, 3, 7]), (81920, [1, 3, 3, 3, 4, 6]), (40960, [1, 3, 3, 3, 5, 5]), (368640, [1, 3, 3, 13]), (5120/9, [2, 2, 2, 2, 3, 3, 3, 3]), (40960, [2, 2, 3, 3, 3, 7]), (358400/9, [2, 3, 3, 3, 3, 6]), (40960, [2, 3, 3, 3, 4, 5]), (184320, [2, 3, 3, 12])]

def node4Piece50Output_sector0_chunk1 : RawPoly ℕ := [(20480/3, [3, 3, 3, 3, 3, 5]), (10240/3, [3, 3, 3, 3, 4, 4]), (81920, [3, 3, 3, 11])]

def node4Piece50Output_sector0 : RawPoly ℕ := [node4Piece50Output_sector0_chunk0, node4Piece50Output_sector0_chunk1].flatten

def node4Piece50Output : SectorVector := [(0, node4Piece50Output_sector0)]
theorem node4Piece50_check : VectorCertificate (neutralBoundS JR (-2) node4Piece50Input) node4Piece50Output := by decide +kernel
theorem node4Piece50_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece50Input) = evaluate node4Piece50Output :=
  neutralBound_value JR _ _ _ node4Piece50_check

def node4Piece51Input_sector0 : RawPoly ℕ := [(320, [1, 2, 3, 9])]

def node4Piece51Input : SectorVector := [(0, node4Piece51Input_sector0)]
def node4Piece51Output_sector0_chunk0 : RawPoly ℕ := [(1280, [1, 1, 1, 1, 2, 2, 3, 9]), (34560, [1, 1, 1, 2, 3, 12]), (11520, [1, 1, 1, 2, 6, 9]), (7680, [1, 1, 1, 3, 5, 9]), (69120, [1, 1, 2, 2, 3, 11]), (23040, [1, 1, 2, 2, 5, 9]), (69120, [1, 1, 2, 3, 3, 10]), (109440, [1, 1, 2, 3, 4, 9]), (69120, [1, 1, 2, 3, 5, 8]), (69120, [1, 1, 2, 3, 6, 7]), (207360, [1, 1, 2, 16]), (7680, [1, 1, 3, 3, 3, 9]), (138240, [1, 1, 3, 15]), (46080, [1, 1, 9, 9]), (34560, [1, 2, 2, 2, 3, 10]), (11520, [1, 2, 2, 2, 4, 9]), (97280, [1, 2, 2, 3, 3, 9]), (69120, [1, 2, 2, 3, 4, 8]), (69120, [1, 2, 2, 3, 5, 7]), (34560, [1, 2, 2, 3, 6, 6]), (207360, [1, 2, 2, 15]), (34560, [1, 2, 3, 3, 3, 8]), (69120, [1, 2, 3, 3, 4, 7]), (69120, [1, 2, 3, 3, 5, 6])]

def node4Piece51Output_sector0_chunk1 : RawPoly ℕ := [(34560, [1, 2, 3, 4, 4, 6]), (34560, [1, 2, 3, 4, 5, 5]), (-1474560, [1, 2, 3, 14]), (207360, [1, 2, 4, 13]), (207360, [1, 2, 5, 12]), (207360, [1, 2, 6, 11]), (207360, [1, 2, 7, 10]), (136320, [1, 2, 8, 9]), (138240, [1, 3, 3, 13]), (138240, [1, 3, 4, 12]), (138240, [1, 3, 5, 11]), (138240, [1, 3, 6, 10]), (138240, [1, 3, 7, 9]), (69120, [1, 3, 8, 8]), (46080, [1, 4, 6, 9]), (23040, [1, 5, 5, 9]), (414720, [1, 19]), (1280, [2, 2, 2, 2, 3, 9]), (69120, [2, 2, 3, 13]), (23040, [2, 2, 7, 9]), (69120, [2, 3, 3, 12]), (69120, [2, 3, 4, 11]), (69120, [2, 3, 5, 10]), (89600, [2, 3, 6, 9])]

def node4Piece51Output_sector0_chunk2 : RawPoly ℕ := [(69120, [2, 3, 7, 8]), (23040, [2, 4, 5, 9]), (207360, [2, 18]), (15360, [3, 3, 5, 9]), (7680, [3, 4, 4, 9]), (138240, [3, 17]), (46080, [9, 11])]

def node4Piece51Output_sector0 : RawPoly ℕ := [node4Piece51Output_sector0_chunk0, node4Piece51Output_sector0_chunk1, node4Piece51Output_sector0_chunk2].flatten

def node4Piece51Output : SectorVector := [(0, node4Piece51Output_sector0)]
theorem node4Piece51_check : VectorCertificate (neutralBoundS JR (-2) node4Piece51Input) node4Piece51Output := by decide +kernel
theorem node4Piece51_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece51Input) = evaluate node4Piece51Output :=
  neutralBound_value JR _ _ _ node4Piece51_check

def node4Piece52Input_sector0 : RawPoly ℕ := [(-210, [1, 2, 4, 8])]

def node4Piece52Input : SectorVector := [(0, node4Piece52Input_sector0)]
def node4Piece52Output_sector0_chunk0 : RawPoly ℕ := [(-840, [1, 1, 1, 1, 2, 2, 4, 8]), (-20160, [1, 1, 1, 2, 4, 11]), (-10080, [1, 1, 1, 2, 7, 8]), (-5040, [1, 1, 1, 4, 5, 8]), (-40320, [1, 1, 2, 2, 4, 10]), (-20160, [1, 1, 2, 2, 6, 8]), (-40320, [1, 1, 2, 3, 4, 9]), (-20160, [1, 1, 2, 3, 5, 8]), (-61740, [1, 1, 2, 4, 4, 8]), (-40320, [1, 1, 2, 4, 5, 7]), (-20160, [1, 1, 2, 4, 6, 6]), (-161280, [1, 1, 2, 16]), (-5040, [1, 1, 3, 3, 4, 8]), (-80640, [1, 1, 4, 14]), (-40320, [1, 1, 8, 10]), (-20160, [1, 2, 2, 2, 4, 9]), (-10080, [1, 2, 2, 2, 5, 8]), (-71400, [1, 2, 2, 3, 4, 8]), (-40320, [1, 2, 2, 4, 4, 7]), (-40320, [1, 2, 2, 4, 5, 6]), (-161280, [1, 2, 2, 15]), (-3360, [1, 2, 3, 3, 3, 8]), (-20160, [1, 2, 3, 3, 4, 7]), (-40320, [1, 2, 3, 4, 4, 6])]

def node4Piece52Output_sector0_chunk1 : RawPoly ℕ := [(-20160, [1, 2, 3, 4, 5, 5]), (-161280, [1, 2, 3, 14]), (-20160, [1, 2, 4, 4, 4, 5]), (635040, [1, 2, 4, 13]), (-161280, [1, 2, 5, 12]), (-161280, [1, 2, 6, 11]), (-161280, [1, 2, 7, 10]), (-48720, [1, 2, 8, 9]), (-80640, [1, 3, 4, 12]), (-40320, [1, 3, 8, 8]), (-80640, [1, 4, 4, 11]), (-80640, [1, 4, 5, 10]), (-80640, [1, 4, 6, 9]), (-90720, [1, 4, 7, 8]), (-40320, [1, 5, 6, 8]), (-322560, [1, 19]), (-840, [2, 2, 2, 2, 4, 8]), (-40320, [2, 2, 4, 12]), (-20160, [2, 2, 8, 8]), (-40320, [2, 3, 4, 11]), (-20160, [2, 3, 7, 8]), (-40320, [2, 4, 4, 10]), (-40320, [2, 4, 5, 9]), (-58800, [2, 4, 6, 8])]

def node4Piece52Output_sector0_chunk2 : RawPoly ℕ := [(-20160, [2, 4, 7, 7]), (-10080, [2, 5, 5, 8]), (-161280, [2, 18]), (-10080, [3, 4, 5, 8]), (-5040, [4, 4, 4, 8]), (-80640, [4, 16]), (-40320, [8, 12])]

def node4Piece52Output_sector0 : RawPoly ℕ := [node4Piece52Output_sector0_chunk0, node4Piece52Output_sector0_chunk1, node4Piece52Output_sector0_chunk2].flatten

def node4Piece52Output : SectorVector := [(0, node4Piece52Output_sector0)]
theorem node4Piece52_check : VectorCertificate (neutralBoundS JR (-2) node4Piece52Input) node4Piece52Output := by decide +kernel
theorem node4Piece52_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece52Input) = evaluate node4Piece52Output :=
  neutralBound_value JR _ _ _ node4Piece52_check

def node4Piece53Input_sector0 : RawPoly ℕ := [(384/7, [1, 2, 5, 7])]

def node4Piece53Input : SectorVector := [(0, node4Piece53Input_sector0)]
def node4Piece53Output_sector0_chunk0 : RawPoly ℕ := [(1536/7, [1, 1, 1, 1, 2, 2, 5, 7]), (4608, [1, 1, 1, 2, 5, 10]), (23040/7, [1, 1, 1, 2, 7, 8]), (9216/7, [1, 1, 1, 5, 5, 7]), (9216, [1, 1, 2, 2, 5, 9]), (46080/7, [1, 1, 2, 2, 7, 7]), (9216, [1, 1, 2, 3, 5, 8]), (46080/7, [1, 1, 2, 3, 6, 7]), (131328/7, [1, 1, 2, 4, 5, 7]), (9216, [1, 1, 2, 5, 5, 6]), (46080, [1, 1, 2, 16]), (9216/7, [1, 1, 3, 3, 5, 7]), (18432, [1, 1, 5, 13]), (92160/7, [1, 1, 7, 11]), (4608, [1, 2, 2, 2, 5, 8]), (23040/7, [1, 2, 2, 2, 6, 7]), (130560/7, [1, 2, 2, 3, 5, 7]), (23040/7, [1, 2, 2, 4, 4, 7]), (9216, [1, 2, 2, 4, 5, 6]), (4608, [1, 2, 2, 5, 5, 5]), (46080, [1, 2, 2, 15]), (23040/7, [1, 2, 3, 3, 4, 7]), (4608, [1, 2, 3, 3, 5, 6]), (9216, [1, 2, 3, 4, 5, 5])]

def node4Piece53Output_sector0_chunk1 : RawPoly ℕ := [(46080, [1, 2, 3, 14]), (1536, [1, 2, 4, 4, 4, 5]), (46080, [1, 2, 4, 13]), (-97536, [1, 2, 5, 12]), (46080, [1, 2, 6, 11]), (-69120/7, [1, 2, 7, 10]), (46080, [1, 2, 8, 9]), (18432, [1, 3, 5, 11]), (92160/7, [1, 3, 7, 9]), (18432, [1, 4, 5, 10]), (92160/7, [1, 4, 7, 8]), (18432, [1, 5, 5, 9]), (18432, [1, 5, 6, 8]), (101376/7, [1, 5, 7, 7]), (46080/7, [1, 6, 6, 7]), (92160, [1, 19]), (1536/7, [2, 2, 2, 2, 5, 7]), (9216, [2, 2, 5, 11]), (46080/7, [2, 2, 7, 9]), (9216, [2, 3, 5, 10]), (46080/7, [2, 3, 7, 8]), (9216, [2, 4, 5, 9]), (46080/7, [2, 4, 7, 7]), (9216, [2, 5, 5, 8])]

def node4Piece53Output_sector0_chunk2 : RawPoly ℕ := [(15360, [2, 5, 6, 7]), (46080, [2, 18]), (18432/7, [3, 5, 5, 7]), (9216/7, [4, 4, 5, 7]), (18432, [5, 15]), (92160/7, [7, 13])]

def node4Piece53Output_sector0 : RawPoly ℕ := [node4Piece53Output_sector0_chunk0, node4Piece53Output_sector0_chunk1, node4Piece53Output_sector0_chunk2].flatten

def node4Piece53Output : SectorVector := [(0, node4Piece53Output_sector0)]
theorem node4Piece53_check : VectorCertificate (neutralBoundS JR (-2) node4Piece53Input) node4Piece53Output := by decide +kernel
theorem node4Piece53_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece53Input) = evaluate node4Piece53Output :=
  neutralBound_value JR _ _ _ node4Piece53_check

def node4Piece54Input_sector0 : RawPoly ℕ := [(240, [1, 3, 3, 8])]

def node4Piece54Input : SectorVector := [(0, node4Piece54Input_sector0)]
def node4Piece54Output_sector0_chunk0 : RawPoly ℕ := [(960, [1, 1, 1, 1, 2, 3, 3, 8]), (23040, [1, 1, 1, 3, 3, 11]), (17280, [1, 1, 1, 3, 6, 8]), (46080, [1, 1, 2, 3, 3, 10]), (34560, [1, 1, 2, 3, 5, 8]), (46080, [1, 1, 3, 3, 3, 9]), (82080, [1, 1, 3, 3, 4, 8]), (46080, [1, 1, 3, 3, 5, 7]), (23040, [1, 1, 3, 3, 6, 6]), (276480, [1, 1, 3, 15]), (51840, [1, 1, 8, 10]), (23040, [1, 2, 2, 3, 3, 9]), (17280, [1, 2, 2, 3, 4, 8]), (70080, [1, 2, 3, 3, 3, 8]), (46080, [1, 2, 3, 3, 4, 7]), (46080, [1, 2, 3, 3, 5, 6]), (276480, [1, 2, 3, 14]), (51840, [1, 2, 8, 9]), (23040, [1, 3, 3, 3, 3, 7]), (46080, [1, 3, 3, 3, 4, 6]), (23040, [1, 3, 3, 3, 5, 5]), (23040, [1, 3, 3, 4, 4, 5]), (-725760, [1, 3, 3, 13]), (276480, [1, 3, 4, 12])]

def node4Piece54Output_sector0_chunk1 : RawPoly ℕ := [(276480, [1, 3, 5, 11]), (276480, [1, 3, 6, 10]), (276480, [1, 3, 7, 9]), (14400, [1, 3, 8, 8]), (51840, [1, 4, 7, 8]), (51840, [1, 5, 6, 8]), (414720, [1, 19]), (960, [2, 2, 2, 3, 3, 8]), (46080, [2, 3, 3, 12]), (34560, [2, 3, 7, 8]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (67200, [3, 3, 6, 8]), (23040, [3, 3, 7, 7]), (34560, [3, 4, 5, 8]), (276480, [3, 17]), (51840, [8, 12])]

def node4Piece54Output_sector0 : RawPoly ℕ := [node4Piece54Output_sector0_chunk0, node4Piece54Output_sector0_chunk1].flatten

def node4Piece54Output : SectorVector := [(0, node4Piece54Output_sector0)]
theorem node4Piece54_check : VectorCertificate (neutralBoundS JR (-2) node4Piece54Input) node4Piece54Output := by decide +kernel
theorem node4Piece54_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece54Input) = evaluate node4Piece54Output :=
  neutralBound_value JR _ _ _ node4Piece54_check

def node4Piece55Input_sector0 : RawPoly ℕ := [(480/7, [1, 3, 4, 7])]

def node4Piece55Input : SectorVector := [(0, node4Piece55Input_sector0)]
def node4Piece55Output_sector0_chunk0 : RawPoly ℕ := [(1920/7, [1, 1, 1, 1, 2, 3, 4, 7]), (5760, [1, 1, 1, 3, 4, 10]), (23040/7, [1, 1, 1, 3, 7, 7]), (17280/7, [1, 1, 1, 4, 6, 7]), (11520, [1, 1, 2, 3, 4, 9]), (46080/7, [1, 1, 2, 3, 6, 7]), (34560/7, [1, 1, 2, 4, 5, 7]), (11520, [1, 1, 3, 3, 4, 8]), (46080/7, [1, 1, 3, 3, 5, 7]), (20160, [1, 1, 3, 4, 4, 7]), (11520, [1, 1, 3, 4, 5, 6]), (46080, [1, 1, 3, 15]), (34560, [1, 1, 4, 14]), (138240/7, [1, 1, 7, 11]), (5760, [1, 2, 2, 3, 4, 8]), (23040/7, [1, 2, 2, 3, 5, 7]), (17280/7, [1, 2, 2, 4, 4, 7]), (157440/7, [1, 2, 3, 3, 4, 7]), (11520, [1, 2, 3, 4, 4, 6]), (5760, [1, 2, 3, 4, 5, 5]), (46080, [1, 2, 3, 14]), (34560, [1, 2, 4, 13]), (138240/7, [1, 2, 7, 10]), (7680/7, [1, 3, 3, 3, 3, 7])]

def node4Piece55Output_sector0_chunk1 : RawPoly ℕ := [(5760, [1, 3, 3, 3, 4, 6]), (11520, [1, 3, 3, 4, 4, 5]), (46080, [1, 3, 3, 13]), (1920, [1, 3, 4, 4, 4, 4]), (-121920, [1, 3, 4, 12]), (46080, [1, 3, 5, 11]), (46080, [1, 3, 6, 10]), (111360/7, [1, 3, 7, 9]), (23040, [1, 3, 8, 8]), (34560, [1, 4, 4, 11]), (34560, [1, 4, 5, 10]), (34560, [1, 4, 6, 9]), (204480/7, [1, 4, 7, 8]), (138240/7, [1, 5, 7, 7]), (69120/7, [1, 6, 6, 7]), (138240, [1, 19]), (1920/7, [2, 2, 2, 3, 4, 7]), (11520, [2, 3, 4, 11]), (46080/7, [2, 3, 7, 8]), (34560/7, [2, 4, 7, 7]), (11520, [3, 3, 4, 10]), (46080/7, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (11520, [3, 4, 5, 8])]

def node4Piece55Output_sector0_chunk2 : RawPoly ℕ := [(19200, [3, 4, 6, 7]), (23040/7, [3, 5, 5, 7]), (46080, [3, 17]), (34560/7, [4, 4, 5, 7]), (34560, [4, 16]), (138240/7, [7, 13])]

def node4Piece55Output_sector0 : RawPoly ℕ := [node4Piece55Output_sector0_chunk0, node4Piece55Output_sector0_chunk1, node4Piece55Output_sector0_chunk2].flatten

def node4Piece55Output : SectorVector := [(0, node4Piece55Output_sector0)]
theorem node4Piece55_check : VectorCertificate (neutralBoundS JR (-2) node4Piece55Input) node4Piece55Output := by decide +kernel
theorem node4Piece55_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece55Input) = evaluate node4Piece55Output :=
  neutralBound_value JR _ _ _ node4Piece55_check

def node4Piece56Input_sector0 : RawPoly ℕ := [(256, [1, 3, 5, 6])]

def node4Piece56Input : SectorVector := [(0, node4Piece56Input_sector0)]
def node4Piece56Output_sector0_chunk0 : RawPoly ℕ := [(1024, [1, 1, 1, 1, 2, 3, 5, 6]), (18432, [1, 1, 1, 3, 5, 9]), (15360, [1, 1, 1, 3, 6, 8]), (9216, [1, 1, 1, 5, 6, 6]), (36864, [1, 1, 2, 3, 5, 8]), (30720, [1, 1, 2, 3, 6, 7]), (18432, [1, 1, 2, 5, 5, 6]), (36864, [1, 1, 3, 3, 5, 7]), (30720, [1, 1, 3, 3, 6, 6]), (87552, [1, 1, 3, 4, 5, 6]), (18432, [1, 1, 3, 5, 5, 5]), (184320, [1, 1, 3, 15]), (110592, [1, 1, 5, 13]), (92160, [1, 1, 6, 12]), (18432, [1, 2, 2, 3, 5, 7]), (15360, [1, 2, 2, 3, 6, 6]), (9216, [1, 2, 2, 4, 5, 6]), (83968, [1, 2, 3, 3, 5, 6]), (15360, [1, 2, 3, 4, 4, 6]), (36864, [1, 2, 3, 4, 5, 5]), (184320, [1, 2, 3, 14]), (110592, [1, 2, 5, 12]), (92160, [1, 2, 6, 11]), (15360, [1, 3, 3, 3, 4, 6])]

def node4Piece56Output_sector0_chunk1 : RawPoly ℕ := [(18432, [1, 3, 3, 3, 5, 5]), (18432, [1, 3, 3, 4, 4, 5]), (184320, [1, 3, 3, 13]), (184320, [1, 3, 4, 12]), (-215040, [1, 3, 5, 11]), (-46080, [1, 3, 6, 10]), (184320, [1, 3, 7, 9]), (92160, [1, 3, 8, 8]), (110592, [1, 4, 5, 10]), (92160, [1, 4, 6, 9]), (110592, [1, 5, 5, 9]), (109056, [1, 5, 6, 8]), (55296, [1, 5, 7, 7]), (92160, [1, 6, 6, 7]), (552960, [1, 19]), (1024, [2, 2, 2, 3, 5, 6]), (36864, [2, 3, 5, 10]), (30720, [2, 3, 6, 9]), (18432, [2, 5, 6, 7]), (36864, [3, 3, 5, 9]), (30720, [3, 3, 6, 8]), (36864, [3, 4, 5, 8]), (30720, [3, 4, 6, 7]), (36864, [3, 5, 5, 7])]

def node4Piece56Output_sector0_chunk2 : RawPoly ℕ := [(53248, [3, 5, 6, 6]), (184320, [3, 17]), (18432, [4, 5, 5, 6]), (110592, [5, 15]), (92160, [6, 14])]

def node4Piece56Output_sector0 : RawPoly ℕ := [node4Piece56Output_sector0_chunk0, node4Piece56Output_sector0_chunk1, node4Piece56Output_sector0_chunk2].flatten

def node4Piece56Output : SectorVector := [(0, node4Piece56Output_sector0)]
theorem node4Piece56_check : VectorCertificate (neutralBoundS JR (-2) node4Piece56Input) node4Piece56Output := by decide +kernel
theorem node4Piece56_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece56Input) = evaluate node4Piece56Output :=
  neutralBound_value JR _ _ _ node4Piece56_check

def node4Piece57Input_sector0 : RawPoly ℕ := [(-120, [1, 4, 4, 6])]

def node4Piece57Input : SectorVector := [(0, node4Piece57Input_sector0)]
def node4Piece57Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 1, 2, 4, 4, 6]), (-8640, [1, 1, 1, 4, 4, 9]), (-11520, [1, 1, 1, 4, 6, 7]), (-17280, [1, 1, 2, 4, 4, 8]), (-23040, [1, 1, 2, 4, 6, 6]), (-17280, [1, 1, 3, 4, 4, 7]), (-23040, [1, 1, 3, 4, 5, 6]), (-29520, [1, 1, 4, 4, 4, 6]), (-8640, [1, 1, 4, 4, 5, 5]), (-138240, [1, 1, 4, 14]), (-46080, [1, 1, 6, 12]), (-8640, [1, 2, 2, 4, 4, 7]), (-11520, [1, 2, 2, 4, 5, 6]), (-43680, [1, 2, 3, 4, 4, 6]), (-17280, [1, 2, 4, 4, 4, 5]), (-138240, [1, 2, 4, 13]), (-46080, [1, 2, 6, 11]), (-3840, [1, 3, 3, 3, 4, 6]), (-8640, [1, 3, 3, 4, 4, 5]), (-8640, [1, 3, 4, 4, 4, 4]), (-138240, [1, 3, 4, 12]), (-46080, [1, 3, 6, 10]), (100800, [1, 4, 4, 11]), (-138240, [1, 4, 5, 10])]

def node4Piece57Output_sector0_chunk1 : RawPoly ℕ := [(-9600, [1, 4, 6, 9]), (-138240, [1, 4, 7, 8]), (-46080, [1, 5, 6, 8]), (-46080, [1, 6, 6, 7]), (-276480, [1, 19]), (-480, [2, 2, 2, 4, 4, 6]), (-17280, [2, 4, 4, 10]), (-23040, [2, 4, 6, 8]), (-17280, [3, 4, 4, 9]), (-23040, [3, 4, 6, 7]), (-17280, [4, 4, 4, 8]), (-17280, [4, 4, 5, 7]), (-24960, [4, 4, 6, 6]), (-11520, [4, 5, 5, 6]), (-138240, [4, 16]), (-46080, [6, 14])]

def node4Piece57Output_sector0 : RawPoly ℕ := [node4Piece57Output_sector0_chunk0, node4Piece57Output_sector0_chunk1].flatten

def node4Piece57Output : SectorVector := [(0, node4Piece57Output_sector0)]
theorem node4Piece57_check : VectorCertificate (neutralBoundS JR (-2) node4Piece57Input) node4Piece57Output := by decide +kernel
theorem node4Piece57_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece57Input) = evaluate node4Piece57Output :=
  neutralBound_value JR _ _ _ node4Piece57_check

def node4Piece58Input_sector0 : RawPoly ℕ := [(-48/5, [1, 4, 5, 5])]

def node4Piece58Input : SectorVector := [(0, node4Piece58Input_sector0)]
def node4Piece58Output_sector0_chunk0 : RawPoly ℕ := [(-192/5, [1, 1, 1, 1, 2, 4, 5, 5]), (-1152, [1, 1, 1, 4, 5, 8]), (-2304/5, [1, 1, 1, 5, 5, 7]), (-2304, [1, 1, 2, 4, 5, 7]), (-4608/5, [1, 1, 2, 5, 5, 6]), (-2304, [1, 1, 3, 4, 5, 6]), (-4608/5, [1, 1, 3, 5, 5, 5]), (-14112/5, [1, 1, 4, 4, 5, 5]), (-5760, [1, 1, 4, 14]), (-9216, [1, 1, 5, 13]), (-1152, [1, 2, 2, 4, 5, 6]), (-2304/5, [1, 2, 2, 5, 5, 5]), (-17472/5, [1, 2, 3, 4, 5, 5]), (-1152, [1, 2, 4, 4, 4, 5]), (-5760, [1, 2, 4, 13]), (-9216, [1, 2, 5, 12]), (-768/5, [1, 3, 3, 3, 5, 5]), (-1152, [1, 3, 3, 4, 4, 5]), (-5760, [1, 3, 4, 12]), (-9216, [1, 3, 5, 11]), (-5760, [1, 4, 4, 11]), (9216, [1, 4, 5, 10]), (-5760, [1, 4, 6, 9]), (-5760, [1, 4, 7, 8])]

def node4Piece58Output_sector0_chunk1 : RawPoly ℕ := [(-11136/5, [1, 5, 5, 9]), (-9216, [1, 5, 6, 8]), (-4608, [1, 5, 7, 7]), (-23040, [1, 19]), (-192/5, [2, 2, 2, 4, 5, 5]), (-2304, [2, 4, 5, 9]), (-4608/5, [2, 5, 5, 8]), (-2304, [3, 4, 5, 8]), (-4608/5, [3, 5, 5, 7]), (-2304, [4, 4, 5, 7]), (-2688, [4, 5, 5, 6]), (-5760, [4, 16]), (-2304/5, [5, 5, 5, 5]), (-9216, [5, 15])]

def node4Piece58Output_sector0 : RawPoly ℕ := [node4Piece58Output_sector0_chunk0, node4Piece58Output_sector0_chunk1].flatten

def node4Piece58Output : SectorVector := [(0, node4Piece58Output_sector0)]
theorem node4Piece58_check : VectorCertificate (neutralBoundS JR (-2) node4Piece58Input) node4Piece58Output := by decide +kernel
theorem node4Piece58_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece58Input) = evaluate node4Piece58Output :=
  neutralBound_value JR _ _ _ node4Piece58_check

def node4Piece59Input_sector0 : RawPoly ℕ := [(240/7, [1, 14])]

def node4Piece59Input : SectorVector := [(0, node4Piece59Input_sector0)]
def node4Piece59Output_sector0_chunk0 : RawPoly ℕ := [(960/7, [1, 1, 1, 1, 2, 14]), (5760, [1, 1, 1, 17]), (11520, [1, 1, 2, 16]), (11520, [1, 1, 3, 15]), (82080/7, [1, 1, 4, 14]), (11520, [1, 1, 5, 13]), (11520, [1, 1, 6, 12]), (11520, [1, 1, 7, 11]), (11520, [1, 1, 8, 10]), (5760, [1, 1, 9, 9]), (5760, [1, 2, 2, 15]), (12480, [1, 2, 3, 14]), (11520, [1, 2, 4, 13]), (11520, [1, 2, 5, 12]), (11520, [1, 2, 6, 11]), (11520, [1, 2, 7, 10]), (11520, [1, 2, 8, 9]), (5760, [1, 3, 3, 13]), (11520, [1, 3, 4, 12]), (11520, [1, 3, 5, 11]), (11520, [1, 3, 6, 10]), (11520, [1, 3, 7, 9]), (5760, [1, 3, 8, 8]), (5760, [1, 4, 4, 11])]

def node4Piece59Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 4, 5, 10]), (11520, [1, 4, 6, 9]), (11520, [1, 4, 7, 8]), (5760, [1, 5, 5, 9]), (11520, [1, 5, 6, 8]), (5760, [1, 5, 7, 7]), (5760, [1, 6, 6, 7]), (-639360, [1, 19]), (960/7, [2, 2, 2, 14]), (11520, [2, 18]), (11520, [3, 17]), (11520, [4, 16]), (11520, [5, 15]), (9600, [6, 14]), (11520, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node4Piece59Output_sector0 : RawPoly ℕ := [node4Piece59Output_sector0_chunk0, node4Piece59Output_sector0_chunk1].flatten

def node4Piece59Output : SectorVector := [(0, node4Piece59Output_sector0)]
theorem node4Piece59_check : VectorCertificate (neutralBoundS JR (-2) node4Piece59Input) node4Piece59Output := by decide +kernel
theorem node4Piece59_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece59Input) = evaluate node4Piece59Output :=
  neutralBound_value JR _ _ _ node4Piece59_check

def node4Piece60Input_sector0 : RawPoly ℕ := [(-312/5, [2, 2, 2, 2, 2, 5])]

def node4Piece60Input : SectorVector := [(0, node4Piece60Input_sector0)]
def node4Piece60Output_sector0 : RawPoly ℕ := [(-1248/5, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (-3744, [1, 1, 2, 2, 2, 2, 2, 8]), (-7488, [1, 1, 2, 2, 2, 2, 5, 5]), (-7488, [1, 2, 2, 2, 2, 2, 2, 7]), (-7488, [1, 2, 2, 2, 2, 2, 3, 6]), (-110448/5, [1, 2, 2, 2, 2, 2, 4, 5]), (-7488, [1, 2, 2, 2, 2, 3, 3, 5]), (-74880, [1, 2, 2, 2, 2, 11]), (-59904, [1, 2, 2, 2, 5, 8]), (-3744, [2, 2, 2, 2, 2, 2, 2, 6]), (-76128/5, [2, 2, 2, 2, 2, 2, 3, 5]), (-3744, [2, 2, 2, 2, 2, 2, 4, 4]), (-3744, [2, 2, 2, 2, 2, 3, 3, 4]), (11232, [2, 2, 2, 2, 2, 10]), (-74880, [2, 2, 2, 2, 3, 9]), (-74880, [2, 2, 2, 2, 4, 8]), (-74880, [2, 2, 2, 2, 5, 7]), (-37440, [2, 2, 2, 2, 6, 6]), (-59904, [2, 2, 2, 3, 5, 6]), (-59904, [2, 2, 2, 4, 5, 5]), (-299520, [2, 2, 2, 14]), (-119808, [2, 2, 5, 11])]

def node4Piece60Output : SectorVector := [(0, node4Piece60Output_sector0)]
theorem node4Piece60_check : VectorCertificate (neutralBoundS JR (-2) node4Piece60Input) node4Piece60Output := by decide +kernel
theorem node4Piece60_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece60Input) = evaluate node4Piece60Output :=
  neutralBound_value JR _ _ _ node4Piece60_check

def node4Piece61Input_sector0 : RawPoly ℕ := [(-160, [2, 2, 2, 2, 3, 4])]

def node4Piece61Input : SectorVector := [(0, node4Piece61Input_sector0)]
def node4Piece61Output_sector0_chunk0 : RawPoly ℕ := [(-640, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-7680, [1, 1, 2, 2, 2, 2, 3, 7]), (-5760, [1, 1, 2, 2, 2, 2, 4, 6]), (-15360, [1, 1, 2, 2, 2, 3, 4, 5]), (-15360, [1, 2, 2, 2, 2, 2, 3, 6]), (-11520, [1, 2, 2, 2, 2, 2, 4, 5]), (-15360, [1, 2, 2, 2, 2, 3, 3, 5]), (-48960, [1, 2, 2, 2, 2, 3, 4, 4]), (-46080, [1, 2, 2, 2, 2, 11]), (-15360, [1, 2, 2, 2, 3, 3, 3, 4]), (-122880, [1, 2, 2, 2, 3, 10]), (-92160, [1, 2, 2, 2, 4, 9]), (-92160, [1, 2, 2, 3, 4, 8]), (-7680, [2, 2, 2, 2, 2, 2, 3, 5]), (-5760, [2, 2, 2, 2, 2, 2, 4, 4]), (-37120, [2, 2, 2, 2, 2, 3, 3, 4]), (-46080, [2, 2, 2, 2, 2, 10]), (-2560, [2, 2, 2, 2, 3, 3, 3, 3]), (-37120, [2, 2, 2, 2, 3, 9]), (-68160, [2, 2, 2, 2, 4, 8]), (-46080, [2, 2, 2, 2, 5, 7]), (-23040, [2, 2, 2, 2, 6, 6]), (-122880, [2, 2, 2, 3, 3, 8]), (-184320, [2, 2, 2, 3, 4, 7])]

def node4Piece61Output_sector0_chunk1 : RawPoly ℕ := [(-122880, [2, 2, 2, 3, 5, 6]), (-92160, [2, 2, 2, 4, 4, 6]), (-46080, [2, 2, 2, 4, 5, 5]), (-368640, [2, 2, 2, 14]), (-92160, [2, 2, 3, 3, 4, 6]), (-92160, [2, 2, 3, 4, 4, 5]), (-368640, [2, 2, 3, 13]), (-276480, [2, 2, 4, 12]), (-122880, [2, 3, 4, 11])]

def node4Piece61Output_sector0 : RawPoly ℕ := [node4Piece61Output_sector0_chunk0, node4Piece61Output_sector0_chunk1].flatten

def node4Piece61Output : SectorVector := [(0, node4Piece61Output_sector0)]
theorem node4Piece61_check : VectorCertificate (neutralBoundS JR (-2) node4Piece61Input) node4Piece61Output := by decide +kernel
theorem node4Piece61_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece61Input) = evaluate node4Piece61Output :=
  neutralBound_value JR _ _ _ node4Piece61_check

def node4Piece62Input_sector0 : RawPoly ℕ := [(160/9, [2, 2, 2, 3, 3, 3])]

def node4Piece62Input : SectorVector := [(0, node4Piece62Input_sector0)]
def node4Piece62Output_sector0 : RawPoly ℕ := [(640/9, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (1920, [1, 1, 2, 2, 2, 3, 3, 6]), (1280, [1, 1, 2, 2, 3, 3, 3, 5]), (3840, [1, 2, 2, 2, 2, 3, 3, 5]), (18880/3, [1, 2, 2, 2, 3, 3, 3, 4]), (11520, [1, 2, 2, 2, 3, 10]), (1280, [1, 2, 2, 3, 3, 3, 3, 3]), (23040, [1, 2, 2, 3, 3, 9]), (5120, [1, 2, 3, 3, 3, 8]), (1920, [2, 2, 2, 2, 2, 3, 3, 4]), (29440/9, [2, 2, 2, 2, 3, 3, 3, 3]), (11520, [2, 2, 2, 2, 3, 9]), (11200, [2, 2, 2, 3, 3, 8]), (11520, [2, 2, 2, 3, 4, 7]), (11520, [2, 2, 2, 3, 5, 6]), (11520, [2, 2, 2, 14]), (17920, [2, 2, 3, 3, 3, 7]), (23040, [2, 2, 3, 3, 4, 6]), (11520, [2, 2, 3, 3, 5, 5]), (69120, [2, 2, 3, 13]), (5120, [2, 3, 3, 3, 3, 6]), (5120, [2, 3, 3, 3, 4, 5]), (46080, [2, 3, 3, 12]), (10240/3, [3, 3, 3, 11])]

def node4Piece62Output : SectorVector := [(0, node4Piece62Output_sector0)]
theorem node4Piece62_check : VectorCertificate (neutralBoundS JR (-2) node4Piece62Input) node4Piece62Output := by decide +kernel
theorem node4Piece62_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece62Input) = evaluate node4Piece62Output :=
  neutralBound_value JR _ _ _ node4Piece62_check

def node4Piece63Input_sector0 : RawPoly ℕ := [(-160, [2, 2, 2, 9])]

def node4Piece63Input : SectorVector := [(0, node4Piece63Input_sector0)]
def node4Piece63Output_sector0_chunk0 : RawPoly ℕ := [(-640, [1, 1, 1, 2, 2, 2, 2, 9]), (-17280, [1, 1, 2, 2, 2, 12]), (-11520, [1, 1, 2, 2, 5, 9]), (-34560, [1, 2, 2, 2, 2, 11]), (-34560, [1, 2, 2, 2, 3, 10]), (-56640, [1, 2, 2, 2, 4, 9]), (-34560, [1, 2, 2, 2, 5, 8]), (-34560, [1, 2, 2, 2, 6, 7]), (-11520, [1, 2, 2, 3, 3, 9]), (-207360, [1, 2, 2, 15]), (-46080, [1, 2, 8, 9]), (-17280, [2, 2, 2, 2, 2, 10]), (-46720, [2, 2, 2, 2, 3, 9]), (-34560, [2, 2, 2, 2, 4, 8]), (-34560, [2, 2, 2, 2, 5, 7]), (-17280, [2, 2, 2, 2, 6, 6]), (-17280, [2, 2, 2, 3, 3, 8]), (-34560, [2, 2, 2, 3, 4, 7]), (-34560, [2, 2, 2, 3, 5, 6]), (-17280, [2, 2, 2, 4, 4, 6]), (-17280, [2, 2, 2, 4, 5, 5]), (737280, [2, 2, 2, 14]), (-207360, [2, 2, 3, 13]), (-207360, [2, 2, 4, 12])]

def node4Piece63Output_sector0_chunk1 : RawPoly ℕ := [(-207360, [2, 2, 5, 11]), (-207360, [2, 2, 6, 10]), (-161280, [2, 2, 7, 9]), (-103680, [2, 2, 8, 8]), (-46080, [2, 3, 6, 9]), (-46080, [2, 4, 5, 9]), (-414720, [2, 18]), (-30720, [9, 11])]

def node4Piece63Output_sector0 : RawPoly ℕ := [node4Piece63Output_sector0_chunk0, node4Piece63Output_sector0_chunk1].flatten

def node4Piece63Output : SectorVector := [(0, node4Piece63Output_sector0)]
theorem node4Piece63_check : VectorCertificate (neutralBoundS JR (-2) node4Piece63Input) node4Piece63Output := by decide +kernel
theorem node4Piece63_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece63Input) = evaluate node4Piece63Output :=
  neutralBound_value JR _ _ _ node4Piece63_check

def node4Piece64Input_sector0 : RawPoly ℕ := [(-60, [2, 2, 3, 8])]

def node4Piece64Input : SectorVector := [(0, node4Piece64Input_sector0)]
def node4Piece64Output_sector0_chunk0 : RawPoly ℕ := [(-240, [1, 1, 1, 2, 2, 2, 3, 8]), (-5760, [1, 1, 2, 2, 3, 11]), (-2160, [1, 1, 2, 2, 6, 8]), (-2880, [1, 1, 2, 3, 5, 8]), (-11520, [1, 2, 2, 2, 3, 10]), (-4320, [1, 2, 2, 2, 5, 8]), (-11520, [1, 2, 2, 3, 3, 9]), (-21240, [1, 2, 2, 3, 4, 8]), (-11520, [1, 2, 2, 3, 5, 7]), (-5760, [1, 2, 2, 3, 6, 6]), (-34560, [1, 2, 2, 15]), (-2880, [1, 2, 3, 3, 3, 8]), (-46080, [1, 2, 3, 14]), (-17280, [1, 2, 8, 9]), (-5760, [1, 3, 8, 8]), (-5760, [2, 2, 2, 2, 3, 9]), (-2160, [2, 2, 2, 2, 4, 8]), (-16800, [2, 2, 2, 3, 3, 8]), (-11520, [2, 2, 2, 3, 4, 7]), (-11520, [2, 2, 2, 3, 5, 6]), (-34560, [2, 2, 2, 14]), (-5760, [2, 2, 3, 3, 3, 7]), (-11520, [2, 2, 3, 3, 4, 6]), (-5760, [2, 2, 3, 3, 5, 5])]

def node4Piece64Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [2, 2, 3, 4, 4, 5]), (181440, [2, 2, 3, 13]), (-34560, [2, 2, 4, 12]), (-34560, [2, 2, 5, 11]), (-34560, [2, 2, 6, 10]), (-34560, [2, 2, 7, 9]), (-8280, [2, 2, 8, 8]), (-46080, [2, 3, 3, 12]), (-46080, [2, 3, 4, 11]), (-46080, [2, 3, 5, 10]), (-46080, [2, 3, 6, 9]), (-46080, [2, 3, 7, 8]), (-17280, [2, 4, 6, 8]), (-8640, [2, 5, 5, 8]), (-138240, [2, 18]), (-5760, [3, 3, 6, 8]), (-5760, [3, 4, 5, 8]), (-46080, [3, 17]), (-17280, [8, 12])]

def node4Piece64Output_sector0 : RawPoly ℕ := [node4Piece64Output_sector0_chunk0, node4Piece64Output_sector0_chunk1].flatten

def node4Piece64Output : SectorVector := [(0, node4Piece64Output_sector0)]
theorem node4Piece64_check : VectorCertificate (neutralBoundS JR (-2) node4Piece64Input) node4Piece64Output := by decide +kernel
theorem node4Piece64_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece64Input) = evaluate node4Piece64Output :=
  neutralBound_value JR _ _ _ node4Piece64_check

def node4Piece65Input_sector0 : RawPoly ℕ := [(-240, [2, 2, 4, 7])]

def node4Piece65Input : SectorVector := [(0, node4Piece65Input_sector0)]
def node4Piece65Output_sector0_chunk0 : RawPoly ℕ := [(-960, [1, 1, 1, 2, 2, 2, 4, 7]), (-20160, [1, 1, 2, 2, 4, 10]), (-11520, [1, 1, 2, 2, 7, 7]), (-11520, [1, 1, 2, 4, 5, 7]), (-40320, [1, 2, 2, 2, 4, 9]), (-23040, [1, 2, 2, 2, 6, 7]), (-40320, [1, 2, 2, 3, 4, 8]), (-23040, [1, 2, 2, 3, 5, 7]), (-73440, [1, 2, 2, 4, 4, 7]), (-40320, [1, 2, 2, 4, 5, 6]), (-161280, [1, 2, 2, 15]), (-11520, [1, 2, 3, 3, 4, 7]), (-161280, [1, 2, 4, 13]), (-92160, [1, 2, 7, 10]), (-23040, [1, 4, 7, 8]), (-20160, [2, 2, 2, 2, 4, 8]), (-11520, [2, 2, 2, 2, 5, 7]), (-75840, [2, 2, 2, 3, 4, 7]), (-40320, [2, 2, 2, 4, 4, 6]), (-20160, [2, 2, 2, 4, 5, 5]), (-161280, [2, 2, 2, 14]), (-3840, [2, 2, 3, 3, 3, 7]), (-20160, [2, 2, 3, 3, 4, 6]), (-40320, [2, 2, 3, 4, 4, 5])]

def node4Piece65Output_sector0_chunk1 : RawPoly ℕ := [(-161280, [2, 2, 3, 13]), (-6720, [2, 2, 4, 4, 4, 4]), (426720, [2, 2, 4, 12]), (-161280, [2, 2, 5, 11]), (-161280, [2, 2, 6, 10]), (-55680, [2, 2, 7, 9]), (-80640, [2, 2, 8, 8]), (-161280, [2, 3, 4, 11]), (-92160, [2, 3, 7, 8]), (-161280, [2, 4, 4, 10]), (-161280, [2, 4, 5, 9]), (-161280, [2, 4, 6, 8]), (-103680, [2, 4, 7, 7]), (-92160, [2, 5, 6, 7]), (-645120, [2, 18]), (-23040, [3, 4, 6, 7]), (-23040, [4, 4, 5, 7]), (-161280, [4, 16]), (-92160, [7, 13])]

def node4Piece65Output_sector0 : RawPoly ℕ := [node4Piece65Output_sector0_chunk0, node4Piece65Output_sector0_chunk1].flatten

def node4Piece65Output : SectorVector := [(0, node4Piece65Output_sector0)]
theorem node4Piece65_check : VectorCertificate (neutralBoundS JR (-2) node4Piece65Input) node4Piece65Output := by decide +kernel
theorem node4Piece65_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece65Input) = evaluate node4Piece65Output :=
  neutralBound_value JR _ _ _ node4Piece65_check

def node4Piece66Input_sector0 : RawPoly ℕ := [(-144, [2, 2, 5, 6])]

def node4Piece66Input : SectorVector := [(0, node4Piece66Input_sector0)]
def node4Piece66Output_sector0_chunk0 : RawPoly ℕ := [(-576, [1, 1, 1, 2, 2, 2, 5, 6]), (-10368, [1, 1, 2, 2, 5, 9]), (-8640, [1, 1, 2, 2, 6, 8]), (-6912, [1, 1, 2, 5, 5, 6]), (-20736, [1, 2, 2, 2, 5, 8]), (-17280, [1, 2, 2, 2, 6, 7]), (-20736, [1, 2, 2, 3, 5, 7]), (-17280, [1, 2, 2, 3, 6, 6]), (-50976, [1, 2, 2, 4, 5, 6]), (-10368, [1, 2, 2, 5, 5, 5]), (-103680, [1, 2, 2, 15]), (-6912, [1, 2, 3, 3, 5, 6]), (-82944, [1, 2, 5, 12]), (-69120, [1, 2, 6, 11]), (-13824, [1, 5, 6, 8]), (-10368, [2, 2, 2, 2, 5, 7]), (-8640, [2, 2, 2, 2, 6, 6]), (-45504, [2, 2, 2, 3, 5, 6]), (-8640, [2, 2, 2, 4, 4, 6]), (-20736, [2, 2, 2, 4, 5, 5]), (-103680, [2, 2, 2, 14]), (-8640, [2, 2, 3, 3, 4, 6]), (-10368, [2, 2, 3, 3, 5, 5]), (-10368, [2, 2, 3, 4, 4, 5])]

def node4Piece66Output_sector0_chunk1 : RawPoly ℕ := [(-103680, [2, 2, 3, 13]), (-103680, [2, 2, 4, 12]), (120960, [2, 2, 5, 11]), (25920, [2, 2, 6, 10]), (-103680, [2, 2, 7, 9]), (-51840, [2, 2, 8, 8]), (-82944, [2, 3, 5, 10]), (-69120, [2, 3, 6, 9]), (-82944, [2, 4, 5, 9]), (-69120, [2, 4, 6, 8]), (-82944, [2, 5, 5, 8]), (-110592, [2, 5, 6, 7]), (-34560, [2, 6, 6, 6]), (-414720, [2, 18]), (-13824, [3, 5, 6, 6]), (-13824, [4, 5, 5, 6]), (-82944, [5, 15]), (-69120, [6, 14])]

def node4Piece66Output_sector0 : RawPoly ℕ := [node4Piece66Output_sector0_chunk0, node4Piece66Output_sector0_chunk1].flatten

def node4Piece66Output : SectorVector := [(0, node4Piece66Output_sector0)]
theorem node4Piece66_check : VectorCertificate (neutralBoundS JR (-2) node4Piece66Input) node4Piece66Output := by decide +kernel
theorem node4Piece66_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece66Input) = evaluate node4Piece66Output :=
  neutralBound_value JR _ _ _ node4Piece66_check

def node4Piece67Input_sector0 : RawPoly ℕ := [(960/7, [2, 3, 3, 7])]

def node4Piece67Input : SectorVector := [(0, node4Piece67Input_sector0)]
def node4Piece67Output_sector0_chunk0 : RawPoly ℕ := [(3840/7, [1, 1, 1, 2, 2, 3, 3, 7]), (11520, [1, 1, 2, 3, 3, 10]), (69120/7, [1, 1, 2, 3, 6, 7]), (23040/7, [1, 1, 3, 3, 5, 7]), (23040, [1, 2, 2, 3, 3, 9]), (138240/7, [1, 2, 2, 3, 5, 7]), (23040, [1, 2, 3, 3, 3, 8]), (339840/7, [1, 2, 3, 3, 4, 7]), (23040, [1, 2, 3, 3, 5, 6]), (138240, [1, 2, 3, 14]), (207360/7, [1, 2, 7, 10]), (23040/7, [1, 3, 3, 3, 3, 7]), (46080, [1, 3, 3, 13]), (276480/7, [1, 3, 7, 9]), (11520, [2, 2, 2, 3, 3, 8]), (69120/7, [2, 2, 2, 3, 4, 7]), (257280/7, [2, 2, 3, 3, 3, 7]), (23040, [2, 2, 3, 3, 4, 6]), (11520, [2, 2, 3, 3, 5, 5]), (138240, [2, 2, 3, 13]), (207360/7, [2, 2, 7, 9]), (11520, [2, 3, 3, 3, 3, 6]), (23040, [2, 3, 3, 3, 4, 5]), (3840, [2, 3, 3, 4, 4, 4])]

def node4Piece67Output_sector0_chunk1 : RawPoly ℕ := [(-243840, [2, 3, 3, 12]), (138240, [2, 3, 4, 11]), (138240, [2, 3, 5, 10]), (138240, [2, 3, 6, 9]), (610560/7, [2, 3, 7, 8]), (207360/7, [2, 4, 7, 7]), (207360/7, [2, 5, 6, 7]), (207360, [2, 18]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (46080, [3, 3, 6, 8]), (253440/7, [3, 3, 7, 7]), (276480/7, [3, 4, 6, 7]), (138240/7, [3, 5, 5, 7]), (276480, [3, 17]), (414720/7, [7, 13])]

def node4Piece67Output_sector0 : RawPoly ℕ := [node4Piece67Output_sector0_chunk0, node4Piece67Output_sector0_chunk1].flatten

def node4Piece67Output : SectorVector := [(0, node4Piece67Output_sector0)]
theorem node4Piece67_check : VectorCertificate (neutralBoundS JR (-2) node4Piece67Input) node4Piece67Output := by decide +kernel
theorem node4Piece67_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece67Input) = evaluate node4Piece67Output :=
  neutralBound_value JR _ _ _ node4Piece67_check

def node4Piece68Input_sector0 : RawPoly ℕ := [(-40, [2, 3, 4, 6])]

def node4Piece68Input : SectorVector := [(0, node4Piece68Input_sector0)]
def node4Piece68Output_sector0_chunk0 : RawPoly ℕ := [(-160, [1, 1, 1, 2, 2, 3, 4, 6]), (-2880, [1, 1, 2, 3, 4, 9]), (-1920, [1, 1, 2, 3, 6, 7]), (-1440, [1, 1, 2, 4, 6, 6]), (-960, [1, 1, 3, 4, 5, 6]), (-5760, [1, 2, 2, 3, 4, 8]), (-3840, [1, 2, 2, 3, 6, 6]), (-2880, [1, 2, 2, 4, 5, 6]), (-5760, [1, 2, 3, 3, 4, 7]), (-3840, [1, 2, 3, 3, 5, 6]), (-12240, [1, 2, 3, 4, 4, 6]), (-2880, [1, 2, 3, 4, 5, 5]), (-23040, [1, 2, 3, 14]), (-17280, [1, 2, 4, 13]), (-11520, [1, 2, 6, 11]), (-960, [1, 3, 3, 3, 4, 6]), (-11520, [1, 3, 4, 12]), (-7680, [1, 3, 6, 10]), (-5760, [1, 4, 6, 9]), (-2880, [2, 2, 2, 3, 4, 7]), (-1920, [2, 2, 2, 3, 5, 6]), (-1440, [2, 2, 2, 4, 4, 6]), (-12160, [2, 2, 3, 3, 4, 6]), (-5760, [2, 2, 3, 4, 4, 5])]

def node4Piece68Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 2, 3, 13]), (-17280, [2, 2, 4, 12]), (-11520, [2, 2, 6, 10]), (-640, [2, 3, 3, 3, 3, 6]), (-2880, [2, 3, 3, 3, 4, 5]), (-2880, [2, 3, 3, 4, 4, 4]), (-23040, [2, 3, 3, 12]), (33600, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-9280, [2, 3, 6, 9]), (-23040, [2, 3, 7, 8]), (-17280, [2, 4, 4, 10]), (-17280, [2, 4, 5, 9]), (-17040, [2, 4, 6, 8]), (-8640, [2, 4, 7, 7]), (-11520, [2, 5, 6, 7]), (-5760, [2, 6, 6, 6]), (-69120, [2, 18]), (-11520, [3, 3, 4, 10]), (-7680, [3, 3, 6, 8]), (-11520, [3, 4, 4, 9]), (-11520, [3, 4, 5, 8]), (-17280, [3, 4, 6, 7]), (-7680, [3, 5, 6, 6])]

def node4Piece68Output_sector0_chunk2 : RawPoly ℕ := [(-46080, [3, 17]), (-5760, [4, 4, 6, 6]), (-2880, [4, 5, 5, 6]), (-34560, [4, 16]), (-23040, [6, 14])]

def node4Piece68Output_sector0 : RawPoly ℕ := [node4Piece68Output_sector0_chunk0, node4Piece68Output_sector0_chunk1, node4Piece68Output_sector0_chunk2].flatten

def node4Piece68Output : SectorVector := [(0, node4Piece68Output_sector0)]
theorem node4Piece68_check : VectorCertificate (neutralBoundS JR (-2) node4Piece68Input) node4Piece68Output := by decide +kernel
theorem node4Piece68_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece68Input) = evaluate node4Piece68Output :=
  neutralBound_value JR _ _ _ node4Piece68_check

def node4Piece69Input_sector0 : RawPoly ℕ := [(288/5, [2, 3, 5, 5])]

def node4Piece69Input : SectorVector := [(0, node4Piece69Input_sector0)]
def node4Piece69Output_sector0_chunk0 : RawPoly ℕ := [(1152/5, [1, 1, 1, 2, 2, 3, 5, 5]), (6912, [1, 1, 2, 3, 5, 8]), (10368/5, [1, 1, 2, 5, 5, 6]), (6912/5, [1, 1, 3, 5, 5, 5]), (13824, [1, 2, 2, 3, 5, 7]), (20736/5, [1, 2, 2, 5, 5, 5]), (13824, [1, 2, 3, 3, 5, 6]), (101952/5, [1, 2, 3, 4, 5, 5]), (34560, [1, 2, 3, 14]), (41472, [1, 2, 5, 12]), (6912/5, [1, 3, 3, 3, 5, 5]), (27648, [1, 3, 5, 11]), (41472/5, [1, 5, 5, 9]), (6912, [2, 2, 2, 3, 5, 6]), (10368/5, [2, 2, 2, 4, 5, 5]), (87552/5, [2, 2, 3, 3, 5, 5]), (6912, [2, 2, 3, 4, 4, 5]), (34560, [2, 2, 3, 13]), (41472, [2, 2, 5, 11]), (6912, [2, 3, 3, 3, 4, 5]), (34560, [2, 3, 3, 12]), (34560, [2, 3, 4, 11]), (-55296, [2, 3, 5, 10]), (34560, [2, 3, 6, 9])]

def node4Piece69Output_sector0_chunk1 : RawPoly ℕ := [(34560, [2, 3, 7, 8]), (41472, [2, 4, 5, 9]), (122688/5, [2, 5, 5, 8]), (41472, [2, 5, 6, 7]), (103680, [2, 18]), (27648, [3, 3, 5, 9]), (27648, [3, 4, 5, 8]), (124416/5, [3, 5, 5, 7]), (13824, [3, 5, 6, 6]), (69120, [3, 17]), (41472/5, [4, 5, 5, 6]), (20736/5, [5, 5, 5, 5]), (82944, [5, 15])]

def node4Piece69Output_sector0 : RawPoly ℕ := [node4Piece69Output_sector0_chunk0, node4Piece69Output_sector0_chunk1].flatten

def node4Piece69Output : SectorVector := [(0, node4Piece69Output_sector0)]
theorem node4Piece69_check : VectorCertificate (neutralBoundS JR (-2) node4Piece69Input) node4Piece69Output := by decide +kernel
theorem node4Piece69_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece69Input) = evaluate node4Piece69Output :=
  neutralBound_value JR _ _ _ node4Piece69_check

def node4Piece70Input_sector0 : RawPoly ℕ := [(-132, [2, 4, 4, 5])]

def node4Piece70Input : SectorVector := [(0, node4Piece70Input_sector0)]
def node4Piece70Output_sector0_chunk0 : RawPoly ℕ := [(-528, [1, 1, 1, 2, 2, 4, 4, 5]), (-7920, [1, 1, 2, 4, 4, 8]), (-12672, [1, 1, 2, 4, 5, 7]), (-3168, [1, 1, 4, 4, 5, 5]), (-15840, [1, 2, 2, 4, 4, 7]), (-25344, [1, 2, 2, 4, 5, 6]), (-15840, [1, 2, 3, 4, 4, 6]), (-25344, [1, 2, 3, 4, 5, 5]), (-34056, [1, 2, 4, 4, 4, 5]), (-126720, [1, 2, 4, 13]), (-50688, [1, 2, 5, 12]), (-3168, [1, 3, 3, 4, 4, 5]), (-31680, [1, 4, 4, 11]), (-50688, [1, 4, 5, 10]), (-7920, [2, 2, 2, 4, 4, 6]), (-12672, [2, 2, 2, 4, 5, 5]), (-44880, [2, 2, 3, 4, 4, 5]), (-7920, [2, 2, 4, 4, 4, 4]), (-126720, [2, 2, 4, 12]), (-50688, [2, 2, 5, 11]), (-4224, [2, 3, 3, 3, 4, 5]), (-7920, [2, 3, 3, 4, 4, 4]), (-126720, [2, 3, 4, 11]), (-50688, [2, 3, 5, 10])]

def node4Piece70Output_sector0_chunk1 : RawPoly ℕ := [(23760, [2, 4, 4, 10]), (-10560, [2, 4, 5, 9]), (-126720, [2, 4, 6, 8]), (-63360, [2, 4, 7, 7]), (-50688, [2, 5, 5, 8]), (-50688, [2, 5, 6, 7]), (-253440, [2, 18]), (-31680, [3, 4, 4, 9]), (-50688, [3, 4, 5, 8]), (-31680, [4, 4, 4, 8]), (-57024, [4, 4, 5, 7]), (-15840, [4, 4, 6, 6]), (-50688, [4, 5, 5, 6]), (-253440, [4, 16]), (-101376, [5, 15])]

def node4Piece70Output_sector0 : RawPoly ℕ := [node4Piece70Output_sector0_chunk0, node4Piece70Output_sector0_chunk1].flatten

def node4Piece70Output : SectorVector := [(0, node4Piece70Output_sector0)]
theorem node4Piece70_check : VectorCertificate (neutralBoundS JR (-2) node4Piece70Input) node4Piece70Output := by decide +kernel
theorem node4Piece70_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece70Input) = evaluate node4Piece70Output :=
  neutralBound_value JR _ _ _ node4Piece70_check

def node4Piece71Input_sector0 : RawPoly ℕ := [(-960/13, [2, 13])]

def node4Piece71Input : SectorVector := [(0, node4Piece71Input_sector0)]
def node4Piece71Output_sector0_chunk0 : RawPoly ℕ := [(-3840/13, [1, 1, 1, 2, 2, 13]), (-11520, [1, 1, 2, 16]), (-23040/13, [1, 1, 5, 13]), (-23040, [1, 2, 2, 15]), (-23040, [1, 2, 3, 14]), (-339840/13, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-23040, [1, 2, 7, 10]), (-23040, [1, 2, 8, 9]), (-23040/13, [1, 3, 3, 13]), (-46080, [1, 19]), (-11520, [2, 2, 2, 14]), (-326400/13, [2, 2, 3, 13]), (-23040, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10]), (-23040, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8]), (-11520, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9]), (-23040, [2, 3, 7, 8])]

def node4Piece71Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (1102080, [2, 18]), (-46080, [3, 17]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-414720/13, [7, 13]), (-46080, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node4Piece71Output_sector0 : RawPoly ℕ := [node4Piece71Output_sector0_chunk0, node4Piece71Output_sector0_chunk1].flatten

def node4Piece71Output : SectorVector := [(0, node4Piece71Output_sector0)]
theorem node4Piece71_check : VectorCertificate (neutralBoundS JR (-2) node4Piece71Input) node4Piece71Output := by decide +kernel
theorem node4Piece71_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece71Input) = evaluate node4Piece71Output :=
  neutralBound_value JR _ _ _ node4Piece71_check

def node4Piece72Input_sector0 : RawPoly ℕ := [(640/9, [3, 3, 3, 6])]

def node4Piece72Input : SectorVector := [(0, node4Piece72Input_sector0)]
def node4Piece72Output_sector0_chunk0 : RawPoly ℕ := [(2560/9, [1, 1, 1, 2, 3, 3, 3, 6]), (5120, [1, 1, 3, 3, 3, 9]), (7680, [1, 1, 3, 3, 6, 6]), (10240, [1, 2, 3, 3, 3, 8]), (15360, [1, 2, 3, 3, 5, 6]), (10240, [1, 3, 3, 3, 3, 7]), (75520/3, [1, 3, 3, 3, 4, 6]), (5120, [1, 3, 3, 3, 5, 5]), (92160, [1, 3, 3, 13]), (46080, [1, 3, 6, 10]), (5120, [2, 2, 3, 3, 3, 7]), (7680, [2, 2, 3, 3, 4, 6]), (163840/9, [2, 3, 3, 3, 3, 6]), (10240, [2, 3, 3, 3, 4, 5]), (92160, [2, 3, 3, 12]), (46080, [2, 3, 6, 9]), (5120, [3, 3, 3, 3, 3, 5]), (5120, [3, 3, 3, 3, 4, 4]), (-179200/3, [3, 3, 3, 11]), (92160, [3, 3, 4, 10]), (92160, [3, 3, 5, 9]), (44800, [3, 3, 6, 8]), (46080, [3, 3, 7, 7]), (46080, [3, 4, 6, 7])]

def node4Piece72Output_sector0_chunk1 : RawPoly ℕ := [(46080, [3, 5, 6, 6]), (276480, [3, 17]), (46080, [6, 14])]

def node4Piece72Output_sector0 : RawPoly ℕ := [node4Piece72Output_sector0_chunk0, node4Piece72Output_sector0_chunk1].flatten

def node4Piece72Output : SectorVector := [(0, node4Piece72Output_sector0)]
theorem node4Piece72_check : VectorCertificate (neutralBoundS JR (-2) node4Piece72Input) node4Piece72Output := by decide +kernel
theorem node4Piece72_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece72Input) = evaluate node4Piece72Output :=
  neutralBound_value JR _ _ _ node4Piece72_check

def node4Piece73Input_sector0 : RawPoly ℕ := [(96, [3, 3, 4, 5])]

def node4Piece73Input : SectorVector := [(0, node4Piece73Input_sector0)]
def node4Piece73Output_sector0_chunk0 : RawPoly ℕ := [(384, [1, 1, 1, 2, 3, 3, 4, 5]), (5760, [1, 1, 3, 3, 4, 8]), (4608, [1, 1, 3, 3, 5, 7]), (6912, [1, 1, 3, 4, 5, 6]), (11520, [1, 2, 3, 3, 4, 7]), (9216, [1, 2, 3, 3, 5, 6]), (13824, [1, 2, 3, 4, 5, 5]), (11520, [1, 3, 3, 3, 4, 6]), (9216, [1, 3, 3, 3, 5, 5]), (29376, [1, 3, 3, 4, 4, 5]), (46080, [1, 3, 3, 13]), (69120, [1, 3, 4, 12]), (55296, [1, 3, 5, 11]), (20736, [1, 4, 5, 10]), (5760, [2, 2, 3, 3, 4, 6]), (4608, [2, 2, 3, 3, 5, 5]), (6912, [2, 2, 3, 4, 4, 5]), (28032, [2, 3, 3, 3, 4, 5]), (5760, [2, 3, 3, 4, 4, 4]), (46080, [2, 3, 3, 12]), (69120, [2, 3, 4, 11]), (55296, [2, 3, 5, 10]), (20736, [2, 4, 5, 9]), (1536, [3, 3, 3, 3, 3, 5])]

def node4Piece73Output_sector0_chunk1 : RawPoly ℕ := [(5760, [3, 3, 3, 3, 4, 4]), (46080, [3, 3, 3, 11]), (-17280, [3, 3, 4, 10]), (22272, [3, 3, 5, 9]), (46080, [3, 3, 6, 8]), (23040, [3, 3, 7, 7]), (69120, [3, 4, 4, 9]), (61056, [3, 4, 5, 8]), (69120, [3, 4, 6, 7]), (55296, [3, 5, 5, 7]), (27648, [3, 5, 6, 6]), (276480, [3, 17]), (20736, [4, 4, 5, 7]), (20736, [4, 5, 5, 6]), (103680, [4, 16]), (82944, [5, 15])]

def node4Piece73Output_sector0 : RawPoly ℕ := [node4Piece73Output_sector0_chunk0, node4Piece73Output_sector0_chunk1].flatten

def node4Piece73Output : SectorVector := [(0, node4Piece73Output_sector0)]
theorem node4Piece73_check : VectorCertificate (neutralBoundS JR (-2) node4Piece73Input) node4Piece73Output := by decide +kernel
theorem node4Piece73_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece73Input) = evaluate node4Piece73Output :=
  neutralBound_value JR _ _ _ node4Piece73_check

def node4Piece74Input_sector0 : RawPoly ℕ := [(-20, [3, 4, 4, 4])]

def node4Piece74Input : SectorVector := [(0, node4Piece74Input_sector0)]
def node4Piece74Output_sector0 : RawPoly ℕ := [(-80, [1, 1, 1, 2, 3, 4, 4, 4]), (-2880, [1, 1, 3, 4, 4, 7]), (-720, [1, 1, 4, 4, 4, 6]), (-5760, [1, 2, 3, 4, 4, 6]), (-1440, [1, 2, 4, 4, 4, 5]), (-5760, [1, 3, 3, 4, 4, 5]), (-4200, [1, 3, 4, 4, 4, 4]), (-23040, [1, 3, 4, 12]), (-17280, [1, 4, 4, 11]), (-2880, [2, 2, 3, 4, 4, 5]), (-720, [2, 2, 4, 4, 4, 4]), (-6560, [2, 3, 3, 4, 4, 4]), (-23040, [2, 3, 4, 11]), (-17280, [2, 4, 4, 10]), (-960, [3, 3, 3, 3, 4, 4]), (-23040, [3, 3, 4, 10]), (9120, [3, 4, 4, 9]), (-23040, [3, 4, 5, 8]), (-23040, [3, 4, 6, 7]), (-30720, [3, 17]), (-8520, [4, 4, 4, 8]), (-17280, [4, 4, 5, 7]), (-8640, [4, 4, 6, 6]), (-69120, [4, 16])]

def node4Piece74Output : SectorVector := [(0, node4Piece74Output_sector0)]
theorem node4Piece74_check : VectorCertificate (neutralBoundS JR (-2) node4Piece74Input) node4Piece74Output := by decide +kernel
theorem node4Piece74_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece74Input) = evaluate node4Piece74Output :=
  neutralBound_value JR _ _ _ node4Piece74_check

def node4Piece75Input_sector0 : RawPoly ℕ := [(80, [3, 12])]

def node4Piece75Input : SectorVector := [(0, node4Piece75Input_sector0)]
def node4Piece75Output_sector0_chunk0 : RawPoly ℕ := [(320, [1, 1, 1, 2, 3, 12]), (11520, [1, 1, 3, 15]), (2880, [1, 1, 6, 12]), (23040, [1, 2, 3, 14]), (5760, [1, 2, 5, 12]), (23040, [1, 3, 3, 13]), (28320, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (23040, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (69120, [1, 19]), (11520, [2, 2, 3, 13]), (2880, [2, 2, 4, 12]), (26240, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (23040, [2, 3, 5, 10]), (23040, [2, 3, 6, 9]), (23040, [2, 3, 7, 8]), (69120, [2, 18]), (11520, [3, 3, 3, 11]), (23040, [3, 3, 4, 10]), (23040, [3, 3, 5, 9]), (23040, [3, 3, 6, 8])]

def node4Piece75Output_sector0_chunk1 : RawPoly ℕ := [(11520, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (23040, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-935040, [3, 17]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14]), (69120, [7, 13]), (34080, [8, 12]), (69120, [9, 11]), (34560, [10, 10])]

def node4Piece75Output_sector0 : RawPoly ℕ := [node4Piece75Output_sector0_chunk0, node4Piece75Output_sector0_chunk1].flatten

def node4Piece75Output : SectorVector := [(0, node4Piece75Output_sector0)]
theorem node4Piece75_check : VectorCertificate (neutralBoundS JR (-2) node4Piece75Input) node4Piece75Output := by decide +kernel
theorem node4Piece75_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece75Input) = evaluate node4Piece75Output :=
  neutralBound_value JR _ _ _ node4Piece75_check

def node4Piece76Input_sector0 : RawPoly ℕ := [(-480/11, [4, 11])]

def node4Piece76Input : SectorVector := [(0, node4Piece76Input_sector0)]
def node4Piece76Output_sector0_chunk0 : RawPoly ℕ := [(-1920/11, [1, 1, 1, 2, 4, 11]), (-5760, [1, 1, 4, 14]), (-23040/11, [1, 1, 7, 11]), (-11520, [1, 2, 4, 13]), (-46080/11, [1, 2, 6, 11]), (-11520, [1, 3, 4, 12]), (-46080/11, [1, 3, 5, 11]), (-146880/11, [1, 4, 4, 11]), (-11520, [1, 4, 5, 10]), (-11520, [1, 4, 6, 9]), (-11520, [1, 4, 7, 8]), (-46080, [1, 19]), (-5760, [2, 2, 4, 12]), (-23040/11, [2, 2, 5, 11]), (-174720/11, [2, 3, 4, 11]), (-11520, [2, 4, 4, 10]), (-11520, [2, 4, 5, 9]), (-11520, [2, 4, 6, 8]), (-5760, [2, 4, 7, 7]), (-46080, [2, 18]), (-7680/11, [3, 3, 3, 11]), (-5760, [3, 3, 4, 10]), (-11520, [3, 4, 4, 9]), (-11520, [3, 4, 5, 8])]

def node4Piece76Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [3, 4, 6, 7]), (-46080, [3, 17]), (-5760, [4, 4, 4, 8]), (-11520, [4, 4, 5, 7]), (-5760, [4, 4, 6, 6]), (-5760, [4, 5, 5, 6]), (388800, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (-111360/11, [9, 11]), (-23040, [10, 10])]

def node4Piece76Output_sector0 : RawPoly ℕ := [node4Piece76Output_sector0_chunk0, node4Piece76Output_sector0_chunk1].flatten

def node4Piece76Output : SectorVector := [(0, node4Piece76Output_sector0)]
theorem node4Piece76_check : VectorCertificate (neutralBoundS JR (-2) node4Piece76Input) node4Piece76Output := by decide +kernel
theorem node4Piece76_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece76Input) = evaluate node4Piece76Output :=
  neutralBound_value JR _ _ _ node4Piece76_check

def node4Piece77Input_sector0 : RawPoly ℕ := [(48/5, [5, 10])]

def node4Piece77Input : SectorVector := [(0, node4Piece77Input_sector0)]
def node4Piece77Output_sector0_chunk0 : RawPoly ℕ := [(192/5, [1, 1, 1, 2, 5, 10]), (1152, [1, 1, 5, 13]), (576, [1, 1, 8, 10]), (2304, [1, 2, 5, 12]), (1152, [1, 2, 7, 10]), (2304, [1, 3, 5, 11]), (1152, [1, 3, 6, 10]), (16992/5, [1, 4, 5, 10]), (2304, [1, 5, 5, 9]), (2304, [1, 5, 6, 8]), (1152, [1, 5, 7, 7]), (11520, [1, 19]), (1152, [2, 2, 5, 11]), (576, [2, 2, 6, 10]), (17472/5, [2, 3, 5, 10]), (576, [2, 4, 4, 10]), (2304, [2, 4, 5, 9]), (2304, [2, 5, 5, 8]), (2304, [2, 5, 6, 7]), (11520, [2, 18]), (576, [3, 3, 4, 10]), (1152, [3, 3, 5, 9]), (2304, [3, 4, 5, 8]), (2304, [3, 5, 5, 7])]

def node4Piece77Output_sector0_chunk1 : RawPoly ℕ := [(1152, [3, 5, 6, 6]), (11520, [3, 17]), (1152, [4, 4, 5, 7]), (2304, [4, 5, 5, 6]), (11520, [4, 16]), (384, [5, 5, 5, 5]), (-62976, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (-7488, [10, 10])]

def node4Piece77Output_sector0 : RawPoly ℕ := [node4Piece77Output_sector0_chunk0, node4Piece77Output_sector0_chunk1].flatten

def node4Piece77Output : SectorVector := [(0, node4Piece77Output_sector0)]
theorem node4Piece77_check : VectorCertificate (neutralBoundS JR (-2) node4Piece77Input) node4Piece77Output := by decide +kernel
theorem node4Piece77_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-2)
    (evaluate node4Piece77Input) = evaluate node4Piece77Output :=
  neutralBound_value JR _ _ _ node4Piece77_check

def node4Pieces : List (SectorVector × SectorVector) := [(node4Piece0Input, node4Piece0Output), (node4Piece1Input, node4Piece1Output), (node4Piece2Input, node4Piece2Output), (node4Piece3Input, node4Piece3Output), (node4Piece4Input, node4Piece4Output), (node4Piece5Input, node4Piece5Output), (node4Piece6Input, node4Piece6Output), (node4Piece7Input, node4Piece7Output), (node4Piece8Input, node4Piece8Output), (node4Piece9Input, node4Piece9Output), (node4Piece10Input, node4Piece10Output), (node4Piece11Input, node4Piece11Output), (node4Piece12Input, node4Piece12Output), (node4Piece13Input, node4Piece13Output), (node4Piece14Input, node4Piece14Output), (node4Piece15Input, node4Piece15Output), (node4Piece16Input, node4Piece16Output), (node4Piece17Input, node4Piece17Output), (node4Piece18Input, node4Piece18Output), (node4Piece19Input, node4Piece19Output), (node4Piece20Input, node4Piece20Output), (node4Piece21Input, node4Piece21Output), (node4Piece22Input, node4Piece22Output), (node4Piece23Input, node4Piece23Output), (node4Piece24Input, node4Piece24Output), (node4Piece25Input, node4Piece25Output), (node4Piece26Input, node4Piece26Output), (node4Piece27Input, node4Piece27Output), (node4Piece28Input, node4Piece28Output), (node4Piece29Input, node4Piece29Output), (node4Piece30Input, node4Piece30Output), (node4Piece31Input, node4Piece31Output), (node4Piece32Input, node4Piece32Output), (node4Piece33Input, node4Piece33Output), (node4Piece34Input, node4Piece34Output), (node4Piece35Input, node4Piece35Output), (node4Piece36Input, node4Piece36Output), (node4Piece37Input, node4Piece37Output), (node4Piece38Input, node4Piece38Output), (node4Piece39Input, node4Piece39Output), (node4Piece40Input, node4Piece40Output), (node4Piece41Input, node4Piece41Output), (node4Piece42Input, node4Piece42Output), (node4Piece43Input, node4Piece43Output), (node4Piece44Input, node4Piece44Output), (node4Piece45Input, node4Piece45Output), (node4Piece46Input, node4Piece46Output), (node4Piece47Input, node4Piece47Output), (node4Piece48Input, node4Piece48Output), (node4Piece49Input, node4Piece49Output), (node4Piece50Input, node4Piece50Output), (node4Piece51Input, node4Piece51Output), (node4Piece52Input, node4Piece52Output), (node4Piece53Input, node4Piece53Output), (node4Piece54Input, node4Piece54Output), (node4Piece55Input, node4Piece55Output), (node4Piece56Input, node4Piece56Output), (node4Piece57Input, node4Piece57Output), (node4Piece58Input, node4Piece58Output), (node4Piece59Input, node4Piece59Output), (node4Piece60Input, node4Piece60Output), (node4Piece61Input, node4Piece61Output), (node4Piece62Input, node4Piece62Output), (node4Piece63Input, node4Piece63Output), (node4Piece64Input, node4Piece64Output), (node4Piece65Input, node4Piece65Output), (node4Piece66Input, node4Piece66Output), (node4Piece67Input, node4Piece67Output), (node4Piece68Input, node4Piece68Output), (node4Piece69Input, node4Piece69Output), (node4Piece70Input, node4Piece70Output), (node4Piece71Input, node4Piece71Output), (node4Piece72Input, node4Piece72Output), (node4Piece73Input, node4Piece73Output), (node4Piece74Input, node4Piece74Output), (node4Piece75Input, node4Piece75Output), (node4Piece76Input, node4Piece76Output), (node4Piece77Input, node4Piece77Output)]

theorem node4Pieces_input : VectorCertificate (node4Pieces.flatMap Prod.fst) node0 := by decide +kernel

theorem node4Pieces_each : ∀ p ∈ node4Pieces,
    (V2m 4 four_ge_one).smul (ls 4 JR) (-2) (evaluate p.1) = evaluate p.2 := by
  simp only [node4Pieces, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨node4Piece0_value, node4Piece1_value, node4Piece2_value, node4Piece3_value, node4Piece4_value, node4Piece5_value, node4Piece6_value, node4Piece7_value, node4Piece8_value, node4Piece9_value, node4Piece10_value, node4Piece11_value, node4Piece12_value, node4Piece13_value, node4Piece14_value, node4Piece15_value, node4Piece16_value, node4Piece17_value, node4Piece18_value, node4Piece19_value, node4Piece20_value, node4Piece21_value, node4Piece22_value, node4Piece23_value, node4Piece24_value, node4Piece25_value, node4Piece26_value, node4Piece27_value, node4Piece28_value, node4Piece29_value, node4Piece30_value, node4Piece31_value, node4Piece32_value, node4Piece33_value, node4Piece34_value, node4Piece35_value, node4Piece36_value, node4Piece37_value, node4Piece38_value, node4Piece39_value, node4Piece40_value, node4Piece41_value, node4Piece42_value, node4Piece43_value, node4Piece44_value, node4Piece45_value, node4Piece46_value, node4Piece47_value, node4Piece48_value, node4Piece49_value, node4Piece50_value, node4Piece51_value, node4Piece52_value, node4Piece53_value, node4Piece54_value, node4Piece55_value, node4Piece56_value, node4Piece57_value, node4Piece58_value, node4Piece59_value, node4Piece60_value, node4Piece61_value, node4Piece62_value, node4Piece63_value, node4Piece64_value, node4Piece65_value, node4Piece66_value, node4Piece67_value, node4Piece68_value, node4Piece69_value, node4Piece70_value, node4Piece71_value, node4Piece72_value, node4Piece73_value, node4Piece74_value, node4Piece75_value, node4Piece76_value, node4Piece77_value, by simp⟩
end VOA.Classification.COne.OrbC2h
