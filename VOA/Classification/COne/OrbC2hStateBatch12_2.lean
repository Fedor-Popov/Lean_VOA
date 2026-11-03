import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch12_0
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

def node12Piece32Input_sector0 : RawPoly ℕ := [(96, [1, 1, 2, 10])]

def node12Piece32Input : SectorVector := [(0, node12Piece32Input_sector0)]
def node12Piece32Output_sector0_chunk0 : RawPoly ℕ := [(384, [1, 1, 1, 1, 1, 2, 3, 10]), (576, [1, 1, 1, 1, 2, 2, 2, 10]), (11520, [1, 1, 1, 1, 2, 14]), (2304, [1, 1, 1, 1, 6, 10]), (23040, [1, 1, 1, 2, 2, 13]), (23040, [1, 1, 1, 2, 3, 12]), (23040, [1, 1, 1, 2, 4, 11]), (28800, [1, 1, 1, 2, 5, 10]), (23040, [1, 1, 1, 2, 6, 9]), (23040, [1, 1, 1, 2, 7, 8]), (4608, [1, 1, 1, 3, 4, 10]), (46080, [1, 1, 1, 17]), (11520, [1, 1, 2, 2, 2, 12]), (23040, [1, 1, 2, 2, 3, 11]), (30240, [1, 1, 2, 2, 4, 10]), (23040, [1, 1, 2, 2, 5, 9]), (23040, [1, 1, 2, 2, 6, 8]), (11520, [1, 1, 2, 2, 7, 7]), (16512, [1, 1, 2, 3, 3, 10]), (23040, [1, 1, 2, 3, 4, 9]), (23040, [1, 1, 2, 3, 5, 8]), (23040, [1, 1, 2, 3, 6, 7]), (11520, [1, 1, 2, 4, 4, 8]), (23040, [1, 1, 2, 4, 5, 7])]

def node12Piece32Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 1, 2, 4, 6, 6]), (11520, [1, 1, 2, 5, 5, 6]), (-711360, [1, 1, 2, 16]), (46080, [1, 1, 3, 15]), (46080, [1, 1, 4, 14]), (46080, [1, 1, 5, 13]), (46080, [1, 1, 6, 12]), (46080, [1, 1, 7, 11]), (32832, [1, 1, 8, 10]), (23040, [1, 1, 9, 9]), (2304, [1, 2, 2, 2, 3, 10]), (46080, [1, 2, 2, 15]), (46080, [1, 2, 3, 14]), (46080, [1, 2, 4, 13]), (46080, [1, 2, 5, 12]), (46080, [1, 2, 6, 11]), (43776, [1, 2, 7, 10]), (46080, [1, 2, 8, 9]), (9216, [1, 3, 6, 10]), (9216, [1, 4, 5, 10]), (92160, [1, 19]), (2304, [2, 2, 6, 10]), (2304, [2, 3, 5, 10]), (1152, [2, 4, 4, 10])]

def node12Piece32Output_sector0_chunk2 : RawPoly ℕ := [(23040, [2, 18]), (4608, [10, 10])]

def node12Piece32Output_sector0 : RawPoly ℕ := [node12Piece32Output_sector0_chunk0, node12Piece32Output_sector0_chunk1, node12Piece32Output_sector0_chunk2].flatten

def node12Piece32Output : SectorVector := [(0, node12Piece32Output_sector0)]

def node12Piece32UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 2, 10])]

def node12Piece32UnitInput_sector0 : RawPoly ℕ := [node12Piece32UnitInput_sector0_chunk0].flatten

def node12Piece32UnitInput : SectorVector := [(0, node12Piece32UnitInput_sector0)]

def node12Piece32UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 2, 3, 10]), (6, [1, 1, 1, 1, 2, 2, 2, 10]), (120, [1, 1, 1, 1, 2, 14]), (24, [1, 1, 1, 1, 6, 10]), (240, [1, 1, 1, 2, 2, 13]), (240, [1, 1, 1, 2, 3, 12]), (240, [1, 1, 1, 2, 4, 11]), (300, [1, 1, 1, 2, 5, 10]), (240, [1, 1, 1, 2, 6, 9]), (240, [1, 1, 1, 2, 7, 8]), (48, [1, 1, 1, 3, 4, 10]), (480, [1, 1, 1, 17]), (120, [1, 1, 2, 2, 2, 12]), (240, [1, 1, 2, 2, 3, 11]), (315, [1, 1, 2, 2, 4, 10]), (240, [1, 1, 2, 2, 5, 9]), (240, [1, 1, 2, 2, 6, 8]), (120, [1, 1, 2, 2, 7, 7]), (172, [1, 1, 2, 3, 3, 10]), (240, [1, 1, 2, 3, 4, 9]), (240, [1, 1, 2, 3, 5, 8]), (240, [1, 1, 2, 3, 6, 7]), (120, [1, 1, 2, 4, 4, 8]), (240, [1, 1, 2, 4, 5, 7])]

def node12Piece32UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [1, 1, 2, 4, 6, 6]), (120, [1, 1, 2, 5, 5, 6]), (-7410, [1, 1, 2, 16]), (480, [1, 1, 3, 15]), (480, [1, 1, 4, 14]), (480, [1, 1, 5, 13]), (480, [1, 1, 6, 12]), (480, [1, 1, 7, 11]), (342, [1, 1, 8, 10]), (240, [1, 1, 9, 9]), (24, [1, 2, 2, 2, 3, 10]), (480, [1, 2, 2, 15]), (480, [1, 2, 3, 14]), (480, [1, 2, 4, 13]), (480, [1, 2, 5, 12]), (480, [1, 2, 6, 11]), (456, [1, 2, 7, 10]), (480, [1, 2, 8, 9]), (96, [1, 3, 6, 10]), (96, [1, 4, 5, 10]), (960, [1, 19]), (24, [2, 2, 6, 10]), (24, [2, 3, 5, 10]), (12, [2, 4, 4, 10])]

def node12Piece32UnitOutput_sector0_chunk2 : RawPoly ℕ := [(240, [2, 18]), (48, [10, 10])]

def node12Piece32UnitOutput_sector0 : RawPoly ℕ := [node12Piece32UnitOutput_sector0_chunk0, node12Piece32UnitOutput_sector0_chunk1, node12Piece32UnitOutput_sector0_chunk2].flatten

def node12Piece32UnitOutput : SectorVector := [(0, node12Piece32UnitOutput_sector0)]

theorem node12Piece32_check : VectorCertificate (neutralBoundS JR (-3) node12Piece32UnitInput) node12Piece32UnitOutput := by decide +kernel

theorem node12Piece32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece32Input) = evaluate node12Piece32Output :=
  mode_of_scaled _ _ (96) node12Piece32UnitInput node12Piece32UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece32_check)

def node12Piece33Input_sector0 : RawPoly ℕ := [(640/9, [1, 1, 3, 3, 3, 3])]

def node12Piece33Input : SectorVector := [(0, node12Piece33Input_sector0)]
def node12Piece33Output_sector0_chunk0 : RawPoly ℕ := [(2560/9, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (1280/3, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (10240, [1, 1, 1, 1, 3, 3, 3, 7]), (20480, [1, 1, 1, 2, 3, 3, 3, 6]), (64000/3, [1, 1, 1, 3, 3, 3, 3, 5]), (10240, [1, 1, 1, 3, 3, 3, 4, 4]), (92160, [1, 1, 1, 3, 3, 11]), (10240, [1, 1, 2, 2, 3, 3, 3, 5]), (72320/3, [1, 1, 2, 3, 3, 3, 3, 4]), (92160, [1, 1, 2, 3, 3, 10]), (48640/9, [1, 1, 3, 3, 3, 3, 3, 3]), (-40960/3, [1, 1, 3, 3, 3, 9]), (92160, [1, 1, 3, 3, 4, 8]), (92160, [1, 1, 3, 3, 5, 7]), (46080, [1, 1, 3, 3, 6, 6]), (184320, [1, 1, 3, 15]), (5120/3, [1, 2, 2, 3, 3, 3, 3, 3]), (40960, [1, 2, 3, 3, 3, 8]), (97280/3, [1, 3, 3, 3, 3, 7]), (40960, [1, 3, 3, 3, 4, 6]), (20480, [1, 3, 3, 3, 5, 5]), (184320, [1, 3, 3, 13]), (5120/3, [2, 3, 3, 3, 3, 6]), (5120/3, [3, 3, 3, 3, 3, 5])]

def node12Piece33Output_sector0_chunk1 : RawPoly ℕ := [(2560/3, [3, 3, 3, 3, 4, 4]), (20480, [3, 3, 3, 11])]

def node12Piece33Output_sector0 : RawPoly ℕ := [node12Piece33Output_sector0_chunk0, node12Piece33Output_sector0_chunk1].flatten

def node12Piece33Output : SectorVector := [(0, node12Piece33Output_sector0)]

def node12Piece33UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 3, 3, 3, 3])]

def node12Piece33UnitInput_sector0 : RawPoly ℕ := [node12Piece33UnitInput_sector0_chunk0].flatten

def node12Piece33UnitInput : SectorVector := [(0, node12Piece33UnitInput_sector0)]

def node12Piece33UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 3, 3, 3, 3, 3]), (6, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (144, [1, 1, 1, 1, 3, 3, 3, 7]), (288, [1, 1, 1, 2, 3, 3, 3, 6]), (300, [1, 1, 1, 3, 3, 3, 3, 5]), (144, [1, 1, 1, 3, 3, 3, 4, 4]), (1296, [1, 1, 1, 3, 3, 11]), (144, [1, 1, 2, 2, 3, 3, 3, 5]), (339, [1, 1, 2, 3, 3, 3, 3, 4]), (1296, [1, 1, 2, 3, 3, 10]), (76, [1, 1, 3, 3, 3, 3, 3, 3]), (-192, [1, 1, 3, 3, 3, 9]), (1296, [1, 1, 3, 3, 4, 8]), (1296, [1, 1, 3, 3, 5, 7]), (648, [1, 1, 3, 3, 6, 6]), (2592, [1, 1, 3, 15]), (24, [1, 2, 2, 3, 3, 3, 3, 3]), (576, [1, 2, 3, 3, 3, 8]), (456, [1, 3, 3, 3, 3, 7]), (576, [1, 3, 3, 3, 4, 6]), (288, [1, 3, 3, 3, 5, 5]), (2592, [1, 3, 3, 13]), (24, [2, 3, 3, 3, 3, 6]), (24, [3, 3, 3, 3, 3, 5])]

def node12Piece33UnitOutput_sector0_chunk1 : RawPoly ℕ := [(12, [3, 3, 3, 3, 4, 4]), (288, [3, 3, 3, 11])]

def node12Piece33UnitOutput_sector0 : RawPoly ℕ := [node12Piece33UnitOutput_sector0_chunk0, node12Piece33UnitOutput_sector0_chunk1].flatten

def node12Piece33UnitOutput : SectorVector := [(0, node12Piece33UnitOutput_sector0)]

theorem node12Piece33_check : VectorCertificate (neutralBoundS JR (-3) node12Piece33UnitInput) node12Piece33UnitOutput := by decide +kernel

theorem node12Piece33_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece33Input) = evaluate node12Piece33Output :=
  mode_of_scaled _ _ (640/9) node12Piece33UnitInput node12Piece33UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece33_check)

def node12Piece34Input_sector0 : RawPoly ℕ := [(160, [1, 1, 3, 9])]

def node12Piece34Input : SectorVector := [(0, node12Piece34Input_sector0)]
def node12Piece34Output_sector0_chunk0 : RawPoly ℕ := [(640, [1, 1, 1, 1, 1, 3, 3, 9]), (960, [1, 1, 1, 1, 2, 2, 3, 9]), (17280, [1, 1, 1, 1, 3, 13]), (5760, [1, 1, 1, 1, 7, 9]), (34560, [1, 1, 1, 2, 3, 12]), (11520, [1, 1, 1, 2, 6, 9]), (34560, [1, 1, 1, 3, 3, 11]), (34560, [1, 1, 1, 3, 4, 10]), (48000, [1, 1, 1, 3, 5, 9]), (34560, [1, 1, 1, 3, 6, 8]), (17280, [1, 1, 1, 3, 7, 7]), (5760, [1, 1, 1, 4, 4, 9]), (103680, [1, 1, 1, 17]), (17280, [1, 1, 2, 2, 3, 11]), (5760, [1, 1, 2, 2, 5, 9]), (34560, [1, 1, 2, 3, 3, 10]), (54240, [1, 1, 2, 3, 4, 9]), (34560, [1, 1, 2, 3, 5, 8]), (34560, [1, 1, 2, 3, 6, 7]), (103680, [1, 1, 2, 16]), (23680, [1, 1, 3, 3, 3, 9]), (34560, [1, 1, 3, 3, 4, 8]), (34560, [1, 1, 3, 3, 5, 7]), (17280, [1, 1, 3, 3, 6, 6])]

def node12Piece34Output_sector0_chunk1 : RawPoly ℕ := [(17280, [1, 1, 3, 4, 4, 7]), (34560, [1, 1, 3, 4, 5, 6]), (5760, [1, 1, 3, 5, 5, 5]), (-852480, [1, 1, 3, 15]), (103680, [1, 1, 4, 14]), (103680, [1, 1, 5, 13]), (103680, [1, 1, 6, 12]), (103680, [1, 1, 7, 11]), (103680, [1, 1, 8, 10]), (-7680, [1, 1, 9, 9]), (3840, [1, 2, 2, 3, 3, 9]), (69120, [1, 2, 3, 14]), (23040, [1, 2, 8, 9]), (69120, [1, 3, 3, 13]), (69120, [1, 3, 4, 12]), (69120, [1, 3, 5, 11]), (69120, [1, 3, 6, 10]), (72960, [1, 3, 7, 9]), (34560, [1, 3, 8, 8]), (23040, [1, 4, 6, 9]), (11520, [1, 5, 5, 9]), (207360, [1, 19]), (3840, [2, 3, 6, 9]), (3840, [3, 3, 5, 9])]

def node12Piece34Output_sector0_chunk2 : RawPoly ℕ := [(1920, [3, 4, 4, 9]), (34560, [3, 17]), (11520, [9, 11])]

def node12Piece34Output_sector0 : RawPoly ℕ := [node12Piece34Output_sector0_chunk0, node12Piece34Output_sector0_chunk1, node12Piece34Output_sector0_chunk2].flatten

def node12Piece34Output : SectorVector := [(0, node12Piece34Output_sector0)]

def node12Piece34UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 3, 9])]

def node12Piece34UnitInput_sector0 : RawPoly ℕ := [node12Piece34UnitInput_sector0_chunk0].flatten

def node12Piece34UnitInput : SectorVector := [(0, node12Piece34UnitInput_sector0)]

def node12Piece34UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 3, 3, 9]), (6, [1, 1, 1, 1, 2, 2, 3, 9]), (108, [1, 1, 1, 1, 3, 13]), (36, [1, 1, 1, 1, 7, 9]), (216, [1, 1, 1, 2, 3, 12]), (72, [1, 1, 1, 2, 6, 9]), (216, [1, 1, 1, 3, 3, 11]), (216, [1, 1, 1, 3, 4, 10]), (300, [1, 1, 1, 3, 5, 9]), (216, [1, 1, 1, 3, 6, 8]), (108, [1, 1, 1, 3, 7, 7]), (36, [1, 1, 1, 4, 4, 9]), (648, [1, 1, 1, 17]), (108, [1, 1, 2, 2, 3, 11]), (36, [1, 1, 2, 2, 5, 9]), (216, [1, 1, 2, 3, 3, 10]), (339, [1, 1, 2, 3, 4, 9]), (216, [1, 1, 2, 3, 5, 8]), (216, [1, 1, 2, 3, 6, 7]), (648, [1, 1, 2, 16]), (148, [1, 1, 3, 3, 3, 9]), (216, [1, 1, 3, 3, 4, 8]), (216, [1, 1, 3, 3, 5, 7]), (108, [1, 1, 3, 3, 6, 6])]

def node12Piece34UnitOutput_sector0_chunk1 : RawPoly ℕ := [(108, [1, 1, 3, 4, 4, 7]), (216, [1, 1, 3, 4, 5, 6]), (36, [1, 1, 3, 5, 5, 5]), (-5328, [1, 1, 3, 15]), (648, [1, 1, 4, 14]), (648, [1, 1, 5, 13]), (648, [1, 1, 6, 12]), (648, [1, 1, 7, 11]), (648, [1, 1, 8, 10]), (-48, [1, 1, 9, 9]), (24, [1, 2, 2, 3, 3, 9]), (432, [1, 2, 3, 14]), (144, [1, 2, 8, 9]), (432, [1, 3, 3, 13]), (432, [1, 3, 4, 12]), (432, [1, 3, 5, 11]), (432, [1, 3, 6, 10]), (456, [1, 3, 7, 9]), (216, [1, 3, 8, 8]), (144, [1, 4, 6, 9]), (72, [1, 5, 5, 9]), (1296, [1, 19]), (24, [2, 3, 6, 9]), (24, [3, 3, 5, 9])]

def node12Piece34UnitOutput_sector0_chunk2 : RawPoly ℕ := [(12, [3, 4, 4, 9]), (216, [3, 17]), (72, [9, 11])]

def node12Piece34UnitOutput_sector0 : RawPoly ℕ := [node12Piece34UnitOutput_sector0_chunk0, node12Piece34UnitOutput_sector0_chunk1, node12Piece34UnitOutput_sector0_chunk2].flatten

def node12Piece34UnitOutput : SectorVector := [(0, node12Piece34UnitOutput_sector0)]

theorem node12Piece34_check : VectorCertificate (neutralBoundS JR (-3) node12Piece34UnitInput) node12Piece34UnitOutput := by decide +kernel

theorem node12Piece34_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece34Input) = evaluate node12Piece34Output :=
  mode_of_scaled _ _ (160) node12Piece34UnitInput node12Piece34UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece34_check)

def node12Piece35Input_sector0 : RawPoly ℕ := [(-180, [1, 1, 4, 8])]

def node12Piece35Input : SectorVector := [(0, node12Piece35Input_sector0)]
def node12Piece35Output_sector0_chunk0 : RawPoly ℕ := [(-720, [1, 1, 1, 1, 1, 3, 4, 8]), (-1080, [1, 1, 1, 1, 2, 2, 4, 8]), (-17280, [1, 1, 1, 1, 4, 12]), (-8640, [1, 1, 1, 1, 8, 8]), (-34560, [1, 1, 1, 2, 4, 11]), (-17280, [1, 1, 1, 2, 7, 8]), (-34560, [1, 1, 1, 3, 4, 10]), (-17280, [1, 1, 1, 3, 6, 8]), (-34560, [1, 1, 1, 4, 4, 9]), (-54000, [1, 1, 1, 4, 5, 8]), (-34560, [1, 1, 1, 4, 6, 7]), (-138240, [1, 1, 1, 17]), (-17280, [1, 1, 2, 2, 4, 10]), (-8640, [1, 1, 2, 2, 6, 8]), (-34560, [1, 1, 2, 3, 4, 9]), (-17280, [1, 1, 2, 3, 5, 8]), (-52380, [1, 1, 2, 4, 4, 8]), (-34560, [1, 1, 2, 4, 5, 7]), (-17280, [1, 1, 2, 4, 6, 6]), (-138240, [1, 1, 2, 16]), (-30960, [1, 1, 3, 3, 4, 8]), (-34560, [1, 1, 3, 4, 4, 7]), (-34560, [1, 1, 3, 4, 5, 6]), (-138240, [1, 1, 3, 15])]

def node12Piece35Output_sector0_chunk1 : RawPoly ℕ := [(-17280, [1, 1, 4, 4, 4, 6]), (-17280, [1, 1, 4, 4, 5, 5]), (652320, [1, 1, 4, 14]), (-138240, [1, 1, 5, 13]), (-138240, [1, 1, 6, 12]), (-138240, [1, 1, 7, 11]), (-2160, [1, 1, 8, 10]), (-69120, [1, 1, 9, 9]), (-4320, [1, 2, 2, 3, 4, 8]), (-69120, [1, 2, 4, 13]), (-34560, [1, 2, 8, 9]), (-69120, [1, 3, 4, 12]), (-34560, [1, 3, 8, 8]), (-69120, [1, 4, 4, 11]), (-69120, [1, 4, 5, 10]), (-69120, [1, 4, 6, 9]), (-82080, [1, 4, 7, 8]), (-34560, [1, 5, 6, 8]), (-276480, [1, 19]), (-4320, [2, 4, 6, 8]), (-4320, [3, 4, 5, 8]), (-2160, [4, 4, 4, 8]), (-34560, [4, 16]), (-17280, [8, 12])]

def node12Piece35Output_sector0 : RawPoly ℕ := [node12Piece35Output_sector0_chunk0, node12Piece35Output_sector0_chunk1].flatten

def node12Piece35Output : SectorVector := [(0, node12Piece35Output_sector0)]

def node12Piece35UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 4, 8])]

def node12Piece35UnitInput_sector0 : RawPoly ℕ := [node12Piece35UnitInput_sector0_chunk0].flatten

def node12Piece35UnitInput : SectorVector := [(0, node12Piece35UnitInput_sector0)]

def node12Piece35UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 3, 4, 8]), (6, [1, 1, 1, 1, 2, 2, 4, 8]), (96, [1, 1, 1, 1, 4, 12]), (48, [1, 1, 1, 1, 8, 8]), (192, [1, 1, 1, 2, 4, 11]), (96, [1, 1, 1, 2, 7, 8]), (192, [1, 1, 1, 3, 4, 10]), (96, [1, 1, 1, 3, 6, 8]), (192, [1, 1, 1, 4, 4, 9]), (300, [1, 1, 1, 4, 5, 8]), (192, [1, 1, 1, 4, 6, 7]), (768, [1, 1, 1, 17]), (96, [1, 1, 2, 2, 4, 10]), (48, [1, 1, 2, 2, 6, 8]), (192, [1, 1, 2, 3, 4, 9]), (96, [1, 1, 2, 3, 5, 8]), (291, [1, 1, 2, 4, 4, 8]), (192, [1, 1, 2, 4, 5, 7]), (96, [1, 1, 2, 4, 6, 6]), (768, [1, 1, 2, 16]), (172, [1, 1, 3, 3, 4, 8]), (192, [1, 1, 3, 4, 4, 7]), (192, [1, 1, 3, 4, 5, 6]), (768, [1, 1, 3, 15])]

def node12Piece35UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [1, 1, 4, 4, 4, 6]), (96, [1, 1, 4, 4, 5, 5]), (-3624, [1, 1, 4, 14]), (768, [1, 1, 5, 13]), (768, [1, 1, 6, 12]), (768, [1, 1, 7, 11]), (12, [1, 1, 8, 10]), (384, [1, 1, 9, 9]), (24, [1, 2, 2, 3, 4, 8]), (384, [1, 2, 4, 13]), (192, [1, 2, 8, 9]), (384, [1, 3, 4, 12]), (192, [1, 3, 8, 8]), (384, [1, 4, 4, 11]), (384, [1, 4, 5, 10]), (384, [1, 4, 6, 9]), (456, [1, 4, 7, 8]), (192, [1, 5, 6, 8]), (1536, [1, 19]), (24, [2, 4, 6, 8]), (24, [3, 4, 5, 8]), (12, [4, 4, 4, 8]), (192, [4, 16]), (96, [8, 12])]

def node12Piece35UnitOutput_sector0 : RawPoly ℕ := [node12Piece35UnitOutput_sector0_chunk0, node12Piece35UnitOutput_sector0_chunk1].flatten

def node12Piece35UnitOutput : SectorVector := [(0, node12Piece35UnitOutput_sector0)]

theorem node12Piece35_check : VectorCertificate (neutralBoundS JR (-3) node12Piece35UnitInput) node12Piece35UnitOutput := by decide +kernel

theorem node12Piece35_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece35Input) = evaluate node12Piece35Output :=
  mode_of_scaled _ _ (-180) node12Piece35UnitInput node12Piece35UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece35_check)

def node12Piece36Input_sector0 : RawPoly ℕ := [(384/7, [1, 1, 5, 7])]

def node12Piece36Input : SectorVector := [(0, node12Piece36Input_sector0)]
def node12Piece36Output_sector0_chunk0 : RawPoly ℕ := [(1536/7, [1, 1, 1, 1, 1, 3, 5, 7]), (2304/7, [1, 1, 1, 1, 2, 2, 5, 7]), (4608, [1, 1, 1, 1, 5, 11]), (23040/7, [1, 1, 1, 1, 7, 9]), (9216, [1, 1, 1, 2, 5, 10]), (46080/7, [1, 1, 1, 2, 7, 8]), (9216, [1, 1, 1, 3, 5, 9]), (46080/7, [1, 1, 1, 3, 7, 7]), (9216, [1, 1, 1, 4, 5, 8]), (46080/7, [1, 1, 1, 4, 6, 7]), (92160/7, [1, 1, 1, 5, 5, 7]), (4608, [1, 1, 1, 5, 6, 6]), (46080, [1, 1, 1, 17]), (4608, [1, 1, 2, 2, 5, 9]), (23040/7, [1, 1, 2, 2, 7, 7]), (9216, [1, 1, 2, 3, 5, 8]), (46080/7, [1, 1, 2, 3, 6, 7]), (130176/7, [1, 1, 2, 4, 5, 7]), (9216, [1, 1, 2, 5, 5, 6]), (46080, [1, 1, 2, 16]), (66048/7, [1, 1, 3, 3, 5, 7]), (23040/7, [1, 1, 3, 4, 4, 7]), (9216, [1, 1, 3, 4, 5, 6]), (4608, [1, 1, 3, 5, 5, 5])]

def node12Piece36Output_sector0_chunk1 : RawPoly ℕ := [(46080, [1, 1, 3, 15]), (4608, [1, 1, 4, 4, 5, 5]), (46080, [1, 1, 4, 14]), (-124416, [1, 1, 5, 13]), (46080, [1, 1, 6, 12]), (-184320/7, [1, 1, 7, 11]), (46080, [1, 1, 8, 10]), (23040, [1, 1, 9, 9]), (9216/7, [1, 2, 2, 3, 5, 7]), (18432, [1, 2, 5, 12]), (92160/7, [1, 2, 7, 10]), (18432, [1, 3, 5, 11]), (92160/7, [1, 3, 7, 9]), (18432, [1, 4, 5, 10]), (92160/7, [1, 4, 7, 8]), (18432, [1, 5, 5, 9]), (18432, [1, 5, 6, 8]), (110592/7, [1, 5, 7, 7]), (46080/7, [1, 6, 6, 7]), (92160, [1, 19]), (9216/7, [2, 5, 6, 7]), (9216/7, [3, 5, 5, 7]), (4608/7, [4, 4, 5, 7]), (9216, [5, 15])]

def node12Piece36Output_sector0_chunk2 : RawPoly ℕ := [(46080/7, [7, 13])]

def node12Piece36Output_sector0 : RawPoly ℕ := [node12Piece36Output_sector0_chunk0, node12Piece36Output_sector0_chunk1, node12Piece36Output_sector0_chunk2].flatten

def node12Piece36Output : SectorVector := [(0, node12Piece36Output_sector0)]

def node12Piece36UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 5, 7])]

def node12Piece36UnitInput_sector0 : RawPoly ℕ := [node12Piece36UnitInput_sector0_chunk0].flatten

def node12Piece36UnitInput : SectorVector := [(0, node12Piece36UnitInput_sector0)]

def node12Piece36UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 1, 3, 5, 7]), (6, [1, 1, 1, 1, 2, 2, 5, 7]), (84, [1, 1, 1, 1, 5, 11]), (60, [1, 1, 1, 1, 7, 9]), (168, [1, 1, 1, 2, 5, 10]), (120, [1, 1, 1, 2, 7, 8]), (168, [1, 1, 1, 3, 5, 9]), (120, [1, 1, 1, 3, 7, 7]), (168, [1, 1, 1, 4, 5, 8]), (120, [1, 1, 1, 4, 6, 7]), (240, [1, 1, 1, 5, 5, 7]), (84, [1, 1, 1, 5, 6, 6]), (840, [1, 1, 1, 17]), (84, [1, 1, 2, 2, 5, 9]), (60, [1, 1, 2, 2, 7, 7]), (168, [1, 1, 2, 3, 5, 8]), (120, [1, 1, 2, 3, 6, 7]), (339, [1, 1, 2, 4, 5, 7]), (168, [1, 1, 2, 5, 5, 6]), (840, [1, 1, 2, 16]), (172, [1, 1, 3, 3, 5, 7]), (60, [1, 1, 3, 4, 4, 7]), (168, [1, 1, 3, 4, 5, 6]), (84, [1, 1, 3, 5, 5, 5])]

def node12Piece36UnitOutput_sector0_chunk1 : RawPoly ℕ := [(840, [1, 1, 3, 15]), (84, [1, 1, 4, 4, 5, 5]), (840, [1, 1, 4, 14]), (-2268, [1, 1, 5, 13]), (840, [1, 1, 6, 12]), (-480, [1, 1, 7, 11]), (840, [1, 1, 8, 10]), (420, [1, 1, 9, 9]), (24, [1, 2, 2, 3, 5, 7]), (336, [1, 2, 5, 12]), (240, [1, 2, 7, 10]), (336, [1, 3, 5, 11]), (240, [1, 3, 7, 9]), (336, [1, 4, 5, 10]), (240, [1, 4, 7, 8]), (336, [1, 5, 5, 9]), (336, [1, 5, 6, 8]), (288, [1, 5, 7, 7]), (120, [1, 6, 6, 7]), (1680, [1, 19]), (24, [2, 5, 6, 7]), (24, [3, 5, 5, 7]), (12, [4, 4, 5, 7]), (168, [5, 15])]

def node12Piece36UnitOutput_sector0_chunk2 : RawPoly ℕ := [(120, [7, 13])]

def node12Piece36UnitOutput_sector0 : RawPoly ℕ := [node12Piece36UnitOutput_sector0_chunk0, node12Piece36UnitOutput_sector0_chunk1, node12Piece36UnitOutput_sector0_chunk2].flatten

def node12Piece36UnitOutput : SectorVector := [(0, node12Piece36UnitOutput_sector0)]

theorem node12Piece36_check : VectorCertificate (neutralBoundS JR (-3) node12Piece36UnitInput) node12Piece36UnitOutput := by decide +kernel

theorem node12Piece36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece36Input) = evaluate node12Piece36Output :=
  mode_of_scaled _ _ (384/7) node12Piece36UnitInput node12Piece36UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece36_check)

def node12Piece37Input_sector0 : RawPoly ℕ := [(-200, [1, 2, 2, 2, 2, 5])]

def node12Piece37Input : SectorVector := [(0, node12Piece37Input_sector0)]
def node12Piece37Output_sector0_chunk0 : RawPoly ℕ := [(-800, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (-1200, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (-12000, [1, 1, 1, 2, 2, 2, 2, 9]), (-19200, [1, 1, 1, 2, 2, 2, 5, 6]), (-24000, [1, 1, 2, 2, 2, 2, 2, 8]), (-24000, [1, 1, 2, 2, 2, 2, 3, 7]), (-24000, [1, 1, 2, 2, 2, 2, 4, 6]), (-50400, [1, 1, 2, 2, 2, 2, 5, 5]), (-38400, [1, 1, 2, 2, 2, 3, 4, 5]), (-192000, [1, 1, 2, 2, 2, 12]), (-115200, [1, 1, 2, 2, 5, 9]), (-12000, [1, 2, 2, 2, 2, 2, 2, 7]), (-24000, [1, 2, 2, 2, 2, 2, 3, 6]), (-48600, [1, 2, 2, 2, 2, 2, 4, 5]), (-34400, [1, 2, 2, 2, 2, 3, 3, 5]), (-12000, [1, 2, 2, 2, 2, 3, 4, 4]), (96000, [1, 2, 2, 2, 2, 11]), (-192000, [1, 2, 2, 2, 3, 10]), (-192000, [1, 2, 2, 2, 4, 9]), (-158400, [1, 2, 2, 2, 5, 8]), (-192000, [1, 2, 2, 2, 6, 7]), (-115200, [1, 2, 2, 3, 5, 7]), (-115200, [1, 2, 2, 4, 5, 6]), (-57600, [1, 2, 2, 5, 5, 5])]

def node12Piece37Output_sector0_chunk1 : RawPoly ℕ := [(-576000, [1, 2, 2, 15]), (-153600, [1, 2, 5, 12]), (-2400, [2, 2, 2, 2, 2, 2, 3, 5]), (-24000, [2, 2, 2, 2, 2, 10]), (-24000, [2, 2, 2, 2, 3, 9]), (-24000, [2, 2, 2, 2, 4, 8]), (-48000, [2, 2, 2, 2, 5, 7]), (-12000, [2, 2, 2, 2, 6, 6]), (-38400, [2, 2, 2, 3, 5, 6]), (-38400, [2, 2, 2, 4, 5, 5]), (-192000, [2, 2, 2, 14]), (-115200, [2, 2, 5, 11])]

def node12Piece37Output_sector0 : RawPoly ℕ := [node12Piece37Output_sector0_chunk0, node12Piece37Output_sector0_chunk1].flatten

def node12Piece37Output : SectorVector := [(0, node12Piece37Output_sector0)]

def node12Piece37UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 2, 5])]

def node12Piece37UnitInput_sector0 : RawPoly ℕ := [node12Piece37UnitInput_sector0_chunk0].flatten

def node12Piece37UnitInput : SectorVector := [(0, node12Piece37UnitInput_sector0)]

def node12Piece37UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (6, [1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (60, [1, 1, 1, 2, 2, 2, 2, 9]), (96, [1, 1, 1, 2, 2, 2, 5, 6]), (120, [1, 1, 2, 2, 2, 2, 2, 8]), (120, [1, 1, 2, 2, 2, 2, 3, 7]), (120, [1, 1, 2, 2, 2, 2, 4, 6]), (252, [1, 1, 2, 2, 2, 2, 5, 5]), (192, [1, 1, 2, 2, 2, 3, 4, 5]), (960, [1, 1, 2, 2, 2, 12]), (576, [1, 1, 2, 2, 5, 9]), (60, [1, 2, 2, 2, 2, 2, 2, 7]), (120, [1, 2, 2, 2, 2, 2, 3, 6]), (243, [1, 2, 2, 2, 2, 2, 4, 5]), (172, [1, 2, 2, 2, 2, 3, 3, 5]), (60, [1, 2, 2, 2, 2, 3, 4, 4]), (-480, [1, 2, 2, 2, 2, 11]), (960, [1, 2, 2, 2, 3, 10]), (960, [1, 2, 2, 2, 4, 9]), (792, [1, 2, 2, 2, 5, 8]), (960, [1, 2, 2, 2, 6, 7]), (576, [1, 2, 2, 3, 5, 7]), (576, [1, 2, 2, 4, 5, 6]), (288, [1, 2, 2, 5, 5, 5])]

def node12Piece37UnitOutput_sector0_chunk1 : RawPoly ℕ := [(2880, [1, 2, 2, 15]), (768, [1, 2, 5, 12]), (12, [2, 2, 2, 2, 2, 2, 3, 5]), (120, [2, 2, 2, 2, 2, 10]), (120, [2, 2, 2, 2, 3, 9]), (120, [2, 2, 2, 2, 4, 8]), (240, [2, 2, 2, 2, 5, 7]), (60, [2, 2, 2, 2, 6, 6]), (192, [2, 2, 2, 3, 5, 6]), (192, [2, 2, 2, 4, 5, 5]), (960, [2, 2, 2, 14]), (576, [2, 2, 5, 11])]

def node12Piece37UnitOutput_sector0 : RawPoly ℕ := [node12Piece37UnitOutput_sector0_chunk0, node12Piece37UnitOutput_sector0_chunk1].flatten

def node12Piece37UnitOutput : SectorVector := [(0, node12Piece37UnitOutput_sector0)]

theorem node12Piece37_check : VectorCertificate (neutralBoundS JR (-3) node12Piece37UnitInput) node12Piece37UnitOutput := by decide +kernel

theorem node12Piece37_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece37Input) = evaluate node12Piece37Output :=
  mode_of_scaled _ _ (-200) node12Piece37UnitInput node12Piece37UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece37_check)

def node12Piece38Input_sector0 : RawPoly ℕ := [(-280, [1, 2, 2, 2, 3, 4])]

def node12Piece38Input : SectorVector := [(0, node12Piece38Input_sector0)]
def node12Piece38Output_sector0_chunk0 : RawPoly ℕ := [(-1120, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (-1680, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-13440, [1, 1, 1, 2, 2, 2, 3, 8]), (-10080, [1, 1, 1, 2, 2, 2, 4, 7]), (-20160, [1, 1, 1, 2, 2, 3, 4, 6]), (-26880, [1, 1, 2, 2, 2, 2, 3, 7]), (-20160, [1, 1, 2, 2, 2, 2, 4, 6]), (-26880, [1, 1, 2, 2, 2, 3, 3, 6]), (-87360, [1, 1, 2, 2, 2, 3, 4, 5]), (-10080, [1, 1, 2, 2, 2, 4, 4, 4]), (-80640, [1, 1, 2, 2, 2, 12]), (-40320, [1, 1, 2, 2, 3, 3, 4, 4]), (-161280, [1, 1, 2, 2, 3, 11]), (-120960, [1, 1, 2, 2, 4, 10]), (-80640, [1, 1, 2, 3, 4, 9]), (-13440, [1, 2, 2, 2, 2, 2, 3, 6]), (-10080, [1, 2, 2, 2, 2, 2, 4, 5]), (-26880, [1, 2, 2, 2, 2, 3, 3, 5]), (-61320, [1, 2, 2, 2, 2, 3, 4, 4]), (-80640, [1, 2, 2, 2, 2, 11]), (-41440, [1, 2, 2, 2, 3, 3, 3, 4]), (-3360, [1, 2, 2, 2, 3, 10]), (-77280, [1, 2, 2, 2, 4, 9]), (-80640, [1, 2, 2, 2, 5, 8])]

def node12Piece38Output_sector0_chunk1 : RawPoly ℕ := [(-80640, [1, 2, 2, 2, 6, 7]), (-161280, [1, 2, 2, 3, 3, 9]), (-206640, [1, 2, 2, 3, 4, 8]), (-161280, [1, 2, 2, 3, 5, 7]), (-80640, [1, 2, 2, 3, 6, 6]), (-120960, [1, 2, 2, 4, 4, 7]), (-120960, [1, 2, 2, 4, 5, 6]), (-483840, [1, 2, 2, 15]), (-80640, [1, 2, 3, 3, 4, 7]), (-80640, [1, 2, 3, 4, 4, 6]), (-40320, [1, 2, 3, 4, 5, 5]), (-322560, [1, 2, 3, 14]), (-241920, [1, 2, 4, 13]), (-53760, [1, 3, 4, 12]), (-3360, [2, 2, 2, 2, 2, 3, 3, 4]), (-26880, [2, 2, 2, 2, 3, 9]), (-20160, [2, 2, 2, 2, 4, 8]), (-26880, [2, 2, 2, 3, 3, 8]), (-67200, [2, 2, 2, 3, 4, 7]), (-26880, [2, 2, 2, 3, 5, 6]), (-20160, [2, 2, 2, 4, 4, 6]), (-10080, [2, 2, 2, 4, 5, 5]), (-80640, [2, 2, 2, 14]), (-40320, [2, 2, 3, 3, 4, 6])]

def node12Piece38Output_sector0_chunk2 : RawPoly ℕ := [(-40320, [2, 2, 3, 4, 4, 5]), (-161280, [2, 2, 3, 13]), (-120960, [2, 2, 4, 12]), (-80640, [2, 3, 4, 11])]

def node12Piece38Output_sector0 : RawPoly ℕ := [node12Piece38Output_sector0_chunk0, node12Piece38Output_sector0_chunk1, node12Piece38Output_sector0_chunk2].flatten

def node12Piece38Output : SectorVector := [(0, node12Piece38Output_sector0)]

def node12Piece38UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 2, 3, 4])]

def node12Piece38UnitInput_sector0 : RawPoly ℕ := [node12Piece38UnitInput_sector0_chunk0].flatten

def node12Piece38UnitInput : SectorVector := [(0, node12Piece38UnitInput_sector0)]

def node12Piece38UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (6, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (48, [1, 1, 1, 2, 2, 2, 3, 8]), (36, [1, 1, 1, 2, 2, 2, 4, 7]), (72, [1, 1, 1, 2, 2, 3, 4, 6]), (96, [1, 1, 2, 2, 2, 2, 3, 7]), (72, [1, 1, 2, 2, 2, 2, 4, 6]), (96, [1, 1, 2, 2, 2, 3, 3, 6]), (312, [1, 1, 2, 2, 2, 3, 4, 5]), (36, [1, 1, 2, 2, 2, 4, 4, 4]), (288, [1, 1, 2, 2, 2, 12]), (144, [1, 1, 2, 2, 3, 3, 4, 4]), (576, [1, 1, 2, 2, 3, 11]), (432, [1, 1, 2, 2, 4, 10]), (288, [1, 1, 2, 3, 4, 9]), (48, [1, 2, 2, 2, 2, 2, 3, 6]), (36, [1, 2, 2, 2, 2, 2, 4, 5]), (96, [1, 2, 2, 2, 2, 3, 3, 5]), (219, [1, 2, 2, 2, 2, 3, 4, 4]), (288, [1, 2, 2, 2, 2, 11]), (148, [1, 2, 2, 2, 3, 3, 3, 4]), (12, [1, 2, 2, 2, 3, 10]), (276, [1, 2, 2, 2, 4, 9]), (288, [1, 2, 2, 2, 5, 8])]

def node12Piece38UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [1, 2, 2, 2, 6, 7]), (576, [1, 2, 2, 3, 3, 9]), (738, [1, 2, 2, 3, 4, 8]), (576, [1, 2, 2, 3, 5, 7]), (288, [1, 2, 2, 3, 6, 6]), (432, [1, 2, 2, 4, 4, 7]), (432, [1, 2, 2, 4, 5, 6]), (1728, [1, 2, 2, 15]), (288, [1, 2, 3, 3, 4, 7]), (288, [1, 2, 3, 4, 4, 6]), (144, [1, 2, 3, 4, 5, 5]), (1152, [1, 2, 3, 14]), (864, [1, 2, 4, 13]), (192, [1, 3, 4, 12]), (12, [2, 2, 2, 2, 2, 3, 3, 4]), (96, [2, 2, 2, 2, 3, 9]), (72, [2, 2, 2, 2, 4, 8]), (96, [2, 2, 2, 3, 3, 8]), (240, [2, 2, 2, 3, 4, 7]), (96, [2, 2, 2, 3, 5, 6]), (72, [2, 2, 2, 4, 4, 6]), (36, [2, 2, 2, 4, 5, 5]), (288, [2, 2, 2, 14]), (144, [2, 2, 3, 3, 4, 6])]

def node12Piece38UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [2, 2, 3, 4, 4, 5]), (576, [2, 2, 3, 13]), (432, [2, 2, 4, 12]), (288, [2, 3, 4, 11])]

def node12Piece38UnitOutput_sector0 : RawPoly ℕ := [node12Piece38UnitOutput_sector0_chunk0, node12Piece38UnitOutput_sector0_chunk1, node12Piece38UnitOutput_sector0_chunk2].flatten

def node12Piece38UnitOutput : SectorVector := [(0, node12Piece38UnitOutput_sector0)]

theorem node12Piece38_check : VectorCertificate (neutralBoundS JR (-3) node12Piece38UnitInput) node12Piece38UnitOutput := by decide +kernel

theorem node12Piece38_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece38Input) = evaluate node12Piece38Output :=
  mode_of_scaled _ _ (-280) node12Piece38UnitInput node12Piece38UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece38_check)

def node12Piece39Input_sector0 : RawPoly ℕ := [(7840/27, [1, 2, 2, 3, 3, 3])]

def node12Piece39Input : SectorVector := [(0, node12Piece39Input_sector0)]
def node12Piece39Output_sector0_chunk0 : RawPoly ℕ := [(31360/27, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (15680/9, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (31360, [1, 1, 1, 2, 2, 3, 3, 7]), (125440/9, [1, 1, 1, 2, 3, 3, 3, 6]), (62720, [1, 1, 2, 2, 2, 3, 3, 6]), (815360/9, [1, 1, 2, 2, 3, 3, 3, 5]), (31360, [1, 1, 2, 2, 3, 3, 4, 4]), (188160, [1, 1, 2, 2, 3, 11]), (250880/9, [1, 1, 2, 3, 3, 3, 3, 4]), (250880, [1, 1, 2, 3, 3, 10]), (250880/9, [1, 1, 3, 3, 3, 9]), (31360, [1, 2, 2, 2, 2, 3, 3, 5]), (760480/9, [1, 2, 2, 2, 3, 3, 3, 4]), (188160, [1, 2, 2, 2, 3, 10]), (784000/27, [1, 2, 2, 3, 3, 3, 3, 3]), (156800/3, [1, 2, 2, 3, 3, 9]), (188160, [1, 2, 2, 3, 4, 8]), (188160, [1, 2, 2, 3, 5, 7]), (94080, [1, 2, 2, 3, 6, 6]), (188160, [1, 2, 2, 15]), (1536640/9, [1, 2, 3, 3, 3, 8]), (250880, [1, 2, 3, 3, 4, 7]), (250880, [1, 2, 3, 3, 5, 6]), (752640, [1, 2, 3, 14])]

def node12Piece39Output_sector0_chunk1 : RawPoly ℕ := [(250880/9, [1, 3, 3, 3, 3, 7]), (250880/9, [1, 3, 3, 3, 4, 6]), (125440/9, [1, 3, 3, 3, 5, 5]), (250880, [1, 3, 3, 13]), (31360/9, [2, 2, 2, 2, 3, 3, 3, 3]), (62720, [2, 2, 2, 3, 3, 8]), (627200/9, [2, 2, 3, 3, 3, 7]), (62720, [2, 2, 3, 3, 4, 6]), (31360, [2, 2, 3, 3, 5, 5]), (188160, [2, 2, 3, 13]), (250880/9, [2, 3, 3, 3, 3, 6]), (250880/9, [2, 3, 3, 3, 4, 5]), (250880, [2, 3, 3, 12]), (250880/9, [3, 3, 3, 11])]

def node12Piece39Output_sector0 : RawPoly ℕ := [node12Piece39Output_sector0_chunk0, node12Piece39Output_sector0_chunk1].flatten

def node12Piece39Output : SectorVector := [(0, node12Piece39Output_sector0)]

def node12Piece39UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 3, 3, 3])]

def node12Piece39UnitInput_sector0 : RawPoly ℕ := [node12Piece39UnitInput_sector0_chunk0].flatten

def node12Piece39UnitInput : SectorVector := [(0, node12Piece39UnitInput_sector0)]

def node12Piece39UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (6, [1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (108, [1, 1, 1, 2, 2, 3, 3, 7]), (48, [1, 1, 1, 2, 3, 3, 3, 6]), (216, [1, 1, 2, 2, 2, 3, 3, 6]), (312, [1, 1, 2, 2, 3, 3, 3, 5]), (108, [1, 1, 2, 2, 3, 3, 4, 4]), (648, [1, 1, 2, 2, 3, 11]), (96, [1, 1, 2, 3, 3, 3, 3, 4]), (864, [1, 1, 2, 3, 3, 10]), (96, [1, 1, 3, 3, 3, 9]), (108, [1, 2, 2, 2, 2, 3, 3, 5]), (291, [1, 2, 2, 2, 3, 3, 3, 4]), (648, [1, 2, 2, 2, 3, 10]), (100, [1, 2, 2, 3, 3, 3, 3, 3]), (180, [1, 2, 2, 3, 3, 9]), (648, [1, 2, 2, 3, 4, 8]), (648, [1, 2, 2, 3, 5, 7]), (324, [1, 2, 2, 3, 6, 6]), (648, [1, 2, 2, 15]), (588, [1, 2, 3, 3, 3, 8]), (864, [1, 2, 3, 3, 4, 7]), (864, [1, 2, 3, 3, 5, 6]), (2592, [1, 2, 3, 14])]

def node12Piece39UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [1, 3, 3, 3, 3, 7]), (96, [1, 3, 3, 3, 4, 6]), (48, [1, 3, 3, 3, 5, 5]), (864, [1, 3, 3, 13]), (12, [2, 2, 2, 2, 3, 3, 3, 3]), (216, [2, 2, 2, 3, 3, 8]), (240, [2, 2, 3, 3, 3, 7]), (216, [2, 2, 3, 3, 4, 6]), (108, [2, 2, 3, 3, 5, 5]), (648, [2, 2, 3, 13]), (96, [2, 3, 3, 3, 3, 6]), (96, [2, 3, 3, 3, 4, 5]), (864, [2, 3, 3, 12]), (96, [3, 3, 3, 11])]

def node12Piece39UnitOutput_sector0 : RawPoly ℕ := [node12Piece39UnitOutput_sector0_chunk0, node12Piece39UnitOutput_sector0_chunk1].flatten

def node12Piece39UnitOutput : SectorVector := [(0, node12Piece39UnitOutput_sector0)]

theorem node12Piece39_check : VectorCertificate (neutralBoundS JR (-3) node12Piece39UnitInput) node12Piece39UnitOutput := by decide +kernel

theorem node12Piece39_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece39Input) = evaluate node12Piece39Output :=
  mode_of_scaled _ _ (7840/27) node12Piece39UnitInput node12Piece39UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece39_check)

def node12Piece40Input_sector0 : RawPoly ℕ := [(-440/3, [1, 2, 2, 9])]

def node12Piece40Input : SectorVector := [(0, node12Piece40Input_sector0)]
def node12Piece40Output_sector0_chunk0 : RawPoly ℕ := [(-1760/3, [1, 1, 1, 1, 2, 2, 3, 9]), (-880, [1, 1, 1, 2, 2, 2, 2, 9]), (-15840, [1, 1, 1, 2, 2, 13]), (-7040, [1, 1, 1, 2, 6, 9]), (-31680, [1, 1, 2, 2, 2, 12]), (-31680, [1, 1, 2, 2, 3, 11]), (-31680, [1, 1, 2, 2, 4, 10]), (-45760, [1, 1, 2, 2, 5, 9]), (-31680, [1, 1, 2, 2, 6, 8]), (-15840, [1, 1, 2, 2, 7, 7]), (-14080, [1, 1, 2, 3, 4, 9]), (-126720, [1, 1, 2, 16]), (-14080, [1, 1, 9, 9]), (-15840, [1, 2, 2, 2, 2, 11]), (-31680, [1, 2, 2, 2, 3, 10]), (-42680, [1, 2, 2, 2, 4, 9]), (-31680, [1, 2, 2, 2, 5, 8]), (-31680, [1, 2, 2, 2, 6, 7]), (-75680/3, [1, 2, 2, 3, 3, 9]), (-31680, [1, 2, 2, 3, 4, 8]), (-31680, [1, 2, 2, 3, 5, 7]), (-15840, [1, 2, 2, 3, 6, 6]), (-15840, [1, 2, 2, 4, 4, 7]), (-31680, [1, 2, 2, 4, 5, 6])]

def node12Piece40Output_sector0_chunk1 : RawPoly ℕ := [(-5280, [1, 2, 2, 5, 5, 5]), (781440, [1, 2, 2, 15]), (-126720, [1, 2, 3, 14]), (-126720, [1, 2, 4, 13]), (-126720, [1, 2, 5, 12]), (-126720, [1, 2, 6, 11]), (-126720, [1, 2, 7, 10]), (-86240, [1, 2, 8, 9]), (-14080, [1, 3, 7, 9]), (-14080, [1, 4, 6, 9]), (-7040, [1, 5, 5, 9]), (-126720, [1, 19]), (-1760, [2, 2, 2, 2, 3, 9]), (-31680, [2, 2, 2, 14]), (-31680, [2, 2, 3, 13]), (-31680, [2, 2, 4, 12]), (-31680, [2, 2, 5, 11]), (-31680, [2, 2, 6, 10]), (-35200, [2, 2, 7, 9]), (-15840, [2, 2, 8, 8]), (-14080, [2, 3, 6, 9]), (-14080, [2, 4, 5, 9]), (-126720, [2, 18]), (-14080, [9, 11])]

def node12Piece40Output_sector0 : RawPoly ℕ := [node12Piece40Output_sector0_chunk0, node12Piece40Output_sector0_chunk1].flatten

def node12Piece40Output : SectorVector := [(0, node12Piece40Output_sector0)]

def node12Piece40UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 2, 9])]

def node12Piece40UnitInput_sector0 : RawPoly ℕ := [node12Piece40UnitInput_sector0_chunk0].flatten

def node12Piece40UnitInput : SectorVector := [(0, node12Piece40UnitInput_sector0)]

def node12Piece40UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 2, 3, 9]), (6, [1, 1, 1, 2, 2, 2, 2, 9]), (108, [1, 1, 1, 2, 2, 13]), (48, [1, 1, 1, 2, 6, 9]), (216, [1, 1, 2, 2, 2, 12]), (216, [1, 1, 2, 2, 3, 11]), (216, [1, 1, 2, 2, 4, 10]), (312, [1, 1, 2, 2, 5, 9]), (216, [1, 1, 2, 2, 6, 8]), (108, [1, 1, 2, 2, 7, 7]), (96, [1, 1, 2, 3, 4, 9]), (864, [1, 1, 2, 16]), (96, [1, 1, 9, 9]), (108, [1, 2, 2, 2, 2, 11]), (216, [1, 2, 2, 2, 3, 10]), (291, [1, 2, 2, 2, 4, 9]), (216, [1, 2, 2, 2, 5, 8]), (216, [1, 2, 2, 2, 6, 7]), (172, [1, 2, 2, 3, 3, 9]), (216, [1, 2, 2, 3, 4, 8]), (216, [1, 2, 2, 3, 5, 7]), (108, [1, 2, 2, 3, 6, 6]), (108, [1, 2, 2, 4, 4, 7]), (216, [1, 2, 2, 4, 5, 6])]

def node12Piece40UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [1, 2, 2, 5, 5, 5]), (-5328, [1, 2, 2, 15]), (864, [1, 2, 3, 14]), (864, [1, 2, 4, 13]), (864, [1, 2, 5, 12]), (864, [1, 2, 6, 11]), (864, [1, 2, 7, 10]), (588, [1, 2, 8, 9]), (96, [1, 3, 7, 9]), (96, [1, 4, 6, 9]), (48, [1, 5, 5, 9]), (864, [1, 19]), (12, [2, 2, 2, 2, 3, 9]), (216, [2, 2, 2, 14]), (216, [2, 2, 3, 13]), (216, [2, 2, 4, 12]), (216, [2, 2, 5, 11]), (216, [2, 2, 6, 10]), (240, [2, 2, 7, 9]), (108, [2, 2, 8, 8]), (96, [2, 3, 6, 9]), (96, [2, 4, 5, 9]), (864, [2, 18]), (96, [9, 11])]

def node12Piece40UnitOutput_sector0 : RawPoly ℕ := [node12Piece40UnitOutput_sector0_chunk0, node12Piece40UnitOutput_sector0_chunk1].flatten

def node12Piece40UnitOutput : SectorVector := [(0, node12Piece40UnitOutput_sector0)]

theorem node12Piece40_check : VectorCertificate (neutralBoundS JR (-3) node12Piece40UnitInput) node12Piece40UnitOutput := by decide +kernel

theorem node12Piece40_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece40Input) = evaluate node12Piece40Output :=
  mode_of_scaled _ _ (-440/3) node12Piece40UnitInput node12Piece40UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece40_check)

def node12Piece41Input_sector0 : RawPoly ℕ := [(360, [1, 2, 3, 8])]

def node12Piece41Input : SectorVector := [(0, node12Piece41Input_sector0)]
def node12Piece41Output_sector0_chunk0 : RawPoly ℕ := [(1440, [1, 1, 1, 1, 2, 3, 3, 8]), (2160, [1, 1, 1, 2, 2, 2, 3, 8]), (34560, [1, 1, 1, 2, 3, 12]), (12960, [1, 1, 1, 2, 7, 8]), (8640, [1, 1, 1, 3, 6, 8]), (69120, [1, 1, 2, 2, 3, 11]), (25920, [1, 1, 2, 2, 6, 8]), (69120, [1, 1, 2, 3, 3, 10]), (69120, [1, 1, 2, 3, 4, 9]), (112320, [1, 1, 2, 3, 5, 8]), (69120, [1, 1, 2, 3, 6, 7]), (12960, [1, 1, 2, 4, 4, 8]), (207360, [1, 1, 2, 16]), (17280, [1, 1, 3, 3, 4, 8]), (138240, [1, 1, 3, 15]), (51840, [1, 1, 8, 10]), (34560, [1, 2, 2, 2, 3, 10]), (12960, [1, 2, 2, 2, 5, 8]), (69120, [1, 2, 2, 3, 3, 9]), (113400, [1, 2, 2, 3, 4, 8]), (69120, [1, 2, 2, 3, 5, 7]), (34560, [1, 2, 2, 3, 6, 6]), (207360, [1, 2, 2, 15]), (53280, [1, 2, 3, 3, 3, 8])]

def node12Piece41Output_sector0_chunk1 : RawPoly ℕ := [(69120, [1, 2, 3, 3, 4, 7]), (69120, [1, 2, 3, 3, 5, 6]), (34560, [1, 2, 3, 4, 4, 6]), (34560, [1, 2, 3, 4, 5, 5]), (-1304640, [1, 2, 3, 14]), (207360, [1, 2, 4, 13]), (207360, [1, 2, 5, 12]), (207360, [1, 2, 6, 11]), (207360, [1, 2, 7, 10]), (99360, [1, 2, 8, 9]), (138240, [1, 3, 3, 13]), (138240, [1, 3, 4, 12]), (138240, [1, 3, 5, 11]), (138240, [1, 3, 6, 10]), (138240, [1, 3, 7, 9]), (54000, [1, 3, 8, 8]), (51840, [1, 4, 7, 8]), (51840, [1, 5, 6, 8]), (414720, [1, 19]), (4320, [2, 2, 2, 3, 3, 8]), (69120, [2, 2, 3, 13]), (25920, [2, 2, 8, 8]), (69120, [2, 3, 3, 12]), (69120, [2, 3, 4, 11])]

def node12Piece41Output_sector0_chunk2 : RawPoly ℕ := [(69120, [2, 3, 5, 10]), (69120, [2, 3, 6, 9]), (86400, [2, 3, 7, 8]), (25920, [2, 4, 6, 8]), (12960, [2, 5, 5, 8]), (207360, [2, 18]), (17280, [3, 3, 6, 8]), (17280, [3, 4, 5, 8]), (138240, [3, 17]), (51840, [8, 12])]

def node12Piece41Output_sector0 : RawPoly ℕ := [node12Piece41Output_sector0_chunk0, node12Piece41Output_sector0_chunk1, node12Piece41Output_sector0_chunk2].flatten

def node12Piece41Output : SectorVector := [(0, node12Piece41Output_sector0)]

def node12Piece41UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 3, 8])]

def node12Piece41UnitInput_sector0 : RawPoly ℕ := [node12Piece41UnitInput_sector0_chunk0].flatten

def node12Piece41UnitInput : SectorVector := [(0, node12Piece41UnitInput_sector0)]

def node12Piece41UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 3, 8]), (6, [1, 1, 1, 2, 2, 2, 3, 8]), (96, [1, 1, 1, 2, 3, 12]), (36, [1, 1, 1, 2, 7, 8]), (24, [1, 1, 1, 3, 6, 8]), (192, [1, 1, 2, 2, 3, 11]), (72, [1, 1, 2, 2, 6, 8]), (192, [1, 1, 2, 3, 3, 10]), (192, [1, 1, 2, 3, 4, 9]), (312, [1, 1, 2, 3, 5, 8]), (192, [1, 1, 2, 3, 6, 7]), (36, [1, 1, 2, 4, 4, 8]), (576, [1, 1, 2, 16]), (48, [1, 1, 3, 3, 4, 8]), (384, [1, 1, 3, 15]), (144, [1, 1, 8, 10]), (96, [1, 2, 2, 2, 3, 10]), (36, [1, 2, 2, 2, 5, 8]), (192, [1, 2, 2, 3, 3, 9]), (315, [1, 2, 2, 3, 4, 8]), (192, [1, 2, 2, 3, 5, 7]), (96, [1, 2, 2, 3, 6, 6]), (576, [1, 2, 2, 15]), (148, [1, 2, 3, 3, 3, 8])]

def node12Piece41UnitOutput_sector0_chunk1 : RawPoly ℕ := [(192, [1, 2, 3, 3, 4, 7]), (192, [1, 2, 3, 3, 5, 6]), (96, [1, 2, 3, 4, 4, 6]), (96, [1, 2, 3, 4, 5, 5]), (-3624, [1, 2, 3, 14]), (576, [1, 2, 4, 13]), (576, [1, 2, 5, 12]), (576, [1, 2, 6, 11]), (576, [1, 2, 7, 10]), (276, [1, 2, 8, 9]), (384, [1, 3, 3, 13]), (384, [1, 3, 4, 12]), (384, [1, 3, 5, 11]), (384, [1, 3, 6, 10]), (384, [1, 3, 7, 9]), (150, [1, 3, 8, 8]), (144, [1, 4, 7, 8]), (144, [1, 5, 6, 8]), (1152, [1, 19]), (12, [2, 2, 2, 3, 3, 8]), (192, [2, 2, 3, 13]), (72, [2, 2, 8, 8]), (192, [2, 3, 3, 12]), (192, [2, 3, 4, 11])]

def node12Piece41UnitOutput_sector0_chunk2 : RawPoly ℕ := [(192, [2, 3, 5, 10]), (192, [2, 3, 6, 9]), (240, [2, 3, 7, 8]), (72, [2, 4, 6, 8]), (36, [2, 5, 5, 8]), (576, [2, 18]), (48, [3, 3, 6, 8]), (48, [3, 4, 5, 8]), (384, [3, 17]), (144, [8, 12])]

def node12Piece41UnitOutput_sector0 : RawPoly ℕ := [node12Piece41UnitOutput_sector0_chunk0, node12Piece41UnitOutput_sector0_chunk1, node12Piece41UnitOutput_sector0_chunk2].flatten

def node12Piece41UnitOutput : SectorVector := [(0, node12Piece41UnitOutput_sector0)]

theorem node12Piece41_check : VectorCertificate (neutralBoundS JR (-3) node12Piece41UnitInput) node12Piece41UnitOutput := by decide +kernel

theorem node12Piece41_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece41Input) = evaluate node12Piece41Output :=
  mode_of_scaled _ _ (360) node12Piece41UnitInput node12Piece41UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece41_check)

def node12Piece42Input_sector0 : RawPoly ℕ := [(-240, [1, 2, 4, 7])]

def node12Piece42Input : SectorVector := [(0, node12Piece42Input_sector0)]
def node12Piece42Output_sector0_chunk0 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 2, 3, 4, 7]), (-1440, [1, 1, 1, 2, 2, 2, 4, 7]), (-20160, [1, 1, 1, 2, 4, 11]), (-11520, [1, 1, 1, 2, 7, 8]), (-5760, [1, 1, 1, 4, 6, 7]), (-40320, [1, 1, 2, 2, 4, 10]), (-23040, [1, 1, 2, 2, 7, 7]), (-40320, [1, 1, 2, 3, 4, 9]), (-23040, [1, 1, 2, 3, 6, 7]), (-40320, [1, 1, 2, 4, 4, 8]), (-74880, [1, 1, 2, 4, 5, 7]), (-20160, [1, 1, 2, 4, 6, 6]), (-161280, [1, 1, 2, 16]), (-11520, [1, 1, 3, 4, 4, 7]), (-80640, [1, 1, 4, 14]), (-46080, [1, 1, 7, 11]), (-20160, [1, 2, 2, 2, 4, 9]), (-11520, [1, 2, 2, 2, 6, 7]), (-40320, [1, 2, 2, 3, 4, 8]), (-23040, [1, 2, 2, 3, 5, 7]), (-64080, [1, 2, 2, 4, 4, 7]), (-40320, [1, 2, 2, 4, 5, 6]), (-161280, [1, 2, 2, 15]), (-41280, [1, 2, 3, 3, 4, 7])]

def node12Piece42Output_sector0_chunk1 : RawPoly ℕ := [(-40320, [1, 2, 3, 4, 4, 6]), (-20160, [1, 2, 3, 4, 5, 5]), (-161280, [1, 2, 3, 14]), (-20160, [1, 2, 4, 4, 4, 5]), (544320, [1, 2, 4, 13]), (-161280, [1, 2, 5, 12]), (-161280, [1, 2, 6, 11]), (-2880, [1, 2, 7, 10]), (-161280, [1, 2, 8, 9]), (-80640, [1, 3, 4, 12]), (-46080, [1, 3, 7, 9]), (-80640, [1, 4, 4, 11]), (-80640, [1, 4, 5, 10]), (-80640, [1, 4, 6, 9]), (-82080, [1, 4, 7, 8]), (-46080, [1, 5, 7, 7]), (-23040, [1, 6, 6, 7]), (-322560, [1, 19]), (-2880, [2, 2, 2, 3, 4, 7]), (-40320, [2, 2, 4, 12]), (-23040, [2, 2, 7, 9]), (-40320, [2, 3, 4, 11]), (-23040, [2, 3, 7, 8]), (-40320, [2, 4, 4, 10])]

def node12Piece42Output_sector0_chunk2 : RawPoly ℕ := [(-40320, [2, 4, 5, 9]), (-40320, [2, 4, 6, 8]), (-37440, [2, 4, 7, 7]), (-23040, [2, 5, 6, 7]), (-161280, [2, 18]), (-11520, [3, 4, 6, 7]), (-11520, [4, 4, 5, 7]), (-80640, [4, 16]), (-46080, [7, 13])]

def node12Piece42Output_sector0 : RawPoly ℕ := [node12Piece42Output_sector0_chunk0, node12Piece42Output_sector0_chunk1, node12Piece42Output_sector0_chunk2].flatten

def node12Piece42Output : SectorVector := [(0, node12Piece42Output_sector0)]

def node12Piece42UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 4, 7])]

def node12Piece42UnitInput_sector0 : RawPoly ℕ := [node12Piece42UnitInput_sector0_chunk0].flatten

def node12Piece42UnitInput : SectorVector := [(0, node12Piece42UnitInput_sector0)]

def node12Piece42UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 4, 7]), (6, [1, 1, 1, 2, 2, 2, 4, 7]), (84, [1, 1, 1, 2, 4, 11]), (48, [1, 1, 1, 2, 7, 8]), (24, [1, 1, 1, 4, 6, 7]), (168, [1, 1, 2, 2, 4, 10]), (96, [1, 1, 2, 2, 7, 7]), (168, [1, 1, 2, 3, 4, 9]), (96, [1, 1, 2, 3, 6, 7]), (168, [1, 1, 2, 4, 4, 8]), (312, [1, 1, 2, 4, 5, 7]), (84, [1, 1, 2, 4, 6, 6]), (672, [1, 1, 2, 16]), (48, [1, 1, 3, 4, 4, 7]), (336, [1, 1, 4, 14]), (192, [1, 1, 7, 11]), (84, [1, 2, 2, 2, 4, 9]), (48, [1, 2, 2, 2, 6, 7]), (168, [1, 2, 2, 3, 4, 8]), (96, [1, 2, 2, 3, 5, 7]), (267, [1, 2, 2, 4, 4, 7]), (168, [1, 2, 2, 4, 5, 6]), (672, [1, 2, 2, 15]), (172, [1, 2, 3, 3, 4, 7])]

def node12Piece42UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [1, 2, 3, 4, 4, 6]), (84, [1, 2, 3, 4, 5, 5]), (672, [1, 2, 3, 14]), (84, [1, 2, 4, 4, 4, 5]), (-2268, [1, 2, 4, 13]), (672, [1, 2, 5, 12]), (672, [1, 2, 6, 11]), (12, [1, 2, 7, 10]), (672, [1, 2, 8, 9]), (336, [1, 3, 4, 12]), (192, [1, 3, 7, 9]), (336, [1, 4, 4, 11]), (336, [1, 4, 5, 10]), (336, [1, 4, 6, 9]), (342, [1, 4, 7, 8]), (192, [1, 5, 7, 7]), (96, [1, 6, 6, 7]), (1344, [1, 19]), (12, [2, 2, 2, 3, 4, 7]), (168, [2, 2, 4, 12]), (96, [2, 2, 7, 9]), (168, [2, 3, 4, 11]), (96, [2, 3, 7, 8]), (168, [2, 4, 4, 10])]

def node12Piece42UnitOutput_sector0_chunk2 : RawPoly ℕ := [(168, [2, 4, 5, 9]), (168, [2, 4, 6, 8]), (156, [2, 4, 7, 7]), (96, [2, 5, 6, 7]), (672, [2, 18]), (48, [3, 4, 6, 7]), (48, [4, 4, 5, 7]), (336, [4, 16]), (192, [7, 13])]

def node12Piece42UnitOutput_sector0 : RawPoly ℕ := [node12Piece42UnitOutput_sector0_chunk0, node12Piece42UnitOutput_sector0_chunk1, node12Piece42UnitOutput_sector0_chunk2].flatten

def node12Piece42UnitOutput : SectorVector := [(0, node12Piece42UnitOutput_sector0)]

theorem node12Piece42_check : VectorCertificate (neutralBoundS JR (-3) node12Piece42UnitInput) node12Piece42UnitOutput := by decide +kernel

theorem node12Piece42_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece42Input) = evaluate node12Piece42Output :=
  mode_of_scaled _ _ (-240) node12Piece42UnitInput node12Piece42UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece42_check)

def node12Piece43Input_sector0 : RawPoly ℕ := [(64, [1, 2, 5, 6])]

def node12Piece43Input : SectorVector := [(0, node12Piece43Input_sector0)]
def node12Piece43Output_sector0_chunk0 : RawPoly ℕ := [(256, [1, 1, 1, 1, 2, 3, 5, 6]), (384, [1, 1, 1, 2, 2, 2, 5, 6]), (4608, [1, 1, 1, 2, 5, 10]), (3840, [1, 1, 1, 2, 6, 9]), (1536, [1, 1, 1, 5, 6, 6]), (9216, [1, 1, 2, 2, 5, 9]), (7680, [1, 1, 2, 2, 6, 8]), (9216, [1, 1, 2, 3, 5, 8]), (7680, [1, 1, 2, 3, 6, 7]), (9216, [1, 1, 2, 4, 5, 7]), (7680, [1, 1, 2, 4, 6, 6]), (16128, [1, 1, 2, 5, 5, 6]), (46080, [1, 1, 2, 16]), (3072, [1, 1, 3, 4, 5, 6]), (18432, [1, 1, 5, 13]), (15360, [1, 1, 6, 12]), (4608, [1, 2, 2, 2, 5, 8]), (3840, [1, 2, 2, 2, 6, 7]), (9216, [1, 2, 2, 3, 5, 7]), (7680, [1, 2, 2, 3, 6, 6]), (20160, [1, 2, 2, 4, 5, 6]), (4608, [1, 2, 2, 5, 5, 5]), (46080, [1, 2, 2, 15]), (11008, [1, 2, 3, 3, 5, 6])]

def node12Piece43Output_sector0_chunk1 : RawPoly ℕ := [(3840, [1, 2, 3, 4, 4, 6]), (9216, [1, 2, 3, 4, 5, 5]), (46080, [1, 2, 3, 14]), (1536, [1, 2, 4, 4, 4, 5]), (46080, [1, 2, 4, 13]), (-78720, [1, 2, 5, 12]), (-30720, [1, 2, 6, 11]), (46080, [1, 2, 7, 10]), (46080, [1, 2, 8, 9]), (18432, [1, 3, 5, 11]), (15360, [1, 3, 6, 10]), (18432, [1, 4, 5, 10]), (15360, [1, 4, 6, 9]), (18432, [1, 5, 5, 9]), (21888, [1, 5, 6, 8]), (9216, [1, 5, 7, 7]), (15360, [1, 6, 6, 7]), (92160, [1, 19]), (768, [2, 2, 2, 3, 5, 6]), (9216, [2, 2, 5, 11]), (7680, [2, 2, 6, 10]), (9216, [2, 3, 5, 10]), (7680, [2, 3, 6, 9]), (9216, [2, 4, 5, 9])]

def node12Piece43Output_sector0_chunk2 : RawPoly ℕ := [(7680, [2, 4, 6, 8]), (9216, [2, 5, 5, 8]), (15360, [2, 5, 6, 7]), (3840, [2, 6, 6, 6]), (46080, [2, 18]), (3072, [3, 5, 6, 6]), (3072, [4, 5, 5, 6]), (18432, [5, 15]), (15360, [6, 14])]

def node12Piece43Output_sector0 : RawPoly ℕ := [node12Piece43Output_sector0_chunk0, node12Piece43Output_sector0_chunk1, node12Piece43Output_sector0_chunk2].flatten

def node12Piece43Output : SectorVector := [(0, node12Piece43Output_sector0)]

def node12Piece43UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 2, 5, 6])]

def node12Piece43UnitInput_sector0 : RawPoly ℕ := [node12Piece43UnitInput_sector0_chunk0].flatten

def node12Piece43UnitInput : SectorVector := [(0, node12Piece43UnitInput_sector0)]

def node12Piece43UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 2, 3, 5, 6]), (6, [1, 1, 1, 2, 2, 2, 5, 6]), (72, [1, 1, 1, 2, 5, 10]), (60, [1, 1, 1, 2, 6, 9]), (24, [1, 1, 1, 5, 6, 6]), (144, [1, 1, 2, 2, 5, 9]), (120, [1, 1, 2, 2, 6, 8]), (144, [1, 1, 2, 3, 5, 8]), (120, [1, 1, 2, 3, 6, 7]), (144, [1, 1, 2, 4, 5, 7]), (120, [1, 1, 2, 4, 6, 6]), (252, [1, 1, 2, 5, 5, 6]), (720, [1, 1, 2, 16]), (48, [1, 1, 3, 4, 5, 6]), (288, [1, 1, 5, 13]), (240, [1, 1, 6, 12]), (72, [1, 2, 2, 2, 5, 8]), (60, [1, 2, 2, 2, 6, 7]), (144, [1, 2, 2, 3, 5, 7]), (120, [1, 2, 2, 3, 6, 6]), (315, [1, 2, 2, 4, 5, 6]), (72, [1, 2, 2, 5, 5, 5]), (720, [1, 2, 2, 15]), (172, [1, 2, 3, 3, 5, 6])]

def node12Piece43UnitOutput_sector0_chunk1 : RawPoly ℕ := [(60, [1, 2, 3, 4, 4, 6]), (144, [1, 2, 3, 4, 5, 5]), (720, [1, 2, 3, 14]), (24, [1, 2, 4, 4, 4, 5]), (720, [1, 2, 4, 13]), (-1230, [1, 2, 5, 12]), (-480, [1, 2, 6, 11]), (720, [1, 2, 7, 10]), (720, [1, 2, 8, 9]), (288, [1, 3, 5, 11]), (240, [1, 3, 6, 10]), (288, [1, 4, 5, 10]), (240, [1, 4, 6, 9]), (288, [1, 5, 5, 9]), (342, [1, 5, 6, 8]), (144, [1, 5, 7, 7]), (240, [1, 6, 6, 7]), (1440, [1, 19]), (12, [2, 2, 2, 3, 5, 6]), (144, [2, 2, 5, 11]), (120, [2, 2, 6, 10]), (144, [2, 3, 5, 10]), (120, [2, 3, 6, 9]), (144, [2, 4, 5, 9])]

def node12Piece43UnitOutput_sector0_chunk2 : RawPoly ℕ := [(120, [2, 4, 6, 8]), (144, [2, 5, 5, 8]), (240, [2, 5, 6, 7]), (60, [2, 6, 6, 6]), (720, [2, 18]), (48, [3, 5, 6, 6]), (48, [4, 5, 5, 6]), (288, [5, 15]), (240, [6, 14])]

def node12Piece43UnitOutput_sector0 : RawPoly ℕ := [node12Piece43UnitOutput_sector0_chunk0, node12Piece43UnitOutput_sector0_chunk1, node12Piece43UnitOutput_sector0_chunk2].flatten

def node12Piece43UnitOutput : SectorVector := [(0, node12Piece43UnitOutput_sector0)]

theorem node12Piece43_check : VectorCertificate (neutralBoundS JR (-3) node12Piece43UnitInput) node12Piece43UnitOutput := by decide +kernel

theorem node12Piece43_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece43Input) = evaluate node12Piece43Output :=
  mode_of_scaled _ _ (64) node12Piece43UnitInput node12Piece43UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece43_check)

def node12Piece44Input_sector0 : RawPoly ℕ := [(1920/7, [1, 3, 3, 7])]

def node12Piece44Input : SectorVector := [(0, node12Piece44Input_sector0)]
def node12Piece44Output_sector0_chunk0 : RawPoly ℕ := [(7680/7, [1, 1, 1, 1, 3, 3, 3, 7]), (11520/7, [1, 1, 1, 2, 2, 3, 3, 7]), (23040, [1, 1, 1, 3, 3, 11]), (138240/7, [1, 1, 1, 3, 7, 7]), (46080, [1, 1, 2, 3, 3, 10]), (276480/7, [1, 1, 2, 3, 6, 7]), (46080, [1, 1, 3, 3, 3, 9]), (46080, [1, 1, 3, 3, 4, 8]), (599040/7, [1, 1, 3, 3, 5, 7]), (23040, [1, 1, 3, 3, 6, 6]), (138240/7, [1, 1, 3, 4, 4, 7]), (276480, [1, 1, 3, 15]), (414720/7, [1, 1, 7, 11]), (23040, [1, 2, 2, 3, 3, 9]), (138240/7, [1, 2, 2, 3, 5, 7]), (46080, [1, 2, 3, 3, 3, 8]), (650880/7, [1, 2, 3, 3, 4, 7]), (46080, [1, 2, 3, 3, 5, 6]), (276480, [1, 2, 3, 14]), (414720/7, [1, 2, 7, 10]), (238080/7, [1, 3, 3, 3, 3, 7]), (46080, [1, 3, 3, 3, 4, 6]), (23040, [1, 3, 3, 3, 5, 5]), (23040, [1, 3, 3, 4, 4, 5])]

def node12Piece44Output_sector0_chunk1 : RawPoly ℕ := [(-622080, [1, 3, 3, 13]), (276480, [1, 3, 4, 12]), (276480, [1, 3, 5, 11]), (276480, [1, 3, 6, 10]), (92160, [1, 3, 7, 9]), (138240, [1, 3, 8, 8]), (414720/7, [1, 4, 7, 8]), (414720/7, [1, 5, 7, 7]), (207360/7, [1, 6, 6, 7]), (414720, [1, 19]), (23040/7, [2, 2, 3, 3, 3, 7]), (46080, [2, 3, 3, 12]), (276480/7, [2, 3, 7, 8]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (46080, [3, 3, 6, 8]), (299520/7, [3, 3, 7, 7]), (276480/7, [3, 4, 6, 7]), (138240/7, [3, 5, 5, 7]), (276480, [3, 17]), (414720/7, [7, 13])]

def node12Piece44Output_sector0 : RawPoly ℕ := [node12Piece44Output_sector0_chunk0, node12Piece44Output_sector0_chunk1].flatten

def node12Piece44Output : SectorVector := [(0, node12Piece44Output_sector0)]

def node12Piece44UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 3, 7])]

def node12Piece44UnitInput_sector0 : RawPoly ℕ := [node12Piece44UnitInput_sector0_chunk0].flatten

def node12Piece44UnitInput : SectorVector := [(0, node12Piece44UnitInput_sector0)]

def node12Piece44UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 3, 3, 7]), (6, [1, 1, 1, 2, 2, 3, 3, 7]), (84, [1, 1, 1, 3, 3, 11]), (72, [1, 1, 1, 3, 7, 7]), (168, [1, 1, 2, 3, 3, 10]), (144, [1, 1, 2, 3, 6, 7]), (168, [1, 1, 3, 3, 3, 9]), (168, [1, 1, 3, 3, 4, 8]), (312, [1, 1, 3, 3, 5, 7]), (84, [1, 1, 3, 3, 6, 6]), (72, [1, 1, 3, 4, 4, 7]), (1008, [1, 1, 3, 15]), (216, [1, 1, 7, 11]), (84, [1, 2, 2, 3, 3, 9]), (72, [1, 2, 2, 3, 5, 7]), (168, [1, 2, 3, 3, 3, 8]), (339, [1, 2, 3, 3, 4, 7]), (168, [1, 2, 3, 3, 5, 6]), (1008, [1, 2, 3, 14]), (216, [1, 2, 7, 10]), (124, [1, 3, 3, 3, 3, 7]), (168, [1, 3, 3, 3, 4, 6]), (84, [1, 3, 3, 3, 5, 5]), (84, [1, 3, 3, 4, 4, 5])]

def node12Piece44UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-2268, [1, 3, 3, 13]), (1008, [1, 3, 4, 12]), (1008, [1, 3, 5, 11]), (1008, [1, 3, 6, 10]), (336, [1, 3, 7, 9]), (504, [1, 3, 8, 8]), (216, [1, 4, 7, 8]), (216, [1, 5, 7, 7]), (108, [1, 6, 6, 7]), (1512, [1, 19]), (12, [2, 2, 3, 3, 3, 7]), (168, [2, 3, 3, 12]), (144, [2, 3, 7, 8]), (168, [3, 3, 3, 11]), (168, [3, 3, 4, 10]), (168, [3, 3, 5, 9]), (168, [3, 3, 6, 8]), (156, [3, 3, 7, 7]), (144, [3, 4, 6, 7]), (72, [3, 5, 5, 7]), (1008, [3, 17]), (216, [7, 13])]

def node12Piece44UnitOutput_sector0 : RawPoly ℕ := [node12Piece44UnitOutput_sector0_chunk0, node12Piece44UnitOutput_sector0_chunk1].flatten

def node12Piece44UnitOutput : SectorVector := [(0, node12Piece44UnitOutput_sector0)]

theorem node12Piece44_check : VectorCertificate (neutralBoundS JR (-3) node12Piece44UnitInput) node12Piece44UnitOutput := by decide +kernel

theorem node12Piece44_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece44Input) = evaluate node12Piece44Output :=
  mode_of_scaled _ _ (1920/7) node12Piece44UnitInput node12Piece44UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece44_check)

def node12Piece45Input_sector0 : RawPoly ℕ := [(80, [1, 3, 4, 6])]

def node12Piece45Input : SectorVector := [(0, node12Piece45Input_sector0)]
def node12Piece45Output_sector0_chunk0 : RawPoly ℕ := [(320, [1, 1, 1, 1, 3, 3, 4, 6]), (480, [1, 1, 1, 2, 2, 3, 4, 6]), (5760, [1, 1, 1, 3, 4, 10]), (3840, [1, 1, 1, 3, 6, 8]), (2880, [1, 1, 1, 4, 6, 7]), (11520, [1, 1, 2, 3, 4, 9]), (7680, [1, 1, 2, 3, 6, 7]), (5760, [1, 1, 2, 4, 6, 6]), (11520, [1, 1, 3, 3, 4, 8]), (7680, [1, 1, 3, 3, 6, 6]), (11520, [1, 1, 3, 4, 4, 7]), (24960, [1, 1, 3, 4, 5, 6]), (46080, [1, 1, 3, 15]), (2880, [1, 1, 4, 4, 4, 6]), (34560, [1, 1, 4, 14]), (23040, [1, 1, 6, 12]), (5760, [1, 2, 2, 3, 4, 8]), (3840, [1, 2, 2, 3, 6, 6]), (2880, [1, 2, 2, 4, 5, 6]), (11520, [1, 2, 3, 3, 4, 7]), (7680, [1, 2, 3, 3, 5, 6]), (23280, [1, 2, 3, 4, 4, 6]), (5760, [1, 2, 3, 4, 5, 5]), (46080, [1, 2, 3, 14])]

def node12Piece45Output_sector0_chunk1 : RawPoly ℕ := [(34560, [1, 2, 4, 13]), (23040, [1, 2, 6, 11]), (11840, [1, 3, 3, 3, 4, 6]), (11520, [1, 3, 3, 4, 4, 5]), (46080, [1, 3, 3, 13]), (1920, [1, 3, 4, 4, 4, 4]), (-98400, [1, 3, 4, 12]), (46080, [1, 3, 5, 11]), (960, [1, 3, 6, 10]), (46080, [1, 3, 7, 9]), (23040, [1, 3, 8, 8]), (34560, [1, 4, 4, 11]), (34560, [1, 4, 5, 10]), (22080, [1, 4, 6, 9]), (34560, [1, 4, 7, 8]), (23040, [1, 5, 6, 8]), (23040, [1, 6, 6, 7]), (138240, [1, 19]), (960, [2, 2, 3, 3, 4, 6]), (11520, [2, 3, 4, 11]), (7680, [2, 3, 6, 9]), (5760, [2, 4, 6, 8]), (11520, [3, 3, 4, 10]), (7680, [3, 3, 6, 8])]

def node12Piece45Output_sector0_chunk2 : RawPoly ℕ := [(11520, [3, 4, 4, 9]), (11520, [3, 4, 5, 8]), (19200, [3, 4, 6, 7]), (7680, [3, 5, 6, 6]), (46080, [3, 17]), (5760, [4, 4, 6, 6]), (2880, [4, 5, 5, 6]), (34560, [4, 16]), (23040, [6, 14])]

def node12Piece45Output_sector0 : RawPoly ℕ := [node12Piece45Output_sector0_chunk0, node12Piece45Output_sector0_chunk1, node12Piece45Output_sector0_chunk2].flatten

def node12Piece45Output : SectorVector := [(0, node12Piece45Output_sector0)]

def node12Piece45UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 4, 6])]

def node12Piece45UnitInput_sector0 : RawPoly ℕ := [node12Piece45UnitInput_sector0_chunk0].flatten

def node12Piece45UnitInput : SectorVector := [(0, node12Piece45UnitInput_sector0)]

def node12Piece45UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 3, 4, 6]), (6, [1, 1, 1, 2, 2, 3, 4, 6]), (72, [1, 1, 1, 3, 4, 10]), (48, [1, 1, 1, 3, 6, 8]), (36, [1, 1, 1, 4, 6, 7]), (144, [1, 1, 2, 3, 4, 9]), (96, [1, 1, 2, 3, 6, 7]), (72, [1, 1, 2, 4, 6, 6]), (144, [1, 1, 3, 3, 4, 8]), (96, [1, 1, 3, 3, 6, 6]), (144, [1, 1, 3, 4, 4, 7]), (312, [1, 1, 3, 4, 5, 6]), (576, [1, 1, 3, 15]), (36, [1, 1, 4, 4, 4, 6]), (432, [1, 1, 4, 14]), (288, [1, 1, 6, 12]), (72, [1, 2, 2, 3, 4, 8]), (48, [1, 2, 2, 3, 6, 6]), (36, [1, 2, 2, 4, 5, 6]), (144, [1, 2, 3, 3, 4, 7]), (96, [1, 2, 3, 3, 5, 6]), (291, [1, 2, 3, 4, 4, 6]), (72, [1, 2, 3, 4, 5, 5]), (576, [1, 2, 3, 14])]

def node12Piece45UnitOutput_sector0_chunk1 : RawPoly ℕ := [(432, [1, 2, 4, 13]), (288, [1, 2, 6, 11]), (148, [1, 3, 3, 3, 4, 6]), (144, [1, 3, 3, 4, 4, 5]), (576, [1, 3, 3, 13]), (24, [1, 3, 4, 4, 4, 4]), (-1230, [1, 3, 4, 12]), (576, [1, 3, 5, 11]), (12, [1, 3, 6, 10]), (576, [1, 3, 7, 9]), (288, [1, 3, 8, 8]), (432, [1, 4, 4, 11]), (432, [1, 4, 5, 10]), (276, [1, 4, 6, 9]), (432, [1, 4, 7, 8]), (288, [1, 5, 6, 8]), (288, [1, 6, 6, 7]), (1728, [1, 19]), (12, [2, 2, 3, 3, 4, 6]), (144, [2, 3, 4, 11]), (96, [2, 3, 6, 9]), (72, [2, 4, 6, 8]), (144, [3, 3, 4, 10]), (96, [3, 3, 6, 8])]

def node12Piece45UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [3, 4, 4, 9]), (144, [3, 4, 5, 8]), (240, [3, 4, 6, 7]), (96, [3, 5, 6, 6]), (576, [3, 17]), (72, [4, 4, 6, 6]), (36, [4, 5, 5, 6]), (432, [4, 16]), (288, [6, 14])]

def node12Piece45UnitOutput_sector0 : RawPoly ℕ := [node12Piece45UnitOutput_sector0_chunk0, node12Piece45UnitOutput_sector0_chunk1, node12Piece45UnitOutput_sector0_chunk2].flatten

def node12Piece45UnitOutput : SectorVector := [(0, node12Piece45UnitOutput_sector0)]

theorem node12Piece45_check : VectorCertificate (neutralBoundS JR (-3) node12Piece45UnitInput) node12Piece45UnitOutput := by decide +kernel

theorem node12Piece45_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece45Input) = evaluate node12Piece45Output :=
  mode_of_scaled _ _ (80) node12Piece45UnitInput node12Piece45UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece45_check)

def node12Piece46Input_sector0 : RawPoly ℕ := [(896/5, [1, 3, 5, 5])]

def node12Piece46Input : SectorVector := [(0, node12Piece46Input_sector0)]
def node12Piece46Output_sector0_chunk0 : RawPoly ℕ := [(3584/5, [1, 1, 1, 1, 3, 3, 5, 5]), (5376/5, [1, 1, 1, 2, 2, 3, 5, 5]), (21504, [1, 1, 1, 3, 5, 9]), (32256/5, [1, 1, 1, 5, 5, 7]), (43008, [1, 1, 2, 3, 5, 8]), (64512/5, [1, 1, 2, 5, 5, 6]), (43008, [1, 1, 3, 3, 5, 7]), (43008, [1, 1, 3, 4, 5, 6]), (172032/5, [1, 1, 3, 5, 5, 5]), (107520, [1, 1, 3, 15]), (32256/5, [1, 1, 4, 4, 5, 5]), (129024, [1, 1, 5, 13]), (21504, [1, 2, 2, 3, 5, 7]), (32256/5, [1, 2, 2, 5, 5, 5]), (43008, [1, 2, 3, 3, 5, 6]), (303744/5, [1, 2, 3, 4, 5, 5]), (107520, [1, 2, 3, 14]), (129024, [1, 2, 5, 12]), (132608/5, [1, 3, 3, 3, 5, 5]), (21504, [1, 3, 3, 4, 4, 5]), (107520, [1, 3, 3, 13]), (107520, [1, 3, 4, 12]), (-279552, [1, 3, 5, 11]), (107520, [1, 3, 6, 10])]

def node12Piece46Output_sector0_chunk1 : RawPoly ℕ := [(107520, [1, 3, 7, 9]), (53760, [1, 3, 8, 8]), (129024, [1, 4, 5, 10]), (247296/5, [1, 5, 5, 9]), (129024, [1, 5, 6, 8]), (64512, [1, 5, 7, 7]), (322560, [1, 19]), (10752/5, [2, 2, 3, 3, 5, 5]), (43008, [2, 3, 5, 10]), (64512/5, [2, 5, 5, 8]), (43008, [3, 3, 5, 9]), (43008, [3, 4, 5, 8]), (43008, [3, 5, 5, 7]), (21504, [3, 5, 6, 6]), (107520, [3, 17]), (64512/5, [4, 5, 5, 6]), (32256/5, [5, 5, 5, 5]), (129024, [5, 15])]

def node12Piece46Output_sector0 : RawPoly ℕ := [node12Piece46Output_sector0_chunk0, node12Piece46Output_sector0_chunk1].flatten

def node12Piece46Output : SectorVector := [(0, node12Piece46Output_sector0)]

def node12Piece46UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 5, 5])]

def node12Piece46UnitInput_sector0 : RawPoly ℕ := [node12Piece46UnitInput_sector0_chunk0].flatten

def node12Piece46UnitInput : SectorVector := [(0, node12Piece46UnitInput_sector0)]

def node12Piece46UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 3, 5, 5]), (6, [1, 1, 1, 2, 2, 3, 5, 5]), (120, [1, 1, 1, 3, 5, 9]), (36, [1, 1, 1, 5, 5, 7]), (240, [1, 1, 2, 3, 5, 8]), (72, [1, 1, 2, 5, 5, 6]), (240, [1, 1, 3, 3, 5, 7]), (240, [1, 1, 3, 4, 5, 6]), (192, [1, 1, 3, 5, 5, 5]), (600, [1, 1, 3, 15]), (36, [1, 1, 4, 4, 5, 5]), (720, [1, 1, 5, 13]), (120, [1, 2, 2, 3, 5, 7]), (36, [1, 2, 2, 5, 5, 5]), (240, [1, 2, 3, 3, 5, 6]), (339, [1, 2, 3, 4, 5, 5]), (600, [1, 2, 3, 14]), (720, [1, 2, 5, 12]), (148, [1, 3, 3, 3, 5, 5]), (120, [1, 3, 3, 4, 4, 5]), (600, [1, 3, 3, 13]), (600, [1, 3, 4, 12]), (-1560, [1, 3, 5, 11]), (600, [1, 3, 6, 10])]

def node12Piece46UnitOutput_sector0_chunk1 : RawPoly ℕ := [(600, [1, 3, 7, 9]), (300, [1, 3, 8, 8]), (720, [1, 4, 5, 10]), (276, [1, 5, 5, 9]), (720, [1, 5, 6, 8]), (360, [1, 5, 7, 7]), (1800, [1, 19]), (12, [2, 2, 3, 3, 5, 5]), (240, [2, 3, 5, 10]), (72, [2, 5, 5, 8]), (240, [3, 3, 5, 9]), (240, [3, 4, 5, 8]), (240, [3, 5, 5, 7]), (120, [3, 5, 6, 6]), (600, [3, 17]), (72, [4, 5, 5, 6]), (36, [5, 5, 5, 5]), (720, [5, 15])]

def node12Piece46UnitOutput_sector0 : RawPoly ℕ := [node12Piece46UnitOutput_sector0_chunk0, node12Piece46UnitOutput_sector0_chunk1].flatten

def node12Piece46UnitOutput : SectorVector := [(0, node12Piece46UnitOutput_sector0)]

theorem node12Piece46_check : VectorCertificate (neutralBoundS JR (-3) node12Piece46UnitInput) node12Piece46UnitOutput := by decide +kernel

theorem node12Piece46_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece46Input) = evaluate node12Piece46Output :=
  mode_of_scaled _ _ (896/5) node12Piece46UnitInput node12Piece46UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece46_check)

def node12Piece47Input_sector0 : RawPoly ℕ := [(-120, [1, 4, 4, 5])]

def node12Piece47Input : SectorVector := [(0, node12Piece47Input_sector0)]
def node12Piece47Output_sector0_chunk0 : RawPoly ℕ := [(-480, [1, 1, 1, 1, 3, 4, 4, 5]), (-720, [1, 1, 1, 2, 2, 4, 4, 5]), (-7200, [1, 1, 1, 4, 4, 9]), (-11520, [1, 1, 1, 4, 5, 8]), (-14400, [1, 1, 2, 4, 4, 8]), (-23040, [1, 1, 2, 4, 5, 7]), (-14400, [1, 1, 3, 4, 4, 7]), (-23040, [1, 1, 3, 4, 5, 6]), (-14400, [1, 1, 4, 4, 4, 6]), (-30240, [1, 1, 4, 4, 5, 5]), (-115200, [1, 1, 4, 14]), (-46080, [1, 1, 5, 13]), (-7200, [1, 2, 2, 4, 4, 7]), (-11520, [1, 2, 2, 4, 5, 6]), (-14400, [1, 2, 3, 4, 4, 6]), (-23040, [1, 2, 3, 4, 5, 5]), (-29160, [1, 2, 4, 4, 4, 5]), (-115200, [1, 2, 4, 13]), (-46080, [1, 2, 5, 12]), (-20640, [1, 3, 3, 4, 4, 5]), (-7200, [1, 3, 4, 4, 4, 4]), (-115200, [1, 3, 4, 12]), (-46080, [1, 3, 5, 11]), (57600, [1, 4, 4, 11])]

def node12Piece47Output_sector0_chunk1 : RawPoly ℕ := [(43200, [1, 4, 5, 10]), (-115200, [1, 4, 6, 9]), (-115200, [1, 4, 7, 8]), (-46080, [1, 5, 5, 9]), (-46080, [1, 5, 6, 8]), (-23040, [1, 5, 7, 7]), (-230400, [1, 19]), (-1440, [2, 2, 3, 4, 4, 5]), (-14400, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-14400, [3, 4, 4, 9]), (-23040, [3, 4, 5, 8]), (-14400, [4, 4, 4, 8]), (-28800, [4, 4, 5, 7]), (-7200, [4, 4, 6, 6]), (-23040, [4, 5, 5, 6]), (-115200, [4, 16]), (-46080, [5, 15])]

def node12Piece47Output_sector0 : RawPoly ℕ := [node12Piece47Output_sector0_chunk0, node12Piece47Output_sector0_chunk1].flatten

def node12Piece47Output : SectorVector := [(0, node12Piece47Output_sector0)]

def node12Piece47UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 4, 5])]

def node12Piece47UnitInput_sector0 : RawPoly ℕ := [node12Piece47UnitInput_sector0_chunk0].flatten

def node12Piece47UnitInput : SectorVector := [(0, node12Piece47UnitInput_sector0)]

def node12Piece47UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 4, 4, 5]), (6, [1, 1, 1, 2, 2, 4, 4, 5]), (60, [1, 1, 1, 4, 4, 9]), (96, [1, 1, 1, 4, 5, 8]), (120, [1, 1, 2, 4, 4, 8]), (192, [1, 1, 2, 4, 5, 7]), (120, [1, 1, 3, 4, 4, 7]), (192, [1, 1, 3, 4, 5, 6]), (120, [1, 1, 4, 4, 4, 6]), (252, [1, 1, 4, 4, 5, 5]), (960, [1, 1, 4, 14]), (384, [1, 1, 5, 13]), (60, [1, 2, 2, 4, 4, 7]), (96, [1, 2, 2, 4, 5, 6]), (120, [1, 2, 3, 4, 4, 6]), (192, [1, 2, 3, 4, 5, 5]), (243, [1, 2, 4, 4, 4, 5]), (960, [1, 2, 4, 13]), (384, [1, 2, 5, 12]), (172, [1, 3, 3, 4, 4, 5]), (60, [1, 3, 4, 4, 4, 4]), (960, [1, 3, 4, 12]), (384, [1, 3, 5, 11]), (-480, [1, 4, 4, 11])]

def node12Piece47UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-360, [1, 4, 5, 10]), (960, [1, 4, 6, 9]), (960, [1, 4, 7, 8]), (384, [1, 5, 5, 9]), (384, [1, 5, 6, 8]), (192, [1, 5, 7, 7]), (1920, [1, 19]), (12, [2, 2, 3, 4, 4, 5]), (120, [2, 4, 4, 10]), (192, [2, 4, 5, 9]), (120, [3, 4, 4, 9]), (192, [3, 4, 5, 8]), (120, [4, 4, 4, 8]), (240, [4, 4, 5, 7]), (60, [4, 4, 6, 6]), (192, [4, 5, 5, 6]), (960, [4, 16]), (384, [5, 15])]

def node12Piece47UnitOutput_sector0 : RawPoly ℕ := [node12Piece47UnitOutput_sector0_chunk0, node12Piece47UnitOutput_sector0_chunk1].flatten

def node12Piece47UnitOutput : SectorVector := [(0, node12Piece47UnitOutput_sector0)]

theorem node12Piece47_check : VectorCertificate (neutralBoundS JR (-3) node12Piece47UnitInput) node12Piece47UnitOutput := by decide +kernel

theorem node12Piece47_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-3)
    (evaluate node12Piece47Input) = evaluate node12Piece47Output :=
  mode_of_scaled _ _ (-120) node12Piece47UnitInput node12Piece47UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node12Piece47_check)

end VOA.Classification.COne.OrbC2h
