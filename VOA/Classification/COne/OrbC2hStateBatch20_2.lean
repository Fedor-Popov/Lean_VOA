import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch20_0
import VOA.Classification.COne.OrbC2hStateNode16
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node20Piece32Input_sector0 : RawPoly ℕ := [(320, [1, 3, 3, 6])]

def node20Piece32Input : SectorVector := [(0, node20Piece32Input_sector0)]
def node20Piece32Output_sector0_chunk0 : RawPoly ℕ := [(1280, [1, 1, 1, 1, 3, 3, 4, 6]), (3840, [1, 1, 1, 2, 3, 3, 3, 6]), (23040, [1, 1, 1, 3, 3, 11]), (23040, [1, 1, 1, 3, 6, 8]), (1280, [1, 1, 2, 2, 2, 3, 3, 6]), (46080, [1, 1, 2, 3, 3, 10]), (46080, [1, 1, 2, 3, 6, 7]), (46080, [1, 1, 3, 3, 3, 9]), (46080, [1, 1, 3, 3, 4, 8]), (46080, [1, 1, 3, 3, 5, 7]), (66560, [1, 1, 3, 3, 6, 6]), (46080, [1, 1, 3, 4, 5, 6]), (276480, [1, 1, 3, 15]), (69120, [1, 1, 6, 12]), (23040, [1, 2, 2, 3, 3, 9]), (23040, [1, 2, 2, 3, 6, 6]), (46080, [1, 2, 3, 3, 3, 8]), (46080, [1, 2, 3, 3, 4, 7]), (99840, [1, 2, 3, 3, 5, 6]), (23040, [1, 2, 3, 4, 4, 6]), (276480, [1, 2, 3, 14]), (69120, [1, 2, 6, 11]), (23040, [1, 3, 3, 3, 3, 7]), (80000, [1, 3, 3, 3, 4, 6])]

def node20Piece32Output_sector0_chunk1 : RawPoly ℕ := [(23040, [1, 3, 3, 3, 5, 5]), (23040, [1, 3, 3, 4, 4, 5]), (-522240, [1, 3, 3, 13]), (276480, [1, 3, 4, 12]), (276480, [1, 3, 5, 11]), (7680, [1, 3, 6, 10]), (276480, [1, 3, 7, 9]), (138240, [1, 3, 8, 8]), (69120, [1, 4, 6, 9]), (69120, [1, 5, 6, 8]), (69120, [1, 6, 6, 7]), (414720, [1, 19]), (3840, [2, 2, 3, 3, 4, 6]), (3840, [2, 3, 3, 3, 3, 6]), (46080, [2, 3, 3, 12]), (46080, [2, 3, 6, 9]), (46080, [3, 3, 3, 11]), (46080, [3, 3, 4, 10]), (46080, [3, 3, 5, 9]), (63360, [3, 3, 6, 8]), (23040, [3, 3, 7, 7]), (46080, [3, 4, 6, 7]), (46080, [3, 5, 6, 6]), (276480, [3, 17])]

def node20Piece32Output_sector0_chunk2 : RawPoly ℕ := [(69120, [6, 14])]

def node20Piece32Output_sector0 : RawPoly ℕ := [node20Piece32Output_sector0_chunk0, node20Piece32Output_sector0_chunk1, node20Piece32Output_sector0_chunk2].flatten

def node20Piece32Output : SectorVector := [(0, node20Piece32Output_sector0)]

def node20Piece32UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 3, 6])]

def node20Piece32UnitInput_sector0 : RawPoly ℕ := [node20Piece32UnitInput_sector0_chunk0].flatten

def node20Piece32UnitInput : SectorVector := [(0, node20Piece32UnitInput_sector0)]

def node20Piece32UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 3, 4, 6]), (12, [1, 1, 1, 2, 3, 3, 3, 6]), (72, [1, 1, 1, 3, 3, 11]), (72, [1, 1, 1, 3, 6, 8]), (4, [1, 1, 2, 2, 2, 3, 3, 6]), (144, [1, 1, 2, 3, 3, 10]), (144, [1, 1, 2, 3, 6, 7]), (144, [1, 1, 3, 3, 3, 9]), (144, [1, 1, 3, 3, 4, 8]), (144, [1, 1, 3, 3, 5, 7]), (208, [1, 1, 3, 3, 6, 6]), (144, [1, 1, 3, 4, 5, 6]), (864, [1, 1, 3, 15]), (216, [1, 1, 6, 12]), (72, [1, 2, 2, 3, 3, 9]), (72, [1, 2, 2, 3, 6, 6]), (144, [1, 2, 3, 3, 3, 8]), (144, [1, 2, 3, 3, 4, 7]), (312, [1, 2, 3, 3, 5, 6]), (72, [1, 2, 3, 4, 4, 6]), (864, [1, 2, 3, 14]), (216, [1, 2, 6, 11]), (72, [1, 3, 3, 3, 3, 7]), (250, [1, 3, 3, 3, 4, 6])]

def node20Piece32UnitOutput_sector0_chunk1 : RawPoly ℕ := [(72, [1, 3, 3, 3, 5, 5]), (72, [1, 3, 3, 4, 4, 5]), (-1632, [1, 3, 3, 13]), (864, [1, 3, 4, 12]), (864, [1, 3, 5, 11]), (24, [1, 3, 6, 10]), (864, [1, 3, 7, 9]), (432, [1, 3, 8, 8]), (216, [1, 4, 6, 9]), (216, [1, 5, 6, 8]), (216, [1, 6, 6, 7]), (1296, [1, 19]), (12, [2, 2, 3, 3, 4, 6]), (12, [2, 3, 3, 3, 3, 6]), (144, [2, 3, 3, 12]), (144, [2, 3, 6, 9]), (144, [3, 3, 3, 11]), (144, [3, 3, 4, 10]), (144, [3, 3, 5, 9]), (198, [3, 3, 6, 8]), (72, [3, 3, 7, 7]), (144, [3, 4, 6, 7]), (144, [3, 5, 6, 6]), (864, [3, 17])]

def node20Piece32UnitOutput_sector0_chunk2 : RawPoly ℕ := [(216, [6, 14])]

def node20Piece32UnitOutput_sector0 : RawPoly ℕ := [node20Piece32UnitOutput_sector0_chunk0, node20Piece32UnitOutput_sector0_chunk1, node20Piece32UnitOutput_sector0_chunk2].flatten

def node20Piece32UnitOutput : SectorVector := [(0, node20Piece32UnitOutput_sector0)]

theorem node20Piece32_check : VectorCertificate (neutralBoundS JR (-4) node20Piece32UnitInput) node20Piece32UnitOutput := by decide +kernel

theorem node20Piece32_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece32Input) = evaluate node20Piece32Output :=
  mode_of_scaled _ _ (320) node20Piece32UnitInput node20Piece32UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece32_check)

def node20Piece33Input_sector0 : RawPoly ℕ := [(160, [1, 3, 4, 5])]

def node20Piece33Input : SectorVector := [(0, node20Piece33Input_sector0)]
def node20Piece33Output_sector0_chunk0 : RawPoly ℕ := [(640, [1, 1, 1, 1, 3, 4, 4, 5]), (1920, [1, 1, 1, 2, 3, 3, 4, 5]), (9600, [1, 1, 1, 3, 4, 10]), (7680, [1, 1, 1, 3, 5, 9]), (5760, [1, 1, 1, 4, 5, 8]), (640, [1, 1, 2, 2, 2, 3, 4, 5]), (19200, [1, 1, 2, 3, 4, 9]), (15360, [1, 1, 2, 3, 5, 8]), (11520, [1, 1, 2, 4, 5, 7]), (19200, [1, 1, 3, 3, 4, 8]), (15360, [1, 1, 3, 3, 5, 7]), (19200, [1, 1, 3, 4, 4, 7]), (44800, [1, 1, 3, 4, 5, 6]), (7680, [1, 1, 3, 5, 5, 5]), (76800, [1, 1, 3, 15]), (11520, [1, 1, 4, 4, 5, 5]), (57600, [1, 1, 4, 14]), (46080, [1, 1, 5, 13]), (9600, [1, 2, 2, 3, 4, 8]), (7680, [1, 2, 2, 3, 5, 7]), (5760, [1, 2, 2, 4, 5, 6]), (19200, [1, 2, 3, 3, 4, 7]), (15360, [1, 2, 3, 3, 5, 6]), (19200, [1, 2, 3, 4, 4, 6])]

def node20Piece33Output_sector0_chunk1 : RawPoly ℕ := [(40320, [1, 2, 3, 4, 5, 5]), (76800, [1, 2, 3, 14]), (5760, [1, 2, 4, 4, 4, 5]), (57600, [1, 2, 4, 13]), (46080, [1, 2, 5, 12]), (9600, [1, 3, 3, 3, 4, 6]), (7680, [1, 3, 3, 3, 5, 5]), (38080, [1, 3, 3, 4, 4, 5]), (76800, [1, 3, 3, 13]), (3200, [1, 3, 4, 4, 4, 4]), (-126400, [1, 3, 4, 12]), (-34560, [1, 3, 5, 11]), (76800, [1, 3, 6, 10]), (76800, [1, 3, 7, 9]), (38400, [1, 3, 8, 8]), (57600, [1, 4, 4, 11]), (19200, [1, 4, 5, 10]), (57600, [1, 4, 6, 9]), (57600, [1, 4, 7, 8]), (46080, [1, 5, 5, 9]), (46080, [1, 5, 6, 8]), (23040, [1, 5, 7, 7]), (230400, [1, 19]), (1920, [2, 2, 3, 4, 4, 5])]

def node20Piece33Output_sector0_chunk2 : RawPoly ℕ := [(1920, [2, 3, 3, 3, 4, 5]), (19200, [2, 3, 4, 11]), (15360, [2, 3, 5, 10]), (11520, [2, 4, 5, 9]), (19200, [3, 3, 4, 10]), (15360, [3, 3, 5, 9]), (19200, [3, 4, 4, 9]), (31680, [3, 4, 5, 8]), (19200, [3, 4, 6, 7]), (15360, [3, 5, 5, 7]), (7680, [3, 5, 6, 6]), (76800, [3, 17]), (11520, [4, 4, 5, 7]), (11520, [4, 5, 5, 6]), (57600, [4, 16]), (46080, [5, 15])]

def node20Piece33Output_sector0 : RawPoly ℕ := [node20Piece33Output_sector0_chunk0, node20Piece33Output_sector0_chunk1, node20Piece33Output_sector0_chunk2].flatten

def node20Piece33Output : SectorVector := [(0, node20Piece33Output_sector0)]

def node20Piece33UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 3, 4, 5])]

def node20Piece33UnitInput_sector0 : RawPoly ℕ := [node20Piece33UnitInput_sector0_chunk0].flatten

def node20Piece33UnitInput : SectorVector := [(0, node20Piece33UnitInput_sector0)]

def node20Piece33UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 3, 4, 4, 5]), (12, [1, 1, 1, 2, 3, 3, 4, 5]), (60, [1, 1, 1, 3, 4, 10]), (48, [1, 1, 1, 3, 5, 9]), (36, [1, 1, 1, 4, 5, 8]), (4, [1, 1, 2, 2, 2, 3, 4, 5]), (120, [1, 1, 2, 3, 4, 9]), (96, [1, 1, 2, 3, 5, 8]), (72, [1, 1, 2, 4, 5, 7]), (120, [1, 1, 3, 3, 4, 8]), (96, [1, 1, 3, 3, 5, 7]), (120, [1, 1, 3, 4, 4, 7]), (280, [1, 1, 3, 4, 5, 6]), (48, [1, 1, 3, 5, 5, 5]), (480, [1, 1, 3, 15]), (72, [1, 1, 4, 4, 5, 5]), (360, [1, 1, 4, 14]), (288, [1, 1, 5, 13]), (60, [1, 2, 2, 3, 4, 8]), (48, [1, 2, 2, 3, 5, 7]), (36, [1, 2, 2, 4, 5, 6]), (120, [1, 2, 3, 3, 4, 7]), (96, [1, 2, 3, 3, 5, 6]), (120, [1, 2, 3, 4, 4, 6])]

def node20Piece33UnitOutput_sector0_chunk1 : RawPoly ℕ := [(252, [1, 2, 3, 4, 5, 5]), (480, [1, 2, 3, 14]), (36, [1, 2, 4, 4, 4, 5]), (360, [1, 2, 4, 13]), (288, [1, 2, 5, 12]), (60, [1, 3, 3, 3, 4, 6]), (48, [1, 3, 3, 3, 5, 5]), (238, [1, 3, 3, 4, 4, 5]), (480, [1, 3, 3, 13]), (20, [1, 3, 4, 4, 4, 4]), (-790, [1, 3, 4, 12]), (-216, [1, 3, 5, 11]), (480, [1, 3, 6, 10]), (480, [1, 3, 7, 9]), (240, [1, 3, 8, 8]), (360, [1, 4, 4, 11]), (120, [1, 4, 5, 10]), (360, [1, 4, 6, 9]), (360, [1, 4, 7, 8]), (288, [1, 5, 5, 9]), (288, [1, 5, 6, 8]), (144, [1, 5, 7, 7]), (1440, [1, 19]), (12, [2, 2, 3, 4, 4, 5])]

def node20Piece33UnitOutput_sector0_chunk2 : RawPoly ℕ := [(12, [2, 3, 3, 3, 4, 5]), (120, [2, 3, 4, 11]), (96, [2, 3, 5, 10]), (72, [2, 4, 5, 9]), (120, [3, 3, 4, 10]), (96, [3, 3, 5, 9]), (120, [3, 4, 4, 9]), (198, [3, 4, 5, 8]), (120, [3, 4, 6, 7]), (96, [3, 5, 5, 7]), (48, [3, 5, 6, 6]), (480, [3, 17]), (72, [4, 4, 5, 7]), (72, [4, 5, 5, 6]), (360, [4, 16]), (288, [5, 15])]

def node20Piece33UnitOutput_sector0 : RawPoly ℕ := [node20Piece33UnitOutput_sector0_chunk0, node20Piece33UnitOutput_sector0_chunk1, node20Piece33UnitOutput_sector0_chunk2].flatten

def node20Piece33UnitOutput : SectorVector := [(0, node20Piece33UnitOutput_sector0)]

theorem node20Piece33_check : VectorCertificate (neutralBoundS JR (-4) node20Piece33UnitInput) node20Piece33UnitOutput := by decide +kernel

theorem node20Piece33_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece33Input) = evaluate node20Piece33Output :=
  mode_of_scaled _ _ (160) node20Piece33UnitInput node20Piece33UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece33_check)

def node20Piece34Input_sector0 : RawPoly ℕ := [(-95, [1, 4, 4, 4])]

def node20Piece34Input : SectorVector := [(0, node20Piece34Input_sector0)]
def node20Piece34Output_sector0_chunk0 : RawPoly ℕ := [(-380, [1, 1, 1, 1, 4, 4, 4, 4]), (-1140, [1, 1, 1, 2, 3, 4, 4, 4]), (-13680, [1, 1, 1, 4, 4, 9]), (-380, [1, 1, 2, 2, 2, 4, 4, 4]), (-27360, [1, 1, 2, 4, 4, 8]), (-27360, [1, 1, 3, 4, 4, 7]), (-26600, [1, 1, 4, 4, 4, 6]), (-13680, [1, 1, 4, 4, 5, 5]), (-109440, [1, 1, 4, 14]), (-13680, [1, 2, 2, 4, 4, 7]), (-27360, [1, 2, 3, 4, 4, 6]), (-29640, [1, 2, 4, 4, 4, 5]), (-109440, [1, 2, 4, 13]), (-13680, [1, 3, 3, 4, 4, 5]), (-16910, [1, 3, 4, 4, 4, 4]), (-109440, [1, 3, 4, 12]), (171000, [1, 4, 4, 11]), (-109440, [1, 4, 5, 10]), (-109440, [1, 4, 6, 9]), (-109440, [1, 4, 7, 8]), (-145920, [1, 19]), (-1140, [2, 2, 4, 4, 4, 4]), (-1140, [2, 3, 3, 4, 4, 4]), (-27360, [2, 4, 4, 10])]

def node20Piece34Output_sector0_chunk1 : RawPoly ℕ := [(-27360, [3, 4, 4, 9]), (-18810, [4, 4, 4, 8]), (-27360, [4, 4, 5, 7]), (-13680, [4, 4, 6, 6]), (-109440, [4, 16])]

def node20Piece34Output_sector0 : RawPoly ℕ := [node20Piece34Output_sector0_chunk0, node20Piece34Output_sector0_chunk1].flatten

def node20Piece34Output : SectorVector := [(0, node20Piece34Output_sector0)]

def node20Piece34UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 4, 4, 4])]

def node20Piece34UnitInput_sector0 : RawPoly ℕ := [node20Piece34UnitInput_sector0_chunk0].flatten

def node20Piece34UnitInput : SectorVector := [(0, node20Piece34UnitInput_sector0)]

def node20Piece34UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 4, 4, 4, 4]), (12, [1, 1, 1, 2, 3, 4, 4, 4]), (144, [1, 1, 1, 4, 4, 9]), (4, [1, 1, 2, 2, 2, 4, 4, 4]), (288, [1, 1, 2, 4, 4, 8]), (288, [1, 1, 3, 4, 4, 7]), (280, [1, 1, 4, 4, 4, 6]), (144, [1, 1, 4, 4, 5, 5]), (1152, [1, 1, 4, 14]), (144, [1, 2, 2, 4, 4, 7]), (288, [1, 2, 3, 4, 4, 6]), (312, [1, 2, 4, 4, 4, 5]), (1152, [1, 2, 4, 13]), (144, [1, 3, 3, 4, 4, 5]), (178, [1, 3, 4, 4, 4, 4]), (1152, [1, 3, 4, 12]), (-1800, [1, 4, 4, 11]), (1152, [1, 4, 5, 10]), (1152, [1, 4, 6, 9]), (1152, [1, 4, 7, 8]), (1536, [1, 19]), (12, [2, 2, 4, 4, 4, 4]), (12, [2, 3, 3, 4, 4, 4]), (288, [2, 4, 4, 10])]

def node20Piece34UnitOutput_sector0_chunk1 : RawPoly ℕ := [(288, [3, 4, 4, 9]), (198, [4, 4, 4, 8]), (288, [4, 4, 5, 7]), (144, [4, 4, 6, 6]), (1152, [4, 16])]

def node20Piece34UnitOutput_sector0 : RawPoly ℕ := [node20Piece34UnitOutput_sector0_chunk0, node20Piece34UnitOutput_sector0_chunk1].flatten

def node20Piece34UnitOutput : SectorVector := [(0, node20Piece34UnitOutput_sector0)]

theorem node20Piece34_check : VectorCertificate (neutralBoundS JR (-4) node20Piece34UnitInput) node20Piece34UnitOutput := by decide +kernel

theorem node20Piece34_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece34Input) = evaluate node20Piece34Output :=
  mode_of_scaled _ _ (-95) node20Piece34UnitInput node20Piece34UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece34_check)

def node20Piece35Input_sector0 : RawPoly ℕ := [(40, [1, 12])]

def node20Piece35Input : SectorVector := [(0, node20Piece35Input_sector0)]
def node20Piece35Output_sector0_chunk0 : RawPoly ℕ := [(160, [1, 1, 1, 1, 4, 12]), (480, [1, 1, 1, 2, 3, 12]), (5760, [1, 1, 1, 17]), (160, [1, 1, 2, 2, 2, 12]), (11520, [1, 1, 2, 16]), (11520, [1, 1, 3, 15]), (11520, [1, 1, 4, 14]), (11520, [1, 1, 5, 13]), (11200, [1, 1, 6, 12]), (11520, [1, 1, 7, 11]), (11520, [1, 1, 8, 10]), (5760, [1, 1, 9, 9]), (5760, [1, 2, 2, 15]), (11520, [1, 2, 3, 14]), (11520, [1, 2, 4, 13]), (12480, [1, 2, 5, 12]), (11520, [1, 2, 6, 11]), (11520, [1, 2, 7, 10]), (11520, [1, 2, 8, 9]), (5760, [1, 3, 3, 13]), (12880, [1, 3, 4, 12]), (11520, [1, 3, 5, 11]), (11520, [1, 3, 6, 10]), (11520, [1, 3, 7, 9])]

def node20Piece35Output_sector0_chunk1 : RawPoly ℕ := [(5760, [1, 3, 8, 8]), (5760, [1, 4, 4, 11]), (11520, [1, 4, 5, 10]), (11520, [1, 4, 6, 9]), (11520, [1, 4, 7, 8]), (5760, [1, 5, 5, 9]), (11520, [1, 5, 6, 8]), (5760, [1, 5, 7, 7]), (5760, [1, 6, 6, 7]), (-559680, [1, 19]), (480, [2, 2, 4, 12]), (480, [2, 3, 3, 12]), (11520, [2, 18]), (11520, [3, 17]), (11520, [4, 16]), (11520, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (7920, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node20Piece35Output_sector0 : RawPoly ℕ := [node20Piece35Output_sector0_chunk0, node20Piece35Output_sector0_chunk1].flatten

def node20Piece35Output : SectorVector := [(0, node20Piece35Output_sector0)]

def node20Piece35UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [1, 12])]

def node20Piece35UnitInput_sector0 : RawPoly ℕ := [node20Piece35UnitInput_sector0_chunk0].flatten

def node20Piece35UnitInput : SectorVector := [(0, node20Piece35UnitInput_sector0)]

def node20Piece35UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 1, 4, 12]), (12, [1, 1, 1, 2, 3, 12]), (144, [1, 1, 1, 17]), (4, [1, 1, 2, 2, 2, 12]), (288, [1, 1, 2, 16]), (288, [1, 1, 3, 15]), (288, [1, 1, 4, 14]), (288, [1, 1, 5, 13]), (280, [1, 1, 6, 12]), (288, [1, 1, 7, 11]), (288, [1, 1, 8, 10]), (144, [1, 1, 9, 9]), (144, [1, 2, 2, 15]), (288, [1, 2, 3, 14]), (288, [1, 2, 4, 13]), (312, [1, 2, 5, 12]), (288, [1, 2, 6, 11]), (288, [1, 2, 7, 10]), (288, [1, 2, 8, 9]), (144, [1, 3, 3, 13]), (322, [1, 3, 4, 12]), (288, [1, 3, 5, 11]), (288, [1, 3, 6, 10]), (288, [1, 3, 7, 9])]

def node20Piece35UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [1, 3, 8, 8]), (144, [1, 4, 4, 11]), (288, [1, 4, 5, 10]), (288, [1, 4, 6, 9]), (288, [1, 4, 7, 8]), (144, [1, 5, 5, 9]), (288, [1, 5, 6, 8]), (144, [1, 5, 7, 7]), (144, [1, 6, 6, 7]), (-13992, [1, 19]), (12, [2, 2, 4, 12]), (12, [2, 3, 3, 12]), (288, [2, 18]), (288, [3, 17]), (288, [4, 16]), (288, [5, 15]), (288, [6, 14]), (288, [7, 13]), (198, [8, 12]), (288, [9, 11]), (144, [10, 10])]

def node20Piece35UnitOutput_sector0 : RawPoly ℕ := [node20Piece35UnitOutput_sector0_chunk0, node20Piece35UnitOutput_sector0_chunk1].flatten

def node20Piece35UnitOutput : SectorVector := [(0, node20Piece35UnitOutput_sector0)]

theorem node20Piece35_check : VectorCertificate (neutralBoundS JR (-4) node20Piece35UnitInput) node20Piece35UnitOutput := by decide +kernel

theorem node20Piece35_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece35Input) = evaluate node20Piece35Output :=
  mode_of_scaled _ _ (40) node20Piece35UnitInput node20Piece35UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece35_check)

def node20Piece36Input_sector0 : RawPoly ℕ := [(-84, [2, 2, 2, 2, 2, 3])]

def node20Piece36Input : SectorVector := [(0, node20Piece36Input_sector0)]
def node20Piece36Output_sector0_chunk0 : RawPoly ℕ := [(-336, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (-1008, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-3024, [1, 1, 2, 2, 2, 2, 2, 8]), (-10080, [1, 1, 2, 2, 2, 2, 3, 7]), (-336, [1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-6048, [1, 2, 2, 2, 2, 2, 2, 7]), (-24528, [1, 2, 2, 2, 2, 2, 3, 6]), (-6048, [1, 2, 2, 2, 2, 2, 4, 5]), (-20160, [1, 2, 2, 2, 2, 3, 3, 5]), (-10080, [1, 2, 2, 2, 2, 3, 4, 4]), (-60480, [1, 2, 2, 2, 2, 11]), (-80640, [1, 2, 2, 2, 3, 10]), (-3024, [2, 2, 2, 2, 2, 2, 2, 6]), (-16128, [2, 2, 2, 2, 2, 2, 3, 5]), (-3024, [2, 2, 2, 2, 2, 2, 4, 4]), (-24024, [2, 2, 2, 2, 2, 3, 3, 4]), (-10080, [2, 2, 2, 2, 2, 10]), (-3360, [2, 2, 2, 2, 3, 3, 3, 3]), (-23520, [2, 2, 2, 2, 3, 9]), (-60480, [2, 2, 2, 2, 4, 8]), (-60480, [2, 2, 2, 2, 5, 7]), (-30240, [2, 2, 2, 2, 6, 6]), (-80640, [2, 2, 2, 3, 3, 8]), (-80640, [2, 2, 2, 3, 4, 7])]

def node20Piece36Output_sector0_chunk1 : RawPoly ℕ := [(-80640, [2, 2, 2, 3, 5, 6]), (-241920, [2, 2, 2, 14]), (-161280, [2, 2, 3, 13])]

def node20Piece36Output_sector0 : RawPoly ℕ := [node20Piece36Output_sector0_chunk0, node20Piece36Output_sector0_chunk1].flatten

def node20Piece36Output : SectorVector := [(0, node20Piece36Output_sector0)]

def node20Piece36UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 2, 2, 3])]

def node20Piece36UnitInput_sector0 : RawPoly ℕ := [node20Piece36UnitInput_sector0_chunk0].flatten

def node20Piece36UnitInput : SectorVector := [(0, node20Piece36UnitInput_sector0)]

def node20Piece36UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (12, [1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (36, [1, 1, 2, 2, 2, 2, 2, 8]), (120, [1, 1, 2, 2, 2, 2, 3, 7]), (4, [1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (72, [1, 2, 2, 2, 2, 2, 2, 7]), (292, [1, 2, 2, 2, 2, 2, 3, 6]), (72, [1, 2, 2, 2, 2, 2, 4, 5]), (240, [1, 2, 2, 2, 2, 3, 3, 5]), (120, [1, 2, 2, 2, 2, 3, 4, 4]), (720, [1, 2, 2, 2, 2, 11]), (960, [1, 2, 2, 2, 3, 10]), (36, [2, 2, 2, 2, 2, 2, 2, 6]), (192, [2, 2, 2, 2, 2, 2, 3, 5]), (36, [2, 2, 2, 2, 2, 2, 4, 4]), (286, [2, 2, 2, 2, 2, 3, 3, 4]), (120, [2, 2, 2, 2, 2, 10]), (40, [2, 2, 2, 2, 3, 3, 3, 3]), (280, [2, 2, 2, 2, 3, 9]), (720, [2, 2, 2, 2, 4, 8]), (720, [2, 2, 2, 2, 5, 7]), (360, [2, 2, 2, 2, 6, 6]), (960, [2, 2, 2, 3, 3, 8]), (960, [2, 2, 2, 3, 4, 7])]

def node20Piece36UnitOutput_sector0_chunk1 : RawPoly ℕ := [(960, [2, 2, 2, 3, 5, 6]), (2880, [2, 2, 2, 14]), (1920, [2, 2, 3, 13])]

def node20Piece36UnitOutput_sector0 : RawPoly ℕ := [node20Piece36UnitOutput_sector0_chunk0, node20Piece36UnitOutput_sector0_chunk1].flatten

def node20Piece36UnitOutput : SectorVector := [(0, node20Piece36UnitOutput_sector0)]

theorem node20Piece36_check : VectorCertificate (neutralBoundS JR (-4) node20Piece36UnitInput) node20Piece36UnitOutput := by decide +kernel

theorem node20Piece36_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece36Input) = evaluate node20Piece36Output :=
  mode_of_scaled _ _ (-84) node20Piece36UnitInput node20Piece36UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece36_check)

def node20Piece37Input_sector0 : RawPoly ℕ := [(-1440/7, [2, 2, 2, 7])]

def node20Piece37Input : SectorVector := [(0, node20Piece37Input_sector0)]
def node20Piece37Output_sector0_chunk0 : RawPoly ℕ := [(-5760/7, [1, 1, 1, 2, 2, 2, 4, 7]), (-17280/7, [1, 1, 2, 2, 2, 2, 3, 7]), (-17280, [1, 1, 2, 2, 2, 12]), (-103680/7, [1, 1, 2, 2, 7, 7]), (-5760/7, [1, 2, 2, 2, 2, 2, 2, 7]), (-34560, [1, 2, 2, 2, 2, 11]), (-34560, [1, 2, 2, 2, 3, 10]), (-34560, [1, 2, 2, 2, 4, 9]), (-34560, [1, 2, 2, 2, 5, 8]), (-420480/7, [1, 2, 2, 2, 6, 7]), (-207360/7, [1, 2, 2, 3, 5, 7]), (-103680/7, [1, 2, 2, 4, 4, 7]), (-207360, [1, 2, 2, 15]), (-414720/7, [1, 2, 7, 10]), (-17280, [2, 2, 2, 2, 2, 10]), (-34560, [2, 2, 2, 2, 3, 9]), (-34560, [2, 2, 2, 2, 4, 8]), (-345600/7, [2, 2, 2, 2, 5, 7]), (-17280, [2, 2, 2, 2, 6, 6]), (-17280, [2, 2, 2, 3, 3, 8]), (-66240, [2, 2, 2, 3, 4, 7]), (-34560, [2, 2, 2, 3, 5, 6]), (-17280, [2, 2, 2, 4, 4, 6]), (-17280, [2, 2, 2, 4, 5, 5])]

def node20Piece37Output_sector0_chunk1 : RawPoly ℕ := [(570240, [2, 2, 2, 14]), (-34560/7, [2, 2, 3, 3, 3, 7]), (-207360, [2, 2, 3, 13]), (-207360, [2, 2, 4, 12]), (-207360, [2, 2, 5, 11]), (-207360, [2, 2, 6, 10]), (-656640/7, [2, 2, 7, 9]), (-103680, [2, 2, 8, 8]), (-414720/7, [2, 3, 7, 8]), (-414720/7, [2, 4, 7, 7]), (-414720/7, [2, 5, 6, 7]), (-414720, [2, 18]), (-276480/7, [7, 13])]

def node20Piece37Output_sector0 : RawPoly ℕ := [node20Piece37Output_sector0_chunk0, node20Piece37Output_sector0_chunk1].flatten

def node20Piece37Output : SectorVector := [(0, node20Piece37Output_sector0)]

def node20Piece37UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 2, 7])]

def node20Piece37UnitInput_sector0 : RawPoly ℕ := [node20Piece37UnitInput_sector0_chunk0].flatten

def node20Piece37UnitInput : SectorVector := [(0, node20Piece37UnitInput_sector0)]

def node20Piece37UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 2, 4, 7]), (12, [1, 1, 2, 2, 2, 2, 3, 7]), (84, [1, 1, 2, 2, 2, 12]), (72, [1, 1, 2, 2, 7, 7]), (4, [1, 2, 2, 2, 2, 2, 2, 7]), (168, [1, 2, 2, 2, 2, 11]), (168, [1, 2, 2, 2, 3, 10]), (168, [1, 2, 2, 2, 4, 9]), (168, [1, 2, 2, 2, 5, 8]), (292, [1, 2, 2, 2, 6, 7]), (144, [1, 2, 2, 3, 5, 7]), (72, [1, 2, 2, 4, 4, 7]), (1008, [1, 2, 2, 15]), (288, [1, 2, 7, 10]), (84, [2, 2, 2, 2, 2, 10]), (168, [2, 2, 2, 2, 3, 9]), (168, [2, 2, 2, 2, 4, 8]), (240, [2, 2, 2, 2, 5, 7]), (84, [2, 2, 2, 2, 6, 6]), (84, [2, 2, 2, 3, 3, 8]), (322, [2, 2, 2, 3, 4, 7]), (168, [2, 2, 2, 3, 5, 6]), (84, [2, 2, 2, 4, 4, 6]), (84, [2, 2, 2, 4, 5, 5])]

def node20Piece37UnitOutput_sector0_chunk1 : RawPoly ℕ := [(-2772, [2, 2, 2, 14]), (24, [2, 2, 3, 3, 3, 7]), (1008, [2, 2, 3, 13]), (1008, [2, 2, 4, 12]), (1008, [2, 2, 5, 11]), (1008, [2, 2, 6, 10]), (456, [2, 2, 7, 9]), (504, [2, 2, 8, 8]), (288, [2, 3, 7, 8]), (288, [2, 4, 7, 7]), (288, [2, 5, 6, 7]), (2016, [2, 18]), (192, [7, 13])]

def node20Piece37UnitOutput_sector0 : RawPoly ℕ := [node20Piece37UnitOutput_sector0_chunk0, node20Piece37UnitOutput_sector0_chunk1].flatten

def node20Piece37UnitOutput : SectorVector := [(0, node20Piece37UnitOutput_sector0)]

theorem node20Piece37_check : VectorCertificate (neutralBoundS JR (-4) node20Piece37UnitInput) node20Piece37UnitOutput := by decide +kernel

theorem node20Piece37_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece37Input) = evaluate node20Piece37Output :=
  mode_of_scaled _ _ (-1440/7) node20Piece37UnitInput node20Piece37UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece37_check)

def node20Piece38Input_sector0 : RawPoly ℕ := [(-80, [2, 2, 3, 6])]

def node20Piece38Input : SectorVector := [(0, node20Piece38Input_sector0)]
def node20Piece38Output_sector0_chunk0 : RawPoly ℕ := [(-320, [1, 1, 1, 2, 2, 3, 4, 6]), (-960, [1, 1, 2, 2, 2, 3, 3, 6]), (-5760, [1, 1, 2, 2, 3, 11]), (-2880, [1, 1, 2, 2, 6, 8]), (-3840, [1, 1, 2, 3, 6, 7]), (-320, [1, 2, 2, 2, 2, 2, 3, 6]), (-11520, [1, 2, 2, 2, 3, 10]), (-5760, [1, 2, 2, 2, 6, 7]), (-11520, [1, 2, 2, 3, 3, 9]), (-11520, [1, 2, 2, 3, 4, 8]), (-11520, [1, 2, 2, 3, 5, 7]), (-17600, [1, 2, 2, 3, 6, 6]), (-5760, [1, 2, 2, 4, 5, 6]), (-34560, [1, 2, 2, 15]), (-7680, [1, 2, 3, 3, 5, 6]), (-3840, [1, 2, 3, 4, 4, 6]), (-46080, [1, 2, 3, 14]), (-23040, [1, 2, 6, 11]), (-7680, [1, 3, 6, 10]), (-5760, [2, 2, 2, 2, 3, 9]), (-2880, [2, 2, 2, 2, 6, 6]), (-11520, [2, 2, 2, 3, 3, 8]), (-11520, [2, 2, 2, 3, 4, 7]), (-21120, [2, 2, 2, 3, 5, 6])]

def node20Piece38Output_sector0_chunk1 : RawPoly ℕ := [(-2880, [2, 2, 2, 4, 4, 6]), (-34560, [2, 2, 2, 14]), (-5760, [2, 2, 3, 3, 3, 7]), (-22880, [2, 2, 3, 3, 4, 6]), (-5760, [2, 2, 3, 3, 5, 5]), (-5760, [2, 2, 3, 4, 4, 5]), (130560, [2, 2, 3, 13]), (-34560, [2, 2, 4, 12]), (-34560, [2, 2, 5, 11]), (-9600, [2, 2, 6, 10]), (-34560, [2, 2, 7, 9]), (-17280, [2, 2, 8, 8]), (-1280, [2, 3, 3, 3, 3, 6]), (-46080, [2, 3, 3, 12]), (-46080, [2, 3, 4, 11]), (-46080, [2, 3, 5, 10]), (-32000, [2, 3, 6, 9]), (-46080, [2, 3, 7, 8]), (-23040, [2, 4, 6, 8]), (-23040, [2, 5, 6, 7]), (-11520, [2, 6, 6, 6]), (-138240, [2, 18]), (-7680, [3, 3, 6, 8]), (-7680, [3, 4, 6, 7])]

def node20Piece38Output_sector0_chunk2 : RawPoly ℕ := [(-7680, [3, 5, 6, 6]), (-46080, [3, 17]), (-23040, [6, 14])]

def node20Piece38Output_sector0 : RawPoly ℕ := [node20Piece38Output_sector0_chunk0, node20Piece38Output_sector0_chunk1, node20Piece38Output_sector0_chunk2].flatten

def node20Piece38Output : SectorVector := [(0, node20Piece38Output_sector0)]

def node20Piece38UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 6])]

def node20Piece38UnitInput_sector0 : RawPoly ℕ := [node20Piece38UnitInput_sector0_chunk0].flatten

def node20Piece38UnitInput : SectorVector := [(0, node20Piece38UnitInput_sector0)]

def node20Piece38UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 4, 6]), (12, [1, 1, 2, 2, 2, 3, 3, 6]), (72, [1, 1, 2, 2, 3, 11]), (36, [1, 1, 2, 2, 6, 8]), (48, [1, 1, 2, 3, 6, 7]), (4, [1, 2, 2, 2, 2, 2, 3, 6]), (144, [1, 2, 2, 2, 3, 10]), (72, [1, 2, 2, 2, 6, 7]), (144, [1, 2, 2, 3, 3, 9]), (144, [1, 2, 2, 3, 4, 8]), (144, [1, 2, 2, 3, 5, 7]), (220, [1, 2, 2, 3, 6, 6]), (72, [1, 2, 2, 4, 5, 6]), (432, [1, 2, 2, 15]), (96, [1, 2, 3, 3, 5, 6]), (48, [1, 2, 3, 4, 4, 6]), (576, [1, 2, 3, 14]), (288, [1, 2, 6, 11]), (96, [1, 3, 6, 10]), (72, [2, 2, 2, 2, 3, 9]), (36, [2, 2, 2, 2, 6, 6]), (144, [2, 2, 2, 3, 3, 8]), (144, [2, 2, 2, 3, 4, 7]), (264, [2, 2, 2, 3, 5, 6])]

def node20Piece38UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 2, 4, 4, 6]), (432, [2, 2, 2, 14]), (72, [2, 2, 3, 3, 3, 7]), (286, [2, 2, 3, 3, 4, 6]), (72, [2, 2, 3, 3, 5, 5]), (72, [2, 2, 3, 4, 4, 5]), (-1632, [2, 2, 3, 13]), (432, [2, 2, 4, 12]), (432, [2, 2, 5, 11]), (120, [2, 2, 6, 10]), (432, [2, 2, 7, 9]), (216, [2, 2, 8, 8]), (16, [2, 3, 3, 3, 3, 6]), (576, [2, 3, 3, 12]), (576, [2, 3, 4, 11]), (576, [2, 3, 5, 10]), (400, [2, 3, 6, 9]), (576, [2, 3, 7, 8]), (288, [2, 4, 6, 8]), (288, [2, 5, 6, 7]), (144, [2, 6, 6, 6]), (1728, [2, 18]), (96, [3, 3, 6, 8]), (96, [3, 4, 6, 7])]

def node20Piece38UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [3, 5, 6, 6]), (576, [3, 17]), (288, [6, 14])]

def node20Piece38UnitOutput_sector0 : RawPoly ℕ := [node20Piece38UnitOutput_sector0_chunk0, node20Piece38UnitOutput_sector0_chunk1, node20Piece38UnitOutput_sector0_chunk2].flatten

def node20Piece38UnitOutput : SectorVector := [(0, node20Piece38UnitOutput_sector0)]

theorem node20Piece38_check : VectorCertificate (neutralBoundS JR (-4) node20Piece38UnitInput) node20Piece38UnitOutput := by decide +kernel

theorem node20Piece38_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece38Input) = evaluate node20Piece38Output :=
  mode_of_scaled _ _ (-80) node20Piece38UnitInput node20Piece38UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece38_check)

def node20Piece39Input_sector0 : RawPoly ℕ := [(-312, [2, 2, 4, 5])]

def node20Piece39Input : SectorVector := [(0, node20Piece39Input_sector0)]
def node20Piece39Output_sector0_chunk0 : RawPoly ℕ := [(-1248, [1, 1, 1, 2, 2, 4, 4, 5]), (-3744, [1, 1, 2, 2, 2, 3, 4, 5]), (-18720, [1, 1, 2, 2, 4, 10]), (-14976, [1, 1, 2, 2, 5, 9]), (-14976, [1, 1, 2, 4, 5, 7]), (-1248, [1, 2, 2, 2, 2, 2, 4, 5]), (-37440, [1, 2, 2, 2, 4, 9]), (-29952, [1, 2, 2, 2, 5, 8]), (-37440, [1, 2, 2, 3, 4, 8]), (-29952, [1, 2, 2, 3, 5, 7]), (-37440, [1, 2, 2, 4, 4, 7]), (-91104, [1, 2, 2, 4, 5, 6]), (-14976, [1, 2, 2, 5, 5, 5]), (-149760, [1, 2, 2, 15]), (-29952, [1, 2, 3, 4, 5, 5]), (-14976, [1, 2, 4, 4, 4, 5]), (-149760, [1, 2, 4, 13]), (-119808, [1, 2, 5, 12]), (-29952, [1, 4, 5, 10]), (-18720, [2, 2, 2, 2, 4, 8]), (-14976, [2, 2, 2, 2, 5, 7]), (-37440, [2, 2, 2, 3, 4, 7]), (-29952, [2, 2, 2, 3, 5, 6]), (-37440, [2, 2, 2, 4, 4, 6])]

def node20Piece39Output_sector0_chunk1 : RawPoly ℕ := [(-63648, [2, 2, 2, 4, 5, 5]), (-149760, [2, 2, 2, 14]), (-18720, [2, 2, 3, 3, 4, 6]), (-14976, [2, 2, 3, 3, 5, 5]), (-85488, [2, 2, 3, 4, 4, 5]), (-149760, [2, 2, 3, 13]), (-6240, [2, 2, 4, 4, 4, 4]), (246480, [2, 2, 4, 12]), (67392, [2, 2, 5, 11]), (-149760, [2, 2, 6, 10]), (-149760, [2, 2, 7, 9]), (-74880, [2, 2, 8, 8]), (-4992, [2, 3, 3, 3, 4, 5]), (-149760, [2, 3, 4, 11]), (-119808, [2, 3, 5, 10]), (-149760, [2, 4, 4, 10]), (-124800, [2, 4, 5, 9]), (-149760, [2, 4, 6, 8]), (-74880, [2, 4, 7, 7]), (-119808, [2, 5, 5, 8]), (-119808, [2, 5, 6, 7]), (-599040, [2, 18]), (-29952, [3, 4, 5, 8]), (-29952, [4, 4, 5, 7])]

def node20Piece39Output_sector0_chunk2 : RawPoly ℕ := [(-29952, [4, 5, 5, 6]), (-149760, [4, 16]), (-119808, [5, 15])]

def node20Piece39Output_sector0 : RawPoly ℕ := [node20Piece39Output_sector0_chunk0, node20Piece39Output_sector0_chunk1, node20Piece39Output_sector0_chunk2].flatten

def node20Piece39Output : SectorVector := [(0, node20Piece39Output_sector0)]

def node20Piece39UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 4, 5])]

def node20Piece39UnitInput_sector0 : RawPoly ℕ := [node20Piece39UnitInput_sector0_chunk0].flatten

def node20Piece39UnitInput : SectorVector := [(0, node20Piece39UnitInput_sector0)]

def node20Piece39UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 4, 4, 5]), (12, [1, 1, 2, 2, 2, 3, 4, 5]), (60, [1, 1, 2, 2, 4, 10]), (48, [1, 1, 2, 2, 5, 9]), (48, [1, 1, 2, 4, 5, 7]), (4, [1, 2, 2, 2, 2, 2, 4, 5]), (120, [1, 2, 2, 2, 4, 9]), (96, [1, 2, 2, 2, 5, 8]), (120, [1, 2, 2, 3, 4, 8]), (96, [1, 2, 2, 3, 5, 7]), (120, [1, 2, 2, 4, 4, 7]), (292, [1, 2, 2, 4, 5, 6]), (48, [1, 2, 2, 5, 5, 5]), (480, [1, 2, 2, 15]), (96, [1, 2, 3, 4, 5, 5]), (48, [1, 2, 4, 4, 4, 5]), (480, [1, 2, 4, 13]), (384, [1, 2, 5, 12]), (96, [1, 4, 5, 10]), (60, [2, 2, 2, 2, 4, 8]), (48, [2, 2, 2, 2, 5, 7]), (120, [2, 2, 2, 3, 4, 7]), (96, [2, 2, 2, 3, 5, 6]), (120, [2, 2, 2, 4, 4, 6])]

def node20Piece39UnitOutput_sector0_chunk1 : RawPoly ℕ := [(204, [2, 2, 2, 4, 5, 5]), (480, [2, 2, 2, 14]), (60, [2, 2, 3, 3, 4, 6]), (48, [2, 2, 3, 3, 5, 5]), (274, [2, 2, 3, 4, 4, 5]), (480, [2, 2, 3, 13]), (20, [2, 2, 4, 4, 4, 4]), (-790, [2, 2, 4, 12]), (-216, [2, 2, 5, 11]), (480, [2, 2, 6, 10]), (480, [2, 2, 7, 9]), (240, [2, 2, 8, 8]), (16, [2, 3, 3, 3, 4, 5]), (480, [2, 3, 4, 11]), (384, [2, 3, 5, 10]), (480, [2, 4, 4, 10]), (400, [2, 4, 5, 9]), (480, [2, 4, 6, 8]), (240, [2, 4, 7, 7]), (384, [2, 5, 5, 8]), (384, [2, 5, 6, 7]), (1920, [2, 18]), (96, [3, 4, 5, 8]), (96, [4, 4, 5, 7])]

def node20Piece39UnitOutput_sector0_chunk2 : RawPoly ℕ := [(96, [4, 5, 5, 6]), (480, [4, 16]), (384, [5, 15])]

def node20Piece39UnitOutput_sector0 : RawPoly ℕ := [node20Piece39UnitOutput_sector0_chunk0, node20Piece39UnitOutput_sector0_chunk1, node20Piece39UnitOutput_sector0_chunk2].flatten

def node20Piece39UnitOutput : SectorVector := [(0, node20Piece39UnitOutput_sector0)]

theorem node20Piece39_check : VectorCertificate (neutralBoundS JR (-4) node20Piece39UnitInput) node20Piece39UnitOutput := by decide +kernel

theorem node20Piece39_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece39Input) = evaluate node20Piece39Output :=
  mode_of_scaled _ _ (-312) node20Piece39UnitInput node20Piece39UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece39_check)

def node20Piece40Input_sector0 : RawPoly ℕ := [(640/3, [2, 3, 3, 5])]

def node20Piece40Input : SectorVector := [(0, node20Piece40Input_sector0)]
def node20Piece40Output_sector0_chunk0 : RawPoly ℕ := [(2560/3, [1, 1, 1, 2, 3, 3, 4, 5]), (2560, [1, 1, 2, 2, 3, 3, 3, 5]), (12800, [1, 1, 2, 3, 3, 10]), (15360, [1, 1, 2, 3, 5, 8]), (5120, [1, 1, 3, 3, 5, 7]), (2560/3, [1, 2, 2, 2, 2, 3, 3, 5]), (25600, [1, 2, 2, 3, 3, 9]), (30720, [1, 2, 2, 3, 5, 7]), (25600, [1, 2, 3, 3, 3, 8]), (25600, [1, 2, 3, 3, 4, 7]), (186880/3, [1, 2, 3, 3, 5, 6]), (30720, [1, 2, 3, 4, 5, 5]), (153600, [1, 2, 3, 14]), (46080, [1, 2, 5, 12]), (10240, [1, 3, 3, 3, 5, 5]), (5120, [1, 3, 3, 4, 4, 5]), (51200, [1, 3, 3, 13]), (61440, [1, 3, 5, 11]), (12800, [2, 2, 2, 3, 3, 8]), (15360, [2, 2, 2, 3, 5, 6]), (25600, [2, 2, 3, 3, 3, 7]), (25600, [2, 2, 3, 3, 4, 6]), (48640, [2, 2, 3, 3, 5, 5]), (15360, [2, 2, 3, 4, 4, 5])]

def node20Piece40Output_sector0_chunk1 : RawPoly ℕ := [(153600, [2, 2, 3, 13]), (46080, [2, 2, 5, 11]), (12800, [2, 3, 3, 3, 3, 6]), (160000/3, [2, 3, 3, 3, 4, 5]), (12800/3, [2, 3, 3, 4, 4, 4]), (-505600/3, [2, 3, 3, 12]), (153600, [2, 3, 4, 11]), (5120, [2, 3, 5, 10]), (153600, [2, 3, 6, 9]), (153600, [2, 3, 7, 8]), (46080, [2, 4, 5, 9]), (46080, [2, 5, 5, 8]), (46080, [2, 5, 6, 7]), (230400, [2, 18]), (5120/3, [3, 3, 3, 3, 3, 5]), (51200, [3, 3, 3, 11]), (51200, [3, 3, 4, 10]), (158720/3, [3, 3, 5, 9]), (51200, [3, 3, 6, 8]), (25600, [3, 3, 7, 7]), (61440, [3, 4, 5, 8]), (61440, [3, 5, 5, 7]), (30720, [3, 5, 6, 6]), (307200, [3, 17])]

def node20Piece40Output_sector0_chunk2 : RawPoly ℕ := [(92160, [5, 15])]

def node20Piece40Output_sector0 : RawPoly ℕ := [node20Piece40Output_sector0_chunk0, node20Piece40Output_sector0_chunk1, node20Piece40Output_sector0_chunk2].flatten

def node20Piece40Output : SectorVector := [(0, node20Piece40Output_sector0)]

def node20Piece40UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 5])]

def node20Piece40UnitInput_sector0 : RawPoly ℕ := [node20Piece40UnitInput_sector0_chunk0].flatten

def node20Piece40UnitInput : SectorVector := [(0, node20Piece40UnitInput_sector0)]

def node20Piece40UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 5]), (12, [1, 1, 2, 2, 3, 3, 3, 5]), (60, [1, 1, 2, 3, 3, 10]), (72, [1, 1, 2, 3, 5, 8]), (24, [1, 1, 3, 3, 5, 7]), (4, [1, 2, 2, 2, 2, 3, 3, 5]), (120, [1, 2, 2, 3, 3, 9]), (144, [1, 2, 2, 3, 5, 7]), (120, [1, 2, 3, 3, 3, 8]), (120, [1, 2, 3, 3, 4, 7]), (292, [1, 2, 3, 3, 5, 6]), (144, [1, 2, 3, 4, 5, 5]), (720, [1, 2, 3, 14]), (216, [1, 2, 5, 12]), (48, [1, 3, 3, 3, 5, 5]), (24, [1, 3, 3, 4, 4, 5]), (240, [1, 3, 3, 13]), (288, [1, 3, 5, 11]), (60, [2, 2, 2, 3, 3, 8]), (72, [2, 2, 2, 3, 5, 6]), (120, [2, 2, 3, 3, 3, 7]), (120, [2, 2, 3, 3, 4, 6]), (228, [2, 2, 3, 3, 5, 5]), (72, [2, 2, 3, 4, 4, 5])]

def node20Piece40UnitOutput_sector0_chunk1 : RawPoly ℕ := [(720, [2, 2, 3, 13]), (216, [2, 2, 5, 11]), (60, [2, 3, 3, 3, 3, 6]), (250, [2, 3, 3, 3, 4, 5]), (20, [2, 3, 3, 4, 4, 4]), (-790, [2, 3, 3, 12]), (720, [2, 3, 4, 11]), (24, [2, 3, 5, 10]), (720, [2, 3, 6, 9]), (720, [2, 3, 7, 8]), (216, [2, 4, 5, 9]), (216, [2, 5, 5, 8]), (216, [2, 5, 6, 7]), (1080, [2, 18]), (8, [3, 3, 3, 3, 3, 5]), (240, [3, 3, 3, 11]), (240, [3, 3, 4, 10]), (248, [3, 3, 5, 9]), (240, [3, 3, 6, 8]), (120, [3, 3, 7, 7]), (288, [3, 4, 5, 8]), (288, [3, 5, 5, 7]), (144, [3, 5, 6, 6]), (1440, [3, 17])]

def node20Piece40UnitOutput_sector0_chunk2 : RawPoly ℕ := [(432, [5, 15])]

def node20Piece40UnitOutput_sector0 : RawPoly ℕ := [node20Piece40UnitOutput_sector0_chunk0, node20Piece40UnitOutput_sector0_chunk1, node20Piece40UnitOutput_sector0_chunk2].flatten

def node20Piece40UnitOutput : SectorVector := [(0, node20Piece40UnitOutput_sector0)]

theorem node20Piece40_check : VectorCertificate (neutralBoundS JR (-4) node20Piece40UnitInput) node20Piece40UnitOutput := by decide +kernel

theorem node20Piece40_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece40Input) = evaluate node20Piece40Output :=
  mode_of_scaled _ _ (640/3) node20Piece40UnitInput node20Piece40UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece40_check)

def node20Piece41Input_sector0 : RawPoly ℕ := [(-110, [2, 3, 4, 4])]

def node20Piece41Input : SectorVector := [(0, node20Piece41Input_sector0)]
def node20Piece41Output_sector0_chunk0 : RawPoly ℕ := [(-440, [1, 1, 1, 2, 3, 4, 4, 4]), (-1320, [1, 1, 2, 2, 3, 3, 4, 4]), (-10560, [1, 1, 2, 3, 4, 9]), (-3960, [1, 1, 2, 4, 4, 8]), (-2640, [1, 1, 3, 4, 4, 7]), (-440, [1, 2, 2, 2, 2, 3, 4, 4]), (-21120, [1, 2, 2, 3, 4, 8]), (-7920, [1, 2, 2, 4, 4, 7]), (-21120, [1, 2, 3, 3, 4, 7]), (-32120, [1, 2, 3, 4, 4, 6]), (-10560, [1, 2, 3, 4, 5, 5]), (-42240, [1, 2, 3, 14]), (-7920, [1, 2, 4, 4, 4, 5]), (-63360, [1, 2, 4, 13]), (-5280, [1, 3, 3, 4, 4, 5]), (-2640, [1, 3, 4, 4, 4, 4]), (-42240, [1, 3, 4, 12]), (-15840, [1, 4, 4, 11]), (-10560, [2, 2, 2, 3, 4, 7]), (-3960, [2, 2, 2, 4, 4, 6]), (-21120, [2, 2, 3, 3, 4, 6]), (-31680, [2, 2, 3, 4, 4, 5]), (-42240, [2, 2, 3, 13]), (-3960, [2, 2, 4, 4, 4, 4])]

def node20Piece41Output_sector0_chunk1 : RawPoly ℕ := [(-63360, [2, 2, 4, 12]), (-10560, [2, 3, 3, 3, 4, 5]), (-20900, [2, 3, 3, 4, 4, 4]), (-42240, [2, 3, 3, 12]), (89760, [2, 3, 4, 11]), (-42240, [2, 3, 5, 10]), (-42240, [2, 3, 6, 9]), (-42240, [2, 3, 7, 8]), (-13200, [2, 4, 4, 10]), (-63360, [2, 4, 5, 9]), (-63360, [2, 4, 6, 8]), (-31680, [2, 4, 7, 7]), (-126720, [2, 18]), (-880, [3, 3, 3, 3, 4, 4]), (-42240, [3, 3, 4, 10]), (-27280, [3, 4, 4, 9]), (-42240, [3, 4, 5, 8]), (-42240, [3, 4, 6, 7]), (-84480, [3, 17]), (-15840, [4, 4, 4, 8]), (-15840, [4, 4, 5, 7]), (-7920, [4, 4, 6, 6]), (-126720, [4, 16])]

def node20Piece41Output_sector0 : RawPoly ℕ := [node20Piece41Output_sector0_chunk0, node20Piece41Output_sector0_chunk1].flatten

def node20Piece41Output : SectorVector := [(0, node20Piece41Output_sector0)]

def node20Piece41UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 4, 4])]

def node20Piece41UnitInput_sector0 : RawPoly ℕ := [node20Piece41UnitInput_sector0_chunk0].flatten

def node20Piece41UnitInput : SectorVector := [(0, node20Piece41UnitInput_sector0)]

def node20Piece41UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 4, 4]), (12, [1, 1, 2, 2, 3, 3, 4, 4]), (96, [1, 1, 2, 3, 4, 9]), (36, [1, 1, 2, 4, 4, 8]), (24, [1, 1, 3, 4, 4, 7]), (4, [1, 2, 2, 2, 2, 3, 4, 4]), (192, [1, 2, 2, 3, 4, 8]), (72, [1, 2, 2, 4, 4, 7]), (192, [1, 2, 3, 3, 4, 7]), (292, [1, 2, 3, 4, 4, 6]), (96, [1, 2, 3, 4, 5, 5]), (384, [1, 2, 3, 14]), (72, [1, 2, 4, 4, 4, 5]), (576, [1, 2, 4, 13]), (48, [1, 3, 3, 4, 4, 5]), (24, [1, 3, 4, 4, 4, 4]), (384, [1, 3, 4, 12]), (144, [1, 4, 4, 11]), (96, [2, 2, 2, 3, 4, 7]), (36, [2, 2, 2, 4, 4, 6]), (192, [2, 2, 3, 3, 4, 6]), (288, [2, 2, 3, 4, 4, 5]), (384, [2, 2, 3, 13]), (36, [2, 2, 4, 4, 4, 4])]

def node20Piece41UnitOutput_sector0_chunk1 : RawPoly ℕ := [(576, [2, 2, 4, 12]), (96, [2, 3, 3, 3, 4, 5]), (190, [2, 3, 3, 4, 4, 4]), (384, [2, 3, 3, 12]), (-816, [2, 3, 4, 11]), (384, [2, 3, 5, 10]), (384, [2, 3, 6, 9]), (384, [2, 3, 7, 8]), (120, [2, 4, 4, 10]), (576, [2, 4, 5, 9]), (576, [2, 4, 6, 8]), (288, [2, 4, 7, 7]), (1152, [2, 18]), (8, [3, 3, 3, 3, 4, 4]), (384, [3, 3, 4, 10]), (248, [3, 4, 4, 9]), (384, [3, 4, 5, 8]), (384, [3, 4, 6, 7]), (768, [3, 17]), (144, [4, 4, 4, 8]), (144, [4, 4, 5, 7]), (72, [4, 4, 6, 6]), (1152, [4, 16])]

def node20Piece41UnitOutput_sector0 : RawPoly ℕ := [node20Piece41UnitOutput_sector0_chunk0, node20Piece41UnitOutput_sector0_chunk1].flatten

def node20Piece41UnitOutput : SectorVector := [(0, node20Piece41UnitOutput_sector0)]

theorem node20Piece41_check : VectorCertificate (neutralBoundS JR (-4) node20Piece41UnitInput) node20Piece41UnitOutput := by decide +kernel

theorem node20Piece41_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece41Input) = evaluate node20Piece41Output :=
  mode_of_scaled _ _ (-110) node20Piece41UnitInput node20Piece41UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece41_check)

def node20Piece42Input_sector0 : RawPoly ℕ := [(-960/11, [2, 11])]

def node20Piece42Input : SectorVector := [(0, node20Piece42Input_sector0)]
def node20Piece42Output_sector0_chunk0 : RawPoly ℕ := [(-3840/11, [1, 1, 1, 2, 4, 11]), (-11520/11, [1, 1, 2, 2, 3, 11]), (-11520, [1, 1, 2, 16]), (-23040/11, [1, 1, 7, 11]), (-3840/11, [1, 2, 2, 2, 2, 11]), (-23040, [1, 2, 2, 15]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-280320/11, [1, 2, 6, 11]), (-23040, [1, 2, 7, 10]), (-23040, [1, 2, 8, 9]), (-46080/11, [1, 3, 5, 11]), (-23040/11, [1, 4, 4, 11]), (-46080, [1, 19]), (-11520, [2, 2, 2, 14]), (-23040, [2, 2, 3, 13]), (-23040, [2, 2, 4, 12]), (-276480/11, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10]), (-23040, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8]), (-11520, [2, 3, 3, 12]), (-309120/11, [2, 3, 4, 11])]

def node20Piece42Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [2, 3, 5, 10]), (-23040, [2, 3, 6, 9]), (-23040, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-23040, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (952320, [2, 18]), (-7680/11, [3, 3, 3, 11]), (-46080, [3, 17]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (-238080/11, [9, 11]), (-23040, [10, 10])]

def node20Piece42Output_sector0 : RawPoly ℕ := [node20Piece42Output_sector0_chunk0, node20Piece42Output_sector0_chunk1].flatten

def node20Piece42Output : SectorVector := [(0, node20Piece42Output_sector0)]

def node20Piece42UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 11])]

def node20Piece42UnitInput_sector0 : RawPoly ℕ := [node20Piece42UnitInput_sector0_chunk0].flatten

def node20Piece42UnitInput : SectorVector := [(0, node20Piece42UnitInput_sector0)]

def node20Piece42UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 4, 11]), (12, [1, 1, 2, 2, 3, 11]), (132, [1, 1, 2, 16]), (24, [1, 1, 7, 11]), (4, [1, 2, 2, 2, 2, 11]), (264, [1, 2, 2, 15]), (264, [1, 2, 3, 14]), (264, [1, 2, 4, 13]), (264, [1, 2, 5, 12]), (292, [1, 2, 6, 11]), (264, [1, 2, 7, 10]), (264, [1, 2, 8, 9]), (48, [1, 3, 5, 11]), (24, [1, 4, 4, 11]), (528, [1, 19]), (132, [2, 2, 2, 14]), (264, [2, 2, 3, 13]), (264, [2, 2, 4, 12]), (288, [2, 2, 5, 11]), (264, [2, 2, 6, 10]), (264, [2, 2, 7, 9]), (132, [2, 2, 8, 8]), (132, [2, 3, 3, 12]), (322, [2, 3, 4, 11])]

def node20Piece42UnitOutput_sector0_chunk1 : RawPoly ℕ := [(264, [2, 3, 5, 10]), (264, [2, 3, 6, 9]), (264, [2, 3, 7, 8]), (132, [2, 4, 4, 10]), (264, [2, 4, 5, 9]), (264, [2, 4, 6, 8]), (132, [2, 4, 7, 7]), (132, [2, 5, 5, 8]), (264, [2, 5, 6, 7]), (44, [2, 6, 6, 6]), (-10912, [2, 18]), (8, [3, 3, 3, 11]), (528, [3, 17]), (528, [4, 16]), (528, [5, 15]), (528, [6, 14]), (528, [7, 13]), (528, [8, 12]), (248, [9, 11]), (264, [10, 10])]

def node20Piece42UnitOutput_sector0 : RawPoly ℕ := [node20Piece42UnitOutput_sector0_chunk0, node20Piece42UnitOutput_sector0_chunk1].flatten

def node20Piece42UnitOutput : SectorVector := [(0, node20Piece42UnitOutput_sector0)]

theorem node20Piece42_check : VectorCertificate (neutralBoundS JR (-4) node20Piece42UnitInput) node20Piece42UnitOutput := by decide +kernel

theorem node20Piece42_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece42Input) = evaluate node20Piece42Output :=
  mode_of_scaled _ _ (-960/11) node20Piece42UnitInput node20Piece42UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece42_check)

def node20Piece43Input_sector0 : RawPoly ℕ := [(2240/27, [3, 3, 3, 4])]

def node20Piece43Input : SectorVector := [(0, node20Piece43Input_sector0)]
def node20Piece43Output_sector0_chunk0 : RawPoly ℕ := [(8960/27, [1, 1, 1, 3, 3, 3, 4, 4]), (8960/9, [1, 1, 2, 3, 3, 3, 3, 4]), (35840/9, [1, 1, 3, 3, 3, 9]), (8960, [1, 1, 3, 3, 4, 8]), (8960/27, [1, 2, 2, 2, 3, 3, 3, 4]), (71680/9, [1, 2, 3, 3, 3, 8]), (17920, [1, 2, 3, 3, 4, 7]), (71680/9, [1, 3, 3, 3, 3, 7]), (654080/27, [1, 3, 3, 3, 4, 6]), (35840/9, [1, 3, 3, 3, 5, 5]), (17920, [1, 3, 3, 4, 4, 5]), (71680, [1, 3, 3, 13]), (53760, [1, 3, 4, 12]), (35840/9, [2, 2, 3, 3, 3, 7]), (8960, [2, 2, 3, 3, 4, 6]), (71680/9, [2, 3, 3, 3, 3, 6]), (232960/9, [2, 3, 3, 3, 4, 5]), (8960, [2, 3, 3, 4, 4, 4]), (71680, [2, 3, 3, 12]), (53760, [2, 3, 4, 11]), (35840/9, [3, 3, 3, 3, 3, 5]), (371840/27, [3, 3, 3, 3, 4, 4]), (-17920, [3, 3, 3, 11]), (-71680/3, [3, 3, 4, 10])]

def node20Piece43Output_sector0_chunk1 : RawPoly ℕ := [(71680, [3, 3, 5, 9]), (71680, [3, 3, 6, 8]), (35840, [3, 3, 7, 7]), (53760, [3, 4, 4, 9]), (53760, [3, 4, 5, 8]), (53760, [3, 4, 6, 7]), (215040, [3, 17]), (53760, [4, 16])]

def node20Piece43Output_sector0 : RawPoly ℕ := [node20Piece43Output_sector0_chunk0, node20Piece43Output_sector0_chunk1].flatten

def node20Piece43Output : SectorVector := [(0, node20Piece43Output_sector0)]

def node20Piece43UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 4])]

def node20Piece43UnitInput_sector0 : RawPoly ℕ := [node20Piece43UnitInput_sector0_chunk0].flatten

def node20Piece43UnitInput : SectorVector := [(0, node20Piece43UnitInput_sector0)]

def node20Piece43UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 4, 4]), (12, [1, 1, 2, 3, 3, 3, 3, 4]), (48, [1, 1, 3, 3, 3, 9]), (108, [1, 1, 3, 3, 4, 8]), (4, [1, 2, 2, 2, 3, 3, 3, 4]), (96, [1, 2, 3, 3, 3, 8]), (216, [1, 2, 3, 3, 4, 7]), (96, [1, 3, 3, 3, 3, 7]), (292, [1, 3, 3, 3, 4, 6]), (48, [1, 3, 3, 3, 5, 5]), (216, [1, 3, 3, 4, 4, 5]), (864, [1, 3, 3, 13]), (648, [1, 3, 4, 12]), (48, [2, 2, 3, 3, 3, 7]), (108, [2, 2, 3, 3, 4, 6]), (96, [2, 3, 3, 3, 3, 6]), (312, [2, 3, 3, 3, 4, 5]), (108, [2, 3, 3, 4, 4, 4]), (864, [2, 3, 3, 12]), (648, [2, 3, 4, 11]), (48, [3, 3, 3, 3, 3, 5]), (166, [3, 3, 3, 3, 4, 4]), (-216, [3, 3, 3, 11]), (-288, [3, 3, 4, 10])]

def node20Piece43UnitOutput_sector0_chunk1 : RawPoly ℕ := [(864, [3, 3, 5, 9]), (864, [3, 3, 6, 8]), (432, [3, 3, 7, 7]), (648, [3, 4, 4, 9]), (648, [3, 4, 5, 8]), (648, [3, 4, 6, 7]), (2592, [3, 17]), (648, [4, 16])]

def node20Piece43UnitOutput_sector0 : RawPoly ℕ := [node20Piece43UnitOutput_sector0_chunk0, node20Piece43UnitOutput_sector0_chunk1].flatten

def node20Piece43UnitOutput : SectorVector := [(0, node20Piece43UnitOutput_sector0)]

theorem node20Piece43_check : VectorCertificate (neutralBoundS JR (-4) node20Piece43UnitInput) node20Piece43UnitOutput := by decide +kernel

theorem node20Piece43_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece43Input) = evaluate node20Piece43Output :=
  mode_of_scaled _ _ (2240/27) node20Piece43UnitInput node20Piece43UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece43_check)

def node20Piece44Input_sector0 : RawPoly ℕ := [(96, [3, 10])]

def node20Piece44Input : SectorVector := [(0, node20Piece44Input_sector0)]
def node20Piece44Output_sector0_chunk0 : RawPoly ℕ := [(384, [1, 1, 1, 3, 4, 10]), (1152, [1, 1, 2, 3, 3, 10]), (11520, [1, 1, 3, 15]), (3456, [1, 1, 8, 10]), (384, [1, 2, 2, 2, 3, 10]), (23040, [1, 2, 3, 14]), (6912, [1, 2, 7, 10]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (28032, [1, 3, 6, 10]), (23040, [1, 3, 7, 9]), (11520, [1, 3, 8, 8]), (6912, [1, 4, 5, 10]), (69120, [1, 19]), (11520, [2, 2, 3, 13]), (3456, [2, 2, 6, 10]), (23040, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (29952, [2, 3, 5, 10]), (23040, [2, 3, 6, 9]), (23040, [2, 3, 7, 8]), (3456, [2, 4, 4, 10]), (69120, [2, 18])]

def node20Piece44Output_sector0_chunk1 : RawPoly ℕ := [(11520, [3, 3, 3, 11]), (27456, [3, 3, 4, 10]), (23040, [3, 3, 5, 9]), (23040, [3, 3, 6, 8]), (11520, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (23040, [3, 4, 5, 8]), (23040, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-794880, [3, 17]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14]), (69120, [7, 13]), (69120, [8, 12]), (69120, [9, 11]), (-23040, [10, 10])]

def node20Piece44Output_sector0 : RawPoly ℕ := [node20Piece44Output_sector0_chunk0, node20Piece44Output_sector0_chunk1].flatten

def node20Piece44Output : SectorVector := [(0, node20Piece44Output_sector0)]

def node20Piece44UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 10])]

def node20Piece44UnitInput_sector0 : RawPoly ℕ := [node20Piece44UnitInput_sector0_chunk0].flatten

def node20Piece44UnitInput : SectorVector := [(0, node20Piece44UnitInput_sector0)]

def node20Piece44UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 10]), (12, [1, 1, 2, 3, 3, 10]), (120, [1, 1, 3, 15]), (36, [1, 1, 8, 10]), (4, [1, 2, 2, 2, 3, 10]), (240, [1, 2, 3, 14]), (72, [1, 2, 7, 10]), (240, [1, 3, 3, 13]), (240, [1, 3, 4, 12]), (240, [1, 3, 5, 11]), (292, [1, 3, 6, 10]), (240, [1, 3, 7, 9]), (120, [1, 3, 8, 8]), (72, [1, 4, 5, 10]), (720, [1, 19]), (120, [2, 2, 3, 13]), (36, [2, 2, 6, 10]), (240, [2, 3, 3, 12]), (240, [2, 3, 4, 11]), (312, [2, 3, 5, 10]), (240, [2, 3, 6, 9]), (240, [2, 3, 7, 8]), (36, [2, 4, 4, 10]), (720, [2, 18])]

def node20Piece44UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [3, 3, 3, 11]), (286, [3, 3, 4, 10]), (240, [3, 3, 5, 9]), (240, [3, 3, 6, 8]), (120, [3, 3, 7, 7]), (120, [3, 4, 4, 9]), (240, [3, 4, 5, 8]), (240, [3, 4, 6, 7]), (120, [3, 5, 5, 7]), (120, [3, 5, 6, 6]), (-8280, [3, 17]), (720, [4, 16]), (720, [5, 15]), (720, [6, 14]), (720, [7, 13]), (720, [8, 12]), (720, [9, 11]), (-240, [10, 10])]

def node20Piece44UnitOutput_sector0 : RawPoly ℕ := [node20Piece44UnitOutput_sector0_chunk0, node20Piece44UnitOutput_sector0_chunk1].flatten

def node20Piece44UnitOutput : SectorVector := [(0, node20Piece44UnitOutput_sector0)]

theorem node20Piece44_check : VectorCertificate (neutralBoundS JR (-4) node20Piece44UnitInput) node20Piece44UnitOutput := by decide +kernel

theorem node20Piece44_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece44Input) = evaluate node20Piece44Output :=
  mode_of_scaled _ _ (96) node20Piece44UnitInput node20Piece44UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece44_check)

def node20Piece45Input_sector0 : RawPoly ℕ := [(-160/3, [4, 9])]

def node20Piece45Input : SectorVector := [(0, node20Piece45Input_sector0)]
def node20Piece45Output_sector0_chunk0 : RawPoly ℕ := [(-640/3, [1, 1, 1, 4, 4, 9]), (-640, [1, 1, 2, 3, 4, 9]), (-5760, [1, 1, 4, 14]), (-2560, [1, 1, 9, 9]), (-640/3, [1, 2, 2, 2, 4, 9]), (-11520, [1, 2, 4, 13]), (-5120, [1, 2, 8, 9]), (-11520, [1, 3, 4, 12]), (-5120, [1, 3, 7, 9]), (-11520, [1, 4, 4, 11]), (-11520, [1, 4, 5, 10]), (-46720/3, [1, 4, 6, 9]), (-11520, [1, 4, 7, 8]), (-2560, [1, 5, 5, 9]), (-46080, [1, 19]), (-5760, [2, 2, 4, 12]), (-2560, [2, 2, 7, 9]), (-11520, [2, 3, 4, 11]), (-5120, [2, 3, 6, 9]), (-11520, [2, 4, 4, 10]), (-16640, [2, 4, 5, 9]), (-11520, [2, 4, 6, 8]), (-5760, [2, 4, 7, 7]), (-46080, [2, 18])]

def node20Piece45Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [3, 3, 4, 10]), (-2560, [3, 3, 5, 9]), (-43840/3, [3, 4, 4, 9]), (-11520, [3, 4, 5, 8]), (-11520, [3, 4, 6, 7]), (-46080, [3, 17]), (-5760, [4, 4, 4, 8]), (-11520, [4, 4, 5, 7]), (-5760, [4, 4, 6, 6]), (-5760, [4, 5, 5, 6]), (323520, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (11520, [9, 11]), (-23040, [10, 10])]

def node20Piece45Output_sector0 : RawPoly ℕ := [node20Piece45Output_sector0_chunk0, node20Piece45Output_sector0_chunk1].flatten

def node20Piece45Output : SectorVector := [(0, node20Piece45Output_sector0)]

def node20Piece45UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 9])]

def node20Piece45UnitInput_sector0 : RawPoly ℕ := [node20Piece45UnitInput_sector0_chunk0].flatten

def node20Piece45UnitInput : SectorVector := [(0, node20Piece45UnitInput_sector0)]

def node20Piece45UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 4, 9]), (12, [1, 1, 2, 3, 4, 9]), (108, [1, 1, 4, 14]), (48, [1, 1, 9, 9]), (4, [1, 2, 2, 2, 4, 9]), (216, [1, 2, 4, 13]), (96, [1, 2, 8, 9]), (216, [1, 3, 4, 12]), (96, [1, 3, 7, 9]), (216, [1, 4, 4, 11]), (216, [1, 4, 5, 10]), (292, [1, 4, 6, 9]), (216, [1, 4, 7, 8]), (48, [1, 5, 5, 9]), (864, [1, 19]), (108, [2, 2, 4, 12]), (48, [2, 2, 7, 9]), (216, [2, 3, 4, 11]), (96, [2, 3, 6, 9]), (216, [2, 4, 4, 10]), (312, [2, 4, 5, 9]), (216, [2, 4, 6, 8]), (108, [2, 4, 7, 7]), (864, [2, 18])]

def node20Piece45UnitOutput_sector0_chunk1 : RawPoly ℕ := [(108, [3, 3, 4, 10]), (48, [3, 3, 5, 9]), (274, [3, 4, 4, 9]), (216, [3, 4, 5, 8]), (216, [3, 4, 6, 7]), (864, [3, 17]), (108, [4, 4, 4, 8]), (216, [4, 4, 5, 7]), (108, [4, 4, 6, 6]), (108, [4, 5, 5, 6]), (-6066, [4, 16]), (864, [5, 15]), (864, [6, 14]), (864, [7, 13]), (864, [8, 12]), (-216, [9, 11]), (432, [10, 10])]

def node20Piece45UnitOutput_sector0 : RawPoly ℕ := [node20Piece45UnitOutput_sector0_chunk0, node20Piece45UnitOutput_sector0_chunk1].flatten

def node20Piece45UnitOutput : SectorVector := [(0, node20Piece45UnitOutput_sector0)]

theorem node20Piece45_check : VectorCertificate (neutralBoundS JR (-4) node20Piece45UnitInput) node20Piece45UnitOutput := by decide +kernel

theorem node20Piece45_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece45Input) = evaluate node20Piece45Output :=
  mode_of_scaled _ _ (-160/3) node20Piece45UnitInput node20Piece45UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece45_check)

def node20Piece46Input_sector0 : RawPoly ℕ := [(12, [5, 8])]

def node20Piece46Input : SectorVector := [(0, node20Piece46Input_sector0)]
def node20Piece46Output_sector0_chunk0 : RawPoly ℕ := [(48, [1, 1, 1, 4, 5, 8]), (144, [1, 1, 2, 3, 5, 8]), (1152, [1, 1, 5, 13]), (720, [1, 1, 8, 10]), (48, [1, 2, 2, 2, 5, 8]), (2304, [1, 2, 5, 12]), (1440, [1, 2, 8, 9]), (2304, [1, 3, 5, 11]), (1440, [1, 3, 8, 8]), (2304, [1, 4, 5, 10]), (1440, [1, 4, 7, 8]), (2304, [1, 5, 5, 9]), (3504, [1, 5, 6, 8]), (1152, [1, 5, 7, 7]), (11520, [1, 19]), (1152, [2, 2, 5, 11]), (720, [2, 2, 8, 8]), (2304, [2, 3, 5, 10]), (1440, [2, 3, 7, 8]), (2304, [2, 4, 5, 9]), (1440, [2, 4, 6, 8]), (3024, [2, 5, 5, 8]), (2304, [2, 5, 6, 7]), (11520, [2, 18])]

def node20Piece46Output_sector0_chunk1 : RawPoly ℕ := [(1152, [3, 3, 5, 9]), (720, [3, 3, 6, 8]), (3864, [3, 4, 5, 8]), (2304, [3, 5, 5, 7]), (1152, [3, 5, 6, 6]), (11520, [3, 17]), (240, [4, 4, 4, 8]), (1152, [4, 4, 5, 7]), (2304, [4, 5, 5, 6]), (11520, [4, 16]), (384, [5, 5, 5, 5]), (-50880, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (-9480, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node20Piece46Output_sector0 : RawPoly ℕ := [node20Piece46Output_sector0_chunk0, node20Piece46Output_sector0_chunk1].flatten

def node20Piece46Output : SectorVector := [(0, node20Piece46Output_sector0)]

def node20Piece46UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 8])]

def node20Piece46UnitInput_sector0 : RawPoly ℕ := [node20Piece46UnitInput_sector0_chunk0].flatten

def node20Piece46UnitInput : SectorVector := [(0, node20Piece46UnitInput_sector0)]

def node20Piece46UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 5, 8]), (12, [1, 1, 2, 3, 5, 8]), (96, [1, 1, 5, 13]), (60, [1, 1, 8, 10]), (4, [1, 2, 2, 2, 5, 8]), (192, [1, 2, 5, 12]), (120, [1, 2, 8, 9]), (192, [1, 3, 5, 11]), (120, [1, 3, 8, 8]), (192, [1, 4, 5, 10]), (120, [1, 4, 7, 8]), (192, [1, 5, 5, 9]), (292, [1, 5, 6, 8]), (96, [1, 5, 7, 7]), (960, [1, 19]), (96, [2, 2, 5, 11]), (60, [2, 2, 8, 8]), (192, [2, 3, 5, 10]), (120, [2, 3, 7, 8]), (192, [2, 4, 5, 9]), (120, [2, 4, 6, 8]), (252, [2, 5, 5, 8]), (192, [2, 5, 6, 7]), (960, [2, 18])]

def node20Piece46UnitOutput_sector0_chunk1 : RawPoly ℕ := [(96, [3, 3, 5, 9]), (60, [3, 3, 6, 8]), (322, [3, 4, 5, 8]), (192, [3, 5, 5, 7]), (96, [3, 5, 6, 6]), (960, [3, 17]), (20, [4, 4, 4, 8]), (96, [4, 4, 5, 7]), (192, [4, 5, 5, 6]), (960, [4, 16]), (32, [5, 5, 5, 5]), (-4240, [5, 15]), (960, [6, 14]), (960, [7, 13]), (-790, [8, 12]), (960, [9, 11]), (480, [10, 10])]

def node20Piece46UnitOutput_sector0 : RawPoly ℕ := [node20Piece46UnitOutput_sector0_chunk0, node20Piece46UnitOutput_sector0_chunk1].flatten

def node20Piece46UnitOutput : SectorVector := [(0, node20Piece46UnitOutput_sector0)]

theorem node20Piece46_check : VectorCertificate (neutralBoundS JR (-4) node20Piece46UnitInput) node20Piece46UnitOutput := by decide +kernel

theorem node20Piece46_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node20Piece46Input) = evaluate node20Piece46Output :=
  mode_of_scaled _ _ (12) node20Piece46UnitInput node20Piece46UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralBound_value JR _ _ _ node20Piece46_check)

end VOA.Classification.COne.OrbC2h
