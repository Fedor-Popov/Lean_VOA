import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hScalePieces
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateBatch88_2
import VOA.Classification.COne.OrbC2hStateNode0
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node88Piece64Input_sector0 : RawPoly ℕ := [(-60, [2, 2, 3, 8])]

def node88Piece64Input : SectorVector := [(0, node88Piece64Input_sector0)]
def node88Piece64Output_sector0_chunk0 : RawPoly ℕ := [(-240, [1, 1, 1, 2, 2, 3, 4, 8]), (-720, [1, 1, 2, 2, 2, 3, 3, 8]), (-5760, [1, 1, 2, 2, 3, 13]), (-2160, [1, 1, 2, 2, 8, 8]), (-2880, [1, 1, 2, 3, 7, 8]), (-240, [1, 2, 2, 2, 2, 2, 3, 8]), (-11520, [1, 2, 2, 2, 3, 12]), (-4320, [1, 2, 2, 2, 7, 8]), (-11520, [1, 2, 2, 3, 3, 11]), (-11520, [1, 2, 2, 3, 4, 10]), (-11520, [1, 2, 2, 3, 5, 9]), (-20400, [1, 2, 2, 3, 6, 8]), (-5760, [1, 2, 2, 3, 7, 7]), (-4320, [1, 2, 2, 4, 5, 8]), (-34560, [1, 2, 2, 17]), (-5760, [1, 2, 3, 3, 5, 8]), (-2880, [1, 2, 3, 4, 4, 8]), (-46080, [1, 2, 3, 16]), (-17280, [1, 2, 8, 11]), (-5760, [1, 3, 8, 10]), (-5760, [2, 2, 2, 2, 3, 11]), (-2160, [2, 2, 2, 2, 6, 8]), (-11520, [2, 2, 2, 3, 3, 10]), (-11520, [2, 2, 2, 3, 4, 9])]

def node88Piece64Output_sector0_chunk1 : RawPoly ℕ := [(-18720, [2, 2, 2, 3, 5, 8]), (-11520, [2, 2, 2, 3, 6, 7]), (-2160, [2, 2, 2, 4, 4, 8]), (-34560, [2, 2, 2, 16]), (-5760, [2, 2, 3, 3, 3, 9]), (-20040, [2, 2, 3, 3, 4, 8]), (-11520, [2, 2, 3, 3, 5, 7]), (-5760, [2, 2, 3, 3, 6, 6]), (-5760, [2, 2, 3, 4, 4, 7]), (-11520, [2, 2, 3, 4, 5, 6]), (-1920, [2, 2, 3, 5, 5, 5]), (231360, [2, 2, 3, 15]), (-34560, [2, 2, 4, 14]), (-34560, [2, 2, 5, 13]), (-34560, [2, 2, 6, 12]), (-34560, [2, 2, 7, 11]), (-15840, [2, 2, 8, 10]), (-17280, [2, 2, 9, 9]), (-960, [2, 3, 3, 3, 3, 8]), (-46080, [2, 3, 3, 14]), (-46080, [2, 3, 4, 13]), (-46080, [2, 3, 5, 12]), (-46080, [2, 3, 6, 11]), (-46080, [2, 3, 7, 10])]

def node88Piece64Output_sector0_chunk2 : RawPoly ℕ := [(-35520, [2, 3, 8, 9]), (-17280, [2, 4, 8, 8]), (-17280, [2, 5, 7, 8]), (-8640, [2, 6, 6, 8]), (-138240, [2, 20]), (-5760, [3, 3, 8, 8]), (-5760, [3, 4, 7, 8]), (-5760, [3, 5, 6, 8]), (-46080, [3, 19]), (-17280, [8, 14])]

def node88Piece64Output_sector0 : RawPoly ℕ := [node88Piece64Output_sector0_chunk0, node88Piece64Output_sector0_chunk1, node88Piece64Output_sector0_chunk2].flatten

def node88Piece64Output : SectorVector := [(0, node88Piece64Output_sector0)]

def node88Piece64UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 3, 8])]

def node88Piece64UnitInput_sector0 : RawPoly ℕ := [node88Piece64UnitInput_sector0_chunk0].flatten

def node88Piece64UnitInput : SectorVector := [(0, node88Piece64UnitInput_sector0)]

def node88Piece64UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 3, 4, 8]), (12, [1, 1, 2, 2, 2, 3, 3, 8]), (96, [1, 1, 2, 2, 3, 13]), (36, [1, 1, 2, 2, 8, 8]), (48, [1, 1, 2, 3, 7, 8]), (4, [1, 2, 2, 2, 2, 2, 3, 8]), (192, [1, 2, 2, 2, 3, 12]), (72, [1, 2, 2, 2, 7, 8]), (192, [1, 2, 2, 3, 3, 11]), (192, [1, 2, 2, 3, 4, 10]), (192, [1, 2, 2, 3, 5, 9]), (340, [1, 2, 2, 3, 6, 8]), (96, [1, 2, 2, 3, 7, 7]), (72, [1, 2, 2, 4, 5, 8]), (576, [1, 2, 2, 17]), (96, [1, 2, 3, 3, 5, 8]), (48, [1, 2, 3, 4, 4, 8]), (768, [1, 2, 3, 16]), (288, [1, 2, 8, 11]), (96, [1, 3, 8, 10]), (96, [2, 2, 2, 2, 3, 11]), (36, [2, 2, 2, 2, 6, 8]), (192, [2, 2, 2, 3, 3, 10]), (192, [2, 2, 2, 3, 4, 9])]

def node88Piece64UnitOutput_sector0_chunk1 : RawPoly ℕ := [(312, [2, 2, 2, 3, 5, 8]), (192, [2, 2, 2, 3, 6, 7]), (36, [2, 2, 2, 4, 4, 8]), (576, [2, 2, 2, 16]), (96, [2, 2, 3, 3, 3, 9]), (334, [2, 2, 3, 3, 4, 8]), (192, [2, 2, 3, 3, 5, 7]), (96, [2, 2, 3, 3, 6, 6]), (96, [2, 2, 3, 4, 4, 7]), (192, [2, 2, 3, 4, 5, 6]), (32, [2, 2, 3, 5, 5, 5]), (-3856, [2, 2, 3, 15]), (576, [2, 2, 4, 14]), (576, [2, 2, 5, 13]), (576, [2, 2, 6, 12]), (576, [2, 2, 7, 11]), (264, [2, 2, 8, 10]), (288, [2, 2, 9, 9]), (16, [2, 3, 3, 3, 3, 8]), (768, [2, 3, 3, 14]), (768, [2, 3, 4, 13]), (768, [2, 3, 5, 12]), (768, [2, 3, 6, 11]), (768, [2, 3, 7, 10])]

def node88Piece64UnitOutput_sector0_chunk2 : RawPoly ℕ := [(592, [2, 3, 8, 9]), (288, [2, 4, 8, 8]), (288, [2, 5, 7, 8]), (144, [2, 6, 6, 8]), (2304, [2, 20]), (96, [3, 3, 8, 8]), (96, [3, 4, 7, 8]), (96, [3, 5, 6, 8]), (768, [3, 19]), (288, [8, 14])]

def node88Piece64UnitOutput_sector0 : RawPoly ℕ := [node88Piece64UnitOutput_sector0_chunk0, node88Piece64UnitOutput_sector0_chunk1, node88Piece64UnitOutput_sector0_chunk2].flatten

def node88Piece64UnitOutput : SectorVector := [(0, node88Piece64UnitOutput_sector0)]

theorem node88Piece64_check : neutralDirectS JR (-4) node88Piece64UnitInput = node88Piece64UnitOutput := by decide +kernel

theorem node88Piece64_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece64Input) = evaluate node88Piece64Output :=
  mode_of_scaled _ _ (-60) node88Piece64UnitInput node88Piece64UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece64_check)

def node88Piece65Input_sector0 : RawPoly ℕ := [(-240, [2, 2, 4, 7])]

def node88Piece65Input : SectorVector := [(0, node88Piece65Input_sector0)]
def node88Piece65Output_sector0_chunk0 : RawPoly ℕ := [(-960, [1, 1, 1, 2, 2, 4, 4, 7]), (-2880, [1, 1, 2, 2, 2, 3, 4, 7]), (-20160, [1, 1, 2, 2, 4, 12]), (-11520, [1, 1, 2, 2, 7, 9]), (-11520, [1, 1, 2, 4, 7, 7]), (-960, [1, 2, 2, 2, 2, 2, 4, 7]), (-40320, [1, 2, 2, 2, 4, 11]), (-23040, [1, 2, 2, 2, 7, 8]), (-40320, [1, 2, 2, 3, 4, 10]), (-23040, [1, 2, 2, 3, 7, 7]), (-40320, [1, 2, 2, 4, 4, 9]), (-40320, [1, 2, 2, 4, 5, 8]), (-81600, [1, 2, 2, 4, 6, 7]), (-11520, [1, 2, 2, 5, 5, 7]), (-161280, [1, 2, 2, 17]), (-23040, [1, 2, 3, 4, 5, 7]), (-11520, [1, 2, 4, 4, 4, 7]), (-161280, [1, 2, 4, 15]), (-92160, [1, 2, 7, 12]), (-23040, [1, 4, 7, 10]), (-20160, [2, 2, 2, 2, 4, 10]), (-11520, [2, 2, 2, 2, 7, 7]), (-40320, [2, 2, 2, 3, 4, 9]), (-23040, [2, 2, 2, 3, 6, 7])]

def node88Piece65Output_sector0_chunk1 : RawPoly ℕ := [(-40320, [2, 2, 2, 4, 4, 8]), (-74880, [2, 2, 2, 4, 5, 7]), (-20160, [2, 2, 2, 4, 6, 6]), (-161280, [2, 2, 2, 16]), (-20160, [2, 2, 3, 3, 4, 8]), (-11520, [2, 2, 3, 3, 5, 7]), (-77280, [2, 2, 3, 4, 4, 7]), (-40320, [2, 2, 3, 4, 5, 6]), (-161280, [2, 2, 3, 15]), (-20160, [2, 2, 4, 4, 4, 6]), (-20160, [2, 2, 4, 4, 5, 5]), (584640, [2, 2, 4, 14]), (-161280, [2, 2, 5, 13]), (-161280, [2, 2, 6, 12]), (5760, [2, 2, 7, 11]), (-161280, [2, 2, 8, 10]), (-80640, [2, 2, 9, 9]), (-3840, [2, 3, 3, 3, 4, 7]), (-161280, [2, 3, 4, 13]), (-92160, [2, 3, 7, 10]), (-161280, [2, 4, 4, 12]), (-161280, [2, 4, 5, 11]), (-161280, [2, 4, 6, 10]), (-142080, [2, 4, 7, 9])]

def node88Piece65Output_sector0_chunk2 : RawPoly ℕ := [(-80640, [2, 4, 8, 8]), (-92160, [2, 5, 7, 8]), (-92160, [2, 6, 7, 7]), (-645120, [2, 20]), (-23040, [3, 4, 7, 8]), (-23040, [4, 4, 7, 7]), (-23040, [4, 5, 6, 7]), (-161280, [4, 18]), (-92160, [7, 15])]

def node88Piece65Output_sector0 : RawPoly ℕ := [node88Piece65Output_sector0_chunk0, node88Piece65Output_sector0_chunk1, node88Piece65Output_sector0_chunk2].flatten

def node88Piece65Output : SectorVector := [(0, node88Piece65Output_sector0)]

def node88Piece65UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 4, 7])]

def node88Piece65UnitInput_sector0 : RawPoly ℕ := [node88Piece65UnitInput_sector0_chunk0].flatten

def node88Piece65UnitInput : SectorVector := [(0, node88Piece65UnitInput_sector0)]

def node88Piece65UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 4, 4, 7]), (12, [1, 1, 2, 2, 2, 3, 4, 7]), (84, [1, 1, 2, 2, 4, 12]), (48, [1, 1, 2, 2, 7, 9]), (48, [1, 1, 2, 4, 7, 7]), (4, [1, 2, 2, 2, 2, 2, 4, 7]), (168, [1, 2, 2, 2, 4, 11]), (96, [1, 2, 2, 2, 7, 8]), (168, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 7, 7]), (168, [1, 2, 2, 4, 4, 9]), (168, [1, 2, 2, 4, 5, 8]), (340, [1, 2, 2, 4, 6, 7]), (48, [1, 2, 2, 5, 5, 7]), (672, [1, 2, 2, 17]), (96, [1, 2, 3, 4, 5, 7]), (48, [1, 2, 4, 4, 4, 7]), (672, [1, 2, 4, 15]), (384, [1, 2, 7, 12]), (96, [1, 4, 7, 10]), (84, [2, 2, 2, 2, 4, 10]), (48, [2, 2, 2, 2, 7, 7]), (168, [2, 2, 2, 3, 4, 9]), (96, [2, 2, 2, 3, 6, 7])]

def node88Piece65UnitOutput_sector0_chunk1 : RawPoly ℕ := [(168, [2, 2, 2, 4, 4, 8]), (312, [2, 2, 2, 4, 5, 7]), (84, [2, 2, 2, 4, 6, 6]), (672, [2, 2, 2, 16]), (84, [2, 2, 3, 3, 4, 8]), (48, [2, 2, 3, 3, 5, 7]), (322, [2, 2, 3, 4, 4, 7]), (168, [2, 2, 3, 4, 5, 6]), (672, [2, 2, 3, 15]), (84, [2, 2, 4, 4, 4, 6]), (84, [2, 2, 4, 4, 5, 5]), (-2436, [2, 2, 4, 14]), (672, [2, 2, 5, 13]), (672, [2, 2, 6, 12]), (-24, [2, 2, 7, 11]), (672, [2, 2, 8, 10]), (336, [2, 2, 9, 9]), (16, [2, 3, 3, 3, 4, 7]), (672, [2, 3, 4, 13]), (384, [2, 3, 7, 10]), (672, [2, 4, 4, 12]), (672, [2, 4, 5, 11]), (672, [2, 4, 6, 10]), (592, [2, 4, 7, 9])]

def node88Piece65UnitOutput_sector0_chunk2 : RawPoly ℕ := [(336, [2, 4, 8, 8]), (384, [2, 5, 7, 8]), (384, [2, 6, 7, 7]), (2688, [2, 20]), (96, [3, 4, 7, 8]), (96, [4, 4, 7, 7]), (96, [4, 5, 6, 7]), (672, [4, 18]), (384, [7, 15])]

def node88Piece65UnitOutput_sector0 : RawPoly ℕ := [node88Piece65UnitOutput_sector0_chunk0, node88Piece65UnitOutput_sector0_chunk1, node88Piece65UnitOutput_sector0_chunk2].flatten

def node88Piece65UnitOutput : SectorVector := [(0, node88Piece65UnitOutput_sector0)]

theorem node88Piece65_check : neutralDirectS JR (-4) node88Piece65UnitInput = node88Piece65UnitOutput := by decide +kernel

theorem node88Piece65_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece65Input) = evaluate node88Piece65Output :=
  mode_of_scaled _ _ (-240) node88Piece65UnitInput node88Piece65UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece65_check)

def node88Piece66Input_sector0 : RawPoly ℕ := [(-144, [2, 2, 5, 6])]

def node88Piece66Input : SectorVector := [(0, node88Piece66Input_sector0)]
def node88Piece66Output_sector0_chunk0 : RawPoly ℕ := [(-576, [1, 1, 1, 2, 2, 4, 5, 6]), (-1728, [1, 1, 2, 2, 2, 3, 5, 6]), (-10368, [1, 1, 2, 2, 5, 11]), (-8640, [1, 1, 2, 2, 6, 10]), (-6912, [1, 1, 2, 5, 6, 7]), (-576, [1, 2, 2, 2, 2, 2, 5, 6]), (-20736, [1, 2, 2, 2, 5, 10]), (-17280, [1, 2, 2, 2, 6, 9]), (-20736, [1, 2, 2, 3, 5, 9]), (-17280, [1, 2, 2, 3, 6, 8]), (-20736, [1, 2, 2, 4, 5, 8]), (-17280, [1, 2, 2, 4, 6, 7]), (-20736, [1, 2, 2, 5, 5, 7]), (-38592, [1, 2, 2, 5, 6, 6]), (-103680, [1, 2, 2, 17]), (-13824, [1, 2, 3, 5, 5, 6]), (-6912, [1, 2, 4, 4, 5, 6]), (-82944, [1, 2, 5, 14]), (-69120, [1, 2, 6, 13]), (-13824, [1, 5, 6, 10]), (-10368, [2, 2, 2, 2, 5, 9]), (-8640, [2, 2, 2, 2, 6, 8]), (-20736, [2, 2, 2, 3, 5, 8]), (-17280, [2, 2, 2, 3, 6, 7])]

def node88Piece66Output_sector0_chunk1 : RawPoly ℕ := [(-20736, [2, 2, 2, 4, 5, 7]), (-17280, [2, 2, 2, 4, 6, 6]), (-36288, [2, 2, 2, 5, 5, 6]), (-103680, [2, 2, 2, 16]), (-10368, [2, 2, 3, 3, 5, 7]), (-8640, [2, 2, 3, 3, 6, 6]), (-53280, [2, 2, 3, 4, 5, 6]), (-10368, [2, 2, 3, 5, 5, 5]), (-103680, [2, 2, 3, 15]), (-2880, [2, 2, 4, 4, 4, 6]), (-10368, [2, 2, 4, 4, 5, 5]), (-103680, [2, 2, 4, 14]), (193536, [2, 2, 5, 13]), (79200, [2, 2, 6, 12]), (-103680, [2, 2, 7, 11]), (-103680, [2, 2, 8, 10]), (-51840, [2, 2, 9, 9]), (-2304, [2, 3, 3, 3, 5, 6]), (-82944, [2, 3, 5, 12]), (-69120, [2, 3, 6, 11]), (-82944, [2, 4, 5, 11]), (-69120, [2, 4, 6, 10]), (-82944, [2, 5, 5, 10]), (-85248, [2, 5, 6, 9])]

def node88Piece66Output_sector0_chunk2 : RawPoly ℕ := [(-82944, [2, 5, 7, 8]), (-69120, [2, 6, 6, 8]), (-34560, [2, 6, 7, 7]), (-414720, [2, 20]), (-13824, [3, 5, 6, 8]), (-13824, [4, 5, 6, 7]), (-13824, [5, 5, 6, 6]), (-82944, [5, 17]), (-69120, [6, 16])]

def node88Piece66Output_sector0 : RawPoly ℕ := [node88Piece66Output_sector0_chunk0, node88Piece66Output_sector0_chunk1, node88Piece66Output_sector0_chunk2].flatten

def node88Piece66Output : SectorVector := [(0, node88Piece66Output_sector0)]

def node88Piece66UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 2, 5, 6])]

def node88Piece66UnitInput_sector0 : RawPoly ℕ := [node88Piece66UnitInput_sector0_chunk0].flatten

def node88Piece66UnitInput : SectorVector := [(0, node88Piece66UnitInput_sector0)]

def node88Piece66UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 2, 4, 5, 6]), (12, [1, 1, 2, 2, 2, 3, 5, 6]), (72, [1, 1, 2, 2, 5, 11]), (60, [1, 1, 2, 2, 6, 10]), (48, [1, 1, 2, 5, 6, 7]), (4, [1, 2, 2, 2, 2, 2, 5, 6]), (144, [1, 2, 2, 2, 5, 10]), (120, [1, 2, 2, 2, 6, 9]), (144, [1, 2, 2, 3, 5, 9]), (120, [1, 2, 2, 3, 6, 8]), (144, [1, 2, 2, 4, 5, 8]), (120, [1, 2, 2, 4, 6, 7]), (144, [1, 2, 2, 5, 5, 7]), (268, [1, 2, 2, 5, 6, 6]), (720, [1, 2, 2, 17]), (96, [1, 2, 3, 5, 5, 6]), (48, [1, 2, 4, 4, 5, 6]), (576, [1, 2, 5, 14]), (480, [1, 2, 6, 13]), (96, [1, 5, 6, 10]), (72, [2, 2, 2, 2, 5, 9]), (60, [2, 2, 2, 2, 6, 8]), (144, [2, 2, 2, 3, 5, 8]), (120, [2, 2, 2, 3, 6, 7])]

def node88Piece66UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [2, 2, 2, 4, 5, 7]), (120, [2, 2, 2, 4, 6, 6]), (252, [2, 2, 2, 5, 5, 6]), (720, [2, 2, 2, 16]), (72, [2, 2, 3, 3, 5, 7]), (60, [2, 2, 3, 3, 6, 6]), (370, [2, 2, 3, 4, 5, 6]), (72, [2, 2, 3, 5, 5, 5]), (720, [2, 2, 3, 15]), (20, [2, 2, 4, 4, 4, 6]), (72, [2, 2, 4, 4, 5, 5]), (720, [2, 2, 4, 14]), (-1344, [2, 2, 5, 13]), (-550, [2, 2, 6, 12]), (720, [2, 2, 7, 11]), (720, [2, 2, 8, 10]), (360, [2, 2, 9, 9]), (16, [2, 3, 3, 3, 5, 6]), (576, [2, 3, 5, 12]), (480, [2, 3, 6, 11]), (576, [2, 4, 5, 11]), (480, [2, 4, 6, 10]), (576, [2, 5, 5, 10]), (592, [2, 5, 6, 9])]

def node88Piece66UnitOutput_sector0_chunk2 : RawPoly ℕ := [(576, [2, 5, 7, 8]), (480, [2, 6, 6, 8]), (240, [2, 6, 7, 7]), (2880, [2, 20]), (96, [3, 5, 6, 8]), (96, [4, 5, 6, 7]), (96, [5, 5, 6, 6]), (576, [5, 17]), (480, [6, 16])]

def node88Piece66UnitOutput_sector0 : RawPoly ℕ := [node88Piece66UnitOutput_sector0_chunk0, node88Piece66UnitOutput_sector0_chunk1, node88Piece66UnitOutput_sector0_chunk2].flatten

def node88Piece66UnitOutput : SectorVector := [(0, node88Piece66UnitOutput_sector0)]

theorem node88Piece66_check : neutralDirectS JR (-4) node88Piece66UnitInput = node88Piece66UnitOutput := by decide +kernel

theorem node88Piece66_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece66Input) = evaluate node88Piece66Output :=
  mode_of_scaled _ _ (-144) node88Piece66UnitInput node88Piece66UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece66_check)

def node88Piece67Input_sector0 : RawPoly ℕ := [(960/7, [2, 3, 3, 7])]

def node88Piece67Input : SectorVector := [(0, node88Piece67Input_sector0)]
def node88Piece67Output_sector0_chunk0 : RawPoly ℕ := [(3840/7, [1, 1, 1, 2, 3, 3, 4, 7]), (11520/7, [1, 1, 2, 2, 3, 3, 3, 7]), (11520, [1, 1, 2, 3, 3, 12]), (69120/7, [1, 1, 2, 3, 7, 8]), (23040/7, [1, 1, 3, 3, 7, 7]), (3840/7, [1, 2, 2, 2, 2, 3, 3, 7]), (23040, [1, 2, 2, 3, 3, 11]), (138240/7, [1, 2, 2, 3, 7, 7]), (23040, [1, 2, 3, 3, 3, 10]), (23040, [1, 2, 3, 3, 4, 9]), (23040, [1, 2, 3, 3, 5, 8]), (326400/7, [1, 2, 3, 3, 6, 7]), (138240/7, [1, 2, 3, 4, 5, 7]), (138240, [1, 2, 3, 16]), (207360/7, [1, 2, 7, 12]), (46080/7, [1, 3, 3, 3, 5, 7]), (23040/7, [1, 3, 3, 4, 4, 7]), (46080, [1, 3, 3, 15]), (276480/7, [1, 3, 7, 11]), (11520, [2, 2, 2, 3, 3, 10]), (69120/7, [2, 2, 2, 3, 6, 7]), (23040, [2, 2, 3, 3, 3, 9]), (23040, [2, 2, 3, 3, 4, 8]), (46080, [2, 2, 3, 3, 5, 7])]

def node88Piece67Output_sector0_chunk1 : RawPoly ℕ := [(11520, [2, 2, 3, 3, 6, 6]), (69120/7, [2, 2, 3, 4, 4, 7]), (138240, [2, 2, 3, 15]), (207360/7, [2, 2, 7, 11]), (11520, [2, 3, 3, 3, 3, 8]), (286080/7, [2, 3, 3, 3, 4, 7]), (23040, [2, 3, 3, 3, 5, 6]), (11520, [2, 3, 3, 4, 4, 6]), (11520, [2, 3, 3, 4, 5, 5]), (-334080, [2, 3, 3, 14]), (138240, [2, 3, 4, 13]), (138240, [2, 3, 5, 12]), (138240, [2, 3, 6, 11]), (299520/7, [2, 3, 7, 10]), (138240, [2, 3, 8, 9]), (207360/7, [2, 4, 7, 9]), (207360/7, [2, 5, 7, 8]), (207360/7, [2, 6, 7, 7]), (207360, [2, 20]), (7680/7, [3, 3, 3, 3, 3, 7]), (46080, [3, 3, 3, 13]), (46080, [3, 3, 4, 12]), (46080, [3, 3, 5, 11]), (46080, [3, 3, 6, 10])]

def node88Piece67Output_sector0_chunk2 : RawPoly ℕ := [(330240/7, [3, 3, 7, 9]), (23040, [3, 3, 8, 8]), (276480/7, [3, 4, 7, 8]), (276480/7, [3, 5, 7, 7]), (138240/7, [3, 6, 6, 7]), (276480, [3, 19]), (414720/7, [7, 15])]

def node88Piece67Output_sector0 : RawPoly ℕ := [node88Piece67Output_sector0_chunk0, node88Piece67Output_sector0_chunk1, node88Piece67Output_sector0_chunk2].flatten

def node88Piece67Output : SectorVector := [(0, node88Piece67Output_sector0)]

def node88Piece67UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 3, 7])]

def node88Piece67UnitInput_sector0 : RawPoly ℕ := [node88Piece67UnitInput_sector0_chunk0].flatten

def node88Piece67UnitInput : SectorVector := [(0, node88Piece67UnitInput_sector0)]

def node88Piece67UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 3, 4, 7]), (12, [1, 1, 2, 2, 3, 3, 3, 7]), (84, [1, 1, 2, 3, 3, 12]), (72, [1, 1, 2, 3, 7, 8]), (24, [1, 1, 3, 3, 7, 7]), (4, [1, 2, 2, 2, 2, 3, 3, 7]), (168, [1, 2, 2, 3, 3, 11]), (144, [1, 2, 2, 3, 7, 7]), (168, [1, 2, 3, 3, 3, 10]), (168, [1, 2, 3, 3, 4, 9]), (168, [1, 2, 3, 3, 5, 8]), (340, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 5, 7]), (1008, [1, 2, 3, 16]), (216, [1, 2, 7, 12]), (48, [1, 3, 3, 3, 5, 7]), (24, [1, 3, 3, 4, 4, 7]), (336, [1, 3, 3, 15]), (288, [1, 3, 7, 11]), (84, [2, 2, 2, 3, 3, 10]), (72, [2, 2, 2, 3, 6, 7]), (168, [2, 2, 3, 3, 3, 9]), (168, [2, 2, 3, 3, 4, 8]), (336, [2, 2, 3, 3, 5, 7])]

def node88Piece67UnitOutput_sector0_chunk1 : RawPoly ℕ := [(84, [2, 2, 3, 3, 6, 6]), (72, [2, 2, 3, 4, 4, 7]), (1008, [2, 2, 3, 15]), (216, [2, 2, 7, 11]), (84, [2, 3, 3, 3, 3, 8]), (298, [2, 3, 3, 3, 4, 7]), (168, [2, 3, 3, 3, 5, 6]), (84, [2, 3, 3, 4, 4, 6]), (84, [2, 3, 3, 4, 5, 5]), (-2436, [2, 3, 3, 14]), (1008, [2, 3, 4, 13]), (1008, [2, 3, 5, 12]), (1008, [2, 3, 6, 11]), (312, [2, 3, 7, 10]), (1008, [2, 3, 8, 9]), (216, [2, 4, 7, 9]), (216, [2, 5, 7, 8]), (216, [2, 6, 7, 7]), (1512, [2, 20]), (8, [3, 3, 3, 3, 3, 7]), (336, [3, 3, 3, 13]), (336, [3, 3, 4, 12]), (336, [3, 3, 5, 11]), (336, [3, 3, 6, 10])]

def node88Piece67UnitOutput_sector0_chunk2 : RawPoly ℕ := [(344, [3, 3, 7, 9]), (168, [3, 3, 8, 8]), (288, [3, 4, 7, 8]), (288, [3, 5, 7, 7]), (144, [3, 6, 6, 7]), (2016, [3, 19]), (432, [7, 15])]

def node88Piece67UnitOutput_sector0 : RawPoly ℕ := [node88Piece67UnitOutput_sector0_chunk0, node88Piece67UnitOutput_sector0_chunk1, node88Piece67UnitOutput_sector0_chunk2].flatten

def node88Piece67UnitOutput : SectorVector := [(0, node88Piece67UnitOutput_sector0)]

theorem node88Piece67_check : neutralDirectS JR (-4) node88Piece67UnitInput = node88Piece67UnitOutput := by decide +kernel

theorem node88Piece67_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece67Input) = evaluate node88Piece67Output :=
  mode_of_scaled _ _ (960/7) node88Piece67UnitInput node88Piece67UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece67_check)

def node88Piece68Input_sector0 : RawPoly ℕ := [(-40, [2, 3, 4, 6])]

def node88Piece68Input : SectorVector := [(0, node88Piece68Input_sector0)]
def node88Piece68Output_sector0_chunk0 : RawPoly ℕ := [(-160, [1, 1, 1, 2, 3, 4, 4, 6]), (-480, [1, 1, 2, 2, 3, 3, 4, 6]), (-2880, [1, 1, 2, 3, 4, 11]), (-1920, [1, 1, 2, 3, 6, 9]), (-1440, [1, 1, 2, 4, 6, 8]), (-960, [1, 1, 3, 4, 6, 7]), (-160, [1, 2, 2, 2, 2, 3, 4, 6]), (-5760, [1, 2, 2, 3, 4, 10]), (-3840, [1, 2, 2, 3, 6, 8]), (-2880, [1, 2, 2, 4, 6, 7]), (-5760, [1, 2, 3, 3, 4, 9]), (-3840, [1, 2, 3, 3, 6, 7]), (-5760, [1, 2, 3, 4, 4, 8]), (-5760, [1, 2, 3, 4, 5, 7]), (-10720, [1, 2, 3, 4, 6, 6]), (-1920, [1, 2, 3, 5, 5, 6]), (-23040, [1, 2, 3, 16]), (-2880, [1, 2, 4, 4, 5, 6]), (-17280, [1, 2, 4, 15]), (-11520, [1, 2, 6, 13]), (-1920, [1, 3, 3, 4, 5, 6]), (-960, [1, 3, 4, 4, 4, 6]), (-11520, [1, 3, 4, 14]), (-7680, [1, 3, 6, 12])]

def node88Piece68Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [1, 4, 6, 11]), (-2880, [2, 2, 2, 3, 4, 9]), (-1920, [2, 2, 2, 3, 6, 7]), (-1440, [2, 2, 2, 4, 6, 6]), (-5760, [2, 2, 3, 3, 4, 8]), (-3840, [2, 2, 3, 3, 6, 6]), (-5760, [2, 2, 3, 4, 4, 7]), (-13440, [2, 2, 3, 4, 5, 6]), (-23040, [2, 2, 3, 15]), (-1440, [2, 2, 4, 4, 4, 6]), (-17280, [2, 2, 4, 14]), (-11520, [2, 2, 6, 12]), (-2880, [2, 3, 3, 3, 4, 7]), (-1920, [2, 3, 3, 3, 5, 6]), (-11440, [2, 3, 3, 4, 4, 6]), (-2880, [2, 3, 3, 4, 5, 5]), (-23040, [2, 3, 3, 14]), (-2880, [2, 3, 4, 4, 4, 5]), (53760, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12]), (960, [2, 3, 6, 11]), (-23040, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-17280, [2, 4, 4, 12])]

def node88Piece68Output_sector0_chunk2 : RawPoly ℕ := [(-17280, [2, 4, 5, 11]), (-10560, [2, 4, 6, 10]), (-17280, [2, 4, 7, 9]), (-8640, [2, 4, 8, 8]), (-11520, [2, 5, 6, 9]), (-11520, [2, 6, 6, 8]), (-5760, [2, 6, 7, 7]), (-69120, [2, 20]), (-320, [3, 3, 3, 3, 4, 6]), (-11520, [3, 3, 4, 12]), (-7680, [3, 3, 6, 10]), (-11520, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-13760, [3, 4, 6, 9]), (-11520, [3, 4, 7, 8]), (-7680, [3, 5, 6, 8]), (-7680, [3, 6, 6, 7]), (-46080, [3, 19]), (-5760, [4, 4, 6, 8]), (-5760, [4, 5, 6, 7]), (-2880, [4, 6, 6, 6]), (-34560, [4, 18]), (-23040, [6, 16])]

def node88Piece68Output_sector0 : RawPoly ℕ := [node88Piece68Output_sector0_chunk0, node88Piece68Output_sector0_chunk1, node88Piece68Output_sector0_chunk2].flatten

def node88Piece68Output : SectorVector := [(0, node88Piece68Output_sector0)]

def node88Piece68UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 4, 6])]

def node88Piece68UnitInput_sector0 : RawPoly ℕ := [node88Piece68UnitInput_sector0_chunk0].flatten

def node88Piece68UnitInput : SectorVector := [(0, node88Piece68UnitInput_sector0)]

def node88Piece68UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 4, 6]), (12, [1, 1, 2, 2, 3, 3, 4, 6]), (72, [1, 1, 2, 3, 4, 11]), (48, [1, 1, 2, 3, 6, 9]), (36, [1, 1, 2, 4, 6, 8]), (24, [1, 1, 3, 4, 6, 7]), (4, [1, 2, 2, 2, 2, 3, 4, 6]), (144, [1, 2, 2, 3, 4, 10]), (96, [1, 2, 2, 3, 6, 8]), (72, [1, 2, 2, 4, 6, 7]), (144, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 6, 7]), (144, [1, 2, 3, 4, 4, 8]), (144, [1, 2, 3, 4, 5, 7]), (268, [1, 2, 3, 4, 6, 6]), (48, [1, 2, 3, 5, 5, 6]), (576, [1, 2, 3, 16]), (72, [1, 2, 4, 4, 5, 6]), (432, [1, 2, 4, 15]), (288, [1, 2, 6, 13]), (48, [1, 3, 3, 4, 5, 6]), (24, [1, 3, 4, 4, 4, 6]), (288, [1, 3, 4, 14]), (192, [1, 3, 6, 12])]

def node88Piece68UnitOutput_sector0_chunk1 : RawPoly ℕ := [(144, [1, 4, 6, 11]), (72, [2, 2, 2, 3, 4, 9]), (48, [2, 2, 2, 3, 6, 7]), (36, [2, 2, 2, 4, 6, 6]), (144, [2, 2, 3, 3, 4, 8]), (96, [2, 2, 3, 3, 6, 6]), (144, [2, 2, 3, 4, 4, 7]), (336, [2, 2, 3, 4, 5, 6]), (576, [2, 2, 3, 15]), (36, [2, 2, 4, 4, 4, 6]), (432, [2, 2, 4, 14]), (288, [2, 2, 6, 12]), (72, [2, 3, 3, 3, 4, 7]), (48, [2, 3, 3, 3, 5, 6]), (286, [2, 3, 3, 4, 4, 6]), (72, [2, 3, 3, 4, 5, 5]), (576, [2, 3, 3, 14]), (72, [2, 3, 4, 4, 4, 5]), (-1344, [2, 3, 4, 13]), (576, [2, 3, 5, 12]), (-24, [2, 3, 6, 11]), (576, [2, 3, 7, 10]), (576, [2, 3, 8, 9]), (432, [2, 4, 4, 12])]

def node88Piece68UnitOutput_sector0_chunk2 : RawPoly ℕ := [(432, [2, 4, 5, 11]), (264, [2, 4, 6, 10]), (432, [2, 4, 7, 9]), (216, [2, 4, 8, 8]), (288, [2, 5, 6, 9]), (288, [2, 6, 6, 8]), (144, [2, 6, 7, 7]), (1728, [2, 20]), (8, [3, 3, 3, 3, 4, 6]), (288, [3, 3, 4, 12]), (192, [3, 3, 6, 10]), (288, [3, 4, 4, 11]), (288, [3, 4, 5, 10]), (344, [3, 4, 6, 9]), (288, [3, 4, 7, 8]), (192, [3, 5, 6, 8]), (192, [3, 6, 6, 7]), (1152, [3, 19]), (144, [4, 4, 6, 8]), (144, [4, 5, 6, 7]), (72, [4, 6, 6, 6]), (864, [4, 18]), (576, [6, 16])]

def node88Piece68UnitOutput_sector0 : RawPoly ℕ := [node88Piece68UnitOutput_sector0_chunk0, node88Piece68UnitOutput_sector0_chunk1, node88Piece68UnitOutput_sector0_chunk2].flatten

def node88Piece68UnitOutput : SectorVector := [(0, node88Piece68UnitOutput_sector0)]

theorem node88Piece68_check : neutralDirectS JR (-4) node88Piece68UnitInput = node88Piece68UnitOutput := by decide +kernel

theorem node88Piece68_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece68Input) = evaluate node88Piece68Output :=
  mode_of_scaled _ _ (-40) node88Piece68UnitInput node88Piece68UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece68_check)

def node88Piece69Input_sector0 : RawPoly ℕ := [(288/5, [2, 3, 5, 5])]

def node88Piece69Input : SectorVector := [(0, node88Piece69Input_sector0)]
def node88Piece69Output_sector0_chunk0 : RawPoly ℕ := [(1152/5, [1, 1, 1, 2, 3, 4, 5, 5]), (3456/5, [1, 1, 2, 2, 3, 3, 5, 5]), (6912, [1, 1, 2, 3, 5, 10]), (10368/5, [1, 1, 2, 5, 5, 8]), (6912/5, [1, 1, 3, 5, 5, 7]), (1152/5, [1, 2, 2, 2, 2, 3, 5, 5]), (13824, [1, 2, 2, 3, 5, 9]), (20736/5, [1, 2, 2, 5, 5, 7]), (13824, [1, 2, 3, 3, 5, 8]), (13824, [1, 2, 3, 4, 5, 7]), (19584, [1, 2, 3, 5, 5, 6]), (34560, [1, 2, 3, 16]), (20736/5, [1, 2, 4, 5, 5, 5]), (41472, [1, 2, 5, 14]), (13824/5, [1, 3, 3, 5, 5, 5]), (6912/5, [1, 3, 4, 4, 5, 5]), (27648, [1, 3, 5, 13]), (41472/5, [1, 5, 5, 11]), (6912, [2, 2, 2, 3, 5, 8]), (10368/5, [2, 2, 2, 5, 5, 6]), (13824, [2, 2, 3, 3, 5, 7]), (13824, [2, 2, 3, 4, 5, 6]), (62208/5, [2, 2, 3, 5, 5, 5]), (34560, [2, 2, 3, 15])]

def node88Piece69Output_sector0_chunk1 : RawPoly ℕ := [(10368/5, [2, 2, 4, 4, 5, 5]), (41472, [2, 2, 5, 13]), (6912, [2, 3, 3, 3, 5, 6]), (96192/5, [2, 3, 3, 4, 5, 5]), (34560, [2, 3, 3, 14]), (2304, [2, 3, 4, 4, 4, 5]), (34560, [2, 3, 4, 13]), (-97920, [2, 3, 5, 12]), (34560, [2, 3, 6, 11]), (34560, [2, 3, 7, 10]), (34560, [2, 3, 8, 9]), (41472, [2, 4, 5, 11]), (76032/5, [2, 5, 5, 10]), (41472, [2, 5, 6, 9]), (41472, [2, 5, 7, 8]), (103680, [2, 20]), (2304/5, [3, 3, 3, 3, 5, 5]), (27648, [3, 3, 5, 11]), (27648, [3, 4, 5, 10]), (99072/5, [3, 5, 5, 9]), (27648, [3, 5, 6, 8]), (13824, [3, 5, 7, 7]), (69120, [3, 19]), (41472/5, [4, 5, 5, 8])]

def node88Piece69Output_sector0_chunk2 : RawPoly ℕ := [(41472/5, [5, 5, 5, 7]), (20736/5, [5, 5, 6, 6]), (82944, [5, 17])]

def node88Piece69Output_sector0 : RawPoly ℕ := [node88Piece69Output_sector0_chunk0, node88Piece69Output_sector0_chunk1, node88Piece69Output_sector0_chunk2].flatten

def node88Piece69Output : SectorVector := [(0, node88Piece69Output_sector0)]

def node88Piece69UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 3, 5, 5])]

def node88Piece69UnitInput_sector0 : RawPoly ℕ := [node88Piece69UnitInput_sector0_chunk0].flatten

def node88Piece69UnitInput : SectorVector := [(0, node88Piece69UnitInput_sector0)]

def node88Piece69UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 3, 4, 5, 5]), (12, [1, 1, 2, 2, 3, 3, 5, 5]), (120, [1, 1, 2, 3, 5, 10]), (36, [1, 1, 2, 5, 5, 8]), (24, [1, 1, 3, 5, 5, 7]), (4, [1, 2, 2, 2, 2, 3, 5, 5]), (240, [1, 2, 2, 3, 5, 9]), (72, [1, 2, 2, 5, 5, 7]), (240, [1, 2, 3, 3, 5, 8]), (240, [1, 2, 3, 4, 5, 7]), (340, [1, 2, 3, 5, 5, 6]), (600, [1, 2, 3, 16]), (72, [1, 2, 4, 5, 5, 5]), (720, [1, 2, 5, 14]), (48, [1, 3, 3, 5, 5, 5]), (24, [1, 3, 4, 4, 5, 5]), (480, [1, 3, 5, 13]), (144, [1, 5, 5, 11]), (120, [2, 2, 2, 3, 5, 8]), (36, [2, 2, 2, 5, 5, 6]), (240, [2, 2, 3, 3, 5, 7]), (240, [2, 2, 3, 4, 5, 6]), (216, [2, 2, 3, 5, 5, 5]), (600, [2, 2, 3, 15])]

def node88Piece69UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 2, 4, 4, 5, 5]), (720, [2, 2, 5, 13]), (120, [2, 3, 3, 3, 5, 6]), (334, [2, 3, 3, 4, 5, 5]), (600, [2, 3, 3, 14]), (40, [2, 3, 4, 4, 4, 5]), (600, [2, 3, 4, 13]), (-1700, [2, 3, 5, 12]), (600, [2, 3, 6, 11]), (600, [2, 3, 7, 10]), (600, [2, 3, 8, 9]), (720, [2, 4, 5, 11]), (264, [2, 5, 5, 10]), (720, [2, 5, 6, 9]), (720, [2, 5, 7, 8]), (1800, [2, 20]), (8, [3, 3, 3, 3, 5, 5]), (480, [3, 3, 5, 11]), (480, [3, 4, 5, 10]), (344, [3, 5, 5, 9]), (480, [3, 5, 6, 8]), (240, [3, 5, 7, 7]), (1200, [3, 19]), (144, [4, 5, 5, 8])]

def node88Piece69UnitOutput_sector0_chunk2 : RawPoly ℕ := [(144, [5, 5, 5, 7]), (72, [5, 5, 6, 6]), (1440, [5, 17])]

def node88Piece69UnitOutput_sector0 : RawPoly ℕ := [node88Piece69UnitOutput_sector0_chunk0, node88Piece69UnitOutput_sector0_chunk1, node88Piece69UnitOutput_sector0_chunk2].flatten

def node88Piece69UnitOutput : SectorVector := [(0, node88Piece69UnitOutput_sector0)]

theorem node88Piece69_check : neutralDirectS JR (-4) node88Piece69UnitInput = node88Piece69UnitOutput := by decide +kernel

theorem node88Piece69_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece69Input) = evaluate node88Piece69Output :=
  mode_of_scaled _ _ (288/5) node88Piece69UnitInput node88Piece69UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece69_check)

def node88Piece70Input_sector0 : RawPoly ℕ := [(-132, [2, 4, 4, 5])]

def node88Piece70Input : SectorVector := [(0, node88Piece70Input_sector0)]
def node88Piece70Output_sector0_chunk0 : RawPoly ℕ := [(-528, [1, 1, 1, 2, 4, 4, 4, 5]), (-1584, [1, 1, 2, 2, 3, 4, 4, 5]), (-7920, [1, 1, 2, 4, 4, 10]), (-12672, [1, 1, 2, 4, 5, 9]), (-3168, [1, 1, 4, 4, 5, 7]), (-528, [1, 2, 2, 2, 2, 4, 4, 5]), (-15840, [1, 2, 2, 4, 4, 9]), (-25344, [1, 2, 2, 4, 5, 8]), (-15840, [1, 2, 3, 4, 4, 8]), (-25344, [1, 2, 3, 4, 5, 7]), (-15840, [1, 2, 4, 4, 4, 7]), (-44880, [1, 2, 4, 4, 5, 6]), (-12672, [1, 2, 4, 5, 5, 5]), (-126720, [1, 2, 4, 15]), (-50688, [1, 2, 5, 14]), (-6336, [1, 3, 4, 4, 5, 5]), (-3168, [1, 4, 4, 4, 4, 5]), (-31680, [1, 4, 4, 13]), (-50688, [1, 4, 5, 12]), (-7920, [2, 2, 2, 4, 4, 8]), (-12672, [2, 2, 2, 4, 5, 7]), (-15840, [2, 2, 3, 4, 4, 7]), (-25344, [2, 2, 3, 4, 5, 6]), (-15840, [2, 2, 4, 4, 4, 6])]

def node88Piece70Output_sector0_chunk1 : RawPoly ℕ := [(-36432, [2, 2, 4, 4, 5, 5]), (-126720, [2, 2, 4, 14]), (-50688, [2, 2, 5, 13]), (-7920, [2, 3, 3, 4, 4, 6]), (-12672, [2, 3, 3, 4, 5, 5]), (-36168, [2, 3, 4, 4, 4, 5]), (-126720, [2, 3, 4, 13]), (-50688, [2, 3, 5, 12]), (-2640, [2, 4, 4, 4, 4, 4]), (72600, [2, 4, 4, 12]), (57024, [2, 4, 5, 11]), (-126720, [2, 4, 6, 10]), (-126720, [2, 4, 7, 9]), (-63360, [2, 4, 8, 8]), (-50688, [2, 5, 5, 10]), (-50688, [2, 5, 6, 9]), (-50688, [2, 5, 7, 8]), (-253440, [2, 20]), (-1056, [3, 3, 3, 4, 4, 5]), (-31680, [3, 4, 4, 11]), (-50688, [3, 4, 5, 10]), (-31680, [4, 4, 4, 10]), (-45408, [4, 4, 5, 9]), (-31680, [4, 4, 6, 8])]

def node88Piece70Output_sector0_chunk2 : RawPoly ℕ := [(-15840, [4, 4, 7, 7]), (-50688, [4, 5, 5, 8]), (-50688, [4, 5, 6, 7]), (-253440, [4, 18]), (-101376, [5, 17])]

def node88Piece70Output_sector0 : RawPoly ℕ := [node88Piece70Output_sector0_chunk0, node88Piece70Output_sector0_chunk1, node88Piece70Output_sector0_chunk2].flatten

def node88Piece70Output : SectorVector := [(0, node88Piece70Output_sector0)]

def node88Piece70UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 4, 4, 5])]

def node88Piece70UnitInput_sector0 : RawPoly ℕ := [node88Piece70UnitInput_sector0_chunk0].flatten

def node88Piece70UnitInput : SectorVector := [(0, node88Piece70UnitInput_sector0)]

def node88Piece70UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 4, 4, 4, 5]), (12, [1, 1, 2, 2, 3, 4, 4, 5]), (60, [1, 1, 2, 4, 4, 10]), (96, [1, 1, 2, 4, 5, 9]), (24, [1, 1, 4, 4, 5, 7]), (4, [1, 2, 2, 2, 2, 4, 4, 5]), (120, [1, 2, 2, 4, 4, 9]), (192, [1, 2, 2, 4, 5, 8]), (120, [1, 2, 3, 4, 4, 8]), (192, [1, 2, 3, 4, 5, 7]), (120, [1, 2, 4, 4, 4, 7]), (340, [1, 2, 4, 4, 5, 6]), (96, [1, 2, 4, 5, 5, 5]), (960, [1, 2, 4, 15]), (384, [1, 2, 5, 14]), (48, [1, 3, 4, 4, 5, 5]), (24, [1, 4, 4, 4, 4, 5]), (240, [1, 4, 4, 13]), (384, [1, 4, 5, 12]), (60, [2, 2, 2, 4, 4, 8]), (96, [2, 2, 2, 4, 5, 7]), (120, [2, 2, 3, 4, 4, 7]), (192, [2, 2, 3, 4, 5, 6]), (120, [2, 2, 4, 4, 4, 6])]

def node88Piece70UnitOutput_sector0_chunk1 : RawPoly ℕ := [(276, [2, 2, 4, 4, 5, 5]), (960, [2, 2, 4, 14]), (384, [2, 2, 5, 13]), (60, [2, 3, 3, 4, 4, 6]), (96, [2, 3, 3, 4, 5, 5]), (274, [2, 3, 4, 4, 4, 5]), (960, [2, 3, 4, 13]), (384, [2, 3, 5, 12]), (20, [2, 4, 4, 4, 4, 4]), (-550, [2, 4, 4, 12]), (-432, [2, 4, 5, 11]), (960, [2, 4, 6, 10]), (960, [2, 4, 7, 9]), (480, [2, 4, 8, 8]), (384, [2, 5, 5, 10]), (384, [2, 5, 6, 9]), (384, [2, 5, 7, 8]), (1920, [2, 20]), (8, [3, 3, 3, 4, 4, 5]), (240, [3, 4, 4, 11]), (384, [3, 4, 5, 10]), (240, [4, 4, 4, 10]), (344, [4, 4, 5, 9]), (240, [4, 4, 6, 8])]

def node88Piece70UnitOutput_sector0_chunk2 : RawPoly ℕ := [(120, [4, 4, 7, 7]), (384, [4, 5, 5, 8]), (384, [4, 5, 6, 7]), (1920, [4, 18]), (768, [5, 17])]

def node88Piece70UnitOutput_sector0 : RawPoly ℕ := [node88Piece70UnitOutput_sector0_chunk0, node88Piece70UnitOutput_sector0_chunk1, node88Piece70UnitOutput_sector0_chunk2].flatten

def node88Piece70UnitOutput : SectorVector := [(0, node88Piece70UnitOutput_sector0)]

theorem node88Piece70_check : neutralDirectS JR (-4) node88Piece70UnitInput = node88Piece70UnitOutput := by decide +kernel

theorem node88Piece70_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece70Input) = evaluate node88Piece70Output :=
  mode_of_scaled _ _ (-132) node88Piece70UnitInput node88Piece70UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece70_check)

def node88Piece71Input_sector0 : RawPoly ℕ := [(-960/13, [2, 13])]

def node88Piece71Input : SectorVector := [(0, node88Piece71Input_sector0)]
def node88Piece71Output_sector0_chunk0 : RawPoly ℕ := [(-3840/13, [1, 1, 1, 2, 4, 13]), (-11520/13, [1, 1, 2, 2, 3, 13]), (-11520, [1, 1, 2, 18]), (-23040/13, [1, 1, 7, 13]), (-3840/13, [1, 2, 2, 2, 2, 13]), (-23040, [1, 2, 2, 17]), (-23040, [1, 2, 3, 16]), (-23040, [1, 2, 4, 15]), (-23040, [1, 2, 5, 14]), (-326400/13, [1, 2, 6, 13]), (-23040, [1, 2, 7, 12]), (-23040, [1, 2, 8, 11]), (-23040, [1, 2, 9, 10]), (-46080/13, [1, 3, 5, 13]), (-23040/13, [1, 4, 4, 13]), (-46080, [1, 21]), (-11520, [2, 2, 2, 16]), (-23040, [2, 2, 3, 15]), (-23040, [2, 2, 4, 14]), (-322560/13, [2, 2, 5, 13]), (-23040, [2, 2, 6, 12]), (-23040, [2, 2, 7, 11]), (-23040, [2, 2, 8, 10]), (-11520, [2, 2, 9, 9])]

def node88Piece71Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 3, 3, 14]), (-355200/13, [2, 3, 4, 13]), (-23040, [2, 3, 5, 12]), (-23040, [2, 3, 6, 11]), (-23040, [2, 3, 7, 10]), (-23040, [2, 3, 8, 9]), (-11520, [2, 4, 4, 12]), (-23040, [2, 4, 5, 11]), (-23040, [2, 4, 6, 10]), (-23040, [2, 4, 7, 9]), (-11520, [2, 4, 8, 8]), (-11520, [2, 5, 5, 10]), (-23040, [2, 5, 6, 9]), (-23040, [2, 5, 7, 8]), (-11520, [2, 6, 6, 8]), (-11520, [2, 6, 7, 7]), (1249920, [2, 20]), (-7680/13, [3, 3, 3, 13]), (-46080, [3, 19]), (-46080, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-46080, [8, 14])]

def node88Piece71Output_sector0_chunk2 : RawPoly ℕ := [(-330240/13, [9, 13]), (-46080, [10, 12]), (-23040, [11, 11])]

def node88Piece71Output_sector0 : RawPoly ℕ := [node88Piece71Output_sector0_chunk0, node88Piece71Output_sector0_chunk1, node88Piece71Output_sector0_chunk2].flatten

def node88Piece71Output : SectorVector := [(0, node88Piece71Output_sector0)]

def node88Piece71UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [2, 13])]

def node88Piece71UnitInput_sector0 : RawPoly ℕ := [node88Piece71UnitInput_sector0_chunk0].flatten

def node88Piece71UnitInput : SectorVector := [(0, node88Piece71UnitInput_sector0)]

def node88Piece71UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 2, 4, 13]), (12, [1, 1, 2, 2, 3, 13]), (156, [1, 1, 2, 18]), (24, [1, 1, 7, 13]), (4, [1, 2, 2, 2, 2, 13]), (312, [1, 2, 2, 17]), (312, [1, 2, 3, 16]), (312, [1, 2, 4, 15]), (312, [1, 2, 5, 14]), (340, [1, 2, 6, 13]), (312, [1, 2, 7, 12]), (312, [1, 2, 8, 11]), (312, [1, 2, 9, 10]), (48, [1, 3, 5, 13]), (24, [1, 4, 4, 13]), (624, [1, 21]), (156, [2, 2, 2, 16]), (312, [2, 2, 3, 15]), (312, [2, 2, 4, 14]), (336, [2, 2, 5, 13]), (312, [2, 2, 6, 12]), (312, [2, 2, 7, 11]), (312, [2, 2, 8, 10]), (156, [2, 2, 9, 9])]

def node88Piece71UnitOutput_sector0_chunk1 : RawPoly ℕ := [(156, [2, 3, 3, 14]), (370, [2, 3, 4, 13]), (312, [2, 3, 5, 12]), (312, [2, 3, 6, 11]), (312, [2, 3, 7, 10]), (312, [2, 3, 8, 9]), (156, [2, 4, 4, 12]), (312, [2, 4, 5, 11]), (312, [2, 4, 6, 10]), (312, [2, 4, 7, 9]), (156, [2, 4, 8, 8]), (156, [2, 5, 5, 10]), (312, [2, 5, 6, 9]), (312, [2, 5, 7, 8]), (156, [2, 6, 6, 8]), (156, [2, 6, 7, 7]), (-16926, [2, 20]), (8, [3, 3, 3, 13]), (624, [3, 19]), (624, [4, 18]), (624, [5, 17]), (624, [6, 16]), (624, [7, 15]), (624, [8, 14])]

def node88Piece71UnitOutput_sector0_chunk2 : RawPoly ℕ := [(344, [9, 13]), (624, [10, 12]), (312, [11, 11])]

def node88Piece71UnitOutput_sector0 : RawPoly ℕ := [node88Piece71UnitOutput_sector0_chunk0, node88Piece71UnitOutput_sector0_chunk1, node88Piece71UnitOutput_sector0_chunk2].flatten

def node88Piece71UnitOutput : SectorVector := [(0, node88Piece71UnitOutput_sector0)]

theorem node88Piece71_check : neutralDirectS JR (-4) node88Piece71UnitInput = node88Piece71UnitOutput := by decide +kernel

theorem node88Piece71_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece71Input) = evaluate node88Piece71Output :=
  mode_of_scaled _ _ (-960/13) node88Piece71UnitInput node88Piece71UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece71_check)

def node88Piece72Input_sector0 : RawPoly ℕ := [(640/9, [3, 3, 3, 6])]

def node88Piece72Input : SectorVector := [(0, node88Piece72Input_sector0)]
def node88Piece72Output_sector0_chunk0 : RawPoly ℕ := [(2560/9, [1, 1, 1, 3, 3, 3, 4, 6]), (2560/3, [1, 1, 2, 3, 3, 3, 3, 6]), (5120, [1, 1, 3, 3, 3, 11]), (7680, [1, 1, 3, 3, 6, 8]), (2560/9, [1, 2, 2, 2, 3, 3, 3, 6]), (10240, [1, 2, 3, 3, 3, 10]), (15360, [1, 2, 3, 3, 6, 7]), (10240, [1, 3, 3, 3, 3, 9]), (10240, [1, 3, 3, 3, 4, 8]), (10240, [1, 3, 3, 3, 5, 7]), (171520/9, [1, 3, 3, 3, 6, 6]), (15360, [1, 3, 3, 4, 5, 6]), (92160, [1, 3, 3, 15]), (46080, [1, 3, 6, 12]), (5120, [2, 2, 3, 3, 3, 9]), (7680, [2, 2, 3, 3, 6, 6]), (10240, [2, 3, 3, 3, 3, 8]), (10240, [2, 3, 3, 3, 4, 7]), (25600, [2, 3, 3, 3, 5, 6]), (7680, [2, 3, 3, 4, 4, 6]), (92160, [2, 3, 3, 14]), (46080, [2, 3, 6, 11]), (5120, [3, 3, 3, 3, 3, 7]), (167680/9, [3, 3, 3, 3, 4, 6])]

def node88Piece72Output_sector0_chunk1 : RawPoly ℕ := [(5120, [3, 3, 3, 3, 5, 5]), (5120, [3, 3, 3, 4, 4, 5]), (-286720/3, [3, 3, 3, 13]), (92160, [3, 3, 4, 12]), (92160, [3, 3, 5, 11]), (10240, [3, 3, 6, 10]), (92160, [3, 3, 7, 9]), (46080, [3, 3, 8, 8]), (46080, [3, 4, 6, 9]), (46080, [3, 5, 6, 8]), (46080, [3, 6, 6, 7]), (276480, [3, 19]), (46080, [6, 16])]

def node88Piece72Output_sector0 : RawPoly ℕ := [node88Piece72Output_sector0_chunk0, node88Piece72Output_sector0_chunk1].flatten

def node88Piece72Output : SectorVector := [(0, node88Piece72Output_sector0)]

def node88Piece72UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 3, 6])]

def node88Piece72UnitInput_sector0 : RawPoly ℕ := [node88Piece72UnitInput_sector0_chunk0].flatten

def node88Piece72UnitInput : SectorVector := [(0, node88Piece72UnitInput_sector0)]

def node88Piece72UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 3, 4, 6]), (12, [1, 1, 2, 3, 3, 3, 3, 6]), (72, [1, 1, 3, 3, 3, 11]), (108, [1, 1, 3, 3, 6, 8]), (4, [1, 2, 2, 2, 3, 3, 3, 6]), (144, [1, 2, 3, 3, 3, 10]), (216, [1, 2, 3, 3, 6, 7]), (144, [1, 3, 3, 3, 3, 9]), (144, [1, 3, 3, 3, 4, 8]), (144, [1, 3, 3, 3, 5, 7]), (268, [1, 3, 3, 3, 6, 6]), (216, [1, 3, 3, 4, 5, 6]), (1296, [1, 3, 3, 15]), (648, [1, 3, 6, 12]), (72, [2, 2, 3, 3, 3, 9]), (108, [2, 2, 3, 3, 6, 6]), (144, [2, 3, 3, 3, 3, 8]), (144, [2, 3, 3, 3, 4, 7]), (360, [2, 3, 3, 3, 5, 6]), (108, [2, 3, 3, 4, 4, 6]), (1296, [2, 3, 3, 14]), (648, [2, 3, 6, 11]), (72, [3, 3, 3, 3, 3, 7]), (262, [3, 3, 3, 3, 4, 6])]

def node88Piece72UnitOutput_sector0_chunk1 : RawPoly ℕ := [(72, [3, 3, 3, 3, 5, 5]), (72, [3, 3, 3, 4, 4, 5]), (-1344, [3, 3, 3, 13]), (1296, [3, 3, 4, 12]), (1296, [3, 3, 5, 11]), (144, [3, 3, 6, 10]), (1296, [3, 3, 7, 9]), (648, [3, 3, 8, 8]), (648, [3, 4, 6, 9]), (648, [3, 5, 6, 8]), (648, [3, 6, 6, 7]), (3888, [3, 19]), (648, [6, 16])]

def node88Piece72UnitOutput_sector0 : RawPoly ℕ := [node88Piece72UnitOutput_sector0_chunk0, node88Piece72UnitOutput_sector0_chunk1].flatten

def node88Piece72UnitOutput : SectorVector := [(0, node88Piece72UnitOutput_sector0)]

theorem node88Piece72_check : neutralDirectS JR (-4) node88Piece72UnitInput = node88Piece72UnitOutput := by decide +kernel

theorem node88Piece72_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece72Input) = evaluate node88Piece72Output :=
  mode_of_scaled _ _ (640/9) node88Piece72UnitInput node88Piece72UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece72_check)

def node88Piece73Input_sector0 : RawPoly ℕ := [(96, [3, 3, 4, 5])]

def node88Piece73Input : SectorVector := [(0, node88Piece73Input_sector0)]
def node88Piece73Output_sector0_chunk0 : RawPoly ℕ := [(384, [1, 1, 1, 3, 3, 4, 4, 5]), (1152, [1, 1, 2, 3, 3, 3, 4, 5]), (5760, [1, 1, 3, 3, 4, 10]), (4608, [1, 1, 3, 3, 5, 9]), (6912, [1, 1, 3, 4, 5, 8]), (384, [1, 2, 2, 2, 3, 3, 4, 5]), (11520, [1, 2, 3, 3, 4, 9]), (9216, [1, 2, 3, 3, 5, 8]), (13824, [1, 2, 3, 4, 5, 7]), (11520, [1, 3, 3, 3, 4, 8]), (9216, [1, 3, 3, 3, 5, 7]), (11520, [1, 3, 3, 4, 4, 7]), (32640, [1, 3, 3, 4, 5, 6]), (4608, [1, 3, 3, 5, 5, 5]), (46080, [1, 3, 3, 15]), (13824, [1, 3, 4, 4, 5, 5]), (69120, [1, 3, 4, 14]), (55296, [1, 3, 5, 13]), (20736, [1, 4, 5, 12]), (5760, [2, 2, 3, 3, 4, 8]), (4608, [2, 2, 3, 3, 5, 7]), (6912, [2, 2, 3, 4, 5, 6]), (11520, [2, 3, 3, 3, 4, 7]), (9216, [2, 3, 3, 3, 5, 6])]

def node88Piece73Output_sector0_chunk1 : RawPoly ℕ := [(11520, [2, 3, 3, 4, 4, 6]), (28800, [2, 3, 3, 4, 5, 5]), (46080, [2, 3, 3, 14]), (6912, [2, 3, 4, 4, 4, 5]), (69120, [2, 3, 4, 13]), (55296, [2, 3, 5, 12]), (20736, [2, 4, 5, 11]), (5760, [3, 3, 3, 3, 4, 6]), (4608, [3, 3, 3, 3, 5, 5]), (24000, [3, 3, 3, 4, 4, 5]), (46080, [3, 3, 3, 13]), (1920, [3, 3, 4, 4, 4, 4]), (-52800, [3, 3, 4, 12]), (-2304, [3, 3, 5, 11]), (46080, [3, 3, 6, 10]), (46080, [3, 3, 7, 9]), (23040, [3, 3, 8, 8]), (69120, [3, 4, 4, 11]), (29952, [3, 4, 5, 10]), (69120, [3, 4, 6, 9]), (69120, [3, 4, 7, 8]), (55296, [3, 5, 5, 9]), (55296, [3, 5, 6, 8]), (27648, [3, 5, 7, 7])]

def node88Piece73Output_sector0_chunk2 : RawPoly ℕ := [(276480, [3, 19]), (20736, [4, 4, 5, 9]), (20736, [4, 5, 5, 8]), (20736, [4, 5, 6, 7]), (103680, [4, 18]), (82944, [5, 17])]

def node88Piece73Output_sector0 : RawPoly ℕ := [node88Piece73Output_sector0_chunk0, node88Piece73Output_sector0_chunk1, node88Piece73Output_sector0_chunk2].flatten

def node88Piece73Output : SectorVector := [(0, node88Piece73Output_sector0)]

def node88Piece73UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 3, 4, 5])]

def node88Piece73UnitInput_sector0 : RawPoly ℕ := [node88Piece73UnitInput_sector0_chunk0].flatten

def node88Piece73UnitInput : SectorVector := [(0, node88Piece73UnitInput_sector0)]

def node88Piece73UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 3, 4, 4, 5]), (12, [1, 1, 2, 3, 3, 3, 4, 5]), (60, [1, 1, 3, 3, 4, 10]), (48, [1, 1, 3, 3, 5, 9]), (72, [1, 1, 3, 4, 5, 8]), (4, [1, 2, 2, 2, 3, 3, 4, 5]), (120, [1, 2, 3, 3, 4, 9]), (96, [1, 2, 3, 3, 5, 8]), (144, [1, 2, 3, 4, 5, 7]), (120, [1, 3, 3, 3, 4, 8]), (96, [1, 3, 3, 3, 5, 7]), (120, [1, 3, 3, 4, 4, 7]), (340, [1, 3, 3, 4, 5, 6]), (48, [1, 3, 3, 5, 5, 5]), (480, [1, 3, 3, 15]), (144, [1, 3, 4, 4, 5, 5]), (720, [1, 3, 4, 14]), (576, [1, 3, 5, 13]), (216, [1, 4, 5, 12]), (60, [2, 2, 3, 3, 4, 8]), (48, [2, 2, 3, 3, 5, 7]), (72, [2, 2, 3, 4, 5, 6]), (120, [2, 3, 3, 3, 4, 7]), (96, [2, 3, 3, 3, 5, 6])]

def node88Piece73UnitOutput_sector0_chunk1 : RawPoly ℕ := [(120, [2, 3, 3, 4, 4, 6]), (300, [2, 3, 3, 4, 5, 5]), (480, [2, 3, 3, 14]), (72, [2, 3, 4, 4, 4, 5]), (720, [2, 3, 4, 13]), (576, [2, 3, 5, 12]), (216, [2, 4, 5, 11]), (60, [3, 3, 3, 3, 4, 6]), (48, [3, 3, 3, 3, 5, 5]), (250, [3, 3, 3, 4, 4, 5]), (480, [3, 3, 3, 13]), (20, [3, 3, 4, 4, 4, 4]), (-550, [3, 3, 4, 12]), (-24, [3, 3, 5, 11]), (480, [3, 3, 6, 10]), (480, [3, 3, 7, 9]), (240, [3, 3, 8, 8]), (720, [3, 4, 4, 11]), (312, [3, 4, 5, 10]), (720, [3, 4, 6, 9]), (720, [3, 4, 7, 8]), (576, [3, 5, 5, 9]), (576, [3, 5, 6, 8]), (288, [3, 5, 7, 7])]

def node88Piece73UnitOutput_sector0_chunk2 : RawPoly ℕ := [(2880, [3, 19]), (216, [4, 4, 5, 9]), (216, [4, 5, 5, 8]), (216, [4, 5, 6, 7]), (1080, [4, 18]), (864, [5, 17])]

def node88Piece73UnitOutput_sector0 : RawPoly ℕ := [node88Piece73UnitOutput_sector0_chunk0, node88Piece73UnitOutput_sector0_chunk1, node88Piece73UnitOutput_sector0_chunk2].flatten

def node88Piece73UnitOutput : SectorVector := [(0, node88Piece73UnitOutput_sector0)]

theorem node88Piece73_check : neutralDirectS JR (-4) node88Piece73UnitInput = node88Piece73UnitOutput := by decide +kernel

theorem node88Piece73_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece73Input) = evaluate node88Piece73Output :=
  mode_of_scaled _ _ (96) node88Piece73UnitInput node88Piece73UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece73_check)

def node88Piece74Input_sector0 : RawPoly ℕ := [(-20, [3, 4, 4, 4])]

def node88Piece74Input : SectorVector := [(0, node88Piece74Input_sector0)]
def node88Piece74Output_sector0_chunk0 : RawPoly ℕ := [(-80, [1, 1, 1, 3, 4, 4, 4, 4]), (-240, [1, 1, 2, 3, 3, 4, 4, 4]), (-2880, [1, 1, 3, 4, 4, 9]), (-720, [1, 1, 4, 4, 4, 8]), (-80, [1, 2, 2, 2, 3, 4, 4, 4]), (-5760, [1, 2, 3, 4, 4, 8]), (-1440, [1, 2, 4, 4, 4, 7]), (-5760, [1, 3, 3, 4, 4, 7]), (-6800, [1, 3, 4, 4, 4, 6]), (-2880, [1, 3, 4, 4, 5, 5]), (-23040, [1, 3, 4, 14]), (-1440, [1, 4, 4, 4, 4, 5]), (-17280, [1, 4, 4, 13]), (-2880, [2, 2, 3, 4, 4, 7]), (-720, [2, 2, 4, 4, 4, 6]), (-5760, [2, 3, 3, 4, 4, 6]), (-7200, [2, 3, 4, 4, 4, 5]), (-23040, [2, 3, 4, 13]), (-720, [2, 4, 4, 4, 4, 4]), (-17280, [2, 4, 4, 12]), (-2880, [3, 3, 3, 4, 4, 5]), (-3800, [3, 3, 4, 4, 4, 4]), (-23040, [3, 3, 4, 12]), (24480, [3, 4, 4, 11])]

def node88Piece74Output_sector0_chunk1 : RawPoly ℕ := [(-23040, [3, 4, 5, 10]), (-23040, [3, 4, 6, 9]), (-23040, [3, 4, 7, 8]), (-30720, [3, 19]), (-5280, [4, 4, 4, 10]), (-17280, [4, 4, 5, 9]), (-17280, [4, 4, 6, 8]), (-8640, [4, 4, 7, 7]), (-69120, [4, 18])]

def node88Piece74Output_sector0 : RawPoly ℕ := [node88Piece74Output_sector0_chunk0, node88Piece74Output_sector0_chunk1].flatten

def node88Piece74Output : SectorVector := [(0, node88Piece74Output_sector0)]

def node88Piece74UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 4, 4, 4])]

def node88Piece74UnitInput_sector0 : RawPoly ℕ := [node88Piece74UnitInput_sector0_chunk0].flatten

def node88Piece74UnitInput : SectorVector := [(0, node88Piece74UnitInput_sector0)]

def node88Piece74UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 4, 4, 4]), (12, [1, 1, 2, 3, 3, 4, 4, 4]), (144, [1, 1, 3, 4, 4, 9]), (36, [1, 1, 4, 4, 4, 8]), (4, [1, 2, 2, 2, 3, 4, 4, 4]), (288, [1, 2, 3, 4, 4, 8]), (72, [1, 2, 4, 4, 4, 7]), (288, [1, 3, 3, 4, 4, 7]), (340, [1, 3, 4, 4, 4, 6]), (144, [1, 3, 4, 4, 5, 5]), (1152, [1, 3, 4, 14]), (72, [1, 4, 4, 4, 4, 5]), (864, [1, 4, 4, 13]), (144, [2, 2, 3, 4, 4, 7]), (36, [2, 2, 4, 4, 4, 6]), (288, [2, 3, 3, 4, 4, 6]), (360, [2, 3, 4, 4, 4, 5]), (1152, [2, 3, 4, 13]), (36, [2, 4, 4, 4, 4, 4]), (864, [2, 4, 4, 12]), (144, [3, 3, 3, 4, 4, 5]), (190, [3, 3, 4, 4, 4, 4]), (1152, [3, 3, 4, 12]), (-1224, [3, 4, 4, 11])]

def node88Piece74UnitOutput_sector0_chunk1 : RawPoly ℕ := [(1152, [3, 4, 5, 10]), (1152, [3, 4, 6, 9]), (1152, [3, 4, 7, 8]), (1536, [3, 19]), (264, [4, 4, 4, 10]), (864, [4, 4, 5, 9]), (864, [4, 4, 6, 8]), (432, [4, 4, 7, 7]), (3456, [4, 18])]

def node88Piece74UnitOutput_sector0 : RawPoly ℕ := [node88Piece74UnitOutput_sector0_chunk0, node88Piece74UnitOutput_sector0_chunk1].flatten

def node88Piece74UnitOutput : SectorVector := [(0, node88Piece74UnitOutput_sector0)]

theorem node88Piece74_check : neutralDirectS JR (-4) node88Piece74UnitInput = node88Piece74UnitOutput := by decide +kernel

theorem node88Piece74_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece74Input) = evaluate node88Piece74Output :=
  mode_of_scaled _ _ (-20) node88Piece74UnitInput node88Piece74UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece74_check)

def node88Piece75Input_sector0 : RawPoly ℕ := [(80, [3, 12])]

def node88Piece75Input : SectorVector := [(0, node88Piece75Input_sector0)]
def node88Piece75Output_sector0_chunk0 : RawPoly ℕ := [(320, [1, 1, 1, 3, 4, 12]), (960, [1, 1, 2, 3, 3, 12]), (11520, [1, 1, 3, 17]), (2880, [1, 1, 8, 12]), (320, [1, 2, 2, 2, 3, 12]), (23040, [1, 2, 3, 16]), (5760, [1, 2, 7, 12]), (23040, [1, 3, 3, 15]), (23040, [1, 3, 4, 14]), (23040, [1, 3, 5, 13]), (27200, [1, 3, 6, 12]), (23040, [1, 3, 7, 11]), (23040, [1, 3, 8, 10]), (11520, [1, 3, 9, 9]), (5760, [1, 4, 5, 12]), (69120, [1, 21]), (11520, [2, 2, 3, 15]), (2880, [2, 2, 6, 12]), (23040, [2, 3, 3, 14]), (23040, [2, 3, 4, 13]), (28800, [2, 3, 5, 12]), (23040, [2, 3, 6, 11]), (23040, [2, 3, 7, 10]), (23040, [2, 3, 8, 9])]

def node88Piece75Output_sector0_chunk1 : RawPoly ℕ := [(2880, [2, 4, 4, 12]), (69120, [2, 20]), (11520, [3, 3, 3, 13]), (26720, [3, 3, 4, 12]), (23040, [3, 3, 5, 11]), (23040, [3, 3, 6, 10]), (23040, [3, 3, 7, 9]), (11520, [3, 3, 8, 8]), (11520, [3, 4, 4, 11]), (23040, [3, 4, 5, 10]), (23040, [3, 4, 6, 9]), (23040, [3, 4, 7, 8]), (11520, [3, 5, 5, 9]), (23040, [3, 5, 6, 8]), (11520, [3, 5, 7, 7]), (11520, [3, 6, 6, 7]), (-1073280, [3, 19]), (69120, [4, 18]), (69120, [5, 17]), (69120, [6, 16]), (69120, [7, 15]), (69120, [8, 14]), (69120, [9, 13]), (21120, [10, 12])]

def node88Piece75Output_sector0_chunk2 : RawPoly ℕ := [(34560, [11, 11])]

def node88Piece75Output_sector0 : RawPoly ℕ := [node88Piece75Output_sector0_chunk0, node88Piece75Output_sector0_chunk1, node88Piece75Output_sector0_chunk2].flatten

def node88Piece75Output : SectorVector := [(0, node88Piece75Output_sector0)]

def node88Piece75UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [3, 12])]

def node88Piece75UnitInput_sector0 : RawPoly ℕ := [node88Piece75UnitInput_sector0_chunk0].flatten

def node88Piece75UnitInput : SectorVector := [(0, node88Piece75UnitInput_sector0)]

def node88Piece75UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 3, 4, 12]), (12, [1, 1, 2, 3, 3, 12]), (144, [1, 1, 3, 17]), (36, [1, 1, 8, 12]), (4, [1, 2, 2, 2, 3, 12]), (288, [1, 2, 3, 16]), (72, [1, 2, 7, 12]), (288, [1, 3, 3, 15]), (288, [1, 3, 4, 14]), (288, [1, 3, 5, 13]), (340, [1, 3, 6, 12]), (288, [1, 3, 7, 11]), (288, [1, 3, 8, 10]), (144, [1, 3, 9, 9]), (72, [1, 4, 5, 12]), (864, [1, 21]), (144, [2, 2, 3, 15]), (36, [2, 2, 6, 12]), (288, [2, 3, 3, 14]), (288, [2, 3, 4, 13]), (360, [2, 3, 5, 12]), (288, [2, 3, 6, 11]), (288, [2, 3, 7, 10]), (288, [2, 3, 8, 9])]

def node88Piece75UnitOutput_sector0_chunk1 : RawPoly ℕ := [(36, [2, 4, 4, 12]), (864, [2, 20]), (144, [3, 3, 3, 13]), (334, [3, 3, 4, 12]), (288, [3, 3, 5, 11]), (288, [3, 3, 6, 10]), (288, [3, 3, 7, 9]), (144, [3, 3, 8, 8]), (144, [3, 4, 4, 11]), (288, [3, 4, 5, 10]), (288, [3, 4, 6, 9]), (288, [3, 4, 7, 8]), (144, [3, 5, 5, 9]), (288, [3, 5, 6, 8]), (144, [3, 5, 7, 7]), (144, [3, 6, 6, 7]), (-13416, [3, 19]), (864, [4, 18]), (864, [5, 17]), (864, [6, 16]), (864, [7, 15]), (864, [8, 14]), (864, [9, 13]), (264, [10, 12])]

def node88Piece75UnitOutput_sector0_chunk2 : RawPoly ℕ := [(432, [11, 11])]

def node88Piece75UnitOutput_sector0 : RawPoly ℕ := [node88Piece75UnitOutput_sector0_chunk0, node88Piece75UnitOutput_sector0_chunk1, node88Piece75UnitOutput_sector0_chunk2].flatten

def node88Piece75UnitOutput : SectorVector := [(0, node88Piece75UnitOutput_sector0)]

theorem node88Piece75_check : neutralDirectS JR (-4) node88Piece75UnitInput = node88Piece75UnitOutput := by decide +kernel

theorem node88Piece75_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece75Input) = evaluate node88Piece75Output :=
  mode_of_scaled _ _ (80) node88Piece75UnitInput node88Piece75UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece75_check)

def node88Piece76Input_sector0 : RawPoly ℕ := [(-480/11, [4, 11])]

def node88Piece76Input : SectorVector := [(0, node88Piece76Input_sector0)]
def node88Piece76Output_sector0_chunk0 : RawPoly ℕ := [(-1920/11, [1, 1, 1, 4, 4, 11]), (-5760/11, [1, 1, 2, 3, 4, 11]), (-5760, [1, 1, 4, 16]), (-23040/11, [1, 1, 9, 11]), (-1920/11, [1, 2, 2, 2, 4, 11]), (-11520, [1, 2, 4, 15]), (-46080/11, [1, 2, 8, 11]), (-11520, [1, 3, 4, 14]), (-46080/11, [1, 3, 7, 11]), (-11520, [1, 4, 4, 13]), (-11520, [1, 4, 5, 12]), (-163200/11, [1, 4, 6, 11]), (-11520, [1, 4, 7, 10]), (-11520, [1, 4, 8, 9]), (-23040/11, [1, 5, 5, 11]), (-46080, [1, 21]), (-5760, [2, 2, 4, 14]), (-23040/11, [2, 2, 7, 11]), (-11520, [2, 3, 4, 13]), (-46080/11, [2, 3, 6, 11]), (-11520, [2, 4, 4, 12]), (-172800/11, [2, 4, 5, 11]), (-11520, [2, 4, 6, 10]), (-11520, [2, 4, 7, 9])]

def node88Piece76Output_sector0_chunk1 : RawPoly ℕ := [(-5760, [2, 4, 8, 8]), (-46080, [2, 20]), (-5760, [3, 3, 4, 12]), (-23040/11, [3, 3, 5, 11]), (-154560/11, [3, 4, 4, 11]), (-11520, [3, 4, 5, 10]), (-11520, [3, 4, 6, 9]), (-11520, [3, 4, 7, 8]), (-46080, [3, 19]), (-5760, [4, 4, 4, 10]), (-11520, [4, 4, 5, 9]), (-11520, [4, 4, 6, 8]), (-5760, [4, 4, 7, 7]), (-5760, [4, 5, 5, 8]), (-11520, [4, 5, 6, 7]), (-1920, [4, 6, 6, 6]), (453120, [4, 18]), (-46080, [5, 17]), (-46080, [6, 16]), (-46080, [7, 15]), (-46080, [8, 14]), (-46080, [9, 13]), (-46080, [10, 12]), (264960/11, [11, 11])]

def node88Piece76Output_sector0 : RawPoly ℕ := [node88Piece76Output_sector0_chunk0, node88Piece76Output_sector0_chunk1].flatten

def node88Piece76Output : SectorVector := [(0, node88Piece76Output_sector0)]

def node88Piece76UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [4, 11])]

def node88Piece76UnitInput_sector0 : RawPoly ℕ := [node88Piece76UnitInput_sector0_chunk0].flatten

def node88Piece76UnitInput : SectorVector := [(0, node88Piece76UnitInput_sector0)]

def node88Piece76UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 4, 11]), (12, [1, 1, 2, 3, 4, 11]), (132, [1, 1, 4, 16]), (48, [1, 1, 9, 11]), (4, [1, 2, 2, 2, 4, 11]), (264, [1, 2, 4, 15]), (96, [1, 2, 8, 11]), (264, [1, 3, 4, 14]), (96, [1, 3, 7, 11]), (264, [1, 4, 4, 13]), (264, [1, 4, 5, 12]), (340, [1, 4, 6, 11]), (264, [1, 4, 7, 10]), (264, [1, 4, 8, 9]), (48, [1, 5, 5, 11]), (1056, [1, 21]), (132, [2, 2, 4, 14]), (48, [2, 2, 7, 11]), (264, [2, 3, 4, 13]), (96, [2, 3, 6, 11]), (264, [2, 4, 4, 12]), (360, [2, 4, 5, 11]), (264, [2, 4, 6, 10]), (264, [2, 4, 7, 9])]

def node88Piece76UnitOutput_sector0_chunk1 : RawPoly ℕ := [(132, [2, 4, 8, 8]), (1056, [2, 20]), (132, [3, 3, 4, 12]), (48, [3, 3, 5, 11]), (322, [3, 4, 4, 11]), (264, [3, 4, 5, 10]), (264, [3, 4, 6, 9]), (264, [3, 4, 7, 8]), (1056, [3, 19]), (132, [4, 4, 4, 10]), (264, [4, 4, 5, 9]), (264, [4, 4, 6, 8]), (132, [4, 4, 7, 7]), (132, [4, 5, 5, 8]), (264, [4, 5, 6, 7]), (44, [4, 6, 6, 6]), (-10384, [4, 18]), (1056, [5, 17]), (1056, [6, 16]), (1056, [7, 15]), (1056, [8, 14]), (1056, [9, 13]), (1056, [10, 12]), (-552, [11, 11])]

def node88Piece76UnitOutput_sector0 : RawPoly ℕ := [node88Piece76UnitOutput_sector0_chunk0, node88Piece76UnitOutput_sector0_chunk1].flatten

def node88Piece76UnitOutput : SectorVector := [(0, node88Piece76UnitOutput_sector0)]

theorem node88Piece76_check : neutralDirectS JR (-4) node88Piece76UnitInput = node88Piece76UnitOutput := by decide +kernel

theorem node88Piece76_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece76Input) = evaluate node88Piece76Output :=
  mode_of_scaled _ _ (-480/11) node88Piece76UnitInput node88Piece76UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece76_check)

def node88Piece77Input_sector0 : RawPoly ℕ := [(48/5, [5, 10])]

def node88Piece77Input : SectorVector := [(0, node88Piece77Input_sector0)]
def node88Piece77Output_sector0_chunk0 : RawPoly ℕ := [(192/5, [1, 1, 1, 4, 5, 10]), (576/5, [1, 1, 2, 3, 5, 10]), (1152, [1, 1, 5, 15]), (576, [1, 1, 10, 10]), (192/5, [1, 2, 2, 2, 5, 10]), (2304, [1, 2, 5, 14]), (1152, [1, 2, 9, 10]), (2304, [1, 3, 5, 13]), (1152, [1, 3, 8, 10]), (2304, [1, 4, 5, 12]), (1152, [1, 4, 7, 10]), (2304, [1, 5, 5, 11]), (3264, [1, 5, 6, 10]), (2304, [1, 5, 7, 9]), (1152, [1, 5, 8, 8]), (11520, [1, 21]), (1152, [2, 2, 5, 13]), (576, [2, 2, 8, 10]), (2304, [2, 3, 5, 12]), (1152, [2, 3, 7, 10]), (2304, [2, 4, 5, 11]), (1152, [2, 4, 6, 10]), (2880, [2, 5, 5, 10]), (2304, [2, 5, 6, 9])]

def node88Piece77Output_sector0_chunk1 : RawPoly ℕ := [(2304, [2, 5, 7, 8]), (11520, [2, 20]), (1152, [3, 3, 5, 11]), (576, [3, 3, 6, 10]), (3552, [3, 4, 5, 10]), (2304, [3, 5, 5, 9]), (2304, [3, 5, 6, 8]), (1152, [3, 5, 7, 7]), (11520, [3, 19]), (192, [4, 4, 4, 10]), (1152, [4, 4, 5, 9]), (2304, [4, 5, 5, 8]), (2304, [4, 5, 6, 7]), (11520, [4, 18]), (1152, [5, 5, 5, 7]), (1152, [5, 5, 6, 6]), (-74880, [5, 17]), (11520, [6, 16]), (11520, [7, 15]), (11520, [8, 14]), (11520, [9, 13]), (-5280, [10, 12]), (5760, [11, 11])]

def node88Piece77Output_sector0 : RawPoly ℕ := [node88Piece77Output_sector0_chunk0, node88Piece77Output_sector0_chunk1].flatten

def node88Piece77Output : SectorVector := [(0, node88Piece77Output_sector0)]

def node88Piece77UnitInput_sector0_chunk0 : RawPoly ℕ := [(1, [5, 10])]

def node88Piece77UnitInput_sector0 : RawPoly ℕ := [node88Piece77UnitInput_sector0_chunk0].flatten

def node88Piece77UnitInput : SectorVector := [(0, node88Piece77UnitInput_sector0)]

def node88Piece77UnitOutput_sector0_chunk0 : RawPoly ℕ := [(4, [1, 1, 1, 4, 5, 10]), (12, [1, 1, 2, 3, 5, 10]), (120, [1, 1, 5, 15]), (60, [1, 1, 10, 10]), (4, [1, 2, 2, 2, 5, 10]), (240, [1, 2, 5, 14]), (120, [1, 2, 9, 10]), (240, [1, 3, 5, 13]), (120, [1, 3, 8, 10]), (240, [1, 4, 5, 12]), (120, [1, 4, 7, 10]), (240, [1, 5, 5, 11]), (340, [1, 5, 6, 10]), (240, [1, 5, 7, 9]), (120, [1, 5, 8, 8]), (1200, [1, 21]), (120, [2, 2, 5, 13]), (60, [2, 2, 8, 10]), (240, [2, 3, 5, 12]), (120, [2, 3, 7, 10]), (240, [2, 4, 5, 11]), (120, [2, 4, 6, 10]), (300, [2, 5, 5, 10]), (240, [2, 5, 6, 9])]

def node88Piece77UnitOutput_sector0_chunk1 : RawPoly ℕ := [(240, [2, 5, 7, 8]), (1200, [2, 20]), (120, [3, 3, 5, 11]), (60, [3, 3, 6, 10]), (370, [3, 4, 5, 10]), (240, [3, 5, 5, 9]), (240, [3, 5, 6, 8]), (120, [3, 5, 7, 7]), (1200, [3, 19]), (20, [4, 4, 4, 10]), (120, [4, 4, 5, 9]), (240, [4, 5, 5, 8]), (240, [4, 5, 6, 7]), (1200, [4, 18]), (120, [5, 5, 5, 7]), (120, [5, 5, 6, 6]), (-7800, [5, 17]), (1200, [6, 16]), (1200, [7, 15]), (1200, [8, 14]), (1200, [9, 13]), (-550, [10, 12]), (600, [11, 11])]

def node88Piece77UnitOutput_sector0 : RawPoly ℕ := [node88Piece77UnitOutput_sector0_chunk0, node88Piece77UnitOutput_sector0_chunk1].flatten

def node88Piece77UnitOutput : SectorVector := [(0, node88Piece77UnitOutput_sector0)]

theorem node88Piece77_check : neutralDirectS JR (-4) node88Piece77UnitInput = node88Piece77UnitOutput := by decide +kernel

theorem node88Piece77_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-4)
    (evaluate node88Piece77Input) = evaluate node88Piece77Output :=
  mode_of_scaled _ _ (48/5) node88Piece77UnitInput node88Piece77UnitOutput _ _
    (by decide +kernel) (by decide +kernel)
    (neutralDirect_value JR _ _ _ node88Piece77_check)

end VOA.Classification.COne.OrbC2h
