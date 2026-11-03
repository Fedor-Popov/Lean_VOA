import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode11
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node15Piece16Input_sector0 : RawPoly ℕ := [(704, [1, 2, 3, 5])]

def node15Piece16Input : SectorVector := [(0, node15Piece16Input_sector0)]
def node15Piece16Output_sector0_chunk0 : RawPoly ℕ := [(2816, [1, 1, 1, 1, 2, 3, 5, 6]), (8448, [1, 1, 1, 2, 2, 3, 5, 5]), (8448, [1, 1, 1, 2, 3, 3, 4, 5]), (42240, [1, 1, 1, 2, 3, 12]), (25344, [1, 1, 1, 2, 5, 10]), (16896, [1, 1, 1, 3, 5, 9]), (8448, [1, 1, 2, 2, 2, 3, 4, 5]), (8448, [1, 1, 2, 2, 3, 3, 3, 5]), (84480, [1, 1, 2, 2, 3, 11]), (50688, [1, 1, 2, 2, 5, 9]), (84480, [1, 1, 2, 3, 3, 10]), (84480, [1, 1, 2, 3, 4, 9]), (147840, [1, 1, 2, 3, 5, 8]), (84480, [1, 1, 2, 3, 6, 7]), (50688, [1, 1, 2, 4, 5, 7]), (50688, [1, 1, 2, 5, 5, 6]), (253440, [1, 1, 2, 16]), (33792, [1, 1, 3, 3, 5, 7]), (33792, [1, 1, 3, 4, 5, 6]), (16896, [1, 1, 3, 5, 5, 5]), (168960, [1, 1, 3, 15]), (101376, [1, 1, 5, 13]), (2816, [1, 2, 2, 2, 2, 3, 3, 5]), (42240, [1, 2, 2, 2, 3, 10])]

def node15Piece16Output_sector0_chunk1 : RawPoly ℕ := [(25344, [1, 2, 2, 2, 5, 8]), (84480, [1, 2, 2, 3, 3, 9]), (84480, [1, 2, 2, 3, 4, 8]), (160512, [1, 2, 2, 3, 5, 7]), (42240, [1, 2, 2, 3, 6, 6]), (50688, [1, 2, 2, 4, 5, 6]), (25344, [1, 2, 2, 5, 5, 5]), (253440, [1, 2, 2, 15]), (42240, [1, 2, 3, 3, 3, 8]), (84480, [1, 2, 3, 3, 4, 7]), (166144, [1, 2, 3, 3, 5, 6]), (42240, [1, 2, 3, 4, 4, 6]), (156288, [1, 2, 3, 4, 5, 5]), (-1013760, [1, 2, 3, 14]), (8448, [1, 2, 4, 4, 4, 5]), (253440, [1, 2, 4, 13]), (-147840, [1, 2, 5, 12]), (253440, [1, 2, 6, 11]), (253440, [1, 2, 7, 10]), (253440, [1, 2, 8, 9]), (16896, [1, 3, 3, 3, 5, 5]), (16896, [1, 3, 3, 4, 4, 5]), (168960, [1, 3, 3, 13]), (168960, [1, 3, 4, 12])]

def node15Piece16Output_sector0_chunk2 : RawPoly ℕ := [(33792, [1, 3, 5, 11]), (168960, [1, 3, 6, 10]), (168960, [1, 3, 7, 9]), (84480, [1, 3, 8, 8]), (101376, [1, 4, 5, 10]), (101376, [1, 5, 5, 9]), (101376, [1, 5, 6, 8]), (50688, [1, 5, 7, 7]), (506880, [1, 19]), (8448, [2, 2, 2, 3, 5, 6]), (16896, [2, 2, 3, 3, 5, 5]), (8448, [2, 2, 3, 4, 4, 5]), (84480, [2, 2, 3, 13]), (50688, [2, 2, 5, 11]), (8448, [2, 3, 3, 3, 4, 5]), (84480, [2, 3, 3, 12]), (84480, [2, 3, 4, 11]), (76032, [2, 3, 5, 10]), (84480, [2, 3, 6, 9]), (84480, [2, 3, 7, 8]), (50688, [2, 4, 5, 9]), (50688, [2, 5, 5, 8]), (50688, [2, 5, 6, 7]), (253440, [2, 18])]

def node15Piece16Output_sector0_chunk3 : RawPoly ℕ := [(33792, [3, 3, 5, 9]), (33792, [3, 4, 5, 8]), (33792, [3, 5, 5, 7]), (16896, [3, 5, 6, 6]), (168960, [3, 17]), (101376, [5, 15])]

def node15Piece16Output_sector0 : RawPoly ℕ := [node15Piece16Output_sector0_chunk0, node15Piece16Output_sector0_chunk1, node15Piece16Output_sector0_chunk2, node15Piece16Output_sector0_chunk3].flatten

def node15Piece16Output : SectorVector := [(0, node15Piece16Output_sector0)]
theorem node15Piece16_check : VectorCertificate (neutralBoundS JR (-6) node15Piece16Input) node15Piece16Output := by decide +kernel
theorem node15Piece16_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece16Input) = evaluate node15Piece16Output :=
  neutralBound_value JR _ _ _ node15Piece16_check

def node15Piece17Input_sector0 : RawPoly ℕ := [(-420, [1, 2, 4, 4])]

def node15Piece17Input : SectorVector := [(0, node15Piece17Input_sector0)]
def node15Piece17Output_sector0_chunk0 : RawPoly ℕ := [(-1680, [1, 1, 1, 1, 2, 4, 4, 6]), (-5040, [1, 1, 1, 2, 2, 4, 4, 5]), (-5040, [1, 1, 1, 2, 3, 4, 4, 4]), (-40320, [1, 1, 1, 2, 4, 11]), (-10080, [1, 1, 1, 4, 4, 9]), (-5040, [1, 1, 2, 2, 2, 4, 4, 4]), (-5040, [1, 1, 2, 2, 3, 3, 4, 4]), (-80640, [1, 1, 2, 2, 4, 10]), (-80640, [1, 1, 2, 3, 4, 9]), (-88200, [1, 1, 2, 4, 4, 8]), (-80640, [1, 1, 2, 4, 5, 7]), (-40320, [1, 1, 2, 4, 6, 6]), (-161280, [1, 1, 2, 16]), (-20160, [1, 1, 3, 4, 4, 7]), (-20160, [1, 1, 4, 4, 4, 6]), (-10080, [1, 1, 4, 4, 5, 5]), (-161280, [1, 1, 4, 14]), (-1680, [1, 2, 2, 2, 2, 3, 4, 4]), (-40320, [1, 2, 2, 2, 4, 9]), (-80640, [1, 2, 2, 3, 4, 8]), (-95760, [1, 2, 2, 4, 4, 7]), (-80640, [1, 2, 2, 4, 5, 6]), (-161280, [1, 2, 2, 15]), (-40320, [1, 2, 3, 3, 4, 7])]

def node15Piece17Output_sector0_chunk1 : RawPoly ℕ := [(-114240, [1, 2, 3, 4, 4, 6]), (-40320, [1, 2, 3, 4, 5, 5]), (-161280, [1, 2, 3, 14]), (-78120, [1, 2, 4, 4, 4, 5]), (745920, [1, 2, 4, 13]), (-161280, [1, 2, 5, 12]), (-161280, [1, 2, 6, 11]), (-161280, [1, 2, 7, 10]), (-161280, [1, 2, 8, 9]), (-10080, [1, 3, 3, 4, 4, 5]), (-10080, [1, 3, 4, 4, 4, 4]), (-161280, [1, 3, 4, 12]), (-20160, [1, 4, 4, 11]), (-161280, [1, 4, 5, 10]), (-161280, [1, 4, 6, 9]), (-161280, [1, 4, 7, 8]), (-322560, [1, 19]), (-5040, [2, 2, 2, 4, 4, 6]), (-10080, [2, 2, 3, 4, 4, 5]), (-5040, [2, 2, 4, 4, 4, 4]), (-80640, [2, 2, 4, 12]), (-5040, [2, 3, 3, 4, 4, 4]), (-80640, [2, 3, 4, 11]), (-45360, [2, 4, 4, 10])]

def node15Piece17Output_sector0_chunk2 : RawPoly ℕ := [(-80640, [2, 4, 5, 9]), (-80640, [2, 4, 6, 8]), (-40320, [2, 4, 7, 7]), (-161280, [2, 18]), (-20160, [3, 4, 4, 9]), (-20160, [4, 4, 4, 8]), (-20160, [4, 4, 5, 7]), (-10080, [4, 4, 6, 6]), (-161280, [4, 16])]

def node15Piece17Output_sector0 : RawPoly ℕ := [node15Piece17Output_sector0_chunk0, node15Piece17Output_sector0_chunk1, node15Piece17Output_sector0_chunk2].flatten

def node15Piece17Output : SectorVector := [(0, node15Piece17Output_sector0)]
theorem node15Piece17_check : VectorCertificate (neutralBoundS JR (-6) node15Piece17Input) node15Piece17Output := by decide +kernel
theorem node15Piece17_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece17Input) = evaluate node15Piece17Output :=
  neutralBound_value JR _ _ _ node15Piece17_check

def node15Piece18Input_sector0 : RawPoly ℕ := [(880/3, [1, 3, 3, 4])]

def node15Piece18Input : SectorVector := [(0, node15Piece18Input_sector0)]
def node15Piece18Output_sector0_chunk0 : RawPoly ℕ := [(3520/3, [1, 1, 1, 1, 3, 3, 4, 6]), (3520, [1, 1, 1, 2, 3, 3, 4, 5]), (3520, [1, 1, 1, 3, 3, 3, 4, 4]), (14080, [1, 1, 1, 3, 3, 11]), (21120, [1, 1, 1, 3, 4, 10]), (3520, [1, 1, 2, 2, 3, 3, 4, 4]), (3520, [1, 1, 2, 3, 3, 3, 3, 4]), (28160, [1, 1, 2, 3, 3, 10]), (42240, [1, 1, 2, 3, 4, 9]), (28160, [1, 1, 3, 3, 3, 9]), (61600, [1, 1, 3, 3, 4, 8]), (28160, [1, 1, 3, 3, 5, 7]), (14080, [1, 1, 3, 3, 6, 6]), (42240, [1, 1, 3, 4, 4, 7]), (42240, [1, 1, 3, 4, 5, 6]), (168960, [1, 1, 3, 15]), (63360, [1, 1, 4, 14]), (3520/3, [1, 2, 2, 2, 3, 3, 3, 4]), (14080, [1, 2, 2, 3, 3, 9]), (21120, [1, 2, 2, 3, 4, 8]), (28160, [1, 2, 3, 3, 3, 8]), (73920, [1, 2, 3, 3, 4, 7]), (28160, [1, 2, 3, 3, 5, 6]), (42240, [1, 2, 3, 4, 4, 6])]

def node15Piece18Output_sector0_chunk1 : RawPoly ℕ := [(21120, [1, 2, 3, 4, 5, 5]), (168960, [1, 2, 3, 14]), (63360, [1, 2, 4, 13]), (14080, [1, 3, 3, 3, 3, 7]), (176000/3, [1, 3, 3, 3, 4, 6]), (14080, [1, 3, 3, 3, 5, 5]), (68640, [1, 3, 3, 4, 4, 5]), (-204160, [1, 3, 3, 13]), (7040, [1, 3, 4, 4, 4, 4]), (-186560, [1, 3, 4, 12]), (168960, [1, 3, 5, 11]), (168960, [1, 3, 6, 10]), (168960, [1, 3, 7, 9]), (84480, [1, 3, 8, 8]), (63360, [1, 4, 4, 11]), (63360, [1, 4, 5, 10]), (63360, [1, 4, 6, 9]), (63360, [1, 4, 7, 8]), (253440, [1, 19]), (3520, [2, 2, 3, 3, 4, 6]), (7040, [2, 3, 3, 3, 4, 5]), (3520, [2, 3, 3, 4, 4, 4]), (28160, [2, 3, 3, 12]), (42240, [2, 3, 4, 11])]

def node15Piece18Output_sector0_chunk2 : RawPoly ℕ := [(3520, [3, 3, 3, 3, 4, 4]), (28160, [3, 3, 3, 11]), (31680, [3, 3, 4, 10]), (28160, [3, 3, 5, 9]), (28160, [3, 3, 6, 8]), (14080, [3, 3, 7, 7]), (42240, [3, 4, 4, 9]), (42240, [3, 4, 5, 8]), (42240, [3, 4, 6, 7]), (168960, [3, 17]), (63360, [4, 16])]

def node15Piece18Output_sector0 : RawPoly ℕ := [node15Piece18Output_sector0_chunk0, node15Piece18Output_sector0_chunk1, node15Piece18Output_sector0_chunk2].flatten

def node15Piece18Output : SectorVector := [(0, node15Piece18Output_sector0)]
theorem node15Piece18_check : VectorCertificate (neutralBoundS JR (-6) node15Piece18Input) node15Piece18Output := by decide +kernel
theorem node15Piece18_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece18Input) = evaluate node15Piece18Output :=
  neutralBound_value JR _ _ _ node15Piece18_check

def node15Piece19Input_sector0 : RawPoly ℕ := [(48, [1, 10])]

def node15Piece19Input : SectorVector := [(0, node15Piece19Input_sector0)]
def node15Piece19Output_sector0_chunk0 : RawPoly ℕ := [(192, [1, 1, 1, 1, 6, 10]), (576, [1, 1, 1, 2, 5, 10]), (576, [1, 1, 1, 3, 4, 10]), (5760, [1, 1, 1, 17]), (576, [1, 1, 2, 2, 4, 10]), (576, [1, 1, 2, 3, 3, 10]), (11520, [1, 1, 2, 16]), (11520, [1, 1, 3, 15]), (11520, [1, 1, 4, 14]), (11520, [1, 1, 5, 13]), (11520, [1, 1, 6, 12]), (11520, [1, 1, 7, 11]), (10080, [1, 1, 8, 10]), (5760, [1, 1, 9, 9]), (192, [1, 2, 2, 2, 3, 10]), (5760, [1, 2, 2, 15]), (11520, [1, 2, 3, 14]), (11520, [1, 2, 4, 13]), (11520, [1, 2, 5, 12]), (11520, [1, 2, 6, 11]), (12096, [1, 2, 7, 10]), (11520, [1, 2, 8, 9]), (5760, [1, 3, 3, 13]), (11520, [1, 3, 4, 12])]

def node15Piece19Output_sector0_chunk1 : RawPoly ℕ := [(11520, [1, 3, 5, 11]), (13056, [1, 3, 6, 10]), (11520, [1, 3, 7, 9]), (5760, [1, 3, 8, 8]), (5760, [1, 4, 4, 11]), (13536, [1, 4, 5, 10]), (11520, [1, 4, 6, 9]), (11520, [1, 4, 7, 8]), (5760, [1, 5, 5, 9]), (11520, [1, 5, 6, 8]), (5760, [1, 5, 7, 7]), (5760, [1, 6, 6, 7]), (-483840, [1, 19]), (576, [2, 2, 6, 10]), (1152, [2, 3, 5, 10]), (576, [2, 4, 4, 10]), (11520, [2, 18]), (576, [3, 3, 4, 10]), (11520, [3, 17]), (11520, [4, 16]), (11520, [5, 15]), (11520, [6, 14]), (11520, [7, 13]), (11520, [8, 12])]

def node15Piece19Output_sector0_chunk2 : RawPoly ℕ := [(11520, [9, 11]), (-576, [10, 10])]

def node15Piece19Output_sector0 : RawPoly ℕ := [node15Piece19Output_sector0_chunk0, node15Piece19Output_sector0_chunk1, node15Piece19Output_sector0_chunk2].flatten

def node15Piece19Output : SectorVector := [(0, node15Piece19Output_sector0)]
theorem node15Piece19_check : VectorCertificate (neutralBoundS JR (-6) node15Piece19Input) node15Piece19Output := by decide +kernel
theorem node15Piece19_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece19Input) = evaluate node15Piece19Output :=
  neutralBound_value JR _ _ _ node15Piece19_check

def node15Piece20Input_sector0 : RawPoly ℕ := [(-272, [2, 2, 2, 5])]

def node15Piece20Input : SectorVector := [(0, node15Piece20Input_sector0)]
def node15Piece20Output_sector0_chunk0 : RawPoly ℕ := [(-1088, [1, 1, 1, 2, 2, 2, 5, 6]), (-3264, [1, 1, 2, 2, 2, 2, 5, 5]), (-3264, [1, 1, 2, 2, 2, 3, 4, 5]), (-16320, [1, 1, 2, 2, 2, 12]), (-19584, [1, 1, 2, 2, 5, 9]), (-3264, [1, 2, 2, 2, 2, 2, 4, 5]), (-3264, [1, 2, 2, 2, 2, 3, 3, 5]), (-32640, [1, 2, 2, 2, 2, 11]), (-32640, [1, 2, 2, 2, 3, 10]), (-32640, [1, 2, 2, 2, 4, 9]), (-60384, [1, 2, 2, 2, 5, 8]), (-32640, [1, 2, 2, 2, 6, 7]), (-39168, [1, 2, 2, 3, 5, 7]), (-39168, [1, 2, 2, 4, 5, 6]), (-19584, [1, 2, 2, 5, 5, 5]), (-195840, [1, 2, 2, 15]), (-78336, [1, 2, 5, 12]), (-1088, [2, 2, 2, 2, 2, 2, 3, 5]), (-16320, [2, 2, 2, 2, 2, 10]), (-32640, [2, 2, 2, 2, 3, 9]), (-32640, [2, 2, 2, 2, 4, 8]), (-48960, [2, 2, 2, 2, 5, 7]), (-16320, [2, 2, 2, 2, 6, 6]), (-16320, [2, 2, 2, 3, 3, 8])]

def node15Piece20Output_sector0_chunk1 : RawPoly ℕ := [(-32640, [2, 2, 2, 3, 4, 7]), (-73984, [2, 2, 2, 3, 5, 6]), (-16320, [2, 2, 2, 4, 4, 6]), (-60384, [2, 2, 2, 4, 5, 5]), (391680, [2, 2, 2, 14]), (-19584, [2, 2, 3, 3, 5, 5]), (-19584, [2, 2, 3, 4, 4, 5]), (-195840, [2, 2, 3, 13]), (-195840, [2, 2, 4, 12]), (39168, [2, 2, 5, 11]), (-195840, [2, 2, 6, 10]), (-195840, [2, 2, 7, 9]), (-97920, [2, 2, 8, 8]), (-78336, [2, 3, 5, 10]), (-78336, [2, 4, 5, 9]), (-78336, [2, 5, 5, 8]), (-78336, [2, 5, 6, 7]), (-391680, [2, 18]), (-52224, [5, 15])]

def node15Piece20Output_sector0 : RawPoly ℕ := [node15Piece20Output_sector0_chunk0, node15Piece20Output_sector0_chunk1].flatten

def node15Piece20Output : SectorVector := [(0, node15Piece20Output_sector0)]
theorem node15Piece20_check : VectorCertificate (neutralBoundS JR (-6) node15Piece20Input) node15Piece20Output := by decide +kernel
theorem node15Piece20_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece20Input) = evaluate node15Piece20Output :=
  neutralBound_value JR _ _ _ node15Piece20_check

def node15Piece21Input_sector0 : RawPoly ℕ := [(-280, [2, 2, 3, 4])]

def node15Piece21Input : SectorVector := [(0, node15Piece21Input_sector0)]
def node15Piece21Output_sector0_chunk0 : RawPoly ℕ := [(-1120, [1, 1, 1, 2, 2, 3, 4, 6]), (-3360, [1, 1, 2, 2, 2, 3, 4, 5]), (-3360, [1, 1, 2, 2, 3, 3, 4, 4]), (-13440, [1, 1, 2, 2, 3, 11]), (-10080, [1, 1, 2, 2, 4, 10]), (-13440, [1, 1, 2, 3, 4, 9]), (-3360, [1, 2, 2, 2, 2, 3, 4, 4]), (-3360, [1, 2, 2, 2, 3, 3, 3, 4]), (-26880, [1, 2, 2, 2, 3, 10]), (-20160, [1, 2, 2, 2, 4, 9]), (-26880, [1, 2, 2, 3, 3, 9]), (-62160, [1, 2, 2, 3, 4, 8]), (-26880, [1, 2, 2, 3, 5, 7]), (-13440, [1, 2, 2, 3, 6, 6]), (-20160, [1, 2, 2, 4, 4, 7]), (-20160, [1, 2, 2, 4, 5, 6]), (-80640, [1, 2, 2, 15]), (-26880, [1, 2, 3, 3, 4, 7]), (-26880, [1, 2, 3, 4, 4, 6]), (-13440, [1, 2, 3, 4, 5, 5]), (-107520, [1, 2, 3, 14]), (-80640, [1, 2, 4, 13]), (-26880, [1, 3, 4, 12]), (-1120, [2, 2, 2, 2, 2, 3, 3, 4])]

def node15Piece21Output_sector0_chunk1 : RawPoly ℕ := [(-13440, [2, 2, 2, 2, 3, 9]), (-10080, [2, 2, 2, 2, 4, 8]), (-26880, [2, 2, 2, 3, 3, 8]), (-57120, [2, 2, 2, 3, 4, 7]), (-26880, [2, 2, 2, 3, 5, 6]), (-20160, [2, 2, 2, 4, 4, 6]), (-10080, [2, 2, 2, 4, 5, 5]), (-80640, [2, 2, 2, 14]), (-13440, [2, 2, 3, 3, 3, 7]), (-66080, [2, 2, 3, 3, 4, 6]), (-13440, [2, 2, 3, 3, 5, 5]), (-65520, [2, 2, 3, 4, 4, 5]), (194880, [2, 2, 3, 13]), (-3360, [2, 2, 4, 4, 4, 4]), (58800, [2, 2, 4, 12]), (-80640, [2, 2, 5, 11]), (-80640, [2, 2, 6, 10]), (-80640, [2, 2, 7, 9]), (-40320, [2, 2, 8, 8]), (-13440, [2, 3, 3, 3, 4, 5]), (-13440, [2, 3, 3, 4, 4, 4]), (-107520, [2, 3, 3, 12]), (-107520, [2, 3, 5, 10]), (-107520, [2, 3, 6, 9])]

def node15Piece21Output_sector0_chunk2 : RawPoly ℕ := [(-107520, [2, 3, 7, 8]), (-80640, [2, 4, 4, 10]), (-80640, [2, 4, 5, 9]), (-80640, [2, 4, 6, 8]), (-40320, [2, 4, 7, 7]), (-322560, [2, 18]), (-26880, [3, 3, 4, 10]), (-26880, [3, 4, 4, 9]), (-26880, [3, 4, 5, 8]), (-26880, [3, 4, 6, 7]), (-107520, [3, 17]), (-80640, [4, 16])]

def node15Piece21Output_sector0 : RawPoly ℕ := [node15Piece21Output_sector0_chunk0, node15Piece21Output_sector0_chunk1, node15Piece21Output_sector0_chunk2].flatten

def node15Piece21Output : SectorVector := [(0, node15Piece21Output_sector0)]
theorem node15Piece21_check : VectorCertificate (neutralBoundS JR (-6) node15Piece21Input) node15Piece21Output := by decide +kernel
theorem node15Piece21_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece21Input) = evaluate node15Piece21Output :=
  neutralBound_value JR _ _ _ node15Piece21_check

def node15Piece22Input_sector0 : RawPoly ℕ := [(4960/27, [2, 3, 3, 3])]

def node15Piece22Input : SectorVector := [(0, node15Piece22Input_sector0)]
def node15Piece22Output_sector0_chunk0 : RawPoly ℕ := [(19840/27, [1, 1, 1, 2, 3, 3, 3, 6]), (19840/9, [1, 1, 2, 2, 3, 3, 3, 5]), (19840/9, [1, 1, 2, 3, 3, 3, 3, 4]), (19840, [1, 1, 2, 3, 3, 10]), (39680/9, [1, 1, 3, 3, 3, 9]), (19840/9, [1, 2, 2, 2, 3, 3, 3, 4]), (19840/9, [1, 2, 2, 3, 3, 3, 3, 3]), (39680, [1, 2, 2, 3, 3, 9]), (367040/9, [1, 2, 3, 3, 3, 8]), (39680, [1, 2, 3, 3, 4, 7]), (39680, [1, 2, 3, 3, 5, 6]), (119040, [1, 2, 3, 14]), (79360/9, [1, 3, 3, 3, 3, 7]), (79360/9, [1, 3, 3, 3, 4, 6]), (39680/9, [1, 3, 3, 3, 5, 5]), (79360, [1, 3, 3, 13]), (19840/27, [2, 2, 2, 2, 3, 3, 3, 3]), (19840, [2, 2, 2, 3, 3, 8]), (376960/9, [2, 2, 3, 3, 3, 7]), (39680, [2, 2, 3, 3, 4, 6]), (19840, [2, 2, 3, 3, 5, 5]), (119040, [2, 2, 3, 13]), (813440/27, [2, 3, 3, 3, 3, 6]), (466240/9, [2, 3, 3, 3, 4, 5])]

def node15Piece22Output_sector0_chunk1 : RawPoly ℕ := [(19840/3, [2, 3, 3, 4, 4, 4]), (-704320/3, [2, 3, 3, 12]), (119040, [2, 3, 4, 11]), (119040, [2, 3, 5, 10]), (119040, [2, 3, 6, 9]), (119040, [2, 3, 7, 8]), (119040, [2, 18]), (39680/9, [3, 3, 3, 3, 3, 5]), (39680/9, [3, 3, 3, 3, 4, 4]), (79360/9, [3, 3, 3, 11]), (79360, [3, 3, 4, 10]), (79360, [3, 3, 5, 9]), (79360, [3, 3, 6, 8]), (39680, [3, 3, 7, 7]), (238080, [3, 17])]

def node15Piece22Output_sector0 : RawPoly ℕ := [node15Piece22Output_sector0_chunk0, node15Piece22Output_sector0_chunk1].flatten

def node15Piece22Output : SectorVector := [(0, node15Piece22Output_sector0)]
theorem node15Piece22_check : VectorCertificate (neutralBoundS JR (-6) node15Piece22Input) node15Piece22Output := by decide +kernel
theorem node15Piece22_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece22Input) = evaluate node15Piece22Output :=
  neutralBound_value JR _ _ _ node15Piece22_check

def node15Piece23Input_sector0 : RawPoly ℕ := [(-320/3, [2, 9])]

def node15Piece23Input : SectorVector := [(0, node15Piece23Input_sector0)]
def node15Piece23Output_sector0_chunk0 : RawPoly ℕ := [(-1280/3, [1, 1, 1, 2, 6, 9]), (-1280, [1, 1, 2, 2, 5, 9]), (-1280, [1, 1, 2, 3, 4, 9]), (-11520, [1, 1, 2, 16]), (-2560, [1, 1, 9, 9]), (-1280, [1, 2, 2, 2, 4, 9]), (-1280, [1, 2, 2, 3, 3, 9]), (-23040, [1, 2, 2, 15]), (-23040, [1, 2, 3, 14]), (-23040, [1, 2, 4, 13]), (-23040, [1, 2, 5, 12]), (-23040, [1, 2, 6, 11]), (-23040, [1, 2, 7, 10]), (-23680, [1, 2, 8, 9]), (-5120, [1, 3, 7, 9]), (-5120, [1, 4, 6, 9]), (-2560, [1, 5, 5, 9]), (-46080, [1, 19]), (-1280/3, [2, 2, 2, 2, 3, 9]), (-11520, [2, 2, 2, 14]), (-23040, [2, 2, 3, 13]), (-23040, [2, 2, 4, 12]), (-23040, [2, 2, 5, 11]), (-23040, [2, 2, 6, 10])]

def node15Piece23Output_sector0_chunk1 : RawPoly ℕ := [(-24320, [2, 2, 7, 9]), (-11520, [2, 2, 8, 8]), (-11520, [2, 3, 3, 12]), (-23040, [2, 3, 4, 11]), (-23040, [2, 3, 5, 10]), (-87040/3, [2, 3, 6, 9]), (-23040, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10]), (-30080, [2, 4, 5, 9]), (-23040, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-11520, [2, 5, 5, 8]), (-23040, [2, 5, 6, 7]), (-3840, [2, 6, 6, 6]), (810240, [2, 18]), (-2560, [3, 3, 5, 9]), (-2560, [3, 4, 4, 9]), (-46080, [3, 17]), (-46080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (-46080, [7, 13]), (-46080, [8, 12]), (-5120, [9, 11])]

def node15Piece23Output_sector0_chunk2 : RawPoly ℕ := [(-23040, [10, 10])]

def node15Piece23Output_sector0 : RawPoly ℕ := [node15Piece23Output_sector0_chunk0, node15Piece23Output_sector0_chunk1, node15Piece23Output_sector0_chunk2].flatten

def node15Piece23Output : SectorVector := [(0, node15Piece23Output_sector0)]
theorem node15Piece23_check : VectorCertificate (neutralBoundS JR (-6) node15Piece23Input) node15Piece23Output := by decide +kernel
theorem node15Piece23_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece23Input) = evaluate node15Piece23Output :=
  neutralBound_value JR _ _ _ node15Piece23_check

def node15Piece24Input_sector0 : RawPoly ℕ := [(120, [3, 8])]

def node15Piece24Input : SectorVector := [(0, node15Piece24Input_sector0)]
def node15Piece24Output_sector0_chunk0 : RawPoly ℕ := [(480, [1, 1, 1, 3, 6, 8]), (1440, [1, 1, 2, 3, 5, 8]), (1440, [1, 1, 3, 3, 4, 8]), (11520, [1, 1, 3, 15]), (4320, [1, 1, 8, 10]), (1440, [1, 2, 2, 3, 4, 8]), (1440, [1, 2, 3, 3, 3, 8]), (23040, [1, 2, 3, 14]), (8640, [1, 2, 8, 9]), (23040, [1, 3, 3, 13]), (23040, [1, 3, 4, 12]), (23040, [1, 3, 5, 11]), (23040, [1, 3, 6, 10]), (23040, [1, 3, 7, 9]), (15120, [1, 3, 8, 8]), (8640, [1, 4, 7, 8]), (8640, [1, 5, 6, 8]), (69120, [1, 19]), (480, [2, 2, 2, 3, 3, 8]), (11520, [2, 2, 3, 13]), (4320, [2, 2, 8, 8]), (23040, [2, 3, 3, 12]), (23040, [2, 3, 4, 11]), (23040, [2, 3, 5, 10])]

def node15Piece24Output_sector0_chunk1 : RawPoly ℕ := [(23040, [2, 3, 6, 9]), (30240, [2, 3, 7, 8]), (8640, [2, 4, 6, 8]), (4320, [2, 5, 5, 8]), (69120, [2, 18]), (11520, [3, 3, 3, 11]), (23040, [3, 3, 4, 10]), (23040, [3, 3, 5, 9]), (28320, [3, 3, 6, 8]), (11520, [3, 3, 7, 7]), (11520, [3, 4, 4, 9]), (33840, [3, 4, 5, 8]), (23040, [3, 4, 6, 7]), (11520, [3, 5, 5, 7]), (11520, [3, 5, 6, 6]), (-662400, [3, 17]), (1440, [4, 4, 4, 8]), (69120, [4, 16]), (69120, [5, 15]), (69120, [6, 14]), (69120, [7, 13]), (-25200, [8, 12]), (69120, [9, 11]), (34560, [10, 10])]

def node15Piece24Output_sector0 : RawPoly ℕ := [node15Piece24Output_sector0_chunk0, node15Piece24Output_sector0_chunk1].flatten

def node15Piece24Output : SectorVector := [(0, node15Piece24Output_sector0)]
theorem node15Piece24_check : VectorCertificate (neutralBoundS JR (-6) node15Piece24Input) node15Piece24Output := by decide +kernel
theorem node15Piece24_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece24Input) = evaluate node15Piece24Output :=
  neutralBound_value JR _ _ _ node15Piece24_check

def node15Piece25Input_sector0 : RawPoly ℕ := [(-480/7, [4, 7])]

def node15Piece25Input : SectorVector := [(0, node15Piece25Input_sector0)]
def node15Piece25Output_sector0_chunk0 : RawPoly ℕ := [(-1920/7, [1, 1, 1, 4, 6, 7]), (-5760/7, [1, 1, 2, 4, 5, 7]), (-5760/7, [1, 1, 3, 4, 4, 7]), (-5760, [1, 1, 4, 14]), (-23040/7, [1, 1, 7, 11]), (-5760/7, [1, 2, 2, 4, 4, 7]), (-5760/7, [1, 2, 3, 3, 4, 7]), (-11520, [1, 2, 4, 13]), (-46080/7, [1, 2, 7, 10]), (-11520, [1, 3, 4, 12]), (-46080/7, [1, 3, 7, 9]), (-11520, [1, 4, 4, 11]), (-11520, [1, 4, 5, 10]), (-11520, [1, 4, 6, 9]), (-106560/7, [1, 4, 7, 8]), (-46080/7, [1, 5, 7, 7]), (-23040/7, [1, 6, 6, 7]), (-46080, [1, 19]), (-1920/7, [2, 2, 2, 3, 4, 7]), (-5760, [2, 2, 4, 12]), (-23040/7, [2, 2, 7, 9]), (-11520, [2, 3, 4, 11]), (-46080/7, [2, 3, 7, 8]), (-11520, [2, 4, 4, 10])]

def node15Piece25Output_sector0_chunk1 : RawPoly ℕ := [(-11520, [2, 4, 5, 9]), (-11520, [2, 4, 6, 8]), (-11520, [2, 4, 7, 7]), (-46080/7, [2, 5, 6, 7]), (-46080, [2, 18]), (-5760, [3, 3, 4, 10]), (-23040/7, [3, 3, 7, 7]), (-11520, [3, 4, 4, 9]), (-11520, [3, 4, 5, 8]), (-130560/7, [3, 4, 6, 7]), (-23040/7, [3, 5, 5, 7]), (-46080, [3, 17]), (-5760, [4, 4, 4, 8]), (-112320/7, [4, 4, 5, 7]), (-5760, [4, 4, 6, 6]), (-5760, [4, 5, 5, 6]), (262080, [4, 16]), (-46080, [5, 15]), (-46080, [6, 14]), (334080/7, [7, 13]), (-46080, [8, 12]), (-46080, [9, 11]), (-23040, [10, 10])]

def node15Piece25Output_sector0 : RawPoly ℕ := [node15Piece25Output_sector0_chunk0, node15Piece25Output_sector0_chunk1].flatten

def node15Piece25Output : SectorVector := [(0, node15Piece25Output_sector0)]
theorem node15Piece25_check : VectorCertificate (neutralBoundS JR (-6) node15Piece25Input) node15Piece25Output := by decide +kernel
theorem node15Piece25_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece25Input) = evaluate node15Piece25Output :=
  neutralBound_value JR _ _ _ node15Piece25_check

def node15Piece26Input_sector0 : RawPoly ℕ := [(16, [5, 6])]

def node15Piece26Input : SectorVector := [(0, node15Piece26Input_sector0)]
def node15Piece26Output_sector0_chunk0 : RawPoly ℕ := [(64, [1, 1, 1, 5, 6, 6]), (192, [1, 1, 2, 5, 5, 6]), (192, [1, 1, 3, 4, 5, 6]), (1152, [1, 1, 5, 13]), (960, [1, 1, 6, 12]), (192, [1, 2, 2, 4, 5, 6]), (192, [1, 2, 3, 3, 5, 6]), (2304, [1, 2, 5, 12]), (1920, [1, 2, 6, 11]), (2304, [1, 3, 5, 11]), (1920, [1, 3, 6, 10]), (2304, [1, 4, 5, 10]), (1920, [1, 4, 6, 9]), (2304, [1, 5, 5, 9]), (3552, [1, 5, 6, 8]), (1152, [1, 5, 7, 7]), (1920, [1, 6, 6, 7]), (11520, [1, 19]), (64, [2, 2, 2, 3, 5, 6]), (1152, [2, 2, 5, 11]), (960, [2, 2, 6, 10]), (2304, [2, 3, 5, 10]), (1920, [2, 3, 6, 9]), (2304, [2, 4, 5, 9])]

def node15Piece26Output_sector0_chunk1 : RawPoly ℕ := [(1920, [2, 4, 6, 8]), (2304, [2, 5, 5, 8]), (4032, [2, 5, 6, 7]), (960, [2, 6, 6, 6]), (11520, [2, 18]), (1152, [3, 3, 5, 9]), (960, [3, 3, 6, 8]), (2304, [3, 4, 5, 8]), (1920, [3, 4, 6, 7]), (2304, [3, 5, 5, 7]), (3200, [3, 5, 6, 6]), (11520, [3, 17]), (1152, [4, 4, 5, 7]), (960, [4, 4, 6, 6]), (3552, [4, 5, 5, 6]), (11520, [4, 16]), (384, [5, 5, 5, 5]), (-39552, [5, 15]), (-23040, [6, 14]), (11520, [7, 13]), (11520, [8, 12]), (11520, [9, 11]), (5760, [10, 10])]

def node15Piece26Output_sector0 : RawPoly ℕ := [node15Piece26Output_sector0_chunk0, node15Piece26Output_sector0_chunk1].flatten

def node15Piece26Output : SectorVector := [(0, node15Piece26Output_sector0)]
theorem node15Piece26_check : VectorCertificate (neutralBoundS JR (-6) node15Piece26Input) node15Piece26Output := by decide +kernel
theorem node15Piece26_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-6)
    (evaluate node15Piece26Input) = evaluate node15Piece26Output :=
  neutralBound_value JR _ _ _ node15Piece26_check

end VOA.Classification.COne.OrbC2h
