import VOA.Classification.COne.OrbC2hStateSums8
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node8_sector0 : RawPoly ℕ := []

def node8_sector1_chunk0 : RawPoly ℕ := [(512/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (512/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1664/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (9088/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (64/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (64/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (64/7, [1, 1, 1, 1, 1, 1, 1, 7]), (40/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 2, 6]), (-2432/45, [1, 1, 1, 1, 1, 1, 3, 5]), (-100/3, [1, 1, 1, 1, 1, 1, 4, 4]), (592/5, [1, 1, 1, 1, 1, 2, 2, 5]), (-688/3, [1, 1, 1, 1, 1, 2, 3, 4]), (-2368/27, [1, 1, 1, 1, 1, 3, 3, 3]), (-208/3, [1, 1, 1, 1, 1, 9]), (1600/9, [1, 1, 1, 1, 2, 2, 3, 3]), (-1280/7, [1, 1, 1, 1, 3, 7]), (-240, [1, 1, 1, 1, 4, 6]), (-64/5, [1, 1, 1, 1, 5, 5]), (80, [1, 1, 1, 2, 2, 2, 2, 3]), (960/7, [1, 1, 1, 2, 2, 7]), (800/3, [1, 1, 1, 2, 3, 6]), (-112, [1, 1, 1, 2, 4, 5])]

def node8_sector1_chunk1 : RawPoly ℕ := [(512/9, [1, 1, 1, 3, 3, 5]), (-920/3, [1, 1, 1, 3, 4, 4]), (-960/11, [1, 1, 1, 11]), (-44, [1, 1, 2, 2, 2, 2, 2, 2]), (-80, [1, 1, 2, 2, 2, 6]), (608, [1, 1, 2, 2, 3, 5]), (-330, [1, 1, 2, 2, 4, 4]), (1120/3, [1, 1, 2, 3, 3, 4]), (96, [1, 1, 2, 10]), (640/9, [1, 1, 3, 3, 3, 3]), (160, [1, 1, 3, 9]), (-180, [1, 1, 4, 8]), (384/7, [1, 1, 5, 7]), (-200, [1, 2, 2, 2, 2, 5]), (-280, [1, 2, 2, 2, 3, 4]), (7840/27, [1, 2, 2, 3, 3, 3]), (-440/3, [1, 2, 2, 9]), (360, [1, 2, 3, 8]), (-240, [1, 2, 4, 7]), (64, [1, 2, 5, 6]), (1920/7, [1, 3, 3, 7]), (80, [1, 3, 4, 6]), (896/5, [1, 3, 5, 5]), (-120, [1, 4, 4, 5])]

def node8_sector1_chunk2 : RawPoly ℕ := [(480/13, [1, 13]), (-88, [2, 2, 2, 2, 2, 4]), (-160/3, [2, 2, 2, 2, 3, 3]), (-180, [2, 2, 2, 8]), (-480/7, [2, 2, 3, 7]), (-280, [2, 2, 4, 6]), (-384/5, [2, 2, 5, 5]), (160, [2, 3, 3, 6]), (-16, [2, 3, 4, 5]), (-80, [2, 4, 4, 4]), (-80, [2, 12]), (2432/27, [3, 3, 3, 5]), (80/3, [3, 3, 4, 4]), (960/11, [3, 11]), (-48, [4, 10]), (32/3, [5, 9])]

def node8_sector1 : RawPoly ℕ := [node8_sector1_chunk0, node8_sector1_chunk1, node8_sector1_chunk2].flatten

def node8_sector2 : RawPoly ℕ := []

def node8 : SectorVector := [(-2, node8_sector0), (0, node8_sector1), (2, node8_sector2)]
theorem node8_check : node8SumData = node8 := by decide +kernel

theorem node8_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-2) (evaluate nineData) = evaluate node8 :=
  mode_of_pieces_eval _ _ _ _ node8Pieces node8Pieces_input
    (node8Pieces_sum.trans (congrArg evaluate node8_check)) node8Pieces_each

end VOA.Classification.COne.OrbC2h
