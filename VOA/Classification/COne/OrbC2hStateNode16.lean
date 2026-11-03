import VOA.Classification.COne.OrbC2hStateSums16
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node16_sector0 : RawPoly ℕ := []

def node16_sector1_chunk0 : RawPoly ℕ := [(2048/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (2144/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (512/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (96/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 1, 6]), (704/15, [1, 1, 1, 1, 1, 1, 2, 5]), (-1120/9, [1, 1, 1, 1, 1, 1, 3, 4]), (-12, [1, 1, 1, 1, 1, 2, 2, 4]), (-1120/9, [1, 1, 1, 1, 1, 2, 3, 3]), (-78, [1, 1, 1, 1, 1, 8]), (640/3, [1, 1, 1, 1, 2, 2, 2, 3]), (-640/3, [1, 1, 1, 1, 3, 6]), (-224, [1, 1, 1, 1, 4, 5]), (-36, [1, 1, 1, 2, 2, 2, 2, 2]), (160, [1, 1, 1, 2, 2, 6]), (1472/3, [1, 1, 1, 2, 3, 5]), (-350, [1, 1, 1, 2, 4, 4]), (-1600/9, [1, 1, 1, 3, 3, 4]), (-96, [1, 1, 1, 10]), (-32, [1, 1, 2, 2, 2, 5]), (120, [1, 1, 2, 2, 3, 4]), (11840/27, [1, 1, 2, 3, 3, 3]), (320/3, [1, 1, 2, 9]), (180, [1, 1, 3, 8])]

def node16_sector1_chunk1 : RawPoly ℕ := [(-1440/7, [1, 1, 4, 7]), (64, [1, 1, 5, 6]), (-340, [1, 2, 2, 2, 2, 4]), (400/3, [1, 2, 2, 2, 3, 3]), (-165, [1, 2, 2, 8]), (2880/7, [1, 2, 3, 7]), (-280, [1, 2, 4, 6]), (384/5, [1, 2, 5, 5]), (320, [1, 3, 3, 6]), (160, [1, 3, 4, 5]), (-95, [1, 4, 4, 4]), (40, [1, 12]), (-84, [2, 2, 2, 2, 2, 3]), (-1440/7, [2, 2, 2, 7]), (-80, [2, 2, 3, 6]), (-312, [2, 2, 4, 5]), (640/3, [2, 3, 3, 5]), (-110, [2, 3, 4, 4]), (-960/11, [2, 11]), (2240/27, [3, 3, 3, 4]), (96, [3, 10]), (-160/3, [4, 9]), (12, [5, 8])]

def node16_sector1 : RawPoly ℕ := [node16_sector1_chunk0, node16_sector1_chunk1].flatten

def node16_sector2 : RawPoly ℕ := []

def node16 : SectorVector := [(-2, node16_sector0), (0, node16_sector1), (2, node16_sector2)]
theorem node16_check : node16SumData = node16 := by decide +kernel

theorem node16_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-1) (evaluate nineData) = evaluate node16 :=
  mode_of_pieces_eval _ _ _ _ node16Pieces node16Pieces_input
    (node16Pieces_sum.trans (congrArg evaluate node16_check)) node16Pieces_each

end VOA.Classification.COne.OrbC2h
