import VOA.Classification.COne.OrbC2hStatePieces76
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node76Piece0Pad : SectorVector := [(-2, node76Piece0Output_sector0), (0, node76Piece0Output_sector1), (2, [])]

theorem node76Piece0Pad_value : evaluate node76Piece0Pad = evaluate node76Piece0Output := by
  simp only [node76Piece0Pad, node76Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece1Pad : SectorVector := [(-2, node76Piece1Output_sector0), (0, node76Piece1Output_sector1), (2, [])]

theorem node76Piece1Pad_value : evaluate node76Piece1Pad = evaluate node76Piece1Output := by
  simp only [node76Piece1Pad, node76Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece2Pad : SectorVector := [(-2, node76Piece2Output_sector0), (0, node76Piece2Output_sector1), (2, [])]

theorem node76Piece2Pad_value : evaluate node76Piece2Pad = evaluate node76Piece2Output := by
  simp only [node76Piece2Pad, node76Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece3Pad : SectorVector := [(-2, node76Piece3Output_sector0), (0, node76Piece3Output_sector1), (2, [])]

theorem node76Piece3Pad_value : evaluate node76Piece3Pad = evaluate node76Piece3Output := by
  simp only [node76Piece3Pad, node76Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece4Pad : SectorVector := [(-2, node76Piece4Output_sector0), (0, node76Piece4Output_sector1), (2, [])]

theorem node76Piece4Pad_value : evaluate node76Piece4Pad = evaluate node76Piece4Output := by
  simp only [node76Piece4Pad, node76Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece5Pad : SectorVector := [(-2, node76Piece5Output_sector0), (0, node76Piece5Output_sector1), (2, [])]

theorem node76Piece5Pad_value : evaluate node76Piece5Pad = evaluate node76Piece5Output := by
  simp only [node76Piece5Pad, node76Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece6Pad : SectorVector := [(-2, node76Piece6Output_sector0), (0, node76Piece6Output_sector1), (2, [])]

theorem node76Piece6Pad_value : evaluate node76Piece6Pad = evaluate node76Piece6Output := by
  simp only [node76Piece6Pad, node76Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece7Pad : SectorVector := [(-2, []), (0, node76Piece7Output_sector0), (2, node76Piece7Output_sector1)]

theorem node76Piece7Pad_value : evaluate node76Piece7Pad = evaluate node76Piece7Output := by
  simp only [node76Piece7Pad, node76Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece8Pad : SectorVector := [(-2, []), (0, node76Piece8Output_sector0), (2, node76Piece8Output_sector1)]

theorem node76Piece8Pad_value : evaluate node76Piece8Pad = evaluate node76Piece8Output := by
  simp only [node76Piece8Pad, node76Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece9Pad : SectorVector := [(-2, []), (0, node76Piece9Output_sector0), (2, node76Piece9Output_sector1)]

theorem node76Piece9Pad_value : evaluate node76Piece9Pad = evaluate node76Piece9Output := by
  simp only [node76Piece9Pad, node76Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece10Pad : SectorVector := [(-2, []), (0, node76Piece10Output_sector0), (2, node76Piece10Output_sector1)]

theorem node76Piece10Pad_value : evaluate node76Piece10Pad = evaluate node76Piece10Output := by
  simp only [node76Piece10Pad, node76Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece11Pad : SectorVector := [(-2, []), (0, node76Piece11Output_sector0), (2, node76Piece11Output_sector1)]

theorem node76Piece11Pad_value : evaluate node76Piece11Pad = evaluate node76Piece11Output := by
  simp only [node76Piece11Pad, node76Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece12Pad : SectorVector := [(-2, []), (0, node76Piece12Output_sector0), (2, node76Piece12Output_sector1)]

theorem node76Piece12Pad_value : evaluate node76Piece12Pad = evaluate node76Piece12Output := by
  simp only [node76Piece12Pad, node76Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76Piece13Pad : SectorVector := [(-2, []), (0, node76Piece13Output_sector0), (2, node76Piece13Output_sector1)]

theorem node76Piece13Pad_value : evaluate node76Piece13Pad = evaluate node76Piece13Output := by
  simp only [node76Piece13Pad, node76Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node76SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(-2310, [0, 1])]

def node76SumGroup0Data_sector0 : RawPoly ℕ := [node76SumGroup0Data_sector0_chunk0].flatten

def node76SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-1024/184275, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (7808/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (2048/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (-1024/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]), (15872/4725, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]), (1024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]), (928/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]), (256/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]), (16/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 8]), (256/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 7]), (256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 6]), (1408/105, [1, 1, 1, 1, 1, 1, 1, 1, 4, 5]), (176/315, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]), (928/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 6]), (256/45, [1, 1, 1, 1, 1, 1, 1, 2, 3, 5]), (88/21, [1, 1, 1, 1, 1, 1, 1, 2, 4, 4]), (-1600/63, [1, 1, 1, 1, 1, 1, 1, 3, 3, 4]), (32/5, [1, 1, 1, 1, 1, 1, 1, 10]), (1472/45, [1, 1, 1, 1, 1, 1, 2, 2, 2, 5]), (-224/9, [1, 1, 1, 1, 1, 1, 2, 2, 3, 4]), (-3328/81, [1, 1, 1, 1, 1, 1, 2, 3, 3, 3]), (64/9, [1, 1, 1, 1, 1, 1, 2, 9]), (-48, [1, 1, 1, 1, 1, 1, 3, 8])]

def node76SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-544/21, [1, 1, 1, 1, 1, 1, 4, 7]), (-64/45, [1, 1, 1, 1, 1, 1, 5, 6]), (6, [1, 1, 1, 1, 1, 2, 2, 2, 2, 4]), (352/9, [1, 1, 1, 1, 1, 2, 2, 2, 3, 3]), (42, [1, 1, 1, 1, 1, 2, 2, 8]), (-1216/21, [1, 1, 1, 1, 1, 2, 3, 7]), (-72, [1, 1, 1, 1, 1, 2, 4, 6]), (928/25, [1, 1, 1, 1, 1, 2, 5, 5]), (-928/9, [1, 1, 1, 1, 1, 3, 3, 6]), (-2272/15, [1, 1, 1, 1, 1, 3, 4, 5]), (-37, [1, 1, 1, 1, 1, 4, 4, 4]), (-52, [1, 1, 1, 1, 1, 12]), (128/9, [1, 1, 1, 1, 2, 2, 2, 2, 2, 3]), (1280/21, [1, 1, 1, 1, 2, 2, 2, 7]), (1280/9, [1, 1, 1, 1, 2, 2, 3, 6]), (32, [1, 1, 1, 1, 2, 2, 4, 5]), (512/9, [1, 1, 1, 1, 2, 3, 3, 5]), (-640/3, [1, 1, 1, 1, 2, 3, 4, 4]), (-2560/27, [1, 1, 1, 1, 3, 3, 3, 4]), (-128, [1, 1, 1, 1, 3, 10]), (-160, [1, 1, 1, 1, 4, 9]), (-48, [1, 1, 1, 1, 5, 8]), (-1600/21, [1, 1, 1, 1, 6, 7]), (-412/63, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2])]

def node76SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(-80/9, [1, 1, 1, 2, 2, 2, 2, 6]), (2240/9, [1, 1, 1, 2, 2, 2, 3, 5]), (-310/3, [1, 1, 1, 2, 2, 2, 4, 4]), (1600/9, [1, 1, 1, 2, 2, 3, 3, 4]), (96, [1, 1, 1, 2, 2, 10]), (1600/27, [1, 1, 1, 2, 3, 3, 3, 3]), (1600/9, [1, 1, 1, 2, 3, 9]), (-150, [1, 1, 1, 2, 4, 8]), (832/7, [1, 1, 1, 2, 5, 7]), (200/9, [1, 1, 1, 2, 6, 6]), (-4160/21, [1, 1, 1, 3, 4, 7]), (128/9, [1, 1, 1, 3, 5, 6]), (-520/3, [1, 1, 1, 4, 4, 6]), (-256/5, [1, 1, 1, 4, 5, 5]), (-480/7, [1, 1, 1, 14]), (-288/5, [1, 1, 2, 2, 2, 2, 2, 5]), (-100, [1, 1, 2, 2, 2, 2, 3, 4]), (4160/27, [1, 1, 2, 2, 2, 3, 3, 3]), (-160/3, [1, 1, 2, 2, 2, 9]), (300, [1, 1, 2, 2, 3, 8]), (-1200/7, [1, 1, 2, 2, 4, 7]), (96, [1, 1, 2, 2, 5, 6]), (8320/21, [1, 1, 2, 3, 3, 7]), (80, [1, 1, 2, 3, 4, 6])]

def node76SumGroup0Data_sector1_chunk3 : RawPoly ℕ := [(1472/5, [1, 1, 2, 3, 5, 5]), (-192, [1, 1, 2, 4, 4, 5]), (960/13, [1, 1, 2, 13]), (320/3, [1, 1, 3, 3, 3, 6]), (320/3, [1, 1, 3, 3, 4, 5]), (-90, [1, 1, 3, 4, 4, 4]), (120, [1, 1, 3, 12]), (-1440/11, [1, 1, 4, 11]), (192/5, [1, 1, 5, 10]), (-139/3, [1, 2, 2, 2, 2, 2, 2, 4]), (-272/9, [1, 2, 2, 2, 2, 2, 3, 3]), (-135, [1, 2, 2, 2, 2, 8]), (-160/3, [1, 2, 2, 2, 3, 7]), (-860/3, [1, 2, 2, 2, 4, 6]), (-336/5, [1, 2, 2, 2, 5, 5]), (2320/9, [1, 2, 2, 3, 3, 6]), (-16, [1, 2, 2, 3, 4, 5]), (-265/2, [1, 2, 2, 4, 4, 4]), (-110, [1, 2, 2, 12]), (7424/27, [1, 2, 3, 3, 3, 5]), (160/3, [1, 2, 3, 3, 4, 4]), (2880/11, [1, 2, 3, 11]), (-168, [1, 2, 4, 10]), (128/3, [1, 2, 5, 9])]

def node76SumGroup0Data_sector1_chunk4 : RawPoly ℕ := [(160/3, [1, 3, 3, 3, 3, 4]), (192, [1, 3, 3, 10]), (160/3, [1, 3, 4, 9]), (192, [1, 3, 5, 8]), (3200/21, [1, 3, 6, 7]), (-90, [1, 4, 4, 8]), (-288/7, [1, 4, 5, 7]), (-100/3, [1, 4, 6, 6]), (192/5, [1, 5, 5, 6]), (30, [1, 16]), (-484/63, [2, 2, 2, 2, 2, 2, 2, 3]), (-320/7, [2, 2, 2, 2, 2, 7]), (-800/9, [2, 2, 2, 2, 3, 6]), (-124, [2, 2, 2, 2, 4, 5]), (-128/9, [2, 2, 2, 3, 3, 5]), (-370/3, [2, 2, 2, 3, 4, 4]), (-1440/11, [2, 2, 2, 11]), (1120/27, [2, 2, 3, 3, 3, 4]), (-48, [2, 2, 3, 10]), (-560/3, [2, 2, 4, 9]), (-108, [2, 2, 5, 8]), (-800/7, [2, 2, 6, 7]), (1216/81, [2, 3, 3, 3, 3, 3]), (320/3, [2, 3, 3, 9])]

def node76SumGroup0Data_sector1_chunk5 : RawPoly ℕ := [(-30, [2, 3, 4, 8]), (64, [2, 3, 5, 7]), (200/9, [2, 3, 6, 6]), (-720/7, [2, 4, 4, 7]), (-112, [2, 4, 5, 6]), (-64/25, [2, 5, 5, 5]), (-64, [2, 15]), (160/3, [3, 3, 3, 8]), (1280/21, [3, 3, 4, 7]), (832/9, [3, 3, 5, 6]), (-40/3, [3, 4, 4, 6]), (128/5, [3, 4, 5, 5]), (480/7, [3, 14]), (-22, [4, 4, 4, 5]), (-480/13, [4, 13]), (8, [5, 12])]

def node76SumGroup0Data_sector1 : RawPoly ℕ := [node76SumGroup0Data_sector1_chunk0, node76SumGroup0Data_sector1_chunk1, node76SumGroup0Data_sector1_chunk2, node76SumGroup0Data_sector1_chunk3, node76SumGroup0Data_sector1_chunk4, node76SumGroup0Data_sector1_chunk5].flatten

def node76SumGroup0Data_sector2_chunk0 : RawPoly ℕ := [(2310, [0, 1])]

def node76SumGroup0Data_sector2 : RawPoly ℕ := [node76SumGroup0Data_sector2_chunk0].flatten

def node76SumGroup0Data : SectorVector := [(-2, node76SumGroup0Data_sector0), (0, node76SumGroup0Data_sector1), (2, node76SumGroup0Data_sector2)]

def node76SumGroup0Outputs : List SectorVector := [node76Piece0Output, node76Piece1Output, node76Piece2Output, node76Piece3Output, node76Piece4Output, node76Piece5Output, node76Piece6Output, node76Piece7Output, node76Piece8Output, node76Piece9Output, node76Piece10Output, node76Piece11Output, node76Piece12Output, node76Piece13Output]

theorem node76SumGroup0_check : zipMany 100000 [node76Piece0Pad, node76Piece1Pad, node76Piece2Pad, node76Piece3Pad, node76Piece4Pad, node76Piece5Pad, node76Piece6Pad, node76Piece7Pad, node76Piece8Pad, node76Piece9Pad, node76Piece10Pad, node76Piece11Pad, node76Piece12Pad, node76Piece13Pad] = node76SumGroup0Data := by decide +kernel

theorem node76SumGroup0_value : evaluate node76SumGroup0Data = (node76SumGroup0Outputs.map evaluate).sum := by
  rw [← node76SumGroup0_check, evaluate_zipMany]
  simp only [node76SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node76Piece0Pad_value, node76Piece1Pad_value, node76Piece2Pad_value, node76Piece3Pad_value, node76Piece4Pad_value, node76Piece5Pad_value, node76Piece6Pad_value, node76Piece7Pad_value, node76Piece8Pad_value, node76Piece9Pad_value, node76Piece10Pad_value, node76Piece11Pad_value, node76Piece12Pad_value, node76Piece13Pad_value]

def node76SumData_sector0_chunk0 : RawPoly ℕ := [(-2310, [0, 1])]

def node76SumData_sector0 : RawPoly ℕ := [node76SumData_sector0_chunk0].flatten

def node76SumData_sector1_chunk0 : RawPoly ℕ := [(-1024/184275, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (7808/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (2048/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (-1024/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]), (15872/4725, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]), (1024/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]), (928/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]), (256/567, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]), (16/3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 8]), (256/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 7]), (256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 6]), (1408/105, [1, 1, 1, 1, 1, 1, 1, 1, 4, 5]), (176/315, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]), (928/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 6]), (256/45, [1, 1, 1, 1, 1, 1, 1, 2, 3, 5]), (88/21, [1, 1, 1, 1, 1, 1, 1, 2, 4, 4]), (-1600/63, [1, 1, 1, 1, 1, 1, 1, 3, 3, 4]), (32/5, [1, 1, 1, 1, 1, 1, 1, 10]), (1472/45, [1, 1, 1, 1, 1, 1, 2, 2, 2, 5]), (-224/9, [1, 1, 1, 1, 1, 1, 2, 2, 3, 4]), (-3328/81, [1, 1, 1, 1, 1, 1, 2, 3, 3, 3]), (64/9, [1, 1, 1, 1, 1, 1, 2, 9]), (-48, [1, 1, 1, 1, 1, 1, 3, 8])]

def node76SumData_sector1_chunk1 : RawPoly ℕ := [(-544/21, [1, 1, 1, 1, 1, 1, 4, 7]), (-64/45, [1, 1, 1, 1, 1, 1, 5, 6]), (6, [1, 1, 1, 1, 1, 2, 2, 2, 2, 4]), (352/9, [1, 1, 1, 1, 1, 2, 2, 2, 3, 3]), (42, [1, 1, 1, 1, 1, 2, 2, 8]), (-1216/21, [1, 1, 1, 1, 1, 2, 3, 7]), (-72, [1, 1, 1, 1, 1, 2, 4, 6]), (928/25, [1, 1, 1, 1, 1, 2, 5, 5]), (-928/9, [1, 1, 1, 1, 1, 3, 3, 6]), (-2272/15, [1, 1, 1, 1, 1, 3, 4, 5]), (-37, [1, 1, 1, 1, 1, 4, 4, 4]), (-52, [1, 1, 1, 1, 1, 12]), (128/9, [1, 1, 1, 1, 2, 2, 2, 2, 2, 3]), (1280/21, [1, 1, 1, 1, 2, 2, 2, 7]), (1280/9, [1, 1, 1, 1, 2, 2, 3, 6]), (32, [1, 1, 1, 1, 2, 2, 4, 5]), (512/9, [1, 1, 1, 1, 2, 3, 3, 5]), (-640/3, [1, 1, 1, 1, 2, 3, 4, 4]), (-2560/27, [1, 1, 1, 1, 3, 3, 3, 4]), (-128, [1, 1, 1, 1, 3, 10]), (-160, [1, 1, 1, 1, 4, 9]), (-48, [1, 1, 1, 1, 5, 8]), (-1600/21, [1, 1, 1, 1, 6, 7]), (-412/63, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2])]

def node76SumData_sector1_chunk2 : RawPoly ℕ := [(-80/9, [1, 1, 1, 2, 2, 2, 2, 6]), (2240/9, [1, 1, 1, 2, 2, 2, 3, 5]), (-310/3, [1, 1, 1, 2, 2, 2, 4, 4]), (1600/9, [1, 1, 1, 2, 2, 3, 3, 4]), (96, [1, 1, 1, 2, 2, 10]), (1600/27, [1, 1, 1, 2, 3, 3, 3, 3]), (1600/9, [1, 1, 1, 2, 3, 9]), (-150, [1, 1, 1, 2, 4, 8]), (832/7, [1, 1, 1, 2, 5, 7]), (200/9, [1, 1, 1, 2, 6, 6]), (-4160/21, [1, 1, 1, 3, 4, 7]), (128/9, [1, 1, 1, 3, 5, 6]), (-520/3, [1, 1, 1, 4, 4, 6]), (-256/5, [1, 1, 1, 4, 5, 5]), (-480/7, [1, 1, 1, 14]), (-288/5, [1, 1, 2, 2, 2, 2, 2, 5]), (-100, [1, 1, 2, 2, 2, 2, 3, 4]), (4160/27, [1, 1, 2, 2, 2, 3, 3, 3]), (-160/3, [1, 1, 2, 2, 2, 9]), (300, [1, 1, 2, 2, 3, 8]), (-1200/7, [1, 1, 2, 2, 4, 7]), (96, [1, 1, 2, 2, 5, 6]), (8320/21, [1, 1, 2, 3, 3, 7]), (80, [1, 1, 2, 3, 4, 6])]

def node76SumData_sector1_chunk3 : RawPoly ℕ := [(1472/5, [1, 1, 2, 3, 5, 5]), (-192, [1, 1, 2, 4, 4, 5]), (960/13, [1, 1, 2, 13]), (320/3, [1, 1, 3, 3, 3, 6]), (320/3, [1, 1, 3, 3, 4, 5]), (-90, [1, 1, 3, 4, 4, 4]), (120, [1, 1, 3, 12]), (-1440/11, [1, 1, 4, 11]), (192/5, [1, 1, 5, 10]), (-139/3, [1, 2, 2, 2, 2, 2, 2, 4]), (-272/9, [1, 2, 2, 2, 2, 2, 3, 3]), (-135, [1, 2, 2, 2, 2, 8]), (-160/3, [1, 2, 2, 2, 3, 7]), (-860/3, [1, 2, 2, 2, 4, 6]), (-336/5, [1, 2, 2, 2, 5, 5]), (2320/9, [1, 2, 2, 3, 3, 6]), (-16, [1, 2, 2, 3, 4, 5]), (-265/2, [1, 2, 2, 4, 4, 4]), (-110, [1, 2, 2, 12]), (7424/27, [1, 2, 3, 3, 3, 5]), (160/3, [1, 2, 3, 3, 4, 4]), (2880/11, [1, 2, 3, 11]), (-168, [1, 2, 4, 10]), (128/3, [1, 2, 5, 9])]

def node76SumData_sector1_chunk4 : RawPoly ℕ := [(160/3, [1, 3, 3, 3, 3, 4]), (192, [1, 3, 3, 10]), (160/3, [1, 3, 4, 9]), (192, [1, 3, 5, 8]), (3200/21, [1, 3, 6, 7]), (-90, [1, 4, 4, 8]), (-288/7, [1, 4, 5, 7]), (-100/3, [1, 4, 6, 6]), (192/5, [1, 5, 5, 6]), (30, [1, 16]), (-484/63, [2, 2, 2, 2, 2, 2, 2, 3]), (-320/7, [2, 2, 2, 2, 2, 7]), (-800/9, [2, 2, 2, 2, 3, 6]), (-124, [2, 2, 2, 2, 4, 5]), (-128/9, [2, 2, 2, 3, 3, 5]), (-370/3, [2, 2, 2, 3, 4, 4]), (-1440/11, [2, 2, 2, 11]), (1120/27, [2, 2, 3, 3, 3, 4]), (-48, [2, 2, 3, 10]), (-560/3, [2, 2, 4, 9]), (-108, [2, 2, 5, 8]), (-800/7, [2, 2, 6, 7]), (1216/81, [2, 3, 3, 3, 3, 3]), (320/3, [2, 3, 3, 9])]

def node76SumData_sector1_chunk5 : RawPoly ℕ := [(-30, [2, 3, 4, 8]), (64, [2, 3, 5, 7]), (200/9, [2, 3, 6, 6]), (-720/7, [2, 4, 4, 7]), (-112, [2, 4, 5, 6]), (-64/25, [2, 5, 5, 5]), (-64, [2, 15]), (160/3, [3, 3, 3, 8]), (1280/21, [3, 3, 4, 7]), (832/9, [3, 3, 5, 6]), (-40/3, [3, 4, 4, 6]), (128/5, [3, 4, 5, 5]), (480/7, [3, 14]), (-22, [4, 4, 4, 5]), (-480/13, [4, 13]), (8, [5, 12])]

def node76SumData_sector1 : RawPoly ℕ := [node76SumData_sector1_chunk0, node76SumData_sector1_chunk1, node76SumData_sector1_chunk2, node76SumData_sector1_chunk3, node76SumData_sector1_chunk4, node76SumData_sector1_chunk5].flatten

def node76SumData_sector2_chunk0 : RawPoly ℕ := [(2310, [0, 1])]

def node76SumData_sector2 : RawPoly ℕ := [node76SumData_sector2_chunk0].flatten

def node76SumData : SectorVector := [(-2, node76SumData_sector0), (0, node76SumData_sector1), (2, node76SumData_sector2)]

def node76OutputGroups : List (List SectorVector) := [node76SumGroup0Outputs]

theorem node76SumData_check : zipMany 100000 [node76SumGroup0Data] = node76SumData := by decide +kernel

theorem node76SumData_value : evaluate node76SumData =
    ((node76OutputGroups.flatten).map evaluate).sum := by
  rw [← node76SumData_check, evaluate_zipMany]
  simp only [node76OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node76SumGroup0_value]

theorem node76Outputs_identity : node76Pieces.map Prod.snd = node76OutputGroups.flatten := rfl

theorem node76Pieces_sum : evaluate (node76Pieces.flatMap Prod.snd) = evaluate node76SumData := by
  rw [evaluate_piece_outputs, node76Outputs_identity, ← node76SumData_value]
end VOA.Classification.COne.OrbC2h
