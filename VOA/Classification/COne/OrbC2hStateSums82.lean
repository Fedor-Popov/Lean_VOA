import VOA.Classification.COne.OrbC2hStatePieces82
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node82Piece0Pad : SectorVector := [(-2, node82Piece0Output_sector0), (0, node82Piece0Output_sector1), (2, [])]

theorem node82Piece0Pad_value : evaluate node82Piece0Pad = evaluate node82Piece0Output := by
  simp only [node82Piece0Pad, node82Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece1Pad : SectorVector := [(-2, node82Piece1Output_sector0), (0, node82Piece1Output_sector1), (2, [])]

theorem node82Piece1Pad_value : evaluate node82Piece1Pad = evaluate node82Piece1Output := by
  simp only [node82Piece1Pad, node82Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece2Pad : SectorVector := [(-2, node82Piece2Output_sector0), (0, node82Piece2Output_sector1), (2, [])]

theorem node82Piece2Pad_value : evaluate node82Piece2Pad = evaluate node82Piece2Output := by
  simp only [node82Piece2Pad, node82Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece3Pad : SectorVector := [(-2, node82Piece3Output_sector0), (0, node82Piece3Output_sector1), (2, [])]

theorem node82Piece3Pad_value : evaluate node82Piece3Pad = evaluate node82Piece3Output := by
  simp only [node82Piece3Pad, node82Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece4Pad : SectorVector := [(-2, node82Piece4Output_sector0), (0, node82Piece4Output_sector1), (2, [])]

theorem node82Piece4Pad_value : evaluate node82Piece4Pad = evaluate node82Piece4Output := by
  simp only [node82Piece4Pad, node82Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece5Pad : SectorVector := [(-2, node82Piece5Output_sector0), (0, node82Piece5Output_sector1), (2, [])]

theorem node82Piece5Pad_value : evaluate node82Piece5Pad = evaluate node82Piece5Output := by
  simp only [node82Piece5Pad, node82Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece6Pad : SectorVector := [(-2, node82Piece6Output_sector0), (0, node82Piece6Output_sector1), (2, [])]

theorem node82Piece6Pad_value : evaluate node82Piece6Pad = evaluate node82Piece6Output := by
  simp only [node82Piece6Pad, node82Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece7Pad : SectorVector := [(-2, []), (0, node82Piece7Output_sector0), (2, node82Piece7Output_sector1)]

theorem node82Piece7Pad_value : evaluate node82Piece7Pad = evaluate node82Piece7Output := by
  simp only [node82Piece7Pad, node82Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece8Pad : SectorVector := [(-2, []), (0, node82Piece8Output_sector0), (2, node82Piece8Output_sector1)]

theorem node82Piece8Pad_value : evaluate node82Piece8Pad = evaluate node82Piece8Output := by
  simp only [node82Piece8Pad, node82Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece9Pad : SectorVector := [(-2, []), (0, node82Piece9Output_sector0), (2, node82Piece9Output_sector1)]

theorem node82Piece9Pad_value : evaluate node82Piece9Pad = evaluate node82Piece9Output := by
  simp only [node82Piece9Pad, node82Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece10Pad : SectorVector := [(-2, []), (0, node82Piece10Output_sector0), (2, node82Piece10Output_sector1)]

theorem node82Piece10Pad_value : evaluate node82Piece10Pad = evaluate node82Piece10Output := by
  simp only [node82Piece10Pad, node82Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece11Pad : SectorVector := [(-2, []), (0, node82Piece11Output_sector0), (2, node82Piece11Output_sector1)]

theorem node82Piece11Pad_value : evaluate node82Piece11Pad = evaluate node82Piece11Output := by
  simp only [node82Piece11Pad, node82Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece12Pad : SectorVector := [(-2, []), (0, node82Piece12Output_sector0), (2, node82Piece12Output_sector1)]

theorem node82Piece12Pad_value : evaluate node82Piece12Pad = evaluate node82Piece12Output := by
  simp only [node82Piece12Pad, node82Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82Piece13Pad : SectorVector := [(-2, []), (0, node82Piece13Output_sector0), (2, node82Piece13Output_sector1)]

theorem node82Piece13Pad_value : evaluate node82Piece13Pad = evaluate node82Piece13Output := by
  simp only [node82Piece13Pad, node82Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node82SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(3360, [])]

def node82SumGroup0Data_sector0 : RawPoly ℕ := [node82SumGroup0Data_sector0_chunk0].flatten

def node82SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-2048/2027025, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (512/9009, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (54784/51975, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (3968/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (512/405, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (128/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (128/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (32/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (128/9, [1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (512/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (48/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (192/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (-1088/63, [1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (-9472/567, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (64/9, [1, 1, 1, 1, 1, 1, 1, 9]), (112/9, [1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (-64/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (8, [1, 1, 1, 1, 1, 1, 2, 8]), (-384/7, [1, 1, 1, 1, 1, 1, 3, 7]), (-272/9, [1, 1, 1, 1, 1, 1, 4, 6]), (448/75, [1, 1, 1, 1, 1, 1, 5, 5]), (328/9, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (48, [1, 1, 1, 1, 1, 2, 2, 7]), (-608/9, [1, 1, 1, 1, 1, 2, 3, 6])]

def node82SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-176/5, [1, 1, 1, 1, 1, 2, 4, 5]), (-4544/45, [1, 1, 1, 1, 1, 3, 3, 5]), (-148, [1, 1, 1, 1, 1, 3, 4, 4]), (-624/11, [1, 1, 1, 1, 1, 11]), (-40/9, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (640/9, [1, 1, 1, 1, 2, 2, 2, 6]), (256, [1, 1, 1, 1, 2, 2, 3, 5]), (-100, [1, 1, 1, 1, 2, 2, 4, 4]), (-1280/9, [1, 1, 1, 1, 2, 3, 3, 4]), (-640/27, [1, 1, 1, 1, 3, 3, 3, 3]), (-1280/9, [1, 1, 1, 1, 3, 9]), (-180, [1, 1, 1, 1, 4, 8]), (-384/7, [1, 1, 1, 1, 5, 7]), (-400/9, [1, 1, 1, 1, 6, 6]), (32/3, [1, 1, 1, 2, 2, 2, 2, 5]), (560/9, [1, 1, 1, 2, 2, 2, 3, 4]), (640/3, [1, 1, 1, 2, 2, 3, 3, 3]), (320/3, [1, 1, 1, 2, 2, 9]), (200, [1, 1, 1, 2, 3, 8]), (-1200/7, [1, 1, 1, 2, 4, 7]), (416/3, [1, 1, 1, 2, 5, 6]), (-2080/9, [1, 1, 1, 3, 4, 6]), (128/3, [1, 1, 1, 3, 5, 5]), (-176, [1, 1, 1, 4, 4, 5])]

def node82SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(-960/13, [1, 1, 1, 13]), (-104, [1, 1, 2, 2, 2, 2, 2, 4]), (560/9, [1, 1, 2, 2, 2, 2, 3, 3]), (-60, [1, 1, 2, 2, 2, 8]), (2400/7, [1, 1, 2, 2, 3, 7]), (-200, [1, 1, 2, 2, 4, 6]), (96, [1, 1, 2, 2, 5, 5]), (4160/9, [1, 1, 2, 3, 3, 6]), (224, [1, 1, 2, 3, 4, 5]), (-160, [1, 1, 2, 4, 4, 4]), (80, [1, 1, 2, 12]), (3968/27, [1, 1, 3, 3, 3, 5]), (-40, [1, 1, 3, 3, 4, 4]), (1440/11, [1, 1, 3, 11]), (-144, [1, 1, 4, 10]), (128/3, [1, 1, 5, 9]), (-388/9, [1, 2, 2, 2, 2, 2, 2, 3]), (-1080/7, [1, 2, 2, 2, 2, 7]), (-560/9, [1, 2, 2, 2, 3, 6]), (-312, [1, 2, 2, 2, 4, 5]), (352, [1, 2, 2, 3, 3, 5]), (-190, [1, 2, 2, 3, 4, 4]), (-120, [1, 2, 2, 11]), (6400/27, [1, 2, 3, 3, 3, 4])]

def node82SumGroup0Data_sector1_chunk3 : RawPoly ℕ := [(288, [1, 2, 3, 10]), (-560/3, [1, 2, 4, 9]), (48, [1, 2, 5, 8]), (1792/81, [1, 3, 3, 3, 3, 3]), (640/3, [1, 3, 3, 9]), (60, [1, 3, 4, 8]), (1536/7, [1, 3, 5, 7]), (800/9, [1, 3, 6, 6]), (-720/7, [1, 4, 4, 7]), (-48, [1, 4, 5, 6]), (512/25, [1, 5, 5, 5]), (32, [1, 15]), (-44/21, [2, 2, 2, 2, 2, 2, 2, 2]), (-160/3, [2, 2, 2, 2, 2, 6]), (-304/3, [2, 2, 2, 2, 3, 5]), (-90, [2, 2, 2, 2, 4, 4]), (-560/9, [2, 2, 2, 3, 3, 4]), (-144, [2, 2, 2, 10]), (320/9, [2, 2, 3, 3, 3, 3]), (-160/3, [2, 2, 3, 9]), (-210, [2, 2, 4, 8]), (-864/7, [2, 2, 5, 7]), (-200/3, [2, 2, 6, 6]), (120, [2, 3, 3, 8])]

def node82SumGroup0Data_sector1_chunk4 : RawPoly ℕ := [(-240/7, [2, 3, 4, 7]), (224/3, [2, 3, 5, 6]), (-120, [2, 4, 4, 6]), (-288/5, [2, 4, 5, 5]), (-480/7, [2, 14]), (1280/21, [3, 3, 3, 7]), (640/9, [3, 3, 4, 6]), (896/15, [3, 3, 5, 5]), (-8, [3, 4, 4, 5]), (960/13, [3, 13]), (-10, [4, 4, 4, 4]), (-40, [4, 12]), (96/11, [5, 11])]

def node82SumGroup0Data_sector1 : RawPoly ℕ := [node82SumGroup0Data_sector1_chunk0, node82SumGroup0Data_sector1_chunk1, node82SumGroup0Data_sector1_chunk2, node82SumGroup0Data_sector1_chunk3, node82SumGroup0Data_sector1_chunk4].flatten

def node82SumGroup0Data_sector2_chunk0 : RawPoly ℕ := [(3360, [])]

def node82SumGroup0Data_sector2 : RawPoly ℕ := [node82SumGroup0Data_sector2_chunk0].flatten

def node82SumGroup0Data : SectorVector := [(-2, node82SumGroup0Data_sector0), (0, node82SumGroup0Data_sector1), (2, node82SumGroup0Data_sector2)]

def node82SumGroup0Outputs : List SectorVector := [node82Piece0Output, node82Piece1Output, node82Piece2Output, node82Piece3Output, node82Piece4Output, node82Piece5Output, node82Piece6Output, node82Piece7Output, node82Piece8Output, node82Piece9Output, node82Piece10Output, node82Piece11Output, node82Piece12Output, node82Piece13Output]

theorem node82SumGroup0_check : zipMany 100000 [node82Piece0Pad, node82Piece1Pad, node82Piece2Pad, node82Piece3Pad, node82Piece4Pad, node82Piece5Pad, node82Piece6Pad, node82Piece7Pad, node82Piece8Pad, node82Piece9Pad, node82Piece10Pad, node82Piece11Pad, node82Piece12Pad, node82Piece13Pad] = node82SumGroup0Data := by decide +kernel

theorem node82SumGroup0_value : evaluate node82SumGroup0Data = (node82SumGroup0Outputs.map evaluate).sum := by
  rw [← node82SumGroup0_check, evaluate_zipMany]
  simp only [node82SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node82Piece0Pad_value, node82Piece1Pad_value, node82Piece2Pad_value, node82Piece3Pad_value, node82Piece4Pad_value, node82Piece5Pad_value, node82Piece6Pad_value, node82Piece7Pad_value, node82Piece8Pad_value, node82Piece9Pad_value, node82Piece10Pad_value, node82Piece11Pad_value, node82Piece12Pad_value, node82Piece13Pad_value]

def node82SumData_sector0_chunk0 : RawPoly ℕ := [(3360, [])]

def node82SumData_sector0 : RawPoly ℕ := [node82SumData_sector0_chunk0].flatten

def node82SumData_sector1_chunk0 : RawPoly ℕ := [(-2048/2027025, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (512/9009, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (54784/51975, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (3968/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (512/405, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (128/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (128/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 7]), (32/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (128/9, [1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (512/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 5]), (48/7, [1, 1, 1, 1, 1, 1, 1, 1, 4, 4]), (192/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (-1088/63, [1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (-9472/567, [1, 1, 1, 1, 1, 1, 1, 3, 3, 3]), (64/9, [1, 1, 1, 1, 1, 1, 1, 9]), (112/9, [1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (-64/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (8, [1, 1, 1, 1, 1, 1, 2, 8]), (-384/7, [1, 1, 1, 1, 1, 1, 3, 7]), (-272/9, [1, 1, 1, 1, 1, 1, 4, 6]), (448/75, [1, 1, 1, 1, 1, 1, 5, 5]), (328/9, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (48, [1, 1, 1, 1, 1, 2, 2, 7]), (-608/9, [1, 1, 1, 1, 1, 2, 3, 6])]

def node82SumData_sector1_chunk1 : RawPoly ℕ := [(-176/5, [1, 1, 1, 1, 1, 2, 4, 5]), (-4544/45, [1, 1, 1, 1, 1, 3, 3, 5]), (-148, [1, 1, 1, 1, 1, 3, 4, 4]), (-624/11, [1, 1, 1, 1, 1, 11]), (-40/9, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2]), (640/9, [1, 1, 1, 1, 2, 2, 2, 6]), (256, [1, 1, 1, 1, 2, 2, 3, 5]), (-100, [1, 1, 1, 1, 2, 2, 4, 4]), (-1280/9, [1, 1, 1, 1, 2, 3, 3, 4]), (-640/27, [1, 1, 1, 1, 3, 3, 3, 3]), (-1280/9, [1, 1, 1, 1, 3, 9]), (-180, [1, 1, 1, 1, 4, 8]), (-384/7, [1, 1, 1, 1, 5, 7]), (-400/9, [1, 1, 1, 1, 6, 6]), (32/3, [1, 1, 1, 2, 2, 2, 2, 5]), (560/9, [1, 1, 1, 2, 2, 2, 3, 4]), (640/3, [1, 1, 1, 2, 2, 3, 3, 3]), (320/3, [1, 1, 1, 2, 2, 9]), (200, [1, 1, 1, 2, 3, 8]), (-1200/7, [1, 1, 1, 2, 4, 7]), (416/3, [1, 1, 1, 2, 5, 6]), (-2080/9, [1, 1, 1, 3, 4, 6]), (128/3, [1, 1, 1, 3, 5, 5]), (-176, [1, 1, 1, 4, 4, 5])]

def node82SumData_sector1_chunk2 : RawPoly ℕ := [(-960/13, [1, 1, 1, 13]), (-104, [1, 1, 2, 2, 2, 2, 2, 4]), (560/9, [1, 1, 2, 2, 2, 2, 3, 3]), (-60, [1, 1, 2, 2, 2, 8]), (2400/7, [1, 1, 2, 2, 3, 7]), (-200, [1, 1, 2, 2, 4, 6]), (96, [1, 1, 2, 2, 5, 5]), (4160/9, [1, 1, 2, 3, 3, 6]), (224, [1, 1, 2, 3, 4, 5]), (-160, [1, 1, 2, 4, 4, 4]), (80, [1, 1, 2, 12]), (3968/27, [1, 1, 3, 3, 3, 5]), (-40, [1, 1, 3, 3, 4, 4]), (1440/11, [1, 1, 3, 11]), (-144, [1, 1, 4, 10]), (128/3, [1, 1, 5, 9]), (-388/9, [1, 2, 2, 2, 2, 2, 2, 3]), (-1080/7, [1, 2, 2, 2, 2, 7]), (-560/9, [1, 2, 2, 2, 3, 6]), (-312, [1, 2, 2, 2, 4, 5]), (352, [1, 2, 2, 3, 3, 5]), (-190, [1, 2, 2, 3, 4, 4]), (-120, [1, 2, 2, 11]), (6400/27, [1, 2, 3, 3, 3, 4])]

def node82SumData_sector1_chunk3 : RawPoly ℕ := [(288, [1, 2, 3, 10]), (-560/3, [1, 2, 4, 9]), (48, [1, 2, 5, 8]), (1792/81, [1, 3, 3, 3, 3, 3]), (640/3, [1, 3, 3, 9]), (60, [1, 3, 4, 8]), (1536/7, [1, 3, 5, 7]), (800/9, [1, 3, 6, 6]), (-720/7, [1, 4, 4, 7]), (-48, [1, 4, 5, 6]), (512/25, [1, 5, 5, 5]), (32, [1, 15]), (-44/21, [2, 2, 2, 2, 2, 2, 2, 2]), (-160/3, [2, 2, 2, 2, 2, 6]), (-304/3, [2, 2, 2, 2, 3, 5]), (-90, [2, 2, 2, 2, 4, 4]), (-560/9, [2, 2, 2, 3, 3, 4]), (-144, [2, 2, 2, 10]), (320/9, [2, 2, 3, 3, 3, 3]), (-160/3, [2, 2, 3, 9]), (-210, [2, 2, 4, 8]), (-864/7, [2, 2, 5, 7]), (-200/3, [2, 2, 6, 6]), (120, [2, 3, 3, 8])]

def node82SumData_sector1_chunk4 : RawPoly ℕ := [(-240/7, [2, 3, 4, 7]), (224/3, [2, 3, 5, 6]), (-120, [2, 4, 4, 6]), (-288/5, [2, 4, 5, 5]), (-480/7, [2, 14]), (1280/21, [3, 3, 3, 7]), (640/9, [3, 3, 4, 6]), (896/15, [3, 3, 5, 5]), (-8, [3, 4, 4, 5]), (960/13, [3, 13]), (-10, [4, 4, 4, 4]), (-40, [4, 12]), (96/11, [5, 11])]

def node82SumData_sector1 : RawPoly ℕ := [node82SumData_sector1_chunk0, node82SumData_sector1_chunk1, node82SumData_sector1_chunk2, node82SumData_sector1_chunk3, node82SumData_sector1_chunk4].flatten

def node82SumData_sector2_chunk0 : RawPoly ℕ := [(3360, [])]

def node82SumData_sector2 : RawPoly ℕ := [node82SumData_sector2_chunk0].flatten

def node82SumData : SectorVector := [(-2, node82SumData_sector0), (0, node82SumData_sector1), (2, node82SumData_sector2)]

def node82OutputGroups : List (List SectorVector) := [node82SumGroup0Outputs]

theorem node82SumData_check : zipMany 100000 [node82SumGroup0Data] = node82SumData := by decide +kernel

theorem node82SumData_value : evaluate node82SumData =
    ((node82OutputGroups.flatten).map evaluate).sum := by
  rw [← node82SumData_check, evaluate_zipMany]
  simp only [node82OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node82SumGroup0_value]

theorem node82Outputs_identity : node82Pieces.map Prod.snd = node82OutputGroups.flatten := rfl

theorem node82Pieces_sum : evaluate (node82Pieces.flatMap Prod.snd) = evaluate node82SumData := by
  rw [evaluate_piece_outputs, node82Outputs_identity, ← node82SumData_value]
end VOA.Classification.COne.OrbC2h
