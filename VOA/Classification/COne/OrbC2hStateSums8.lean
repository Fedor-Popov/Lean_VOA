import VOA.Classification.COne.OrbC2hStatePieces8
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node8Piece0Pad : SectorVector := [(-2, node8Piece0Output_sector0), (0, node8Piece0Output_sector1), (2, [])]

theorem node8Piece0Pad_value : evaluate node8Piece0Pad = evaluate node8Piece0Output := by
  simp only [node8Piece0Pad, node8Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece1Pad : SectorVector := [(-2, node8Piece1Output_sector0), (0, node8Piece1Output_sector1), (2, [])]

theorem node8Piece1Pad_value : evaluate node8Piece1Pad = evaluate node8Piece1Output := by
  simp only [node8Piece1Pad, node8Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece2Pad : SectorVector := [(-2, node8Piece2Output_sector0), (0, node8Piece2Output_sector1), (2, [])]

theorem node8Piece2Pad_value : evaluate node8Piece2Pad = evaluate node8Piece2Output := by
  simp only [node8Piece2Pad, node8Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece3Pad : SectorVector := [(-2, node8Piece3Output_sector0), (0, node8Piece3Output_sector1), (2, [])]

theorem node8Piece3Pad_value : evaluate node8Piece3Pad = evaluate node8Piece3Output := by
  simp only [node8Piece3Pad, node8Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece4Pad : SectorVector := [(-2, node8Piece4Output_sector0), (0, node8Piece4Output_sector1), (2, [])]

theorem node8Piece4Pad_value : evaluate node8Piece4Pad = evaluate node8Piece4Output := by
  simp only [node8Piece4Pad, node8Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece5Pad : SectorVector := [(-2, node8Piece5Output_sector0), (0, node8Piece5Output_sector1), (2, [])]

theorem node8Piece5Pad_value : evaluate node8Piece5Pad = evaluate node8Piece5Output := by
  simp only [node8Piece5Pad, node8Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece6Pad : SectorVector := [(-2, node8Piece6Output_sector0), (0, node8Piece6Output_sector1), (2, [])]

theorem node8Piece6Pad_value : evaluate node8Piece6Pad = evaluate node8Piece6Output := by
  simp only [node8Piece6Pad, node8Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece7Pad : SectorVector := [(-2, []), (0, node8Piece7Output_sector0), (2, node8Piece7Output_sector1)]

theorem node8Piece7Pad_value : evaluate node8Piece7Pad = evaluate node8Piece7Output := by
  simp only [node8Piece7Pad, node8Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece8Pad : SectorVector := [(-2, []), (0, node8Piece8Output_sector0), (2, node8Piece8Output_sector1)]

theorem node8Piece8Pad_value : evaluate node8Piece8Pad = evaluate node8Piece8Output := by
  simp only [node8Piece8Pad, node8Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece9Pad : SectorVector := [(-2, []), (0, node8Piece9Output_sector0), (2, node8Piece9Output_sector1)]

theorem node8Piece9Pad_value : evaluate node8Piece9Pad = evaluate node8Piece9Output := by
  simp only [node8Piece9Pad, node8Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece10Pad : SectorVector := [(-2, []), (0, node8Piece10Output_sector0), (2, node8Piece10Output_sector1)]

theorem node8Piece10Pad_value : evaluate node8Piece10Pad = evaluate node8Piece10Output := by
  simp only [node8Piece10Pad, node8Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece11Pad : SectorVector := [(-2, []), (0, node8Piece11Output_sector0), (2, node8Piece11Output_sector1)]

theorem node8Piece11Pad_value : evaluate node8Piece11Pad = evaluate node8Piece11Output := by
  simp only [node8Piece11Pad, node8Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece12Pad : SectorVector := [(-2, []), (0, node8Piece12Output_sector0), (2, node8Piece12Output_sector1)]

theorem node8Piece12Pad_value : evaluate node8Piece12Pad = evaluate node8Piece12Output := by
  simp only [node8Piece12Pad, node8Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8Piece13Pad : SectorVector := [(-2, []), (0, node8Piece13Output_sector0), (2, node8Piece13Output_sector1)]

theorem node8Piece13Pad_value : evaluate node8Piece13Pad = evaluate node8Piece13Output := by
  simp only [node8Piece13Pad, node8Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node8SumGroup0Data_sector0 : RawPoly ℕ := [].flatten

def node8SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(512/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (512/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1664/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (9088/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (64/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (64/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (64/7, [1, 1, 1, 1, 1, 1, 1, 7]), (40/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 2, 6]), (-2432/45, [1, 1, 1, 1, 1, 1, 3, 5]), (-100/3, [1, 1, 1, 1, 1, 1, 4, 4]), (592/5, [1, 1, 1, 1, 1, 2, 2, 5]), (-688/3, [1, 1, 1, 1, 1, 2, 3, 4]), (-2368/27, [1, 1, 1, 1, 1, 3, 3, 3]), (-208/3, [1, 1, 1, 1, 1, 9]), (1600/9, [1, 1, 1, 1, 2, 2, 3, 3]), (-1280/7, [1, 1, 1, 1, 3, 7]), (-240, [1, 1, 1, 1, 4, 6]), (-64/5, [1, 1, 1, 1, 5, 5]), (80, [1, 1, 1, 2, 2, 2, 2, 3]), (960/7, [1, 1, 1, 2, 2, 7]), (800/3, [1, 1, 1, 2, 3, 6]), (-112, [1, 1, 1, 2, 4, 5])]

def node8SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(512/9, [1, 1, 1, 3, 3, 5]), (-920/3, [1, 1, 1, 3, 4, 4]), (-960/11, [1, 1, 1, 11]), (-44, [1, 1, 2, 2, 2, 2, 2, 2]), (-80, [1, 1, 2, 2, 2, 6]), (608, [1, 1, 2, 2, 3, 5]), (-330, [1, 1, 2, 2, 4, 4]), (1120/3, [1, 1, 2, 3, 3, 4]), (96, [1, 1, 2, 10]), (640/9, [1, 1, 3, 3, 3, 3]), (160, [1, 1, 3, 9]), (-180, [1, 1, 4, 8]), (384/7, [1, 1, 5, 7]), (-200, [1, 2, 2, 2, 2, 5]), (-280, [1, 2, 2, 2, 3, 4]), (7840/27, [1, 2, 2, 3, 3, 3]), (-440/3, [1, 2, 2, 9]), (360, [1, 2, 3, 8]), (-240, [1, 2, 4, 7]), (64, [1, 2, 5, 6]), (1920/7, [1, 3, 3, 7]), (80, [1, 3, 4, 6]), (896/5, [1, 3, 5, 5]), (-120, [1, 4, 4, 5])]

def node8SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(480/13, [1, 13]), (-88, [2, 2, 2, 2, 2, 4]), (-160/3, [2, 2, 2, 2, 3, 3]), (-180, [2, 2, 2, 8]), (-480/7, [2, 2, 3, 7]), (-280, [2, 2, 4, 6]), (-384/5, [2, 2, 5, 5]), (160, [2, 3, 3, 6]), (-16, [2, 3, 4, 5]), (-80, [2, 4, 4, 4]), (-80, [2, 12]), (2432/27, [3, 3, 3, 5]), (80/3, [3, 3, 4, 4]), (960/11, [3, 11]), (-48, [4, 10]), (32/3, [5, 9])]

def node8SumGroup0Data_sector1 : RawPoly ℕ := [node8SumGroup0Data_sector1_chunk0, node8SumGroup0Data_sector1_chunk1, node8SumGroup0Data_sector1_chunk2].flatten

def node8SumGroup0Data_sector2 : RawPoly ℕ := [].flatten

def node8SumGroup0Data : SectorVector := [(-2, node8SumGroup0Data_sector0), (0, node8SumGroup0Data_sector1), (2, node8SumGroup0Data_sector2)]

def node8SumGroup0Outputs : List SectorVector := [node8Piece0Output, node8Piece1Output, node8Piece2Output, node8Piece3Output, node8Piece4Output, node8Piece5Output, node8Piece6Output, node8Piece7Output, node8Piece8Output, node8Piece9Output, node8Piece10Output, node8Piece11Output, node8Piece12Output, node8Piece13Output]

theorem node8SumGroup0_check : zipMany 100000 [node8Piece0Pad, node8Piece1Pad, node8Piece2Pad, node8Piece3Pad, node8Piece4Pad, node8Piece5Pad, node8Piece6Pad, node8Piece7Pad, node8Piece8Pad, node8Piece9Pad, node8Piece10Pad, node8Piece11Pad, node8Piece12Pad, node8Piece13Pad] = node8SumGroup0Data := by decide +kernel

theorem node8SumGroup0_value : evaluate node8SumGroup0Data = (node8SumGroup0Outputs.map evaluate).sum := by
  rw [← node8SumGroup0_check, evaluate_zipMany]
  simp only [node8SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node8Piece0Pad_value, node8Piece1Pad_value, node8Piece2Pad_value, node8Piece3Pad_value, node8Piece4Pad_value, node8Piece5Pad_value, node8Piece6Pad_value, node8Piece7Pad_value, node8Piece8Pad_value, node8Piece9Pad_value, node8Piece10Pad_value, node8Piece11Pad_value, node8Piece12Pad_value, node8Piece13Pad_value]

def node8SumData_sector0 : RawPoly ℕ := [].flatten

def node8SumData_sector1_chunk0 : RawPoly ℕ := [(512/135135, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (512/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1664/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (9088/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (64/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-256/63, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (64/63, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (64/7, [1, 1, 1, 1, 1, 1, 1, 7]), (40/3, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 2, 6]), (-2432/45, [1, 1, 1, 1, 1, 1, 3, 5]), (-100/3, [1, 1, 1, 1, 1, 1, 4, 4]), (592/5, [1, 1, 1, 1, 1, 2, 2, 5]), (-688/3, [1, 1, 1, 1, 1, 2, 3, 4]), (-2368/27, [1, 1, 1, 1, 1, 3, 3, 3]), (-208/3, [1, 1, 1, 1, 1, 9]), (1600/9, [1, 1, 1, 1, 2, 2, 3, 3]), (-1280/7, [1, 1, 1, 1, 3, 7]), (-240, [1, 1, 1, 1, 4, 6]), (-64/5, [1, 1, 1, 1, 5, 5]), (80, [1, 1, 1, 2, 2, 2, 2, 3]), (960/7, [1, 1, 1, 2, 2, 7]), (800/3, [1, 1, 1, 2, 3, 6]), (-112, [1, 1, 1, 2, 4, 5])]

def node8SumData_sector1_chunk1 : RawPoly ℕ := [(512/9, [1, 1, 1, 3, 3, 5]), (-920/3, [1, 1, 1, 3, 4, 4]), (-960/11, [1, 1, 1, 11]), (-44, [1, 1, 2, 2, 2, 2, 2, 2]), (-80, [1, 1, 2, 2, 2, 6]), (608, [1, 1, 2, 2, 3, 5]), (-330, [1, 1, 2, 2, 4, 4]), (1120/3, [1, 1, 2, 3, 3, 4]), (96, [1, 1, 2, 10]), (640/9, [1, 1, 3, 3, 3, 3]), (160, [1, 1, 3, 9]), (-180, [1, 1, 4, 8]), (384/7, [1, 1, 5, 7]), (-200, [1, 2, 2, 2, 2, 5]), (-280, [1, 2, 2, 2, 3, 4]), (7840/27, [1, 2, 2, 3, 3, 3]), (-440/3, [1, 2, 2, 9]), (360, [1, 2, 3, 8]), (-240, [1, 2, 4, 7]), (64, [1, 2, 5, 6]), (1920/7, [1, 3, 3, 7]), (80, [1, 3, 4, 6]), (896/5, [1, 3, 5, 5]), (-120, [1, 4, 4, 5])]

def node8SumData_sector1_chunk2 : RawPoly ℕ := [(480/13, [1, 13]), (-88, [2, 2, 2, 2, 2, 4]), (-160/3, [2, 2, 2, 2, 3, 3]), (-180, [2, 2, 2, 8]), (-480/7, [2, 2, 3, 7]), (-280, [2, 2, 4, 6]), (-384/5, [2, 2, 5, 5]), (160, [2, 3, 3, 6]), (-16, [2, 3, 4, 5]), (-80, [2, 4, 4, 4]), (-80, [2, 12]), (2432/27, [3, 3, 3, 5]), (80/3, [3, 3, 4, 4]), (960/11, [3, 11]), (-48, [4, 10]), (32/3, [5, 9])]

def node8SumData_sector1 : RawPoly ℕ := [node8SumData_sector1_chunk0, node8SumData_sector1_chunk1, node8SumData_sector1_chunk2].flatten

def node8SumData_sector2 : RawPoly ℕ := [].flatten

def node8SumData : SectorVector := [(-2, node8SumData_sector0), (0, node8SumData_sector1), (2, node8SumData_sector2)]

def node8OutputGroups : List (List SectorVector) := [node8SumGroup0Outputs]

theorem node8SumData_check : zipMany 100000 [node8SumGroup0Data] = node8SumData := by decide +kernel

theorem node8SumData_value : evaluate node8SumData =
    ((node8OutputGroups.flatten).map evaluate).sum := by
  rw [← node8SumData_check, evaluate_zipMany]
  simp only [node8OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node8SumGroup0_value]

theorem node8Outputs_identity : node8Pieces.map Prod.snd = node8OutputGroups.flatten := rfl

theorem node8Pieces_sum : evaluate (node8Pieces.flatMap Prod.snd) = evaluate node8SumData := by
  rw [evaluate_piece_outputs, node8Outputs_identity, ← node8SumData_value]
end VOA.Classification.COne.OrbC2h
