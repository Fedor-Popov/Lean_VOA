import VOA.Classification.COne.OrbC2hStatePieces18
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node18Piece0Pad : SectorVector := [(-1, node18Piece0Output_sector0), (1, [])]

theorem node18Piece0Pad_value : evaluate node18Piece0Pad = evaluate node18Piece0Output := by
  simp only [node18Piece0Pad, node18Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece1Pad : SectorVector := [(-1, node18Piece1Output_sector0), (1, [])]

theorem node18Piece1Pad_value : evaluate node18Piece1Pad = evaluate node18Piece1Output := by
  simp only [node18Piece1Pad, node18Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece2Pad : SectorVector := [(-1, node18Piece2Output_sector0), (1, [])]

theorem node18Piece2Pad_value : evaluate node18Piece2Pad = evaluate node18Piece2Output := by
  simp only [node18Piece2Pad, node18Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece3Pad : SectorVector := [(-1, node18Piece3Output_sector0), (1, [])]

theorem node18Piece3Pad_value : evaluate node18Piece3Pad = evaluate node18Piece3Output := by
  simp only [node18Piece3Pad, node18Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece4Pad : SectorVector := [(-1, node18Piece4Output_sector0), (1, [])]

theorem node18Piece4Pad_value : evaluate node18Piece4Pad = evaluate node18Piece4Output := by
  simp only [node18Piece4Pad, node18Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece5Pad : SectorVector := [(-1, node18Piece5Output_sector0), (1, [])]

theorem node18Piece5Pad_value : evaluate node18Piece5Pad = evaluate node18Piece5Output := by
  simp only [node18Piece5Pad, node18Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece6Pad : SectorVector := [(-1, node18Piece6Output_sector0), (1, [])]

theorem node18Piece6Pad_value : evaluate node18Piece6Pad = evaluate node18Piece6Output := by
  simp only [node18Piece6Pad, node18Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece7Pad : SectorVector := [(-1, []), (1, node18Piece7Output_sector0)]

theorem node18Piece7Pad_value : evaluate node18Piece7Pad = evaluate node18Piece7Output := by
  simp only [node18Piece7Pad, node18Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece8Pad : SectorVector := [(-1, []), (1, node18Piece8Output_sector0)]

theorem node18Piece8Pad_value : evaluate node18Piece8Pad = evaluate node18Piece8Output := by
  simp only [node18Piece8Pad, node18Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece9Pad : SectorVector := [(-1, []), (1, node18Piece9Output_sector0)]

theorem node18Piece9Pad_value : evaluate node18Piece9Pad = evaluate node18Piece9Output := by
  simp only [node18Piece9Pad, node18Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece10Pad : SectorVector := [(-1, []), (1, node18Piece10Output_sector0)]

theorem node18Piece10Pad_value : evaluate node18Piece10Pad = evaluate node18Piece10Output := by
  simp only [node18Piece10Pad, node18Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece11Pad : SectorVector := [(-1, []), (1, node18Piece11Output_sector0)]

theorem node18Piece11Pad_value : evaluate node18Piece11Pad = evaluate node18Piece11Output := by
  simp only [node18Piece11Pad, node18Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece12Pad : SectorVector := [(-1, []), (1, node18Piece12Output_sector0)]

theorem node18Piece12Pad_value : evaluate node18Piece12Pad = evaluate node18Piece12Output := by
  simp only [node18Piece12Pad, node18Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18Piece13Pad : SectorVector := [(-1, []), (1, node18Piece13Output_sector0)]

theorem node18Piece13Pad_value : evaluate node18Piece13Pad = evaluate node18Piece13Output := by
  simp only [node18Piece13Pad, node18Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node18SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (164, [0, 1, 1, 1, 1, 1, 1, 3]), (-123, [0, 1, 1, 1, 1, 1, 2, 2]), (-84, [0, 1, 1, 1, 1, 5]), (-1740, [0, 1, 1, 1, 2, 4]), (1180, [0, 1, 1, 1, 3, 3]), (930, [0, 1, 1, 2, 2, 3]), (-3780, [0, 1, 1, 7]), (2325/4, [0, 1, 2, 2, 2, 2]), (-1590, [0, 1, 2, 6]), (924, [0, 1, 3, 5]), (-1170, [0, 1, 4, 4]), (342, [0, 2, 2, 5]), (-1740, [0, 2, 3, 4]), (-240, [0, 3, 3, 3]), (-8700, [0, 9]), (-76, [1, 1, 1, 1, 1, 1, 1, 2]), (-570, [1, 1, 1, 1, 1, 4]), (1660, [1, 1, 1, 1, 2, 3]), (1150, [1, 1, 1, 2, 2, 2]), (-2600, [1, 1, 1, 6]), (-936, [1, 1, 2, 5]), (-1380, [1, 1, 3, 4]), (-1935, [1, 2, 2, 4])]

def node18SumGroup0Data_sector0_chunk1 : RawPoly ℕ := [(-1000, [1, 2, 3, 3]), (-24120, [1, 8]), (430, [2, 2, 2, 3]), (-6840, [2, 7]), (-1160, [3, 6]), (900, [4, 5])]

def node18SumGroup0Data_sector0 : RawPoly ℕ := [node18SumGroup0Data_sector0_chunk0, node18SumGroup0Data_sector0_chunk1].flatten

def node18SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (-164, [0, 1, 1, 1, 1, 1, 1, 3]), (123, [0, 1, 1, 1, 1, 1, 2, 2]), (84, [0, 1, 1, 1, 1, 5]), (1740, [0, 1, 1, 1, 2, 4]), (-1180, [0, 1, 1, 1, 3, 3]), (-930, [0, 1, 1, 2, 2, 3]), (3780, [0, 1, 1, 7]), (-2325/4, [0, 1, 2, 2, 2, 2]), (1590, [0, 1, 2, 6]), (-924, [0, 1, 3, 5]), (1170, [0, 1, 4, 4]), (-342, [0, 2, 2, 5]), (1740, [0, 2, 3, 4]), (240, [0, 3, 3, 3]), (8700, [0, 9]), (-76, [1, 1, 1, 1, 1, 1, 1, 2]), (-570, [1, 1, 1, 1, 1, 4]), (1660, [1, 1, 1, 1, 2, 3]), (1150, [1, 1, 1, 2, 2, 2]), (-2600, [1, 1, 1, 6]), (-936, [1, 1, 2, 5]), (-1380, [1, 1, 3, 4]), (-1935, [1, 2, 2, 4])]

def node18SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-1000, [1, 2, 3, 3]), (-24120, [1, 8]), (430, [2, 2, 2, 3]), (-6840, [2, 7]), (-1160, [3, 6]), (900, [4, 5])]

def node18SumGroup0Data_sector1 : RawPoly ℕ := [node18SumGroup0Data_sector1_chunk0, node18SumGroup0Data_sector1_chunk1].flatten

def node18SumGroup0Data : SectorVector := [(-1, node18SumGroup0Data_sector0), (1, node18SumGroup0Data_sector1)]

def node18SumGroup0Outputs : List SectorVector := [node18Piece0Output, node18Piece1Output, node18Piece2Output, node18Piece3Output, node18Piece4Output, node18Piece5Output, node18Piece6Output, node18Piece7Output, node18Piece8Output, node18Piece9Output, node18Piece10Output, node18Piece11Output, node18Piece12Output, node18Piece13Output]

theorem node18SumGroup0_check : zipMany 100000 [node18Piece0Pad, node18Piece1Pad, node18Piece2Pad, node18Piece3Pad, node18Piece4Pad, node18Piece5Pad, node18Piece6Pad, node18Piece7Pad, node18Piece8Pad, node18Piece9Pad, node18Piece10Pad, node18Piece11Pad, node18Piece12Pad, node18Piece13Pad] = node18SumGroup0Data := by decide +kernel

theorem node18SumGroup0_value : evaluate node18SumGroup0Data = (node18SumGroup0Outputs.map evaluate).sum := by
  rw [← node18SumGroup0_check, evaluate_zipMany]
  simp only [node18SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node18Piece0Pad_value, node18Piece1Pad_value, node18Piece2Pad_value, node18Piece3Pad_value, node18Piece4Pad_value, node18Piece5Pad_value, node18Piece6Pad_value, node18Piece7Pad_value, node18Piece8Pad_value, node18Piece9Pad_value, node18Piece10Pad_value, node18Piece11Pad_value, node18Piece12Pad_value, node18Piece13Pad_value]

def node18SumData_sector0_chunk0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (164, [0, 1, 1, 1, 1, 1, 1, 3]), (-123, [0, 1, 1, 1, 1, 1, 2, 2]), (-84, [0, 1, 1, 1, 1, 5]), (-1740, [0, 1, 1, 1, 2, 4]), (1180, [0, 1, 1, 1, 3, 3]), (930, [0, 1, 1, 2, 2, 3]), (-3780, [0, 1, 1, 7]), (2325/4, [0, 1, 2, 2, 2, 2]), (-1590, [0, 1, 2, 6]), (924, [0, 1, 3, 5]), (-1170, [0, 1, 4, 4]), (342, [0, 2, 2, 5]), (-1740, [0, 2, 3, 4]), (-240, [0, 3, 3, 3]), (-8700, [0, 9]), (-76, [1, 1, 1, 1, 1, 1, 1, 2]), (-570, [1, 1, 1, 1, 1, 4]), (1660, [1, 1, 1, 1, 2, 3]), (1150, [1, 1, 1, 2, 2, 2]), (-2600, [1, 1, 1, 6]), (-936, [1, 1, 2, 5]), (-1380, [1, 1, 3, 4]), (-1935, [1, 2, 2, 4])]

def node18SumData_sector0_chunk1 : RawPoly ℕ := [(-1000, [1, 2, 3, 3]), (-24120, [1, 8]), (430, [2, 2, 2, 3]), (-6840, [2, 7]), (-1160, [3, 6]), (900, [4, 5])]

def node18SumData_sector0 : RawPoly ℕ := [node18SumData_sector0_chunk0, node18SumData_sector0_chunk1].flatten

def node18SumData_sector1_chunk0 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (-164, [0, 1, 1, 1, 1, 1, 1, 3]), (123, [0, 1, 1, 1, 1, 1, 2, 2]), (84, [0, 1, 1, 1, 1, 5]), (1740, [0, 1, 1, 1, 2, 4]), (-1180, [0, 1, 1, 1, 3, 3]), (-930, [0, 1, 1, 2, 2, 3]), (3780, [0, 1, 1, 7]), (-2325/4, [0, 1, 2, 2, 2, 2]), (1590, [0, 1, 2, 6]), (-924, [0, 1, 3, 5]), (1170, [0, 1, 4, 4]), (-342, [0, 2, 2, 5]), (1740, [0, 2, 3, 4]), (240, [0, 3, 3, 3]), (8700, [0, 9]), (-76, [1, 1, 1, 1, 1, 1, 1, 2]), (-570, [1, 1, 1, 1, 1, 4]), (1660, [1, 1, 1, 1, 2, 3]), (1150, [1, 1, 1, 2, 2, 2]), (-2600, [1, 1, 1, 6]), (-936, [1, 1, 2, 5]), (-1380, [1, 1, 3, 4]), (-1935, [1, 2, 2, 4])]

def node18SumData_sector1_chunk1 : RawPoly ℕ := [(-1000, [1, 2, 3, 3]), (-24120, [1, 8]), (430, [2, 2, 2, 3]), (-6840, [2, 7]), (-1160, [3, 6]), (900, [4, 5])]

def node18SumData_sector1 : RawPoly ℕ := [node18SumData_sector1_chunk0, node18SumData_sector1_chunk1].flatten

def node18SumData : SectorVector := [(-1, node18SumData_sector0), (1, node18SumData_sector1)]

def node18OutputGroups : List (List SectorVector) := [node18SumGroup0Outputs]

theorem node18SumData_check : zipMany 100000 [node18SumGroup0Data] = node18SumData := by decide +kernel

theorem node18SumData_value : evaluate node18SumData =
    ((node18OutputGroups.flatten).map evaluate).sum := by
  rw [← node18SumData_check, evaluate_zipMany]
  simp only [node18OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node18SumGroup0_value]

theorem node18Outputs_identity : node18Pieces.map Prod.snd = node18OutputGroups.flatten := rfl

theorem node18Pieces_sum : evaluate (node18Pieces.flatMap Prod.snd) = evaluate node18SumData := by
  rw [evaluate_piece_outputs, node18Outputs_identity, ← node18SumData_value]
end VOA.Classification.COne.OrbC2h
