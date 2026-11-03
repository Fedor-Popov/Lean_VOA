import VOA.Classification.COne.OrbC2hStatePieces16
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node16Piece0Pad : SectorVector := [(-2, node16Piece0Output_sector0), (0, node16Piece0Output_sector1), (2, [])]

theorem node16Piece0Pad_value : evaluate node16Piece0Pad = evaluate node16Piece0Output := by
  simp only [node16Piece0Pad, node16Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece1Pad : SectorVector := [(-2, node16Piece1Output_sector0), (0, node16Piece1Output_sector1), (2, [])]

theorem node16Piece1Pad_value : evaluate node16Piece1Pad = evaluate node16Piece1Output := by
  simp only [node16Piece1Pad, node16Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece2Pad : SectorVector := [(-2, node16Piece2Output_sector0), (0, node16Piece2Output_sector1), (2, [])]

theorem node16Piece2Pad_value : evaluate node16Piece2Pad = evaluate node16Piece2Output := by
  simp only [node16Piece2Pad, node16Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece3Pad : SectorVector := [(-2, node16Piece3Output_sector0), (0, node16Piece3Output_sector1), (2, [])]

theorem node16Piece3Pad_value : evaluate node16Piece3Pad = evaluate node16Piece3Output := by
  simp only [node16Piece3Pad, node16Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece4Pad : SectorVector := [(-2, node16Piece4Output_sector0), (0, node16Piece4Output_sector1), (2, [])]

theorem node16Piece4Pad_value : evaluate node16Piece4Pad = evaluate node16Piece4Output := by
  simp only [node16Piece4Pad, node16Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece5Pad : SectorVector := [(-2, node16Piece5Output_sector0), (0, node16Piece5Output_sector1), (2, [])]

theorem node16Piece5Pad_value : evaluate node16Piece5Pad = evaluate node16Piece5Output := by
  simp only [node16Piece5Pad, node16Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece6Pad : SectorVector := [(-2, node16Piece6Output_sector0), (0, node16Piece6Output_sector1), (2, [])]

theorem node16Piece6Pad_value : evaluate node16Piece6Pad = evaluate node16Piece6Output := by
  simp only [node16Piece6Pad, node16Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece7Pad : SectorVector := [(-2, []), (0, node16Piece7Output_sector0), (2, node16Piece7Output_sector1)]

theorem node16Piece7Pad_value : evaluate node16Piece7Pad = evaluate node16Piece7Output := by
  simp only [node16Piece7Pad, node16Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece8Pad : SectorVector := [(-2, []), (0, node16Piece8Output_sector0), (2, node16Piece8Output_sector1)]

theorem node16Piece8Pad_value : evaluate node16Piece8Pad = evaluate node16Piece8Output := by
  simp only [node16Piece8Pad, node16Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece9Pad : SectorVector := [(-2, []), (0, node16Piece9Output_sector0), (2, node16Piece9Output_sector1)]

theorem node16Piece9Pad_value : evaluate node16Piece9Pad = evaluate node16Piece9Output := by
  simp only [node16Piece9Pad, node16Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece10Pad : SectorVector := [(-2, []), (0, node16Piece10Output_sector0), (2, node16Piece10Output_sector1)]

theorem node16Piece10Pad_value : evaluate node16Piece10Pad = evaluate node16Piece10Output := by
  simp only [node16Piece10Pad, node16Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece11Pad : SectorVector := [(-2, []), (0, node16Piece11Output_sector0), (2, node16Piece11Output_sector1)]

theorem node16Piece11Pad_value : evaluate node16Piece11Pad = evaluate node16Piece11Output := by
  simp only [node16Piece11Pad, node16Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece12Pad : SectorVector := [(-2, []), (0, node16Piece12Output_sector0), (2, node16Piece12Output_sector1)]

theorem node16Piece12Pad_value : evaluate node16Piece12Pad = evaluate node16Piece12Output := by
  simp only [node16Piece12Pad, node16Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16Piece13Pad : SectorVector := [(-2, []), (0, node16Piece13Output_sector0), (2, node16Piece13Output_sector1)]

theorem node16Piece13Pad_value : evaluate node16Piece13Pad = evaluate node16Piece13Output := by
  simp only [node16Piece13Pad, node16Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node16SumGroup0Data_sector0 : RawPoly ℕ := [].flatten

def node16SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(2048/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (2144/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (512/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (96/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 1, 6]), (704/15, [1, 1, 1, 1, 1, 1, 2, 5]), (-1120/9, [1, 1, 1, 1, 1, 1, 3, 4]), (-12, [1, 1, 1, 1, 1, 2, 2, 4]), (-1120/9, [1, 1, 1, 1, 1, 2, 3, 3]), (-78, [1, 1, 1, 1, 1, 8]), (640/3, [1, 1, 1, 1, 2, 2, 2, 3]), (-640/3, [1, 1, 1, 1, 3, 6]), (-224, [1, 1, 1, 1, 4, 5]), (-36, [1, 1, 1, 2, 2, 2, 2, 2]), (160, [1, 1, 1, 2, 2, 6]), (1472/3, [1, 1, 1, 2, 3, 5]), (-350, [1, 1, 1, 2, 4, 4]), (-1600/9, [1, 1, 1, 3, 3, 4]), (-96, [1, 1, 1, 10]), (-32, [1, 1, 2, 2, 2, 5]), (120, [1, 1, 2, 2, 3, 4]), (11840/27, [1, 1, 2, 3, 3, 3]), (320/3, [1, 1, 2, 9]), (180, [1, 1, 3, 8])]

def node16SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-1440/7, [1, 1, 4, 7]), (64, [1, 1, 5, 6]), (-340, [1, 2, 2, 2, 2, 4]), (400/3, [1, 2, 2, 2, 3, 3]), (-165, [1, 2, 2, 8]), (2880/7, [1, 2, 3, 7]), (-280, [1, 2, 4, 6]), (384/5, [1, 2, 5, 5]), (320, [1, 3, 3, 6]), (160, [1, 3, 4, 5]), (-95, [1, 4, 4, 4]), (40, [1, 12]), (-84, [2, 2, 2, 2, 2, 3]), (-1440/7, [2, 2, 2, 7]), (-80, [2, 2, 3, 6]), (-312, [2, 2, 4, 5]), (640/3, [2, 3, 3, 5]), (-110, [2, 3, 4, 4]), (-960/11, [2, 11]), (2240/27, [3, 3, 3, 4]), (96, [3, 10]), (-160/3, [4, 9]), (12, [5, 8])]

def node16SumGroup0Data_sector1 : RawPoly ℕ := [node16SumGroup0Data_sector1_chunk0, node16SumGroup0Data_sector1_chunk1].flatten

def node16SumGroup0Data_sector2 : RawPoly ℕ := [].flatten

def node16SumGroup0Data : SectorVector := [(-2, node16SumGroup0Data_sector0), (0, node16SumGroup0Data_sector1), (2, node16SumGroup0Data_sector2)]

def node16SumGroup0Outputs : List SectorVector := [node16Piece0Output, node16Piece1Output, node16Piece2Output, node16Piece3Output, node16Piece4Output, node16Piece5Output, node16Piece6Output, node16Piece7Output, node16Piece8Output, node16Piece9Output, node16Piece10Output, node16Piece11Output, node16Piece12Output, node16Piece13Output]

theorem node16SumGroup0_check : zipMany 100000 [node16Piece0Pad, node16Piece1Pad, node16Piece2Pad, node16Piece3Pad, node16Piece4Pad, node16Piece5Pad, node16Piece6Pad, node16Piece7Pad, node16Piece8Pad, node16Piece9Pad, node16Piece10Pad, node16Piece11Pad, node16Piece12Pad, node16Piece13Pad] = node16SumGroup0Data := by decide +kernel

theorem node16SumGroup0_value : evaluate node16SumGroup0Data = (node16SumGroup0Outputs.map evaluate).sum := by
  rw [← node16SumGroup0_check, evaluate_zipMany]
  simp only [node16SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node16Piece0Pad_value, node16Piece1Pad_value, node16Piece2Pad_value, node16Piece3Pad_value, node16Piece4Pad_value, node16Piece5Pad_value, node16Piece6Pad_value, node16Piece7Pad_value, node16Piece8Pad_value, node16Piece9Pad_value, node16Piece10Pad_value, node16Piece11Pad_value, node16Piece12Pad_value, node16Piece13Pad_value]

def node16SumData_sector0 : RawPoly ℕ := [].flatten

def node16SumData_sector1_chunk0 : RawPoly ℕ := [(2048/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (2144/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (512/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (96/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (32/3, [1, 1, 1, 1, 1, 1, 1, 6]), (704/15, [1, 1, 1, 1, 1, 1, 2, 5]), (-1120/9, [1, 1, 1, 1, 1, 1, 3, 4]), (-12, [1, 1, 1, 1, 1, 2, 2, 4]), (-1120/9, [1, 1, 1, 1, 1, 2, 3, 3]), (-78, [1, 1, 1, 1, 1, 8]), (640/3, [1, 1, 1, 1, 2, 2, 2, 3]), (-640/3, [1, 1, 1, 1, 3, 6]), (-224, [1, 1, 1, 1, 4, 5]), (-36, [1, 1, 1, 2, 2, 2, 2, 2]), (160, [1, 1, 1, 2, 2, 6]), (1472/3, [1, 1, 1, 2, 3, 5]), (-350, [1, 1, 1, 2, 4, 4]), (-1600/9, [1, 1, 1, 3, 3, 4]), (-96, [1, 1, 1, 10]), (-32, [1, 1, 2, 2, 2, 5]), (120, [1, 1, 2, 2, 3, 4]), (11840/27, [1, 1, 2, 3, 3, 3]), (320/3, [1, 1, 2, 9]), (180, [1, 1, 3, 8])]

def node16SumData_sector1_chunk1 : RawPoly ℕ := [(-1440/7, [1, 1, 4, 7]), (64, [1, 1, 5, 6]), (-340, [1, 2, 2, 2, 2, 4]), (400/3, [1, 2, 2, 2, 3, 3]), (-165, [1, 2, 2, 8]), (2880/7, [1, 2, 3, 7]), (-280, [1, 2, 4, 6]), (384/5, [1, 2, 5, 5]), (320, [1, 3, 3, 6]), (160, [1, 3, 4, 5]), (-95, [1, 4, 4, 4]), (40, [1, 12]), (-84, [2, 2, 2, 2, 2, 3]), (-1440/7, [2, 2, 2, 7]), (-80, [2, 2, 3, 6]), (-312, [2, 2, 4, 5]), (640/3, [2, 3, 3, 5]), (-110, [2, 3, 4, 4]), (-960/11, [2, 11]), (2240/27, [3, 3, 3, 4]), (96, [3, 10]), (-160/3, [4, 9]), (12, [5, 8])]

def node16SumData_sector1 : RawPoly ℕ := [node16SumData_sector1_chunk0, node16SumData_sector1_chunk1].flatten

def node16SumData_sector2 : RawPoly ℕ := [].flatten

def node16SumData : SectorVector := [(-2, node16SumData_sector0), (0, node16SumData_sector1), (2, node16SumData_sector2)]

def node16OutputGroups : List (List SectorVector) := [node16SumGroup0Outputs]

theorem node16SumData_check : zipMany 100000 [node16SumGroup0Data] = node16SumData := by decide +kernel

theorem node16SumData_value : evaluate node16SumData =
    ((node16OutputGroups.flatten).map evaluate).sum := by
  rw [← node16SumData_check, evaluate_zipMany]
  simp only [node16OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node16SumGroup0_value]

theorem node16Outputs_identity : node16Pieces.map Prod.snd = node16OutputGroups.flatten := rfl

theorem node16Pieces_sum : evaluate (node16Pieces.flatMap Prod.snd) = evaluate node16SumData := by
  rw [evaluate_piece_outputs, node16Outputs_identity, ← node16SumData_value]
end VOA.Classification.COne.OrbC2h
