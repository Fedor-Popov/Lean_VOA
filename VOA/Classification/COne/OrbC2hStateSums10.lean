import VOA.Classification.COne.OrbC2hStatePieces10
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node10Piece0Pad : SectorVector := [(-1, node10Piece0Output_sector0), (1, [])]

theorem node10Piece0Pad_value : evaluate node10Piece0Pad = evaluate node10Piece0Output := by
  simp only [node10Piece0Pad, node10Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece1Pad : SectorVector := [(-1, node10Piece1Output_sector0), (1, [])]

theorem node10Piece1Pad_value : evaluate node10Piece1Pad = evaluate node10Piece1Output := by
  simp only [node10Piece1Pad, node10Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece2Pad : SectorVector := [(-1, node10Piece2Output_sector0), (1, [])]

theorem node10Piece2Pad_value : evaluate node10Piece2Pad = evaluate node10Piece2Output := by
  simp only [node10Piece2Pad, node10Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece3Pad : SectorVector := [(-1, node10Piece3Output_sector0), (1, [])]

theorem node10Piece3Pad_value : evaluate node10Piece3Pad = evaluate node10Piece3Output := by
  simp only [node10Piece3Pad, node10Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece4Pad : SectorVector := [(-1, node10Piece4Output_sector0), (1, [])]

theorem node10Piece4Pad_value : evaluate node10Piece4Pad = evaluate node10Piece4Output := by
  simp only [node10Piece4Pad, node10Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece5Pad : SectorVector := [(-1, node10Piece5Output_sector0), (1, [])]

theorem node10Piece5Pad_value : evaluate node10Piece5Pad = evaluate node10Piece5Output := by
  simp only [node10Piece5Pad, node10Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece6Pad : SectorVector := [(-1, node10Piece6Output_sector0), (1, [])]

theorem node10Piece6Pad_value : evaluate node10Piece6Pad = evaluate node10Piece6Output := by
  simp only [node10Piece6Pad, node10Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece7Pad : SectorVector := [(-1, []), (1, node10Piece7Output_sector0)]

theorem node10Piece7Pad_value : evaluate node10Piece7Pad = evaluate node10Piece7Output := by
  simp only [node10Piece7Pad, node10Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece8Pad : SectorVector := [(-1, []), (1, node10Piece8Output_sector0)]

theorem node10Piece8Pad_value : evaluate node10Piece8Pad = evaluate node10Piece8Output := by
  simp only [node10Piece8Pad, node10Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece9Pad : SectorVector := [(-1, []), (1, node10Piece9Output_sector0)]

theorem node10Piece9Pad_value : evaluate node10Piece9Pad = evaluate node10Piece9Output := by
  simp only [node10Piece9Pad, node10Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece10Pad : SectorVector := [(-1, []), (1, node10Piece10Output_sector0)]

theorem node10Piece10Pad_value : evaluate node10Piece10Pad = evaluate node10Piece10Output := by
  simp only [node10Piece10Pad, node10Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece11Pad : SectorVector := [(-1, []), (1, node10Piece11Output_sector0)]

theorem node10Piece11Pad_value : evaluate node10Piece11Pad = evaluate node10Piece11Output := by
  simp only [node10Piece11Pad, node10Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece12Pad : SectorVector := [(-1, []), (1, node10Piece12Output_sector0)]

theorem node10Piece12Pad_value : evaluate node10Piece12Pad = evaluate node10Piece12Output := by
  simp only [node10Piece12Pad, node10Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10Piece13Pad : SectorVector := [(-1, []), (1, node10Piece13Output_sector0)]

theorem node10Piece13Pad_value : evaluate node10Piece13Pad = evaluate node10Piece13Output := by
  simp only [node10Piece13Pad, node10Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node10SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (20, [0, 1, 1, 1, 1, 1, 2, 3]), (-190, [0, 1, 1, 1, 1, 2, 2, 2]), (-160, [0, 1, 1, 1, 1, 6]), (-1176, [0, 1, 1, 1, 2, 5]), (780, [0, 1, 1, 1, 3, 4]), (45, [0, 1, 1, 2, 2, 4]), (1240, [0, 1, 1, 2, 3, 3]), (-4500, [0, 1, 1, 8]), (1130, [0, 1, 2, 2, 2, 3]), (-2160, [0, 1, 2, 7]), (80, [0, 1, 3, 6]), (-360, [0, 1, 4, 5]), (30, [0, 2, 2, 2, 2, 2]), (-60, [0, 2, 2, 6]), (-240, [0, 2, 3, 5]), (-720, [0, 2, 4, 4]), (-720, [0, 3, 3, 4]), (-9720, [0, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-16, [1, 1, 1, 1, 1, 1, 2, 2]), (-528, [1, 1, 1, 1, 1, 5]), (2640, [1, 1, 1, 1, 2, 4])]

def node10SumGroup0Data_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3]), (2320, [1, 1, 1, 2, 2, 3]), (-3360, [1, 1, 1, 7]), (-480, [1, 1, 2, 2, 2, 2]), (-1200, [1, 1, 2, 6]), (-4416, [1, 1, 3, 5]), (3060, [1, 1, 4, 4]), (-3816, [1, 2, 2, 5]), (2640, [1, 2, 3, 4]), (-960, [1, 3, 3, 3]), (-27600, [1, 9]), (-600, [2, 2, 2, 4]), (2480, [2, 2, 3, 3]), (-8280, [2, 8]), (-1920, [3, 7]), (1200, [4, 6]), (-288, [5, 5])]

def node10SumGroup0Data_sector0 : RawPoly ℕ := [node10SumGroup0Data_sector0_chunk0, node10SumGroup0Data_sector0_chunk1].flatten

def node10SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (-150, [0, 1, 1, 1, 1, 1, 1, 4]), (-20, [0, 1, 1, 1, 1, 1, 2, 3]), (190, [0, 1, 1, 1, 1, 2, 2, 2]), (160, [0, 1, 1, 1, 1, 6]), (1176, [0, 1, 1, 1, 2, 5]), (-780, [0, 1, 1, 1, 3, 4]), (-45, [0, 1, 1, 2, 2, 4]), (-1240, [0, 1, 1, 2, 3, 3]), (4500, [0, 1, 1, 8]), (-1130, [0, 1, 2, 2, 2, 3]), (2160, [0, 1, 2, 7]), (-80, [0, 1, 3, 6]), (360, [0, 1, 4, 5]), (-30, [0, 2, 2, 2, 2, 2]), (60, [0, 2, 2, 6]), (240, [0, 2, 3, 5]), (720, [0, 2, 4, 4]), (720, [0, 3, 3, 4]), (9720, [0, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-16, [1, 1, 1, 1, 1, 1, 2, 2]), (-528, [1, 1, 1, 1, 1, 5]), (2640, [1, 1, 1, 1, 2, 4])]

def node10SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3]), (2320, [1, 1, 1, 2, 2, 3]), (-3360, [1, 1, 1, 7]), (-480, [1, 1, 2, 2, 2, 2]), (-1200, [1, 1, 2, 6]), (-4416, [1, 1, 3, 5]), (3060, [1, 1, 4, 4]), (-3816, [1, 2, 2, 5]), (2640, [1, 2, 3, 4]), (-960, [1, 3, 3, 3]), (-27600, [1, 9]), (-600, [2, 2, 2, 4]), (2480, [2, 2, 3, 3]), (-8280, [2, 8]), (-1920, [3, 7]), (1200, [4, 6]), (-288, [5, 5])]

def node10SumGroup0Data_sector1 : RawPoly ℕ := [node10SumGroup0Data_sector1_chunk0, node10SumGroup0Data_sector1_chunk1].flatten

def node10SumGroup0Data : SectorVector := [(-1, node10SumGroup0Data_sector0), (1, node10SumGroup0Data_sector1)]

def node10SumGroup0Outputs : List SectorVector := [node10Piece0Output, node10Piece1Output, node10Piece2Output, node10Piece3Output, node10Piece4Output, node10Piece5Output, node10Piece6Output, node10Piece7Output, node10Piece8Output, node10Piece9Output, node10Piece10Output, node10Piece11Output, node10Piece12Output, node10Piece13Output]

theorem node10SumGroup0_check : zipMany 100000 [node10Piece0Pad, node10Piece1Pad, node10Piece2Pad, node10Piece3Pad, node10Piece4Pad, node10Piece5Pad, node10Piece6Pad, node10Piece7Pad, node10Piece8Pad, node10Piece9Pad, node10Piece10Pad, node10Piece11Pad, node10Piece12Pad, node10Piece13Pad] = node10SumGroup0Data := by decide +kernel

theorem node10SumGroup0_value : evaluate node10SumGroup0Data = (node10SumGroup0Outputs.map evaluate).sum := by
  rw [← node10SumGroup0_check, evaluate_zipMany]
  simp only [node10SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node10Piece0Pad_value, node10Piece1Pad_value, node10Piece2Pad_value, node10Piece3Pad_value, node10Piece4Pad_value, node10Piece5Pad_value, node10Piece6Pad_value, node10Piece7Pad_value, node10Piece8Pad_value, node10Piece9Pad_value, node10Piece10Pad_value, node10Piece11Pad_value, node10Piece12Pad_value, node10Piece13Pad_value]

def node10SumData_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (150, [0, 1, 1, 1, 1, 1, 1, 4]), (20, [0, 1, 1, 1, 1, 1, 2, 3]), (-190, [0, 1, 1, 1, 1, 2, 2, 2]), (-160, [0, 1, 1, 1, 1, 6]), (-1176, [0, 1, 1, 1, 2, 5]), (780, [0, 1, 1, 1, 3, 4]), (45, [0, 1, 1, 2, 2, 4]), (1240, [0, 1, 1, 2, 3, 3]), (-4500, [0, 1, 1, 8]), (1130, [0, 1, 2, 2, 2, 3]), (-2160, [0, 1, 2, 7]), (80, [0, 1, 3, 6]), (-360, [0, 1, 4, 5]), (30, [0, 2, 2, 2, 2, 2]), (-60, [0, 2, 2, 6]), (-240, [0, 2, 3, 5]), (-720, [0, 2, 4, 4]), (-720, [0, 3, 3, 4]), (-9720, [0, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-16, [1, 1, 1, 1, 1, 1, 2, 2]), (-528, [1, 1, 1, 1, 1, 5]), (2640, [1, 1, 1, 1, 2, 4])]

def node10SumData_sector0_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3]), (2320, [1, 1, 1, 2, 2, 3]), (-3360, [1, 1, 1, 7]), (-480, [1, 1, 2, 2, 2, 2]), (-1200, [1, 1, 2, 6]), (-4416, [1, 1, 3, 5]), (3060, [1, 1, 4, 4]), (-3816, [1, 2, 2, 5]), (2640, [1, 2, 3, 4]), (-960, [1, 3, 3, 3]), (-27600, [1, 9]), (-600, [2, 2, 2, 4]), (2480, [2, 2, 3, 3]), (-8280, [2, 8]), (-1920, [3, 7]), (1200, [4, 6]), (-288, [5, 5])]

def node10SumData_sector0 : RawPoly ℕ := [node10SumData_sector0_chunk0, node10SumData_sector0_chunk1].flatten

def node10SumData_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2]), (-150, [0, 1, 1, 1, 1, 1, 1, 4]), (-20, [0, 1, 1, 1, 1, 1, 2, 3]), (190, [0, 1, 1, 1, 1, 2, 2, 2]), (160, [0, 1, 1, 1, 1, 6]), (1176, [0, 1, 1, 1, 2, 5]), (-780, [0, 1, 1, 1, 3, 4]), (-45, [0, 1, 1, 2, 2, 4]), (-1240, [0, 1, 1, 2, 3, 3]), (4500, [0, 1, 1, 8]), (-1130, [0, 1, 2, 2, 2, 3]), (2160, [0, 1, 2, 7]), (-80, [0, 1, 3, 6]), (360, [0, 1, 4, 5]), (-30, [0, 2, 2, 2, 2, 2]), (60, [0, 2, 2, 6]), (240, [0, 2, 3, 5]), (720, [0, 2, 4, 4]), (720, [0, 3, 3, 4]), (9720, [0, 10]), (-96, [1, 1, 1, 1, 1, 1, 1, 3]), (-16, [1, 1, 1, 1, 1, 1, 2, 2]), (-528, [1, 1, 1, 1, 1, 5]), (2640, [1, 1, 1, 1, 2, 4])]

def node10SumData_sector1_chunk1 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3]), (2320, [1, 1, 1, 2, 2, 3]), (-3360, [1, 1, 1, 7]), (-480, [1, 1, 2, 2, 2, 2]), (-1200, [1, 1, 2, 6]), (-4416, [1, 1, 3, 5]), (3060, [1, 1, 4, 4]), (-3816, [1, 2, 2, 5]), (2640, [1, 2, 3, 4]), (-960, [1, 3, 3, 3]), (-27600, [1, 9]), (-600, [2, 2, 2, 4]), (2480, [2, 2, 3, 3]), (-8280, [2, 8]), (-1920, [3, 7]), (1200, [4, 6]), (-288, [5, 5])]

def node10SumData_sector1 : RawPoly ℕ := [node10SumData_sector1_chunk0, node10SumData_sector1_chunk1].flatten

def node10SumData : SectorVector := [(-1, node10SumData_sector0), (1, node10SumData_sector1)]

def node10OutputGroups : List (List SectorVector) := [node10SumGroup0Outputs]

theorem node10SumData_check : zipMany 100000 [node10SumGroup0Data] = node10SumData := by decide +kernel

theorem node10SumData_value : evaluate node10SumData =
    ((node10OutputGroups.flatten).map evaluate).sum := by
  rw [← node10SumData_check, evaluate_zipMany]
  simp only [node10OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node10SumGroup0_value]

theorem node10Outputs_identity : node10Pieces.map Prod.snd = node10OutputGroups.flatten := rfl

theorem node10Pieces_sum : evaluate (node10Pieces.flatMap Prod.snd) = evaluate node10SumData := by
  rw [evaluate_piece_outputs, node10Outputs_identity, ← node10SumData_value]
end VOA.Classification.COne.OrbC2h
