import VOA.Classification.COne.OrbC2hStatePieces83
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node83Piece0Pad : SectorVector := [(-1, node83Piece0Output_sector0), (1, [])]

theorem node83Piece0Pad_value : evaluate node83Piece0Pad = evaluate node83Piece0Output := by
  simp only [node83Piece0Pad, node83Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece1Pad : SectorVector := [(-1, node83Piece1Output_sector0), (1, [])]

theorem node83Piece1Pad_value : evaluate node83Piece1Pad = evaluate node83Piece1Output := by
  simp only [node83Piece1Pad, node83Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece2Pad : SectorVector := [(-1, node83Piece2Output_sector0), (1, [])]

theorem node83Piece2Pad_value : evaluate node83Piece2Pad = evaluate node83Piece2Output := by
  simp only [node83Piece2Pad, node83Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece3Pad : SectorVector := [(-1, node83Piece3Output_sector0), (1, [])]

theorem node83Piece3Pad_value : evaluate node83Piece3Pad = evaluate node83Piece3Output := by
  simp only [node83Piece3Pad, node83Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece4Pad : SectorVector := [(-1, node83Piece4Output_sector0), (1, [])]

theorem node83Piece4Pad_value : evaluate node83Piece4Pad = evaluate node83Piece4Output := by
  simp only [node83Piece4Pad, node83Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece5Pad : SectorVector := [(-1, node83Piece5Output_sector0), (1, [])]

theorem node83Piece5Pad_value : evaluate node83Piece5Pad = evaluate node83Piece5Output := by
  simp only [node83Piece5Pad, node83Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece6Pad : SectorVector := [(-1, node83Piece6Output_sector0), (1, [])]

theorem node83Piece6Pad_value : evaluate node83Piece6Pad = evaluate node83Piece6Output := by
  simp only [node83Piece6Pad, node83Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece7Pad : SectorVector := [(-1, []), (1, node83Piece7Output_sector0)]

theorem node83Piece7Pad_value : evaluate node83Piece7Pad = evaluate node83Piece7Output := by
  simp only [node83Piece7Pad, node83Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece8Pad : SectorVector := [(-1, []), (1, node83Piece8Output_sector0)]

theorem node83Piece8Pad_value : evaluate node83Piece8Pad = evaluate node83Piece8Output := by
  simp only [node83Piece8Pad, node83Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece9Pad : SectorVector := [(-1, []), (1, node83Piece9Output_sector0)]

theorem node83Piece9Pad_value : evaluate node83Piece9Pad = evaluate node83Piece9Output := by
  simp only [node83Piece9Pad, node83Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece10Pad : SectorVector := [(-1, []), (1, node83Piece10Output_sector0)]

theorem node83Piece10Pad_value : evaluate node83Piece10Pad = evaluate node83Piece10Output := by
  simp only [node83Piece10Pad, node83Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece11Pad : SectorVector := [(-1, []), (1, node83Piece11Output_sector0)]

theorem node83Piece11Pad_value : evaluate node83Piece11Pad = evaluate node83Piece11Output := by
  simp only [node83Piece11Pad, node83Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece12Pad : SectorVector := [(-1, []), (1, node83Piece12Output_sector0)]

theorem node83Piece12Pad_value : evaluate node83Piece12Pad = evaluate node83Piece12Output := by
  simp only [node83Piece12Pad, node83Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83Piece13Pad : SectorVector := [(-1, []), (1, node83Piece13Output_sector0)]

theorem node83Piece13Pad_value : evaluate node83Piece13Pad = evaluate node83Piece13Output := by
  simp only [node83Piece13Pad, node83Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node83SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (136, [0, 1, 1, 1, 1, 1, 1, 6]), (-24, [0, 1, 1, 1, 1, 1, 2, 5]), (266, [0, 1, 1, 1, 1, 1, 3, 4]), (-390, [0, 1, 1, 1, 1, 2, 2, 4]), (-60, [0, 1, 1, 1, 1, 2, 3, 3]), (-330, [0, 1, 1, 1, 1, 8]), (-110, [0, 1, 1, 1, 2, 2, 2, 3]), (-720, [0, 1, 1, 1, 2, 7]), (1000, [0, 1, 1, 1, 3, 6]), (-336, [0, 1, 1, 1, 4, 5]), (30, [0, 1, 1, 2, 2, 2, 2, 2]), (300, [0, 1, 1, 2, 2, 6]), (1272, [0, 1, 1, 2, 3, 5]), (-720, [0, 1, 1, 2, 4, 4]), (1540, [0, 1, 1, 3, 3, 4]), (-6120, [0, 1, 1, 10]), (1284, [0, 1, 2, 2, 2, 5]), (1095, [0, 1, 2, 2, 3, 4]), (120, [0, 1, 2, 3, 3, 3]), (-3480, [0, 1, 2, 9]), (-600, [0, 1, 3, 8])]

def node83SumGroup0Data_sector0_chunk1 : RawPoly ℕ := [(-180, [0, 1, 4, 7]), (456, [0, 1, 5, 6]), (90, [0, 2, 2, 2, 2, 4]), (-150, [0, 2, 2, 2, 3, 3]), (-315, [0, 2, 2, 8]), (-360, [0, 2, 3, 7]), (-720, [0, 2, 4, 6]), (576, [0, 2, 5, 5]), (-360, [0, 3, 3, 6]), (-84, [0, 3, 4, 5]), (-240, [0, 4, 4, 4]), (-11940, [0, 12]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-112, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (144, [1, 1, 1, 1, 1, 2, 2, 3]), (-336, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (2240, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (120, [1, 1, 1, 1, 4, 4]), (3120, [1, 1, 1, 2, 2, 5]), (3040, [1, 1, 1, 2, 3, 4]), (-800, [1, 1, 1, 3, 3, 3])]

def node83SumGroup0Data_sector0_chunk2 : RawPoly ℕ := [(-5120, [1, 1, 1, 9]), (-600, [1, 1, 2, 2, 2, 4]), (-720, [1, 1, 2, 2, 3, 3]), (-3240, [1, 1, 2, 8]), (-1920, [1, 1, 3, 7]), (2640, [1, 1, 4, 6]), (-576, [1, 1, 5, 5]), (-640, [1, 2, 2, 2, 2, 3]), (-1800, [1, 2, 2, 7]), (-1360, [1, 2, 3, 6]), (2448, [1, 2, 4, 5]), (-2016, [1, 3, 3, 5]), (3900, [1, 3, 4, 4]), (-35280, [1, 11]), (-720, [2, 2, 2, 6]), (1824, [2, 2, 3, 5]), (360, [2, 2, 4, 4]), (4160, [2, 3, 3, 4]), (-11520, [2, 10]), (160, [3, 3, 3, 3]), (-3680, [3, 9]), (180, [4, 8]), (864, [5, 7])]

def node83SumGroup0Data_sector0 : RawPoly ℕ := [node83SumGroup0Data_sector0_chunk0, node83SumGroup0Data_sector0_chunk1, node83SumGroup0Data_sector0_chunk2].flatten

def node83SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (-4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (-136, [0, 1, 1, 1, 1, 1, 1, 6]), (24, [0, 1, 1, 1, 1, 1, 2, 5]), (-266, [0, 1, 1, 1, 1, 1, 3, 4]), (390, [0, 1, 1, 1, 1, 2, 2, 4]), (60, [0, 1, 1, 1, 1, 2, 3, 3]), (330, [0, 1, 1, 1, 1, 8]), (110, [0, 1, 1, 1, 2, 2, 2, 3]), (720, [0, 1, 1, 1, 2, 7]), (-1000, [0, 1, 1, 1, 3, 6]), (336, [0, 1, 1, 1, 4, 5]), (-30, [0, 1, 1, 2, 2, 2, 2, 2]), (-300, [0, 1, 1, 2, 2, 6]), (-1272, [0, 1, 1, 2, 3, 5]), (720, [0, 1, 1, 2, 4, 4]), (-1540, [0, 1, 1, 3, 3, 4]), (6120, [0, 1, 1, 10]), (-1284, [0, 1, 2, 2, 2, 5]), (-1095, [0, 1, 2, 2, 3, 4]), (-120, [0, 1, 2, 3, 3, 3]), (3480, [0, 1, 2, 9]), (600, [0, 1, 3, 8])]

def node83SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(180, [0, 1, 4, 7]), (-456, [0, 1, 5, 6]), (-90, [0, 2, 2, 2, 2, 4]), (150, [0, 2, 2, 2, 3, 3]), (315, [0, 2, 2, 8]), (360, [0, 2, 3, 7]), (720, [0, 2, 4, 6]), (-576, [0, 2, 5, 5]), (360, [0, 3, 3, 6]), (84, [0, 3, 4, 5]), (240, [0, 4, 4, 4]), (11940, [0, 12]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-112, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (144, [1, 1, 1, 1, 1, 2, 2, 3]), (-336, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (2240, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (120, [1, 1, 1, 1, 4, 4]), (3120, [1, 1, 1, 2, 2, 5]), (3040, [1, 1, 1, 2, 3, 4]), (-800, [1, 1, 1, 3, 3, 3])]

def node83SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(-5120, [1, 1, 1, 9]), (-600, [1, 1, 2, 2, 2, 4]), (-720, [1, 1, 2, 2, 3, 3]), (-3240, [1, 1, 2, 8]), (-1920, [1, 1, 3, 7]), (2640, [1, 1, 4, 6]), (-576, [1, 1, 5, 5]), (-640, [1, 2, 2, 2, 2, 3]), (-1800, [1, 2, 2, 7]), (-1360, [1, 2, 3, 6]), (2448, [1, 2, 4, 5]), (-2016, [1, 3, 3, 5]), (3900, [1, 3, 4, 4]), (-35280, [1, 11]), (-720, [2, 2, 2, 6]), (1824, [2, 2, 3, 5]), (360, [2, 2, 4, 4]), (4160, [2, 3, 3, 4]), (-11520, [2, 10]), (160, [3, 3, 3, 3]), (-3680, [3, 9]), (180, [4, 8]), (864, [5, 7])]

def node83SumGroup0Data_sector1 : RawPoly ℕ := [node83SumGroup0Data_sector1_chunk0, node83SumGroup0Data_sector1_chunk1, node83SumGroup0Data_sector1_chunk2].flatten

def node83SumGroup0Data : SectorVector := [(-1, node83SumGroup0Data_sector0), (1, node83SumGroup0Data_sector1)]

def node83SumGroup0Outputs : List SectorVector := [node83Piece0Output, node83Piece1Output, node83Piece2Output, node83Piece3Output, node83Piece4Output, node83Piece5Output, node83Piece6Output, node83Piece7Output, node83Piece8Output, node83Piece9Output, node83Piece10Output, node83Piece11Output, node83Piece12Output, node83Piece13Output]

theorem node83SumGroup0_check : zipMany 100000 [node83Piece0Pad, node83Piece1Pad, node83Piece2Pad, node83Piece3Pad, node83Piece4Pad, node83Piece5Pad, node83Piece6Pad, node83Piece7Pad, node83Piece8Pad, node83Piece9Pad, node83Piece10Pad, node83Piece11Pad, node83Piece12Pad, node83Piece13Pad] = node83SumGroup0Data := by decide +kernel

theorem node83SumGroup0_value : evaluate node83SumGroup0Data = (node83SumGroup0Outputs.map evaluate).sum := by
  rw [← node83SumGroup0_check, evaluate_zipMany]
  simp only [node83SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node83Piece0Pad_value, node83Piece1Pad_value, node83Piece2Pad_value, node83Piece3Pad_value, node83Piece4Pad_value, node83Piece5Pad_value, node83Piece6Pad_value, node83Piece7Pad_value, node83Piece8Pad_value, node83Piece9Pad_value, node83Piece10Pad_value, node83Piece11Pad_value, node83Piece12Pad_value, node83Piece13Pad_value]

def node83SumData_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (136, [0, 1, 1, 1, 1, 1, 1, 6]), (-24, [0, 1, 1, 1, 1, 1, 2, 5]), (266, [0, 1, 1, 1, 1, 1, 3, 4]), (-390, [0, 1, 1, 1, 1, 2, 2, 4]), (-60, [0, 1, 1, 1, 1, 2, 3, 3]), (-330, [0, 1, 1, 1, 1, 8]), (-110, [0, 1, 1, 1, 2, 2, 2, 3]), (-720, [0, 1, 1, 1, 2, 7]), (1000, [0, 1, 1, 1, 3, 6]), (-336, [0, 1, 1, 1, 4, 5]), (30, [0, 1, 1, 2, 2, 2, 2, 2]), (300, [0, 1, 1, 2, 2, 6]), (1272, [0, 1, 1, 2, 3, 5]), (-720, [0, 1, 1, 2, 4, 4]), (1540, [0, 1, 1, 3, 3, 4]), (-6120, [0, 1, 1, 10]), (1284, [0, 1, 2, 2, 2, 5]), (1095, [0, 1, 2, 2, 3, 4]), (120, [0, 1, 2, 3, 3, 3]), (-3480, [0, 1, 2, 9]), (-600, [0, 1, 3, 8])]

def node83SumData_sector0_chunk1 : RawPoly ℕ := [(-180, [0, 1, 4, 7]), (456, [0, 1, 5, 6]), (90, [0, 2, 2, 2, 2, 4]), (-150, [0, 2, 2, 2, 3, 3]), (-315, [0, 2, 2, 8]), (-360, [0, 2, 3, 7]), (-720, [0, 2, 4, 6]), (576, [0, 2, 5, 5]), (-360, [0, 3, 3, 6]), (-84, [0, 3, 4, 5]), (-240, [0, 4, 4, 4]), (-11940, [0, 12]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-112, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (144, [1, 1, 1, 1, 1, 2, 2, 3]), (-336, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (2240, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (120, [1, 1, 1, 1, 4, 4]), (3120, [1, 1, 1, 2, 2, 5]), (3040, [1, 1, 1, 2, 3, 4]), (-800, [1, 1, 1, 3, 3, 3])]

def node83SumData_sector0_chunk2 : RawPoly ℕ := [(-5120, [1, 1, 1, 9]), (-600, [1, 1, 2, 2, 2, 4]), (-720, [1, 1, 2, 2, 3, 3]), (-3240, [1, 1, 2, 8]), (-1920, [1, 1, 3, 7]), (2640, [1, 1, 4, 6]), (-576, [1, 1, 5, 5]), (-640, [1, 2, 2, 2, 2, 3]), (-1800, [1, 2, 2, 7]), (-1360, [1, 2, 3, 6]), (2448, [1, 2, 4, 5]), (-2016, [1, 3, 3, 5]), (3900, [1, 3, 4, 4]), (-35280, [1, 11]), (-720, [2, 2, 2, 6]), (1824, [2, 2, 3, 5]), (360, [2, 2, 4, 4]), (4160, [2, 3, 3, 4]), (-11520, [2, 10]), (160, [3, 3, 3, 3]), (-3680, [3, 9]), (180, [4, 8]), (864, [5, 7])]

def node83SumData_sector0 : RawPoly ℕ := [node83SumData_sector0_chunk0, node83SumData_sector0_chunk1, node83SumData_sector0_chunk2].flatten

def node83SumData_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]), (-4, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]), (-136, [0, 1, 1, 1, 1, 1, 1, 6]), (24, [0, 1, 1, 1, 1, 1, 2, 5]), (-266, [0, 1, 1, 1, 1, 1, 3, 4]), (390, [0, 1, 1, 1, 1, 2, 2, 4]), (60, [0, 1, 1, 1, 1, 2, 3, 3]), (330, [0, 1, 1, 1, 1, 8]), (110, [0, 1, 1, 1, 2, 2, 2, 3]), (720, [0, 1, 1, 1, 2, 7]), (-1000, [0, 1, 1, 1, 3, 6]), (336, [0, 1, 1, 1, 4, 5]), (-30, [0, 1, 1, 2, 2, 2, 2, 2]), (-300, [0, 1, 1, 2, 2, 6]), (-1272, [0, 1, 1, 2, 3, 5]), (720, [0, 1, 1, 2, 4, 4]), (-1540, [0, 1, 1, 3, 3, 4]), (6120, [0, 1, 1, 10]), (-1284, [0, 1, 2, 2, 2, 5]), (-1095, [0, 1, 2, 2, 3, 4]), (-120, [0, 1, 2, 3, 3, 3]), (3480, [0, 1, 2, 9]), (600, [0, 1, 3, 8])]

def node83SumData_sector1_chunk1 : RawPoly ℕ := [(180, [0, 1, 4, 7]), (-456, [0, 1, 5, 6]), (-90, [0, 2, 2, 2, 2, 4]), (150, [0, 2, 2, 2, 3, 3]), (315, [0, 2, 2, 8]), (360, [0, 2, 3, 7]), (720, [0, 2, 4, 6]), (-576, [0, 2, 5, 5]), (360, [0, 3, 3, 6]), (84, [0, 3, 4, 5]), (240, [0, 4, 4, 4]), (11940, [0, 12]), (-96, [1, 1, 1, 1, 1, 1, 1, 5]), (-112, [1, 1, 1, 1, 1, 1, 2, 4]), (-96, [1, 1, 1, 1, 1, 1, 3, 3]), (144, [1, 1, 1, 1, 1, 2, 2, 3]), (-336, [1, 1, 1, 1, 1, 7]), (80, [1, 1, 1, 1, 2, 2, 2, 2]), (2240, [1, 1, 1, 1, 2, 6]), (-960, [1, 1, 1, 1, 3, 5]), (120, [1, 1, 1, 1, 4, 4]), (3120, [1, 1, 1, 2, 2, 5]), (3040, [1, 1, 1, 2, 3, 4]), (-800, [1, 1, 1, 3, 3, 3])]

def node83SumData_sector1_chunk2 : RawPoly ℕ := [(-5120, [1, 1, 1, 9]), (-600, [1, 1, 2, 2, 2, 4]), (-720, [1, 1, 2, 2, 3, 3]), (-3240, [1, 1, 2, 8]), (-1920, [1, 1, 3, 7]), (2640, [1, 1, 4, 6]), (-576, [1, 1, 5, 5]), (-640, [1, 2, 2, 2, 2, 3]), (-1800, [1, 2, 2, 7]), (-1360, [1, 2, 3, 6]), (2448, [1, 2, 4, 5]), (-2016, [1, 3, 3, 5]), (3900, [1, 3, 4, 4]), (-35280, [1, 11]), (-720, [2, 2, 2, 6]), (1824, [2, 2, 3, 5]), (360, [2, 2, 4, 4]), (4160, [2, 3, 3, 4]), (-11520, [2, 10]), (160, [3, 3, 3, 3]), (-3680, [3, 9]), (180, [4, 8]), (864, [5, 7])]

def node83SumData_sector1 : RawPoly ℕ := [node83SumData_sector1_chunk0, node83SumData_sector1_chunk1, node83SumData_sector1_chunk2].flatten

def node83SumData : SectorVector := [(-1, node83SumData_sector0), (1, node83SumData_sector1)]

def node83OutputGroups : List (List SectorVector) := [node83SumGroup0Outputs]

theorem node83SumData_check : zipMany 100000 [node83SumGroup0Data] = node83SumData := by decide +kernel

theorem node83SumData_value : evaluate node83SumData =
    ((node83OutputGroups.flatten).map evaluate).sum := by
  rw [← node83SumData_check, evaluate_zipMany]
  simp only [node83OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node83SumGroup0_value]

theorem node83Outputs_identity : node83Pieces.map Prod.snd = node83OutputGroups.flatten := rfl

theorem node83Pieces_sum : evaluate (node83Pieces.flatMap Prod.snd) = evaluate node83SumData := by
  rw [evaluate_piece_outputs, node83Outputs_identity, ← node83SumData_value]
end VOA.Classification.COne.OrbC2h
