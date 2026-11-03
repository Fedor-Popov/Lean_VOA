import VOA.Classification.COne.OrbC2hStatePieces77
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node77Piece0Pad : SectorVector := [(-1, node77Piece0Output_sector0), (1, [])]

theorem node77Piece0Pad_value : evaluate node77Piece0Pad = evaluate node77Piece0Output := by
  simp only [node77Piece0Pad, node77Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece1Pad : SectorVector := [(-1, node77Piece1Output_sector0), (1, [])]

theorem node77Piece1Pad_value : evaluate node77Piece1Pad = evaluate node77Piece1Output := by
  simp only [node77Piece1Pad, node77Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece2Pad : SectorVector := [(-1, node77Piece2Output_sector0), (1, [])]

theorem node77Piece2Pad_value : evaluate node77Piece2Pad = evaluate node77Piece2Output := by
  simp only [node77Piece2Pad, node77Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece3Pad : SectorVector := [(-1, node77Piece3Output_sector0), (1, [])]

theorem node77Piece3Pad_value : evaluate node77Piece3Pad = evaluate node77Piece3Output := by
  simp only [node77Piece3Pad, node77Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece4Pad : SectorVector := [(-1, node77Piece4Output_sector0), (1, [])]

theorem node77Piece4Pad_value : evaluate node77Piece4Pad = evaluate node77Piece4Output := by
  simp only [node77Piece4Pad, node77Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece5Pad : SectorVector := [(-1, node77Piece5Output_sector0), (1, [])]

theorem node77Piece5Pad_value : evaluate node77Piece5Pad = evaluate node77Piece5Output := by
  simp only [node77Piece5Pad, node77Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece6Pad : SectorVector := [(-1, node77Piece6Output_sector0), (1, [])]

theorem node77Piece6Pad_value : evaluate node77Piece6Pad = evaluate node77Piece6Output := by
  simp only [node77Piece6Pad, node77Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece7Pad : SectorVector := [(-1, []), (1, node77Piece7Output_sector0)]

theorem node77Piece7Pad_value : evaluate node77Piece7Pad = evaluate node77Piece7Output := by
  simp only [node77Piece7Pad, node77Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece8Pad : SectorVector := [(-1, []), (1, node77Piece8Output_sector0)]

theorem node77Piece8Pad_value : evaluate node77Piece8Pad = evaluate node77Piece8Output := by
  simp only [node77Piece8Pad, node77Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece9Pad : SectorVector := [(-1, []), (1, node77Piece9Output_sector0)]

theorem node77Piece9Pad_value : evaluate node77Piece9Pad = evaluate node77Piece9Output := by
  simp only [node77Piece9Pad, node77Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece10Pad : SectorVector := [(-1, []), (1, node77Piece10Output_sector0)]

theorem node77Piece10Pad_value : evaluate node77Piece10Pad = evaluate node77Piece10Output := by
  simp only [node77Piece10Pad, node77Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece11Pad : SectorVector := [(-1, []), (1, node77Piece11Output_sector0)]

theorem node77Piece11Pad_value : evaluate node77Piece11Pad = evaluate node77Piece11Output := by
  simp only [node77Piece11Pad, node77Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece12Pad : SectorVector := [(-1, []), (1, node77Piece12Output_sector0)]

theorem node77Piece12Pad_value : evaluate node77Piece12Pad = evaluate node77Piece12Output := by
  simp only [node77Piece12Pad, node77Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77Piece13Pad : SectorVector := [(-1, []), (1, node77Piece13Output_sector0)]

theorem node77Piece13Pad_value : evaluate node77Piece13Pad = evaluate node77Piece13Output := by
  simp only [node77Piece13Pad, node77Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node77SumGroup0Data_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (126, [0, 1, 1, 1, 1, 1, 1, 7]), (1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (-29, [0, 1, 1, 1, 1, 1, 2, 6]), (266, [0, 1, 1, 1, 1, 1, 3, 5]), (231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (-390, [0, 1, 1, 1, 1, 2, 2, 5]), (-240, [0, 1, 1, 1, 1, 2, 3, 4]), (80, [0, 1, 1, 1, 1, 3, 3, 3]), (-430, [0, 1, 1, 1, 1, 9]), (-150, [0, 1, 1, 1, 2, 2, 2, 4]), (-75, [0, 1, 1, 1, 2, 2, 3, 3]), (-420, [0, 1, 1, 1, 2, 8]), (900, [0, 1, 1, 1, 3, 7]), (-360, [0, 1, 1, 1, 4, 6]), (24, [0, 1, 1, 1, 5, 5]), (100, [0, 1, 1, 2, 2, 2, 2, 3]), (225, [0, 1, 1, 2, 2, 7]), (1150, [0, 1, 1, 2, 3, 6]), (-648, [0, 1, 1, 2, 4, 5]), (1936, [0, 1, 1, 3, 3, 5])]

def node77SumGroup0Data_sector0_chunk1 : RawPoly ℕ := [(435, [0, 1, 1, 3, 4, 4]), (-7020, [0, 1, 1, 11]), (15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (2445/2, [0, 1, 2, 2, 2, 6]), (1527, [0, 1, 2, 2, 3, 5]), (2025/4, [0, 1, 2, 2, 4, 4]), (-4230, [0, 1, 2, 10]), (80, [0, 1, 3, 3, 3, 3]), (-1000, [0, 1, 3, 9]), (270, [0, 1, 4, 8]), (396, [0, 1, 5, 7]), (96, [0, 2, 2, 2, 2, 5]), (-60, [0, 2, 2, 2, 3, 4]), (-210, [0, 2, 2, 3, 3, 3]), (-465, [0, 2, 2, 9]), (-60, [0, 2, 3, 8]), (-720, [0, 2, 4, 7]), (546, [0, 2, 5, 6]), (-360, [0, 3, 3, 7]), (-720, [0, 3, 4, 6]), (636, [0, 3, 5, 5]), (-27, [0, 4, 4, 5]), (-13140, [0, 13]), (-96, [1, 1, 1, 1, 1, 1, 1, 6])]

def node77SumGroup0Data_sector0_chunk2 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (144, [1, 1, 1, 1, 1, 2, 2, 4]), (24, [1, 1, 1, 1, 1, 2, 3, 3]), (-216, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (2040, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (120, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2]), (3020, [1, 1, 1, 2, 2, 6]), (2680, [1, 1, 1, 2, 3, 5]), (2670, [1, 1, 1, 2, 4, 4]), (-1260, [1, 1, 1, 3, 3, 4]), (-6120, [1, 1, 1, 10]), (-720, [1, 1, 2, 2, 2, 5]), (-360, [1, 1, 2, 2, 3, 4]), (-600, [1, 1, 2, 3, 3, 3]), (-4440, [1, 1, 2, 9]), (-720, [1, 1, 3, 8]), (2340, [1, 1, 4, 7]), (-576, [1, 1, 5, 6]), (-690, [1, 2, 2, 2, 2, 4]), (-480, [1, 2, 2, 2, 3, 3])]

def node77SumGroup0Data_sector0_chunk3 : RawPoly ℕ := [(-900, [1, 2, 2, 8]), (-1560, [1, 2, 3, 7]), (3450, [1, 2, 4, 6]), (-1152, [1, 2, 5, 5]), (-1440, [1, 3, 3, 6]), (2748, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-39480, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (-720, [2, 2, 2, 7]), (2300, [2, 2, 3, 6]), (-216, [2, 2, 4, 5]), (3224, [2, 3, 3, 5]), (3030, [2, 3, 4, 4]), (-13320, [2, 11]), (600, [3, 3, 3, 4]), (-4680, [3, 10]), (-420, [4, 9]), (1584, [5, 8])]

def node77SumGroup0Data_sector0 : RawPoly ℕ := [node77SumGroup0Data_sector0_chunk0, node77SumGroup0Data_sector0_chunk1, node77SumGroup0Data_sector0_chunk2, node77SumGroup0Data_sector0_chunk3].flatten

def node77SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (-12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (-126, [0, 1, 1, 1, 1, 1, 1, 7]), (-1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (29, [0, 1, 1, 1, 1, 1, 2, 6]), (-266, [0, 1, 1, 1, 1, 1, 3, 5]), (-231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (390, [0, 1, 1, 1, 1, 2, 2, 5]), (240, [0, 1, 1, 1, 1, 2, 3, 4]), (-80, [0, 1, 1, 1, 1, 3, 3, 3]), (430, [0, 1, 1, 1, 1, 9]), (150, [0, 1, 1, 1, 2, 2, 2, 4]), (75, [0, 1, 1, 1, 2, 2, 3, 3]), (420, [0, 1, 1, 1, 2, 8]), (-900, [0, 1, 1, 1, 3, 7]), (360, [0, 1, 1, 1, 4, 6]), (-24, [0, 1, 1, 1, 5, 5]), (-100, [0, 1, 1, 2, 2, 2, 2, 3]), (-225, [0, 1, 1, 2, 2, 7]), (-1150, [0, 1, 1, 2, 3, 6]), (648, [0, 1, 1, 2, 4, 5]), (-1936, [0, 1, 1, 3, 3, 5])]

def node77SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(-435, [0, 1, 1, 3, 4, 4]), (7020, [0, 1, 1, 11]), (-15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (-2445/2, [0, 1, 2, 2, 2, 6]), (-1527, [0, 1, 2, 2, 3, 5]), (-2025/4, [0, 1, 2, 2, 4, 4]), (4230, [0, 1, 2, 10]), (-80, [0, 1, 3, 3, 3, 3]), (1000, [0, 1, 3, 9]), (-270, [0, 1, 4, 8]), (-396, [0, 1, 5, 7]), (-96, [0, 2, 2, 2, 2, 5]), (60, [0, 2, 2, 2, 3, 4]), (210, [0, 2, 2, 3, 3, 3]), (465, [0, 2, 2, 9]), (60, [0, 2, 3, 8]), (720, [0, 2, 4, 7]), (-546, [0, 2, 5, 6]), (360, [0, 3, 3, 7]), (720, [0, 3, 4, 6]), (-636, [0, 3, 5, 5]), (27, [0, 4, 4, 5]), (13140, [0, 13]), (-96, [1, 1, 1, 1, 1, 1, 1, 6])]

def node77SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (144, [1, 1, 1, 1, 1, 2, 2, 4]), (24, [1, 1, 1, 1, 1, 2, 3, 3]), (-216, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (2040, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (120, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2]), (3020, [1, 1, 1, 2, 2, 6]), (2680, [1, 1, 1, 2, 3, 5]), (2670, [1, 1, 1, 2, 4, 4]), (-1260, [1, 1, 1, 3, 3, 4]), (-6120, [1, 1, 1, 10]), (-720, [1, 1, 2, 2, 2, 5]), (-360, [1, 1, 2, 2, 3, 4]), (-600, [1, 1, 2, 3, 3, 3]), (-4440, [1, 1, 2, 9]), (-720, [1, 1, 3, 8]), (2340, [1, 1, 4, 7]), (-576, [1, 1, 5, 6]), (-690, [1, 2, 2, 2, 2, 4]), (-480, [1, 2, 2, 2, 3, 3])]

def node77SumGroup0Data_sector1_chunk3 : RawPoly ℕ := [(-900, [1, 2, 2, 8]), (-1560, [1, 2, 3, 7]), (3450, [1, 2, 4, 6]), (-1152, [1, 2, 5, 5]), (-1440, [1, 3, 3, 6]), (2748, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-39480, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (-720, [2, 2, 2, 7]), (2300, [2, 2, 3, 6]), (-216, [2, 2, 4, 5]), (3224, [2, 3, 3, 5]), (3030, [2, 3, 4, 4]), (-13320, [2, 11]), (600, [3, 3, 3, 4]), (-4680, [3, 10]), (-420, [4, 9]), (1584, [5, 8])]

def node77SumGroup0Data_sector1 : RawPoly ℕ := [node77SumGroup0Data_sector1_chunk0, node77SumGroup0Data_sector1_chunk1, node77SumGroup0Data_sector1_chunk2, node77SumGroup0Data_sector1_chunk3].flatten

def node77SumGroup0Data : SectorVector := [(-1, node77SumGroup0Data_sector0), (1, node77SumGroup0Data_sector1)]

def node77SumGroup0Outputs : List SectorVector := [node77Piece0Output, node77Piece1Output, node77Piece2Output, node77Piece3Output, node77Piece4Output, node77Piece5Output, node77Piece6Output, node77Piece7Output, node77Piece8Output, node77Piece9Output, node77Piece10Output, node77Piece11Output, node77Piece12Output, node77Piece13Output]

theorem node77SumGroup0_check : zipMany 100000 [node77Piece0Pad, node77Piece1Pad, node77Piece2Pad, node77Piece3Pad, node77Piece4Pad, node77Piece5Pad, node77Piece6Pad, node77Piece7Pad, node77Piece8Pad, node77Piece9Pad, node77Piece10Pad, node77Piece11Pad, node77Piece12Pad, node77Piece13Pad] = node77SumGroup0Data := by decide +kernel

theorem node77SumGroup0_value : evaluate node77SumGroup0Data = (node77SumGroup0Outputs.map evaluate).sum := by
  rw [← node77SumGroup0_check, evaluate_zipMany]
  simp only [node77SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node77Piece0Pad_value, node77Piece1Pad_value, node77Piece2Pad_value, node77Piece3Pad_value, node77Piece4Pad_value, node77Piece5Pad_value, node77Piece6Pad_value, node77Piece7Pad_value, node77Piece8Pad_value, node77Piece9Pad_value, node77Piece10Pad_value, node77Piece11Pad_value, node77Piece12Pad_value, node77Piece13Pad_value]

def node77SumData_sector0_chunk0 : RawPoly ℕ := [(4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (126, [0, 1, 1, 1, 1, 1, 1, 7]), (1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (-29, [0, 1, 1, 1, 1, 1, 2, 6]), (266, [0, 1, 1, 1, 1, 1, 3, 5]), (231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (-390, [0, 1, 1, 1, 1, 2, 2, 5]), (-240, [0, 1, 1, 1, 1, 2, 3, 4]), (80, [0, 1, 1, 1, 1, 3, 3, 3]), (-430, [0, 1, 1, 1, 1, 9]), (-150, [0, 1, 1, 1, 2, 2, 2, 4]), (-75, [0, 1, 1, 1, 2, 2, 3, 3]), (-420, [0, 1, 1, 1, 2, 8]), (900, [0, 1, 1, 1, 3, 7]), (-360, [0, 1, 1, 1, 4, 6]), (24, [0, 1, 1, 1, 5, 5]), (100, [0, 1, 1, 2, 2, 2, 2, 3]), (225, [0, 1, 1, 2, 2, 7]), (1150, [0, 1, 1, 2, 3, 6]), (-648, [0, 1, 1, 2, 4, 5]), (1936, [0, 1, 1, 3, 3, 5])]

def node77SumData_sector0_chunk1 : RawPoly ℕ := [(435, [0, 1, 1, 3, 4, 4]), (-7020, [0, 1, 1, 11]), (15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (2445/2, [0, 1, 2, 2, 2, 6]), (1527, [0, 1, 2, 2, 3, 5]), (2025/4, [0, 1, 2, 2, 4, 4]), (-4230, [0, 1, 2, 10]), (80, [0, 1, 3, 3, 3, 3]), (-1000, [0, 1, 3, 9]), (270, [0, 1, 4, 8]), (396, [0, 1, 5, 7]), (96, [0, 2, 2, 2, 2, 5]), (-60, [0, 2, 2, 2, 3, 4]), (-210, [0, 2, 2, 3, 3, 3]), (-465, [0, 2, 2, 9]), (-60, [0, 2, 3, 8]), (-720, [0, 2, 4, 7]), (546, [0, 2, 5, 6]), (-360, [0, 3, 3, 7]), (-720, [0, 3, 4, 6]), (636, [0, 3, 5, 5]), (-27, [0, 4, 4, 5]), (-13140, [0, 13]), (-96, [1, 1, 1, 1, 1, 1, 1, 6])]

def node77SumData_sector0_chunk2 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (144, [1, 1, 1, 1, 1, 2, 2, 4]), (24, [1, 1, 1, 1, 1, 2, 3, 3]), (-216, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (2040, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (120, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2]), (3020, [1, 1, 1, 2, 2, 6]), (2680, [1, 1, 1, 2, 3, 5]), (2670, [1, 1, 1, 2, 4, 4]), (-1260, [1, 1, 1, 3, 3, 4]), (-6120, [1, 1, 1, 10]), (-720, [1, 1, 2, 2, 2, 5]), (-360, [1, 1, 2, 2, 3, 4]), (-600, [1, 1, 2, 3, 3, 3]), (-4440, [1, 1, 2, 9]), (-720, [1, 1, 3, 8]), (2340, [1, 1, 4, 7]), (-576, [1, 1, 5, 6]), (-690, [1, 2, 2, 2, 2, 4]), (-480, [1, 2, 2, 2, 3, 3])]

def node77SumData_sector0_chunk3 : RawPoly ℕ := [(-900, [1, 2, 2, 8]), (-1560, [1, 2, 3, 7]), (3450, [1, 2, 4, 6]), (-1152, [1, 2, 5, 5]), (-1440, [1, 3, 3, 6]), (2748, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-39480, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (-720, [2, 2, 2, 7]), (2300, [2, 2, 3, 6]), (-216, [2, 2, 4, 5]), (3224, [2, 3, 3, 5]), (3030, [2, 3, 4, 4]), (-13320, [2, 11]), (600, [3, 3, 3, 4]), (-4680, [3, 10]), (-420, [4, 9]), (1584, [5, 8])]

def node77SumData_sector0 : RawPoly ℕ := [node77SumData_sector0_chunk0, node77SumData_sector0_chunk1, node77SumData_sector0_chunk2, node77SumData_sector0_chunk3].flatten

def node77SumData_sector1_chunk0 : RawPoly ℕ := [(-4, [0, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (-12, [0, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (-6, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (-12, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (-126, [0, 1, 1, 1, 1, 1, 1, 7]), (-1, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (29, [0, 1, 1, 1, 1, 1, 2, 6]), (-266, [0, 1, 1, 1, 1, 1, 3, 5]), (-231/2, [0, 1, 1, 1, 1, 1, 4, 4]), (390, [0, 1, 1, 1, 1, 2, 2, 5]), (240, [0, 1, 1, 1, 1, 2, 3, 4]), (-80, [0, 1, 1, 1, 1, 3, 3, 3]), (430, [0, 1, 1, 1, 1, 9]), (150, [0, 1, 1, 1, 2, 2, 2, 4]), (75, [0, 1, 1, 1, 2, 2, 3, 3]), (420, [0, 1, 1, 1, 2, 8]), (-900, [0, 1, 1, 1, 3, 7]), (360, [0, 1, 1, 1, 4, 6]), (-24, [0, 1, 1, 1, 5, 5]), (-100, [0, 1, 1, 2, 2, 2, 2, 3]), (-225, [0, 1, 1, 2, 2, 7]), (-1150, [0, 1, 1, 2, 3, 6]), (648, [0, 1, 1, 2, 4, 5]), (-1936, [0, 1, 1, 3, 3, 5])]

def node77SumData_sector1_chunk1 : RawPoly ℕ := [(-435, [0, 1, 1, 3, 4, 4]), (7020, [0, 1, 1, 11]), (-15/2, [0, 1, 2, 2, 2, 2, 2, 2]), (-2445/2, [0, 1, 2, 2, 2, 6]), (-1527, [0, 1, 2, 2, 3, 5]), (-2025/4, [0, 1, 2, 2, 4, 4]), (4230, [0, 1, 2, 10]), (-80, [0, 1, 3, 3, 3, 3]), (1000, [0, 1, 3, 9]), (-270, [0, 1, 4, 8]), (-396, [0, 1, 5, 7]), (-96, [0, 2, 2, 2, 2, 5]), (60, [0, 2, 2, 2, 3, 4]), (210, [0, 2, 2, 3, 3, 3]), (465, [0, 2, 2, 9]), (60, [0, 2, 3, 8]), (720, [0, 2, 4, 7]), (-546, [0, 2, 5, 6]), (360, [0, 3, 3, 7]), (720, [0, 3, 4, 6]), (-636, [0, 3, 5, 5]), (27, [0, 4, 4, 5]), (13140, [0, 13]), (-96, [1, 1, 1, 1, 1, 1, 1, 6])]

def node77SumData_sector1_chunk2 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 5]), (-192, [1, 1, 1, 1, 1, 1, 3, 4]), (144, [1, 1, 1, 1, 1, 2, 2, 4]), (24, [1, 1, 1, 1, 1, 2, 3, 3]), (-216, [1, 1, 1, 1, 1, 8]), (240, [1, 1, 1, 1, 2, 2, 2, 3]), (2040, [1, 1, 1, 1, 2, 7]), (-960, [1, 1, 1, 1, 3, 6]), (120, [1, 1, 1, 1, 4, 5]), (20, [1, 1, 1, 2, 2, 2, 2, 2]), (3020, [1, 1, 1, 2, 2, 6]), (2680, [1, 1, 1, 2, 3, 5]), (2670, [1, 1, 1, 2, 4, 4]), (-1260, [1, 1, 1, 3, 3, 4]), (-6120, [1, 1, 1, 10]), (-720, [1, 1, 2, 2, 2, 5]), (-360, [1, 1, 2, 2, 3, 4]), (-600, [1, 1, 2, 3, 3, 3]), (-4440, [1, 1, 2, 9]), (-720, [1, 1, 3, 8]), (2340, [1, 1, 4, 7]), (-576, [1, 1, 5, 6]), (-690, [1, 2, 2, 2, 2, 4]), (-480, [1, 2, 2, 2, 3, 3])]

def node77SumData_sector1_chunk3 : RawPoly ℕ := [(-900, [1, 2, 2, 8]), (-1560, [1, 2, 3, 7]), (3450, [1, 2, 4, 6]), (-1152, [1, 2, 5, 5]), (-1440, [1, 3, 3, 6]), (2748, [1, 3, 4, 5]), (2505, [1, 4, 4, 4]), (-39480, [1, 12]), (20, [2, 2, 2, 2, 2, 3]), (-720, [2, 2, 2, 7]), (2300, [2, 2, 3, 6]), (-216, [2, 2, 4, 5]), (3224, [2, 3, 3, 5]), (3030, [2, 3, 4, 4]), (-13320, [2, 11]), (600, [3, 3, 3, 4]), (-4680, [3, 10]), (-420, [4, 9]), (1584, [5, 8])]

def node77SumData_sector1 : RawPoly ℕ := [node77SumData_sector1_chunk0, node77SumData_sector1_chunk1, node77SumData_sector1_chunk2, node77SumData_sector1_chunk3].flatten

def node77SumData : SectorVector := [(-1, node77SumData_sector0), (1, node77SumData_sector1)]

def node77OutputGroups : List (List SectorVector) := [node77SumGroup0Outputs]

theorem node77SumData_check : zipMany 100000 [node77SumGroup0Data] = node77SumData := by decide +kernel

theorem node77SumData_value : evaluate node77SumData =
    ((node77OutputGroups.flatten).map evaluate).sum := by
  rw [← node77SumData_check, evaluate_zipMany]
  simp only [node77OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node77SumGroup0_value]

theorem node77Outputs_identity : node77Pieces.map Prod.snd = node77OutputGroups.flatten := rfl

theorem node77Pieces_sum : evaluate (node77Pieces.flatMap Prod.snd) = evaluate node77SumData := by
  rw [evaluate_piece_outputs, node77Outputs_identity, ← node77SumData_value]
end VOA.Classification.COne.OrbC2h
