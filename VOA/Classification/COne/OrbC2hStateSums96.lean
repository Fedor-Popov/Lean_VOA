import VOA.Classification.COne.OrbC2hStatePieces96
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node96Piece0Pad : SectorVector := [(-2, []), (0, node96Piece0Output_sector0), (2, [])]

theorem node96Piece0Pad_value : evaluate node96Piece0Pad = evaluate node96Piece0Output := by
  simp only [node96Piece0Pad, node96Piece0Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece1Pad : SectorVector := [(-2, []), (0, node96Piece1Output_sector0), (2, [])]

theorem node96Piece1Pad_value : evaluate node96Piece1Pad = evaluate node96Piece1Output := by
  simp only [node96Piece1Pad, node96Piece1Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece2Pad : SectorVector := [(-2, []), (0, node96Piece2Output_sector0), (2, [])]

theorem node96Piece2Pad_value : evaluate node96Piece2Pad = evaluate node96Piece2Output := by
  simp only [node96Piece2Pad, node96Piece2Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece3Pad : SectorVector := [(-2, []), (0, node96Piece3Output_sector0), (2, [])]

theorem node96Piece3Pad_value : evaluate node96Piece3Pad = evaluate node96Piece3Output := by
  simp only [node96Piece3Pad, node96Piece3Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece4Pad : SectorVector := [(-2, []), (0, node96Piece4Output_sector0), (2, [])]

theorem node96Piece4Pad_value : evaluate node96Piece4Pad = evaluate node96Piece4Output := by
  simp only [node96Piece4Pad, node96Piece4Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece5Pad : SectorVector := [(-2, []), (0, node96Piece5Output_sector0), (2, [])]

theorem node96Piece5Pad_value : evaluate node96Piece5Pad = evaluate node96Piece5Output := by
  simp only [node96Piece5Pad, node96Piece5Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece6Pad : SectorVector := [(-2, []), (0, node96Piece6Output_sector0), (2, [])]

theorem node96Piece6Pad_value : evaluate node96Piece6Pad = evaluate node96Piece6Output := by
  simp only [node96Piece6Pad, node96Piece6Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece7Pad : SectorVector := [(-2, []), (0, node96Piece7Output_sector0), (2, [])]

theorem node96Piece7Pad_value : evaluate node96Piece7Pad = evaluate node96Piece7Output := by
  simp only [node96Piece7Pad, node96Piece7Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece8Pad : SectorVector := [(-2, []), (0, node96Piece8Output_sector0), (2, [])]

theorem node96Piece8Pad_value : evaluate node96Piece8Pad = evaluate node96Piece8Output := by
  simp only [node96Piece8Pad, node96Piece8Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece9Pad : SectorVector := [(-2, []), (0, node96Piece9Output_sector0), (2, [])]

theorem node96Piece9Pad_value : evaluate node96Piece9Pad = evaluate node96Piece9Output := by
  simp only [node96Piece9Pad, node96Piece9Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece10Pad : SectorVector := [(-2, []), (0, node96Piece10Output_sector0), (2, [])]

theorem node96Piece10Pad_value : evaluate node96Piece10Pad = evaluate node96Piece10Output := by
  simp only [node96Piece10Pad, node96Piece10Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece11Pad : SectorVector := [(-2, []), (0, node96Piece11Output_sector0), (2, [])]

theorem node96Piece11Pad_value : evaluate node96Piece11Pad = evaluate node96Piece11Output := by
  simp only [node96Piece11Pad, node96Piece11Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece12Pad : SectorVector := [(-2, []), (0, node96Piece12Output_sector0), (2, [])]

theorem node96Piece12Pad_value : evaluate node96Piece12Pad = evaluate node96Piece12Output := by
  simp only [node96Piece12Pad, node96Piece12Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece13Pad : SectorVector := [(-2, []), (0, node96Piece13Output_sector0), (2, [])]

theorem node96Piece13Pad_value : evaluate node96Piece13Pad = evaluate node96Piece13Output := by
  simp only [node96Piece13Pad, node96Piece13Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece14Pad : SectorVector := [(-2, []), (0, node96Piece14Output_sector0), (2, [])]

theorem node96Piece14Pad_value : evaluate node96Piece14Pad = evaluate node96Piece14Output := by
  simp only [node96Piece14Pad, node96Piece14Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece15Pad : SectorVector := [(-2, []), (0, node96Piece15Output_sector0), (2, [])]

theorem node96Piece15Pad_value : evaluate node96Piece15Pad = evaluate node96Piece15Output := by
  simp only [node96Piece15Pad, node96Piece15Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece16Pad : SectorVector := [(-2, []), (0, node96Piece16Output_sector0), (2, [])]

theorem node96Piece16Pad_value : evaluate node96Piece16Pad = evaluate node96Piece16Output := by
  simp only [node96Piece16Pad, node96Piece16Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece17Pad : SectorVector := [(-2, []), (0, node96Piece17Output_sector0), (2, [])]

theorem node96Piece17Pad_value : evaluate node96Piece17Pad = evaluate node96Piece17Output := by
  simp only [node96Piece17Pad, node96Piece17Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece18Pad : SectorVector := [(-2, []), (0, node96Piece18Output_sector0), (2, [])]

theorem node96Piece18Pad_value : evaluate node96Piece18Pad = evaluate node96Piece18Output := by
  simp only [node96Piece18Pad, node96Piece18Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece19Pad : SectorVector := [(-2, []), (0, node96Piece19Output_sector0), (2, [])]

theorem node96Piece19Pad_value : evaluate node96Piece19Pad = evaluate node96Piece19Output := by
  simp only [node96Piece19Pad, node96Piece19Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece20Pad : SectorVector := [(-2, []), (0, node96Piece20Output_sector0), (2, [])]

theorem node96Piece20Pad_value : evaluate node96Piece20Pad = evaluate node96Piece20Output := by
  simp only [node96Piece20Pad, node96Piece20Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece21Pad : SectorVector := [(-2, []), (0, node96Piece21Output_sector0), (2, [])]

theorem node96Piece21Pad_value : evaluate node96Piece21Pad = evaluate node96Piece21Output := by
  simp only [node96Piece21Pad, node96Piece21Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece22Pad : SectorVector := [(-2, []), (0, node96Piece22Output_sector0), (2, [])]

theorem node96Piece22Pad_value : evaluate node96Piece22Pad = evaluate node96Piece22Output := by
  simp only [node96Piece22Pad, node96Piece22Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece23Pad : SectorVector := [(-2, []), (0, node96Piece23Output_sector0), (2, [])]

theorem node96Piece23Pad_value : evaluate node96Piece23Pad = evaluate node96Piece23Output := by
  simp only [node96Piece23Pad, node96Piece23Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece24Pad : SectorVector := [(-2, []), (0, node96Piece24Output_sector0), (2, [])]

theorem node96Piece24Pad_value : evaluate node96Piece24Pad = evaluate node96Piece24Output := by
  simp only [node96Piece24Pad, node96Piece24Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece25Pad : SectorVector := [(-2, []), (0, node96Piece25Output_sector0), (2, [])]

theorem node96Piece25Pad_value : evaluate node96Piece25Pad = evaluate node96Piece25Output := by
  simp only [node96Piece25Pad, node96Piece25Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece26Pad : SectorVector := [(-2, []), (0, node96Piece26Output_sector0), (2, [])]

theorem node96Piece26Pad_value : evaluate node96Piece26Pad = evaluate node96Piece26Output := by
  simp only [node96Piece26Pad, node96Piece26Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece27Pad : SectorVector := [(-2, []), (0, node96Piece27Output_sector0), (2, [])]

theorem node96Piece27Pad_value : evaluate node96Piece27Pad = evaluate node96Piece27Output := by
  simp only [node96Piece27Pad, node96Piece27Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece28Pad : SectorVector := [(-2, []), (0, node96Piece28Output_sector0), (2, [])]

theorem node96Piece28Pad_value : evaluate node96Piece28Pad = evaluate node96Piece28Output := by
  simp only [node96Piece28Pad, node96Piece28Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece29Pad : SectorVector := [(-2, []), (0, node96Piece29Output_sector0), (2, [])]

theorem node96Piece29Pad_value : evaluate node96Piece29Pad = evaluate node96Piece29Output := by
  simp only [node96Piece29Pad, node96Piece29Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece30Pad : SectorVector := [(-2, []), (0, node96Piece30Output_sector0), (2, [])]

theorem node96Piece30Pad_value : evaluate node96Piece30Pad = evaluate node96Piece30Output := by
  simp only [node96Piece30Pad, node96Piece30Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece31Pad : SectorVector := [(-2, []), (0, node96Piece31Output_sector0), (2, [])]

theorem node96Piece31Pad_value : evaluate node96Piece31Pad = evaluate node96Piece31Output := by
  simp only [node96Piece31Pad, node96Piece31Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece32Pad : SectorVector := [(-2, []), (0, node96Piece32Output_sector0), (2, [])]

theorem node96Piece32Pad_value : evaluate node96Piece32Pad = evaluate node96Piece32Output := by
  simp only [node96Piece32Pad, node96Piece32Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece33Pad : SectorVector := [(-2, []), (0, node96Piece33Output_sector0), (2, [])]

theorem node96Piece33Pad_value : evaluate node96Piece33Pad = evaluate node96Piece33Output := by
  simp only [node96Piece33Pad, node96Piece33Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece34Pad : SectorVector := [(-2, []), (0, node96Piece34Output_sector0), (2, [])]

theorem node96Piece34Pad_value : evaluate node96Piece34Pad = evaluate node96Piece34Output := by
  simp only [node96Piece34Pad, node96Piece34Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece35Pad : SectorVector := [(-2, []), (0, node96Piece35Output_sector0), (2, [])]

theorem node96Piece35Pad_value : evaluate node96Piece35Pad = evaluate node96Piece35Output := by
  simp only [node96Piece35Pad, node96Piece35Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece36Pad : SectorVector := [(-2, []), (0, node96Piece36Output_sector0), (2, [])]

theorem node96Piece36Pad_value : evaluate node96Piece36Pad = evaluate node96Piece36Output := by
  simp only [node96Piece36Pad, node96Piece36Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece37Pad : SectorVector := [(-2, []), (0, node96Piece37Output_sector0), (2, [])]

theorem node96Piece37Pad_value : evaluate node96Piece37Pad = evaluate node96Piece37Output := by
  simp only [node96Piece37Pad, node96Piece37Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece38Pad : SectorVector := [(-2, []), (0, node96Piece38Output_sector0), (2, [])]

theorem node96Piece38Pad_value : evaluate node96Piece38Pad = evaluate node96Piece38Output := by
  simp only [node96Piece38Pad, node96Piece38Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece39Pad : SectorVector := [(-2, []), (0, node96Piece39Output_sector0), (2, [])]

theorem node96Piece39Pad_value : evaluate node96Piece39Pad = evaluate node96Piece39Output := by
  simp only [node96Piece39Pad, node96Piece39Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece40Pad : SectorVector := [(-2, []), (0, node96Piece40Output_sector0), (2, [])]

theorem node96Piece40Pad_value : evaluate node96Piece40Pad = evaluate node96Piece40Output := by
  simp only [node96Piece40Pad, node96Piece40Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece41Pad : SectorVector := [(-2, []), (0, node96Piece41Output_sector0), (2, [])]

theorem node96Piece41Pad_value : evaluate node96Piece41Pad = evaluate node96Piece41Output := by
  simp only [node96Piece41Pad, node96Piece41Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece42Pad : SectorVector := [(-2, []), (0, node96Piece42Output_sector0), (2, [])]

theorem node96Piece42Pad_value : evaluate node96Piece42Pad = evaluate node96Piece42Output := by
  simp only [node96Piece42Pad, node96Piece42Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece43Pad : SectorVector := [(-2, []), (0, node96Piece43Output_sector0), (2, [])]

theorem node96Piece43Pad_value : evaluate node96Piece43Pad = evaluate node96Piece43Output := by
  simp only [node96Piece43Pad, node96Piece43Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece44Pad : SectorVector := [(-2, []), (0, node96Piece44Output_sector0), (2, [])]

theorem node96Piece44Pad_value : evaluate node96Piece44Pad = evaluate node96Piece44Output := by
  simp only [node96Piece44Pad, node96Piece44Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece45Pad : SectorVector := [(-2, []), (0, node96Piece45Output_sector0), (2, [])]

theorem node96Piece45Pad_value : evaluate node96Piece45Pad = evaluate node96Piece45Output := by
  simp only [node96Piece45Pad, node96Piece45Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96Piece46Pad : SectorVector := [(-2, []), (0, node96Piece46Output_sector0), (2, [])]

theorem node96Piece46Pad_value : evaluate node96Piece46Pad = evaluate node96Piece46Output := by
  simp only [node96Piece46Pad, node96Piece46Output, evaluate, evRc_nil, map_zero, add_zero, zero_add]

def node96SumGroup0Data_sector0 : RawPoly ℕ := [].flatten

def node96SumGroup0Data_sector1_chunk0 : RawPoly ℕ := [(8192/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (94208/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (32768/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1159808/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (8192/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (188416/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (985088/2079, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (12416/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (65152/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (2574848/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (74624/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (145408/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (11136/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (43648/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (607232/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (633856/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (808256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8])]

def node96SumGroup0Data_sector1_chunk1 : RawPoly ℕ := [(572416/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (299648/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (58112/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (82688/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (38912/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (121984/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1200256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (58880/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (98560/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (6656/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (201536/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-8704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (12416/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (19904/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (88576/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (27056/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (9216/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (13568/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (147072/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (3968/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (483584/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12])]

def node96SumGroup0Data_sector1_chunk2 : RawPoly ℕ := [(4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-512/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (137216/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (4352, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (477184/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (88504/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (43776/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (384/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (21888/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (127360/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (173072/35, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (169856/105, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (912/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (12480, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (-46336/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-107264/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16064, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (648328/35, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (122240/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (-77312/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (-233480/21, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (-528896/105, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (-55040/21, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (11264/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7])]

def node96SumGroup0Data_sector1_chunk3 : RawPoly ℕ := [(200128/35, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (6912/5, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (-4160, [1, 1, 1, 1, 1, 1, 1, 15]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (75776/15, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (14192/9, [1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (17408, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (-4480/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (15232, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (11520, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (128128/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (10688, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (-92216/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (-45312, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (-8192, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (-6400, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (4928, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (-83840, [1, 1, 1, 1, 1, 1, 2, 14]), (-35840/3, [1, 1, 1, 1, 1, 1, 3, 3, 3, 7]), (-386816/9, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (-39168/5, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (-549824/15, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (88448/3, [1, 1, 1, 1, 1, 1, 3, 13])]

def node96SumGroup0Data_sector1_chunk4 : RawPoly ℕ := [(-4480/3, [1, 1, 1, 1, 1, 1, 4, 4, 4, 4]), (70592/3, [1, 1, 1, 1, 1, 1, 4, 12]), (-220288/5, [1, 1, 1, 1, 1, 1, 5, 11]), (-40960, [1, 1, 1, 1, 1, 1, 6, 10]), (-28800, [1, 1, 1, 1, 1, 1, 7, 9]), (-15804, [1, 1, 1, 1, 1, 1, 8, 8]), (-432, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (2080, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (18560/9, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (17376, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9]), (43848, [1, 1, 1, 1, 1, 2, 2, 2, 3, 8]), (19248, [1, 1, 1, 1, 1, 2, 2, 2, 4, 7]), (132096/5, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (-12608/3, [1, 1, 1, 1, 1, 2, 2, 3, 3, 7]), (-640, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (92352/5, [1, 1, 1, 1, 1, 2, 2, 3, 5, 5]), (-13464/5, [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]), (150624, [1, 1, 1, 1, 1, 2, 2, 13]), (-300800/9, [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]), (-794752/15, [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]), (-37568/3, [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]), (170752/3, [1, 1, 1, 1, 1, 2, 3, 12]), (-91008, [1, 1, 1, 1, 1, 2, 4, 11]), (-116352/5, [1, 1, 1, 1, 1, 2, 5, 10])]

def node96SumGroup0Data_sector1_chunk5 : RawPoly ℕ := [(-14976, [1, 1, 1, 1, 1, 2, 6, 9]), (-21096, [1, 1, 1, 1, 1, 2, 7, 8]), (-8960/3, [1, 1, 1, 1, 1, 3, 3, 3, 3, 5]), (-35840/3, [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]), (-127808, [1, 1, 1, 1, 1, 3, 3, 11]), (-181248, [1, 1, 1, 1, 1, 3, 4, 10]), (-747136/5, [1, 1, 1, 1, 1, 3, 5, 9]), (-174464, [1, 1, 1, 1, 1, 3, 6, 8]), (-76608, [1, 1, 1, 1, 1, 3, 7, 7]), (-89280, [1, 1, 1, 1, 1, 4, 4, 9]), (-584316/5, [1, 1, 1, 1, 1, 4, 5, 8]), (-106752, [1, 1, 1, 1, 1, 4, 6, 7]), (-77376/5, [1, 1, 1, 1, 1, 5, 5, 7]), (-107328/5, [1, 1, 1, 1, 1, 5, 6, 6]), (27360, [1, 1, 1, 1, 1, 17]), (-432, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (1264/3, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-744, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8]), (40000, [1, 1, 1, 1, 2, 2, 2, 2, 3, 7]), (7920, [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]), (3360, [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]), (162560/3, [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]), (73952, [1, 1, 1, 1, 2, 2, 2, 3, 4, 5]), (1840, [1, 1, 1, 1, 2, 2, 2, 4, 4, 4])]

def node96SumGroup0Data_sector1_chunk6 : RawPoly ℕ := [(-19840, [1, 1, 1, 1, 2, 2, 2, 12]), (18944/3, [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]), (21520/3, [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]), (1920, [1, 1, 1, 1, 2, 2, 3, 11]), (95280, [1, 1, 1, 1, 2, 2, 4, 10]), (150912, [1, 1, 1, 1, 2, 2, 5, 9]), (111480, [1, 1, 1, 1, 2, 2, 6, 8]), (54720, [1, 1, 1, 1, 2, 2, 7, 7]), (-22400/3, [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]), (22400, [1, 1, 1, 1, 2, 3, 3, 10]), (-77440, [1, 1, 1, 1, 2, 3, 4, 9]), (41968, [1, 1, 1, 1, 2, 3, 5, 8]), (-17920, [1, 1, 1, 1, 2, 3, 6, 7]), (-37320, [1, 1, 1, 1, 2, 4, 4, 8]), (-20736, [1, 1, 1, 1, 2, 4, 5, 7]), (-16320, [1, 1, 1, 1, 2, 4, 6, 6]), (30720, [1, 1, 1, 1, 2, 5, 5, 6]), (105600, [1, 1, 1, 1, 2, 16]), (-135680/3, [1, 1, 1, 1, 3, 3, 3, 9]), (-370520/3, [1, 1, 1, 1, 3, 3, 4, 8]), (-143360/3, [1, 1, 1, 1, 3, 3, 5, 7]), (-60160, [1, 1, 1, 1, 3, 3, 6, 6]), (-87040, [1, 1, 1, 1, 3, 4, 4, 7]), (-163328, [1, 1, 1, 1, 3, 4, 5, 6])]

def node96SumGroup0Data_sector1_chunk7 : RawPoly ℕ := [(-4096, [1, 1, 1, 1, 3, 5, 5, 5]), (83840, [1, 1, 1, 1, 3, 15]), (-16000, [1, 1, 1, 1, 4, 4, 4, 6]), (-49728, [1, 1, 1, 1, 4, 4, 5, 5]), (-38400, [1, 1, 1, 1, 4, 14]), (50304, [1, 1, 1, 1, 5, 13]), (-144000, [1, 1, 1, 1, 6, 12]), (-274560, [1, 1, 1, 1, 7, 11]), (-241800, [1, 1, 1, 1, 8, 10]), (-137280, [1, 1, 1, 1, 9, 9]), (-144, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-6480, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (-640, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-11880, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (54368/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (5920, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (81600, [1, 1, 1, 2, 2, 2, 2, 11]), (10240, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (120320, [1, 1, 1, 2, 2, 2, 3, 10]), (47040, [1, 1, 1, 2, 2, 2, 4, 9]), (67584, [1, 1, 1, 2, 2, 2, 5, 8]), (67200, [1, 1, 1, 2, 2, 2, 6, 7]), (490240/3, [1, 1, 1, 2, 2, 3, 3, 9]), (201920, [1, 1, 1, 2, 2, 3, 4, 8])]

def node96SumGroup0Data_sector1_chunk8 : RawPoly ℕ := [(281344, [1, 1, 1, 2, 2, 3, 5, 7]), (120320, [1, 1, 1, 2, 2, 3, 6, 6]), (8640, [1, 1, 1, 2, 2, 4, 4, 7]), (74496, [1, 1, 1, 2, 2, 4, 5, 6]), (21504, [1, 1, 1, 2, 2, 5, 5, 5]), (115200, [1, 1, 1, 2, 2, 15]), (-1280/3, [1, 1, 1, 2, 3, 3, 3, 8]), (87040/3, [1, 1, 1, 2, 3, 3, 4, 7]), (290048/3, [1, 1, 1, 2, 3, 3, 5, 6]), (26880, [1, 1, 1, 2, 3, 4, 4, 6]), (110976, [1, 1, 1, 2, 3, 4, 5, 5]), (-552960, [1, 1, 1, 2, 3, 14]), (-4864, [1, 1, 1, 2, 4, 4, 4, 5]), (149760, [1, 1, 1, 2, 4, 13]), (-3712, [1, 1, 1, 2, 5, 12]), (145920, [1, 1, 1, 2, 6, 11]), (268800, [1, 1, 1, 2, 7, 10]), (250080, [1, 1, 1, 2, 8, 9]), (-10240, [1, 1, 1, 3, 3, 3, 4, 6]), (11776, [1, 1, 1, 3, 3, 3, 5, 5]), (1024, [1, 1, 1, 3, 3, 4, 4, 5]), (-194560/3, [1, 1, 1, 3, 3, 13]), (-517120/3, [1, 1, 1, 3, 4, 12]), (-138240, [1, 1, 1, 3, 5, 11])]

def node96SumGroup0Data_sector1_chunk9 : RawPoly ℕ := [(30720, [1, 1, 1, 3, 6, 10]), (-5120, [1, 1, 1, 3, 7, 9]), (-21280, [1, 1, 1, 3, 8, 8]), (-107520, [1, 1, 1, 4, 4, 11]), (-36864, [1, 1, 1, 4, 5, 10]), (-153600, [1, 1, 1, 4, 6, 9]), (-126240, [1, 1, 1, 4, 7, 8]), (-15360, [1, 1, 1, 5, 5, 9]), (-80160, [1, 1, 1, 5, 6, 8]), (-7680, [1, 1, 1, 5, 7, 7]), (-46080, [1, 1, 1, 6, 6, 7]), (-503040, [1, 1, 1, 19]), (-1296, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-2592, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-1296, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (-1296, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-14256, [1, 1, 2, 2, 2, 2, 2, 10]), (4800, [1, 1, 2, 2, 2, 2, 3, 9]), (-25920, [1, 1, 2, 2, 2, 2, 4, 8]), (-25920, [1, 1, 2, 2, 2, 2, 5, 7]), (-7200, [1, 1, 2, 2, 2, 2, 6, 6]), (30720, [1, 1, 2, 2, 2, 3, 3, 8]), (30720, [1, 1, 2, 2, 2, 3, 4, 7]), (59904, [1, 1, 2, 2, 2, 3, 5, 6])]

def node96SumGroup0Data_sector1_chunk10 : RawPoly ℕ := [(5760, [1, 1, 2, 2, 2, 4, 4, 6]), (57600, [1, 1, 2, 2, 2, 14]), (5760, [1, 1, 2, 2, 3, 3, 4, 6]), (35328, [1, 1, 2, 2, 3, 3, 5, 5]), (17664, [1, 1, 2, 2, 3, 4, 4, 5]), (430080, [1, 1, 2, 2, 3, 13]), (66240, [1, 1, 2, 2, 4, 12]), (175104, [1, 1, 2, 2, 5, 11]), (63360, [1, 1, 2, 2, 6, 10]), (69120, [1, 1, 2, 2, 7, 9]), (34560, [1, 1, 2, 2, 8, 8]), (17664, [1, 1, 2, 3, 3, 3, 4, 5]), (440320/3, [1, 1, 2, 3, 3, 12]), (176640, [1, 1, 2, 3, 4, 11]), (194304, [1, 1, 2, 3, 5, 10]), (192000, [1, 1, 2, 3, 6, 9]), (176640, [1, 1, 2, 3, 7, 8]), (73728, [1, 1, 2, 4, 5, 9]), (46080, [1, 1, 2, 4, 6, 8]), (105984, [1, 1, 2, 5, 5, 8]), (152064, [1, 1, 2, 5, 6, 7]), (23040, [1, 1, 2, 6, 6, 6]), (806400, [1, 1, 2, 18]), (70656, [1, 1, 3, 3, 5, 9])]

def node96SumGroup0Data_sector1_chunk11 : RawPoly ℕ := [(-30720, [1, 1, 3, 3, 6, 8]), (38400, [1, 1, 3, 4, 5, 8]), (-30720, [1, 1, 3, 4, 6, 7]), (70656, [1, 1, 3, 5, 5, 7]), (4608, [1, 1, 3, 5, 6, 6]), (168960, [1, 1, 3, 17]), (-32256, [1, 1, 4, 4, 5, 7]), (-32256, [1, 1, 4, 5, 5, 6]), (-161280, [1, 1, 4, 16]), (82944, [1, 1, 5, 15]), (-46080, [1, 1, 6, 14]), (-18720, [1, 1, 8, 12]), (-2592, [1, 2, 2, 2, 2, 2, 2, 9]), (-2592, [1, 2, 2, 2, 2, 2, 3, 8]), (-2592, [1, 2, 2, 2, 2, 2, 4, 7]), (-2592, [1, 2, 2, 2, 2, 2, 5, 6]), (-25920, [1, 2, 2, 2, 2, 13]), (20480, [1, 2, 2, 2, 3, 12]), (11520, [1, 2, 2, 2, 6, 9]), (35328, [1, 2, 2, 3, 5, 9]), (11520, [1, 2, 2, 3, 6, 8]), (11520, [1, 2, 2, 4, 6, 7]), (11520, [1, 2, 2, 5, 6, 6]), (69120, [1, 2, 2, 17])]

def node96SumGroup0Data_sector1_chunk12 : RawPoly ℕ := [(35328, [1, 2, 3, 3, 5, 8]), (35328, [1, 2, 3, 4, 5, 7]), (35328, [1, 2, 3, 5, 5, 6]), (176640, [1, 2, 3, 16]), (105984, [1, 2, 5, 14]), (46080, [1, 2, 6, 13]), (70656, [1, 3, 5, 13]), (-20480, [1, 3, 6, 12]), (-21504, [1, 4, 5, 12]), (-864, [2, 2, 2, 2, 2, 12]), (3840, [2, 2, 6, 12]), (11776, [2, 3, 5, 12])]

def node96SumGroup0Data_sector1 : RawPoly ℕ := [node96SumGroup0Data_sector1_chunk0, node96SumGroup0Data_sector1_chunk1, node96SumGroup0Data_sector1_chunk2, node96SumGroup0Data_sector1_chunk3, node96SumGroup0Data_sector1_chunk4, node96SumGroup0Data_sector1_chunk5, node96SumGroup0Data_sector1_chunk6, node96SumGroup0Data_sector1_chunk7, node96SumGroup0Data_sector1_chunk8, node96SumGroup0Data_sector1_chunk9, node96SumGroup0Data_sector1_chunk10, node96SumGroup0Data_sector1_chunk11, node96SumGroup0Data_sector1_chunk12].flatten

def node96SumGroup0Data_sector2 : RawPoly ℕ := [].flatten

def node96SumGroup0Data : SectorVector := [(-2, node96SumGroup0Data_sector0), (0, node96SumGroup0Data_sector1), (2, node96SumGroup0Data_sector2)]

def node96SumGroup0Outputs : List SectorVector := [node96Piece0Output, node96Piece1Output, node96Piece2Output, node96Piece3Output, node96Piece4Output, node96Piece5Output, node96Piece6Output, node96Piece7Output, node96Piece8Output, node96Piece9Output, node96Piece10Output, node96Piece11Output, node96Piece12Output, node96Piece13Output, node96Piece14Output, node96Piece15Output]

theorem node96SumGroup0_check : zipMany 100000 [node96Piece0Pad, node96Piece1Pad, node96Piece2Pad, node96Piece3Pad, node96Piece4Pad, node96Piece5Pad, node96Piece6Pad, node96Piece7Pad, node96Piece8Pad, node96Piece9Pad, node96Piece10Pad, node96Piece11Pad, node96Piece12Pad, node96Piece13Pad, node96Piece14Pad, node96Piece15Pad] = node96SumGroup0Data := by decide +kernel

theorem node96SumGroup0_value : evaluate node96SumGroup0Data = (node96SumGroup0Outputs.map evaluate).sum := by
  rw [← node96SumGroup0_check, evaluate_zipMany]
  simp only [node96SumGroup0Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node96Piece0Pad_value, node96Piece1Pad_value, node96Piece2Pad_value, node96Piece3Pad_value, node96Piece4Pad_value, node96Piece5Pad_value, node96Piece6Pad_value, node96Piece7Pad_value, node96Piece8Pad_value, node96Piece9Pad_value, node96Piece10Pad_value, node96Piece11Pad_value, node96Piece12Pad_value, node96Piece13Pad_value, node96Piece14Pad_value, node96Piece15Pad_value]

def node96SumGroup1Data_sector0 : RawPoly ℕ := [].flatten

def node96SumGroup1Data_sector1_chunk0 : RawPoly ℕ := [(-1400, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (-6400/9, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (-384, [1, 1, 1, 1, 1, 1, 6, 10]), (-128, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (480, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (-4200, [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]), (47360/27, [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]), (-6400/3, [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]), (-4200, [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]), (-33600, [1, 1, 1, 1, 1, 2, 4, 11]), (-1152, [1, 1, 1, 1, 1, 2, 5, 10]), (1280/3, [1, 1, 1, 1, 1, 2, 6, 9]), (-6400/3, [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]), (-25600/3, [1, 1, 1, 1, 1, 3, 3, 11]), (-13952, [1, 1, 1, 1, 1, 3, 4, 10]), (720, [1, 1, 1, 1, 1, 3, 6, 8]), (-8400, [1, 1, 1, 1, 1, 4, 4, 9]), (-5760/7, [1, 1, 1, 1, 1, 4, 6, 7]), (256, [1, 1, 1, 1, 1, 5, 6, 6]), (-11520, [1, 1, 1, 1, 1, 17]), (-1360, [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]), (-384, [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]), (1600/3, [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]), (1056, [1, 1, 1, 1, 2, 2, 2, 3, 4, 5])]

def node96SumGroup1Data_sector1_chunk1 : RawPoly ℕ := [(-4200, [1, 1, 1, 1, 2, 2, 2, 4, 4, 4]), (-1920, [1, 1, 1, 1, 2, 2, 2, 12]), (47360/9, [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]), (-14680/3, [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]), (5760, [1, 1, 1, 1, 2, 2, 3, 11]), (-64032, [1, 1, 1, 1, 2, 2, 4, 10]), (-1024, [1, 1, 1, 1, 2, 2, 5, 9]), (-660, [1, 1, 1, 1, 2, 2, 6, 8]), (28160/9, [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]), (87424/3, [1, 1, 1, 1, 2, 3, 3, 10]), (-85760, [1, 1, 1, 1, 2, 3, 4, 9]), (2160, [1, 1, 1, 1, 2, 3, 5, 8]), (11520/7, [1, 1, 1, 1, 2, 3, 6, 7]), (-81900, [1, 1, 1, 1, 2, 4, 4, 8]), (-487680/7, [1, 1, 1, 1, 2, 4, 5, 7]), (-34720, [1, 1, 1, 1, 2, 4, 6, 6]), (5376/5, [1, 1, 1, 1, 2, 5, 5, 6]), (-145920, [1, 1, 1, 1, 2, 16]), (-58880/9, [1, 1, 1, 1, 3, 3, 3, 9]), (-39440, [1, 1, 1, 1, 3, 3, 4, 8]), (-51200/3, [1, 1, 1, 1, 3, 3, 5, 7]), (-25600/3, [1, 1, 1, 1, 3, 3, 6, 6]), (-314080/7, [1, 1, 1, 1, 3, 4, 4, 7]), (-24832, [1, 1, 1, 1, 3, 4, 5, 6])]

def node96SumGroup1Data_sector1_chunk2 : RawPoly ℕ := [(-108160, [1, 1, 1, 1, 3, 15]), (-16800, [1, 1, 1, 1, 4, 4, 4, 6]), (-8400, [1, 1, 1, 1, 4, 4, 5, 5]), (-213120, [1, 1, 1, 1, 4, 14]), (-18432, [1, 1, 1, 1, 5, 13]), (-19200, [1, 1, 1, 1, 6, 12]), (-230400/7, [1, 1, 1, 1, 7, 11]), (-15984, [1, 1, 1, 1, 8, 10]), (-8960, [1, 1, 1, 1, 9, 9]), (-4464, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (1216, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (-4040, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (-20160, [1, 1, 1, 2, 2, 2, 2, 11]), (68320/9, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (16896, [1, 1, 1, 2, 2, 2, 3, 10]), (-60160, [1, 1, 1, 2, 2, 2, 4, 9]), (-9852, [1, 1, 1, 2, 2, 2, 5, 8]), (-3840, [1, 1, 1, 2, 2, 2, 6, 7]), (47360/9, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (325760/3, [1, 1, 1, 2, 2, 3, 3, 9]), (-50300, [1, 1, 1, 2, 2, 3, 4, 8]), (82944/7, [1, 1, 1, 2, 2, 3, 5, 7]), (5760, [1, 1, 1, 2, 2, 3, 6, 6]), (-633000/7, [1, 1, 1, 2, 2, 4, 4, 7])]

def node96SumGroup1Data_sector1_chunk3 : RawPoly ℕ := [(-65760, [1, 1, 1, 2, 2, 4, 5, 6]), (-6912/5, [1, 1, 1, 2, 2, 5, 5, 5]), (-127200, [1, 1, 1, 2, 2, 15]), (836720/9, [1, 1, 1, 2, 3, 3, 3, 8]), (457280/21, [1, 1, 1, 2, 3, 3, 4, 7]), (235264/3, [1, 1, 1, 2, 3, 3, 5, 6]), (-129440, [1, 1, 1, 2, 3, 4, 4, 6]), (-198592/5, [1, 1, 1, 2, 3, 4, 5, 5]), (162560, [1, 1, 1, 2, 3, 14]), (-81900, [1, 1, 1, 2, 4, 4, 4, 5]), (428640, [1, 1, 1, 2, 4, 13]), (-125184, [1, 1, 1, 2, 5, 12]), (-140160, [1, 1, 1, 2, 6, 11]), (-1015680/7, [1, 1, 1, 2, 7, 10]), (-126160, [1, 1, 1, 2, 8, 9]), (112640/9, [1, 1, 1, 3, 3, 3, 3, 7]), (-23040, [1, 1, 1, 3, 3, 3, 4, 6]), (17920/9, [1, 1, 1, 3, 3, 3, 5, 5]), (-175600/3, [1, 1, 1, 3, 3, 4, 4, 5]), (302080, [1, 1, 1, 3, 3, 13]), (-38000/3, [1, 1, 1, 3, 4, 4, 4, 4]), (-252160/3, [1, 1, 1, 3, 4, 12]), (-81664, [1, 1, 1, 3, 5, 11]), (-90880, [1, 1, 1, 3, 6, 10])]

def node96SumGroup1Data_sector1_chunk4 : RawPoly ℕ := [(-669440/7, [1, 1, 1, 3, 7, 9]), (-35720, [1, 1, 1, 3, 8, 8]), (-134880, [1, 1, 1, 4, 4, 11]), (-229824, [1, 1, 1, 4, 5, 10]), (-224320, [1, 1, 1, 4, 6, 9]), (-1634400/7, [1, 1, 1, 4, 7, 8]), (10496/5, [1, 1, 1, 5, 5, 9]), (5664, [1, 1, 1, 5, 6, 8]), (-186624/7, [1, 1, 1, 5, 7, 7]), (-96000/7, [1, 1, 1, 6, 6, 7]), (556800, [1, 1, 1, 19]), (-128, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-4080, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (-2000, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-34560, [1, 1, 2, 2, 2, 2, 2, 10]), (90560/27, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (-33280/3, [1, 1, 2, 2, 2, 2, 3, 9]), (-89220, [1, 1, 2, 2, 2, 2, 4, 8]), (-39936, [1, 1, 2, 2, 2, 2, 5, 7]), (-18240, [1, 1, 2, 2, 2, 2, 6, 6]), (90100, [1, 1, 2, 2, 2, 3, 3, 8]), (-108960/7, [1, 1, 2, 2, 2, 3, 4, 7]), (20736, [1, 1, 2, 2, 2, 3, 5, 6]), (-74520, [1, 1, 2, 2, 2, 4, 4, 6])]

def node96SumGroup1Data_sector1_chunk5 : RawPoly ℕ := [(-180192/5, [1, 1, 2, 2, 2, 4, 5, 5]), (-179520, [1, 1, 2, 2, 2, 14]), (9508480/63, [1, 1, 2, 2, 3, 3, 3, 7]), (138240, [1, 1, 2, 2, 3, 3, 4, 6]), (306688/5, [1, 1, 2, 2, 3, 3, 5, 5]), (6336, [1, 1, 2, 2, 3, 4, 4, 5]), (393600, [1, 1, 2, 2, 3, 13]), (-11160, [1, 1, 2, 2, 4, 4, 4, 4]), (-494640, [1, 1, 2, 2, 4, 12]), (44352, [1, 1, 2, 2, 5, 11]), (-23616, [1, 1, 2, 2, 6, 10]), (203200/7, [1, 1, 2, 2, 7, 9]), (-2970, [1, 1, 2, 2, 8, 8]), (2510080/27, [1, 1, 2, 3, 3, 3, 3, 6]), (1239040/9, [1, 1, 2, 3, 3, 3, 4, 5]), (7640/3, [1, 1, 2, 3, 3, 4, 4, 4]), (-667520/3, [1, 1, 2, 3, 3, 12]), (80640, [1, 1, 2, 3, 4, 11]), (468480, [1, 1, 2, 3, 5, 10]), (1346560/3, [1, 1, 2, 3, 6, 9]), (477840, [1, 1, 2, 3, 7, 8]), (-170856, [1, 1, 2, 4, 4, 10]), (-188288, [1, 1, 2, 4, 5, 9]), (-246000, [1, 1, 2, 4, 6, 8])]

def node96SumGroup1Data_sector1_chunk6 : RawPoly ℕ := [(-748800/7, [1, 1, 2, 4, 7, 7]), (149472/5, [1, 1, 2, 5, 5, 8]), (241152/7, [1, 1, 2, 5, 6, 7]), (-5760, [1, 1, 2, 6, 6, 6]), (-883200, [1, 1, 2, 18]), (94720/9, [1, 1, 3, 3, 3, 3, 3, 5]), (37120/9, [1, 1, 3, 3, 3, 3, 4, 4]), (87680/3, [1, 1, 3, 3, 3, 11]), (144384, [1, 1, 3, 3, 4, 10]), (179968, [1, 1, 3, 3, 5, 9]), (193200, [1, 1, 3, 3, 6, 8]), (673920/7, [1, 1, 3, 3, 7, 7]), (-130400, [1, 1, 3, 4, 4, 9]), (-31224, [1, 1, 3, 4, 5, 8]), (-82560, [1, 1, 3, 4, 6, 7]), (150912/5, [1, 1, 3, 5, 5, 7]), (33152, [1, 1, 3, 5, 6, 6]), (-594240, [1, 1, 3, 17]), (-65520, [1, 1, 4, 4, 4, 8]), (-726624/7, [1, 1, 4, 4, 5, 7]), (-52080, [1, 1, 4, 4, 6, 6]), (-15168/5, [1, 1, 4, 5, 5, 6]), (279360, [1, 1, 4, 16]), (16896/5, [1, 1, 5, 5, 5, 5])]

def node96SumGroup1Data_sector1_chunk7 : RawPoly ℕ := [(-166656, [1, 1, 5, 15]), (-188160, [1, 1, 6, 14]), (2027520/7, [1, 1, 7, 13]), (-142920, [1, 1, 8, 12]), (-42240, [1, 1, 9, 11]), (25344, [1, 1, 10, 10]), (-1360, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (1600/3, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-16320, [1, 2, 2, 2, 2, 2, 2, 9]), (-23700, [1, 2, 2, 2, 2, 2, 3, 8]), (-69360, [1, 2, 2, 2, 2, 2, 4, 7]), (-33408, [1, 2, 2, 2, 2, 2, 5, 6]), (110080/7, [1, 2, 2, 2, 2, 3, 3, 7]), (-87840, [1, 2, 2, 2, 2, 3, 4, 6]), (-39744/5, [1, 2, 2, 2, 2, 3, 5, 5]), (-96648, [1, 2, 2, 2, 2, 4, 4, 5]), (176640, [1, 2, 2, 2, 2, 13]), (392320/9, [1, 2, 2, 2, 3, 3, 3, 6]), (16352, [1, 2, 2, 2, 3, 3, 4, 5]), (-26560, [1, 2, 2, 2, 3, 4, 4, 4]), (-289280, [1, 2, 2, 2, 3, 12]), (-13440, [1, 2, 2, 2, 4, 11]), (-264000, [1, 2, 2, 2, 5, 10]), (-282560, [1, 2, 2, 2, 6, 9])]

def node96SumGroup1Data_sector1_chunk8 : RawPoly ℕ := [(-1867380/7, [1, 2, 2, 2, 7, 8]), (275840/9, [1, 2, 2, 3, 3, 3, 3, 5]), (207040/9, [1, 2, 2, 3, 3, 3, 4, 4]), (284960, [1, 2, 2, 3, 3, 11]), (-48960, [1, 2, 2, 3, 4, 10]), (190016, [1, 2, 2, 3, 5, 9]), (132000, [1, 2, 2, 3, 6, 8]), (925920/7, [1, 2, 2, 3, 7, 7]), (-257360, [1, 2, 2, 4, 4, 9]), (-264114, [1, 2, 2, 4, 5, 8]), (-1839840/7, [1, 2, 2, 4, 6, 7]), (383328/35, [1, 2, 2, 5, 5, 7]), (-36576, [1, 2, 2, 5, 6, 6]), (398160, [1, 2, 2, 17]), (94720/9, [1, 2, 3, 3, 3, 3, 3, 4]), (597760/3, [1, 2, 3, 3, 3, 10]), (289600, [1, 2, 3, 3, 4, 9]), (306896, [1, 2, 3, 3, 5, 8]), (2318720/7, [1, 2, 3, 3, 6, 7]), (-11520, [1, 2, 3, 4, 4, 8]), (889344/7, [1, 2, 3, 4, 5, 7]), (-23360, [1, 2, 3, 4, 6, 6]), (48768, [1, 2, 3, 5, 5, 6]), (-670080, [1, 2, 3, 16])]

def node96SumGroup1Data_sector1_chunk9 : RawPoly ℕ := [(-45360, [1, 2, 4, 4, 4, 7]), (-93408, [1, 2, 4, 4, 5, 6]), (9408, [1, 2, 4, 5, 5, 5]), (321600, [1, 2, 4, 15]), (-264960, [1, 2, 5, 14]), (329280, [1, 2, 6, 13]), (-1837440/7, [1, 2, 7, 12]), (132480, [1, 2, 8, 11]), (-10752, [1, 2, 9, 10]), (378880/9, [1, 3, 3, 3, 3, 9]), (302560/9, [1, 3, 3, 3, 4, 8]), (3274240/63, [1, 3, 3, 3, 5, 7]), (189440/9, [1, 3, 3, 3, 6, 6]), (-55040/7, [1, 3, 3, 4, 4, 7]), (-17984, [1, 3, 3, 4, 5, 6]), (9216/5, [1, 3, 3, 5, 5, 5]), (560640, [1, 3, 3, 15]), (-6720, [1, 3, 4, 4, 4, 6]), (9216/5, [1, 3, 4, 4, 5, 5]), (3840, [1, 3, 4, 14]), (262656, [1, 3, 5, 13]), (168960, [1, 3, 6, 12]), (622080/7, [1, 3, 7, 11]), (167328, [1, 3, 8, 10])]

def node96SumGroup1Data_sector1_chunk10 : RawPoly ℕ := [(113920, [1, 3, 9, 9]), (-200160, [1, 4, 4, 13]), (-94464, [1, 4, 5, 12]), (-94080, [1, 4, 6, 11]), (-87552, [1, 4, 7, 10]), (-129440, [1, 4, 8, 9]), (147456/5, [1, 5, 5, 11]), (-5376, [1, 5, 6, 10]), (596992/7, [1, 5, 7, 9]), (37728, [1, 5, 8, 8]), (-33280, [1, 6, 6, 9]), (-60000/7, [1, 6, 7, 8]), (69120/7, [1, 7, 7, 7]), (103680, [1, 21]), (-4080, [2, 2, 2, 2, 2, 2, 4, 6]), (1600, [2, 2, 2, 2, 2, 3, 3, 6]), (-8160, [2, 2, 2, 2, 2, 3, 4, 5]), (-4080, [2, 2, 2, 2, 2, 4, 4, 4]), (-32640, [2, 2, 2, 2, 2, 12]), (3200, [2, 2, 2, 2, 3, 3, 3, 5]), (-2480, [2, 2, 2, 2, 3, 3, 4, 4]), (-13440, [2, 2, 2, 2, 3, 11]), (-53040, [2, 2, 2, 2, 4, 10]), (-33408, [2, 2, 2, 2, 5, 9])]

def node96SumGroup1Data_sector1_chunk11 : RawPoly ℕ := [(-34620, [2, 2, 2, 2, 6, 8]), (-16320, [2, 2, 2, 2, 7, 7]), (1600, [2, 2, 2, 3, 3, 3, 3, 4]), (20800, [2, 2, 2, 3, 3, 10]), (-43200, [2, 2, 2, 3, 4, 9]), (14472, [2, 2, 2, 3, 5, 8]), (168960/7, [2, 2, 2, 3, 6, 7]), (-67260, [2, 2, 2, 4, 4, 8]), (-66048, [2, 2, 2, 4, 5, 7]), (-36000, [2, 2, 2, 4, 6, 6]), (768/5, [2, 2, 2, 5, 5, 6]), (-267840, [2, 2, 2, 16]), (267520/9, [2, 2, 3, 3, 3, 9]), (20100, [2, 2, 3, 3, 4, 8]), (203520/7, [2, 2, 3, 3, 5, 7]), (9600, [2, 2, 3, 3, 6, 6]), (54720/7, [2, 2, 3, 4, 4, 7]), (-3840, [2, 2, 3, 4, 5, 6]), (9216/5, [2, 2, 3, 5, 5, 5]), (164160, [2, 2, 3, 15]), (-3360, [2, 2, 4, 4, 4, 6]), (4608/5, [2, 2, 4, 4, 5, 5]), (-259200, [2, 2, 4, 14]), (-17856, [2, 2, 5, 13])]

def node96SumGroup1Data_sector1_chunk12 : RawPoly ℕ := [(-58560, [2, 2, 6, 12]), (-14400/7, [2, 2, 7, 11]), (-25740, [2, 2, 8, 10]), (-13280, [2, 2, 9, 9]), (94720/9, [2, 3, 3, 3, 3, 8]), (974080/63, [2, 3, 3, 3, 4, 7]), (94720/9, [2, 3, 3, 3, 5, 6]), (-3360, [2, 3, 3, 4, 4, 6]), (4608/5, [2, 3, 3, 4, 5, 5]), (202240, [2, 3, 3, 14]), (40320, [2, 3, 4, 13]), (87552, [2, 3, 5, 12]), (42240, [2, 3, 6, 11]), (449280/7, [2, 3, 7, 10]), (60160, [2, 3, 8, 9]), (-48720, [2, 4, 4, 12]), (-21888, [2, 4, 5, 11]), (-43680, [2, 4, 6, 10]), (-91520/7, [2, 4, 7, 9]), (-36000, [2, 4, 8, 8]), (59904/5, [2, 5, 5, 10]), (-4352, [2, 5, 6, 9]), (225504/7, [2, 5, 7, 8]), (-34800, [2, 6, 6, 8])]

def node96SumGroup1Data_sector1_chunk13 : RawPoly ℕ := [(113280/7, [2, 6, 7, 7]), (-11520, [2, 20]), (189440/9, [3, 3, 3, 13]), (-12800/3, [3, 3, 4, 12]), (138240/7, [3, 3, 7, 9]), (4320, [3, 3, 8, 8]), (-13440, [3, 4, 6, 9]), (133920/7, [3, 4, 7, 8]), (18432/5, [3, 5, 5, 9]), (5856, [3, 5, 6, 8]), (138240/7, [3, 5, 7, 7]), (69120/7, [3, 6, 6, 7]), (172800, [3, 19]), (-13440, [4, 4, 6, 8]), (-34560/7, [4, 4, 7, 7]), (18432/5, [4, 5, 5, 8]), (-117888/7, [4, 5, 6, 7]), (-6720, [4, 6, 6, 6]), (-115200, [4, 18]), (18432/5, [5, 5, 5, 7]), (16896/5, [5, 5, 6, 6]), (46080, [5, 17]), (-46080, [6, 16]), (276480/7, [7, 15])]

def node96SumGroup1Data_sector1_chunk14 : RawPoly ℕ := [(-2880, [8, 14]), (5120, [9, 13]), (-2304, [10, 12])]

def node96SumGroup1Data_sector1 : RawPoly ℕ := [node96SumGroup1Data_sector1_chunk0, node96SumGroup1Data_sector1_chunk1, node96SumGroup1Data_sector1_chunk2, node96SumGroup1Data_sector1_chunk3, node96SumGroup1Data_sector1_chunk4, node96SumGroup1Data_sector1_chunk5, node96SumGroup1Data_sector1_chunk6, node96SumGroup1Data_sector1_chunk7, node96SumGroup1Data_sector1_chunk8, node96SumGroup1Data_sector1_chunk9, node96SumGroup1Data_sector1_chunk10, node96SumGroup1Data_sector1_chunk11, node96SumGroup1Data_sector1_chunk12, node96SumGroup1Data_sector1_chunk13, node96SumGroup1Data_sector1_chunk14].flatten

def node96SumGroup1Data_sector2 : RawPoly ℕ := [].flatten

def node96SumGroup1Data : SectorVector := [(-2, node96SumGroup1Data_sector0), (0, node96SumGroup1Data_sector1), (2, node96SumGroup1Data_sector2)]

def node96SumGroup1Outputs : List SectorVector := [node96Piece16Output, node96Piece17Output, node96Piece18Output, node96Piece19Output, node96Piece20Output, node96Piece21Output, node96Piece22Output, node96Piece23Output, node96Piece24Output, node96Piece25Output, node96Piece26Output, node96Piece27Output, node96Piece28Output, node96Piece29Output, node96Piece30Output, node96Piece31Output]

theorem node96SumGroup1_check : zipMany 100000 [node96Piece16Pad, node96Piece17Pad, node96Piece18Pad, node96Piece19Pad, node96Piece20Pad, node96Piece21Pad, node96Piece22Pad, node96Piece23Pad, node96Piece24Pad, node96Piece25Pad, node96Piece26Pad, node96Piece27Pad, node96Piece28Pad, node96Piece29Pad, node96Piece30Pad, node96Piece31Pad] = node96SumGroup1Data := by decide +kernel

theorem node96SumGroup1_value : evaluate node96SumGroup1Data = (node96SumGroup1Outputs.map evaluate).sum := by
  rw [← node96SumGroup1_check, evaluate_zipMany]
  simp only [node96SumGroup1Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node96Piece16Pad_value, node96Piece17Pad_value, node96Piece18Pad_value, node96Piece19Pad_value, node96Piece20Pad_value, node96Piece21Pad_value, node96Piece22Pad_value, node96Piece23Pad_value, node96Piece24Pad_value, node96Piece25Pad_value, node96Piece26Pad_value, node96Piece27Pad_value, node96Piece28Pad_value, node96Piece29Pad_value, node96Piece30Pad_value, node96Piece31Pad_value]

def node96SumGroup2Data_sector0 : RawPoly ℕ := [].flatten

def node96SumGroup2Data_sector1_chunk0 : RawPoly ℕ := [(1280, [1, 1, 1, 1, 3, 3, 6, 6]), (640, [1, 1, 1, 1, 3, 4, 5, 6]), (-380, [1, 1, 1, 1, 4, 4, 4, 6]), (160, [1, 1, 1, 1, 6, 12]), (-336, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-5760/7, [1, 1, 1, 2, 2, 2, 6, 7]), (-320, [1, 1, 1, 2, 2, 3, 6, 6]), (-1248, [1, 1, 1, 2, 2, 4, 5, 6]), (14080/3, [1, 1, 1, 2, 3, 3, 5, 6]), (-440, [1, 1, 1, 2, 3, 4, 4, 6]), (1920, [1, 1, 1, 2, 3, 4, 5, 5]), (-1140, [1, 1, 1, 2, 4, 4, 4, 5]), (480, [1, 1, 1, 2, 5, 12]), (-3840/11, [1, 1, 1, 2, 6, 11]), (112640/27, [1, 1, 1, 3, 3, 3, 4, 6]), (1920, [1, 1, 1, 3, 3, 4, 4, 5]), (23040, [1, 1, 1, 3, 3, 13]), (-1140, [1, 1, 1, 3, 4, 4, 4, 4]), (10080, [1, 1, 1, 3, 4, 12]), (7680, [1, 1, 1, 3, 5, 11]), (23424, [1, 1, 1, 3, 6, 10]), (-13680, [1, 1, 1, 4, 4, 11]), (5760, [1, 1, 1, 4, 5, 10]), (-640/3, [1, 1, 1, 4, 6, 9])]

def node96SumGroup2Data_sector1_chunk1 : RawPoly ℕ := [(48, [1, 1, 1, 5, 6, 8]), (5760, [1, 1, 1, 19]), (-1008, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-1008, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-3024, [1, 1, 2, 2, 2, 2, 2, 10]), (-10080, [1, 1, 2, 2, 2, 2, 3, 9]), (-17280/7, [1, 1, 2, 2, 2, 2, 5, 7]), (-17280/7, [1, 1, 2, 2, 2, 3, 4, 7]), (-960, [1, 1, 2, 2, 2, 3, 5, 6]), (-3744, [1, 1, 2, 2, 2, 4, 5, 5]), (-17280, [1, 1, 2, 2, 2, 14]), (2880, [1, 1, 2, 2, 3, 3, 4, 6]), (2560, [1, 1, 2, 2, 3, 3, 5, 5]), (-3144, [1, 1, 2, 2, 3, 4, 4, 5]), (-5760, [1, 1, 2, 2, 3, 13]), (-1140, [1, 1, 2, 2, 4, 4, 4, 4]), (-18240, [1, 1, 2, 2, 4, 12]), (-176256/11, [1, 1, 2, 2, 5, 11]), (-2880, [1, 1, 2, 2, 6, 10]), (-103680/7, [1, 1, 2, 2, 7, 9]), (3840, [1, 1, 2, 3, 3, 3, 3, 6]), (49280/9, [1, 1, 2, 3, 3, 3, 4, 5]), (-2460, [1, 1, 2, 3, 3, 4, 4, 4]), (59360, [1, 1, 2, 3, 3, 12])]

def node96SumGroup2Data_sector1_chunk2 : RawPoly ℕ := [(83520/11, [1, 1, 2, 3, 4, 11]), (31872, [1, 1, 2, 3, 5, 10]), (42240, [1, 1, 2, 3, 6, 9]), (-31320, [1, 1, 2, 4, 4, 10]), (-4096, [1, 1, 2, 4, 5, 9]), (144, [1, 1, 2, 5, 5, 8]), (8960/9, [1, 1, 3, 3, 3, 3, 4, 4]), (450560/9, [1, 1, 3, 3, 3, 11]), (75392, [1, 1, 3, 3, 4, 10]), (66560, [1, 1, 3, 3, 5, 9]), (82560, [1, 1, 3, 3, 6, 8]), (23040, [1, 1, 3, 3, 7, 7]), (-11440, [1, 1, 3, 4, 4, 9]), (41424, [1, 1, 3, 4, 5, 8]), (65280, [1, 1, 3, 4, 6, 7]), (15360, [1, 1, 3, 5, 5, 7]), (53760, [1, 1, 3, 5, 6, 6]), (376320, [1, 1, 3, 17]), (-24510, [1, 1, 4, 4, 4, 8]), (-15840, [1, 1, 4, 4, 5, 7]), (-13680, [1, 1, 4, 4, 6, 6]), (11520, [1, 1, 4, 5, 5, 6]), (-46080, [1, 1, 4, 16]), (58752, [1, 1, 5, 15])]

def node96SumGroup2Data_sector1_chunk3 : RawPoly ℕ := [(80640, [1, 1, 6, 14]), (11520, [1, 1, 7, 13]), (11040, [1, 1, 8, 12]), (75520/11, [1, 1, 9, 11]), (9216, [1, 1, 10, 10]), (-1008, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-1008, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-6048, [1, 2, 2, 2, 2, 2, 2, 9]), (-22680, [1, 2, 2, 2, 2, 2, 3, 8]), (-59616/7, [1, 2, 2, 2, 2, 2, 4, 7]), (-6048, [1, 2, 2, 2, 2, 2, 5, 6]), (-158400/7, [1, 2, 2, 2, 2, 3, 3, 7]), (-21120, [1, 2, 2, 2, 2, 3, 4, 6]), (-10080, [1, 2, 2, 2, 2, 3, 5, 5]), (-3744, [1, 2, 2, 2, 2, 4, 4, 5]), (-95040, [1, 2, 2, 2, 2, 13]), (320, [1, 2, 2, 2, 3, 3, 3, 6]), (-544, [1, 2, 2, 2, 3, 3, 4, 5]), (-1700, [1, 2, 2, 2, 3, 4, 4, 4]), (-126560, [1, 2, 2, 2, 3, 12]), (-803520/11, [1, 2, 2, 2, 4, 11]), (-64512, [1, 2, 2, 2, 5, 10]), (-40320, [1, 2, 2, 2, 6, 9]), (-388800/7, [1, 2, 2, 2, 7, 8])]

def node96SumGroup2Data_sector1_chunk4 : RawPoly ℕ := [(2560, [1, 2, 2, 3, 3, 3, 3, 5]), (-2920/9, [1, 2, 2, 3, 3, 3, 4, 4]), (396800/11, [1, 2, 2, 3, 3, 11]), (-59328, [1, 2, 2, 3, 4, 10]), (-3072, [1, 2, 2, 3, 5, 9]), (1440, [1, 2, 2, 3, 6, 8]), (-247680/7, [1, 2, 2, 3, 7, 7]), (-59680, [1, 2, 2, 4, 4, 9]), (-78336, [1, 2, 2, 4, 5, 8]), (-509760/7, [1, 2, 2, 4, 6, 7]), (-313344/7, [1, 2, 2, 5, 5, 7]), (-20736, [1, 2, 2, 5, 6, 6]), (-408960, [1, 2, 2, 17]), (8960/9, [1, 2, 3, 3, 3, 3, 3, 4]), (727168/9, [1, 2, 3, 3, 3, 10]), (87040, [1, 2, 3, 3, 4, 9]), (119184, [1, 2, 3, 3, 5, 8]), (113920, [1, 2, 3, 3, 6, 7]), (-37860, [1, 2, 3, 4, 4, 8]), (27648, [1, 2, 3, 4, 5, 7]), (37440, [1, 2, 3, 4, 6, 6]), (65280, [1, 2, 3, 5, 5, 6]), (430080, [1, 2, 3, 16]), (-36420, [1, 2, 4, 4, 4, 7])]

def node96SumGroup2Data_sector1_chunk5 : RawPoly ℕ := [(-53712, [1, 2, 4, 4, 5, 6]), (-9216, [1, 2, 4, 5, 5, 5]), (-288000, [1, 2, 4, 15]), (-36864, [1, 2, 5, 14]), (34560, [1, 2, 6, 13]), (-492000/7, [1, 2, 7, 12]), (-116640/11, [1, 2, 8, 11]), (-9728, [1, 2, 9, 10]), (279040/9, [1, 3, 3, 3, 3, 9]), (78080, [1, 3, 3, 3, 4, 8]), (647680/9, [1, 3, 3, 3, 5, 7]), (542720/9, [1, 3, 3, 3, 6, 6]), (41200, [1, 3, 3, 4, 4, 7]), (179200, [1, 3, 3, 4, 5, 6]), (20480, [1, 3, 3, 5, 5, 5]), (-470400, [1, 3, 3, 15]), (-18400, [1, 3, 4, 4, 4, 6]), (19200, [1, 3, 4, 4, 5, 5]), (9600, [1, 3, 4, 14]), (294144, [1, 3, 5, 13]), (-6400, [1, 3, 6, 12]), (4220160/11, [1, 3, 7, 11]), (392160, [1, 3, 8, 10]), (188800, [1, 3, 9, 9])]

def node96SumGroup2Data_sector1_chunk6 : RawPoly ℕ := [(-15750, [1, 4, 4, 4, 4, 5]), (289080, [1, 4, 4, 13]), (-145968, [1, 4, 5, 12]), (144000/11, [1, 4, 6, 11]), (-44928, [1, 4, 7, 10]), (-53280, [1, 4, 8, 9]), (572544/11, [1, 5, 5, 11]), (135936, [1, 5, 6, 10]), (54784, [1, 5, 7, 9]), (30888, [1, 5, 8, 8]), (72320, [1, 6, 6, 9]), (82080, [1, 6, 7, 8]), (1920, [1, 7, 7, 7]), (-144960, [1, 21]), (-336, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (-3024, [2, 2, 2, 2, 2, 2, 2, 8]), (-111600/7, [2, 2, 2, 2, 2, 2, 3, 7]), (-6048, [2, 2, 2, 2, 2, 2, 4, 6]), (-3024, [2, 2, 2, 2, 2, 2, 5, 5]), (-24176, [2, 2, 2, 2, 2, 3, 3, 6]), (-28968, [2, 2, 2, 2, 2, 3, 4, 5]), (-1008, [2, 2, 2, 2, 2, 4, 4, 4]), (-11736, [2, 2, 2, 2, 2, 12]), (-27680/3, [2, 2, 2, 2, 3, 3, 3, 5])]

def node96SumGroup2Data_sector1_chunk7 : RawPoly ℕ := [(-10520, [2, 2, 2, 2, 3, 3, 4, 4]), (-225600/11, [2, 2, 2, 2, 3, 11]), (-113760, [2, 2, 2, 2, 4, 10]), (-110016, [2, 2, 2, 2, 5, 9]), (-97920, [2, 2, 2, 2, 6, 8]), (-419040/7, [2, 2, 2, 2, 7, 7]), (8960/27, [2, 2, 2, 3, 3, 3, 3, 4]), (-96256, [2, 2, 2, 3, 3, 10]), (-524800/3, [2, 2, 2, 3, 4, 9]), (-141264, [2, 2, 2, 3, 5, 8]), (-1166400/7, [2, 2, 2, 3, 6, 7]), (-58680, [2, 2, 2, 4, 4, 8]), (-1025568/7, [2, 2, 2, 4, 5, 7]), (-41760, [2, 2, 2, 4, 6, 6]), (-50112, [2, 2, 2, 5, 5, 6]), (279360, [2, 2, 2, 16]), (214400/9, [2, 2, 3, 3, 3, 9]), (-16800, [2, 2, 3, 3, 4, 8]), (123008/7, [2, 2, 3, 3, 5, 7]), (-320, [2, 2, 3, 3, 6, 6]), (-618600/7, [2, 2, 3, 4, 4, 7]), (-114720, [2, 2, 3, 4, 5, 6]), (-1536, [2, 2, 3, 5, 5, 5]), (-243840, [2, 2, 3, 15])]

def node96SumGroup2Data_sector1_chunk8 : RawPoly ℕ := [(-28740, [2, 2, 4, 4, 4, 6]), (-73224, [2, 2, 4, 4, 5, 5]), (40320, [2, 2, 4, 14]), (-60480, [2, 2, 5, 13]), (-374400, [2, 2, 6, 12]), (-18328320/77, [2, 2, 7, 11]), (-410544, [2, 2, 8, 10]), (-209920, [2, 2, 9, 9]), (186880/9, [2, 3, 3, 3, 3, 8]), (359360/9, [2, 3, 3, 3, 4, 7]), (582400/9, [2, 3, 3, 3, 5, 6]), (-520, [2, 3, 3, 4, 4, 6]), (44864, [2, 3, 3, 4, 5, 5]), (-215040, [2, 3, 3, 14]), (-35956, [2, 3, 4, 4, 4, 5]), (172320, [2, 3, 4, 13]), (-263744, [2, 3, 5, 12]), (1509120/11, [2, 3, 6, 11]), (82560/7, [2, 3, 7, 10]), (61600, [2, 3, 8, 9]), (-2460, [2, 4, 4, 4, 4, 4]), (-192420, [2, 4, 4, 12]), (-103680, [2, 4, 5, 11]), (-263808, [2, 4, 6, 10])]

def node96SumGroup2Data_sector1_chunk9 : RawPoly ℕ := [(-2179840/7, [2, 4, 7, 9]), (-122400, [2, 4, 8, 8]), (-79488, [2, 5, 5, 10]), (-122624, [2, 5, 6, 9]), (-1066896/7, [2, 5, 7, 8]), (-33840, [2, 6, 6, 8]), (-576000/7, [2, 6, 7, 7]), (86400, [2, 20]), (35840/9, [3, 3, 3, 3, 3, 7]), (578560/27, [3, 3, 3, 3, 4, 6]), (81920/9, [3, 3, 3, 3, 5, 5]), (250160/9, [3, 3, 3, 4, 4, 5]), (200960/3, [3, 3, 3, 13]), (-2380/3, [3, 3, 4, 4, 4, 4]), (65440/3, [3, 3, 4, 12]), (2045312/11, [3, 3, 5, 11]), (192384, [3, 3, 6, 10]), (189440, [3, 3, 7, 9]), (96720, [3, 3, 8, 8]), (304320/11, [3, 4, 4, 11]), (90432, [3, 4, 5, 10]), (225280/3, [3, 4, 6, 9]), (43680, [3, 4, 7, 8]), (88064, [3, 5, 5, 9])]

def node96SumGroup2Data_sector1_chunk10 : RawPoly ℕ := [(142080, [3, 5, 6, 8]), (51072, [3, 5, 7, 7]), (49920, [3, 6, 6, 7]), (-245760, [3, 19]), (-35268, [4, 4, 4, 10]), (-75520, [4, 4, 5, 9]), (-54000, [4, 4, 6, 8]), (-27360, [4, 4, 7, 7]), (-20952, [4, 5, 5, 8]), (-27648, [4, 5, 6, 7]), (-1920, [4, 6, 6, 6]), (153600, [4, 18]), (1152, [5, 5, 5, 7]), (1152, [5, 5, 6, 6]), (-54720, [5, 17]), (46080, [6, 16]), (-276480/7, [7, 15]), (-25920, [8, 14]), (72960, [9, 13]), (-80736, [10, 12]), (368640/11, [11, 11])]

def node96SumGroup2Data_sector1 : RawPoly ℕ := [node96SumGroup2Data_sector1_chunk0, node96SumGroup2Data_sector1_chunk1, node96SumGroup2Data_sector1_chunk2, node96SumGroup2Data_sector1_chunk3, node96SumGroup2Data_sector1_chunk4, node96SumGroup2Data_sector1_chunk5, node96SumGroup2Data_sector1_chunk6, node96SumGroup2Data_sector1_chunk7, node96SumGroup2Data_sector1_chunk8, node96SumGroup2Data_sector1_chunk9, node96SumGroup2Data_sector1_chunk10].flatten

def node96SumGroup2Data_sector2 : RawPoly ℕ := [].flatten

def node96SumGroup2Data : SectorVector := [(-2, node96SumGroup2Data_sector0), (0, node96SumGroup2Data_sector1), (2, node96SumGroup2Data_sector2)]

def node96SumGroup2Outputs : List SectorVector := [node96Piece32Output, node96Piece33Output, node96Piece34Output, node96Piece35Output, node96Piece36Output, node96Piece37Output, node96Piece38Output, node96Piece39Output, node96Piece40Output, node96Piece41Output, node96Piece42Output, node96Piece43Output, node96Piece44Output, node96Piece45Output, node96Piece46Output]

theorem node96SumGroup2_check : zipMany 100000 [node96Piece32Pad, node96Piece33Pad, node96Piece34Pad, node96Piece35Pad, node96Piece36Pad, node96Piece37Pad, node96Piece38Pad, node96Piece39Pad, node96Piece40Pad, node96Piece41Pad, node96Piece42Pad, node96Piece43Pad, node96Piece44Pad, node96Piece45Pad, node96Piece46Pad] = node96SumGroup2Data := by decide +kernel

theorem node96SumGroup2_value : evaluate node96SumGroup2Data = (node96SumGroup2Outputs.map evaluate).sum := by
  rw [← node96SumGroup2_check, evaluate_zipMany]
  simp only [node96SumGroup2Outputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    node96Piece32Pad_value, node96Piece33Pad_value, node96Piece34Pad_value, node96Piece35Pad_value, node96Piece36Pad_value, node96Piece37Pad_value, node96Piece38Pad_value, node96Piece39Pad_value, node96Piece40Pad_value, node96Piece41Pad_value, node96Piece42Pad_value, node96Piece43Pad_value, node96Piece44Pad_value, node96Piece45Pad_value, node96Piece46Pad_value]

def node96SumData_sector0 : RawPoly ℕ := [].flatten

def node96SumData_sector1_chunk0 : RawPoly ℕ := [(8192/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]), (8192/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]), (94208/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]), (32768/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]), (1159808/10395, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]), (8192/1485, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]), (188416/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]), (985088/2079, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]), (12416/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5]), (16384/495, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]), (65152/385, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]), (2574848/3465, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]), (74624/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]), (145408/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]), (11136/35, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]), (43648/105, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]), (607232/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]), (633856/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]), (808256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8])]

def node96SumData_sector1_chunk1 : RawPoly ℕ := [(572416/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]), (299648/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]), (58112/189, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]), (2048/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]), (82688/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]), (38912/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]), (121984/21, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7]), (1200256/315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]), (58880/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]), (98560/27, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]), (6656/9, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]), (201536/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]), (-8704/63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]), (1152/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]), (12416/63, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]), (19904/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]), (88576/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]), (27056/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]), (9216/5, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]), (13568/7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]), (147072/35, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]), (3968/3, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]), (483584/21, [1, 1, 1, 1, 1, 1, 1, 1, 2, 12])]

def node96SumData_sector1_chunk2 : RawPoly ℕ := [(4096/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5]), (-512/7, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]), (137216/21, [1, 1, 1, 1, 1, 1, 1, 1, 3, 11]), (4352, [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]), (477184/35, [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]), (88504/7, [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]), (43776/7, [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]), (384/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]), (21888/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]), (127360/21, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6]), (173072/35, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]), (169856/105, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]), (912/7, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]), (12480, [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]), (-46336/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]), (-107264/21, [1, 1, 1, 1, 1, 1, 1, 2, 3, 10]), (16064, [1, 1, 1, 1, 1, 1, 1, 2, 4, 9]), (648328/35, [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]), (122240/7, [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]), (-77312/7, [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]), (-233480/21, [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]), (-528896/105, [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]), (-55040/21, [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]), (11264/7, [1, 1, 1, 1, 1, 1, 1, 4, 4, 7])]

def node96SumData_sector1_chunk3 : RawPoly ℕ := [(200128/35, [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]), (6912/5, [1, 1, 1, 1, 1, 1, 1, 5, 5, 5]), (-4160, [1, 1, 1, 1, 1, 1, 1, 15]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]), (75776/15, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]), (1008, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]), (14192/9, [1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]), (17408, [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]), (-4480/3, [1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]), (15232, [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]), (11520, [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]), (128128/5, [1, 1, 1, 1, 1, 1, 2, 2, 5, 7]), (10688, [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]), (-92216/3, [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]), (-45312, [1, 1, 1, 1, 1, 1, 2, 3, 4, 7]), (-8192, [1, 1, 1, 1, 1, 1, 2, 3, 5, 6]), (-7800, [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]), (4928, [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]), (-83840, [1, 1, 1, 1, 1, 1, 2, 14]), (-35840/3, [1, 1, 1, 1, 1, 1, 3, 3, 3, 7]), (-131072/3, [1, 1, 1, 1, 1, 1, 3, 3, 4, 6]), (-39168/5, [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]), (-549824/15, [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]), (88448/3, [1, 1, 1, 1, 1, 1, 3, 13])]

def node96SumData_sector1_chunk4 : RawPoly ℕ := [(-4480/3, [1, 1, 1, 1, 1, 1, 4, 4, 4, 4]), (70592/3, [1, 1, 1, 1, 1, 1, 4, 12]), (-220288/5, [1, 1, 1, 1, 1, 1, 5, 11]), (-41344, [1, 1, 1, 1, 1, 1, 6, 10]), (-28800, [1, 1, 1, 1, 1, 1, 7, 9]), (-15804, [1, 1, 1, 1, 1, 1, 8, 8]), (-432, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5]), (2080, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4]), (18560/9, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3]), (17376, [1, 1, 1, 1, 1, 2, 2, 2, 2, 9]), (43848, [1, 1, 1, 1, 1, 2, 2, 2, 3, 8]), (19248, [1, 1, 1, 1, 1, 2, 2, 2, 4, 7]), (131456/5, [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]), (-12608/3, [1, 1, 1, 1, 1, 2, 2, 3, 3, 7]), (-160, [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]), (92352/5, [1, 1, 1, 1, 1, 2, 2, 3, 5, 5]), (-34464/5, [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]), (150624, [1, 1, 1, 1, 1, 2, 2, 13]), (-855040/27, [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]), (-275584/5, [1, 1, 1, 1, 1, 2, 3, 3, 4, 5]), (-50168/3, [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]), (170752/3, [1, 1, 1, 1, 1, 2, 3, 12]), (-124608, [1, 1, 1, 1, 1, 2, 4, 11]), (-122112/5, [1, 1, 1, 1, 1, 2, 5, 10])]

def node96SumData_sector1_chunk5 : RawPoly ℕ := [(-43648/3, [1, 1, 1, 1, 1, 2, 6, 9]), (-21096, [1, 1, 1, 1, 1, 2, 7, 8]), (-8960/3, [1, 1, 1, 1, 1, 3, 3, 3, 3, 5]), (-14080, [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]), (-409024/3, [1, 1, 1, 1, 1, 3, 3, 11]), (-195200, [1, 1, 1, 1, 1, 3, 4, 10]), (-747136/5, [1, 1, 1, 1, 1, 3, 5, 9]), (-173744, [1, 1, 1, 1, 1, 3, 6, 8]), (-76608, [1, 1, 1, 1, 1, 3, 7, 7]), (-97680, [1, 1, 1, 1, 1, 4, 4, 9]), (-584316/5, [1, 1, 1, 1, 1, 4, 5, 8]), (-753024/7, [1, 1, 1, 1, 1, 4, 6, 7]), (-77376/5, [1, 1, 1, 1, 1, 5, 5, 7]), (-106048/5, [1, 1, 1, 1, 1, 5, 6, 6]), (15840, [1, 1, 1, 1, 1, 17]), (-432, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4]), (1264/3, [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3]), (-744, [1, 1, 1, 1, 2, 2, 2, 2, 2, 8]), (40000, [1, 1, 1, 1, 2, 2, 2, 2, 3, 7]), (6560, [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]), (2976, [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]), (54720, [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]), (75008, [1, 1, 1, 1, 2, 2, 2, 3, 4, 5]), (-2360, [1, 1, 1, 1, 2, 2, 2, 4, 4, 4])]

def node96SumData_sector1_chunk6 : RawPoly ℕ := [(-21760, [1, 1, 1, 1, 2, 2, 2, 12]), (104192/9, [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]), (2280, [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]), (7680, [1, 1, 1, 1, 2, 2, 3, 11]), (31248, [1, 1, 1, 1, 2, 2, 4, 10]), (149888, [1, 1, 1, 1, 2, 2, 5, 9]), (110820, [1, 1, 1, 1, 2, 2, 6, 8]), (54720, [1, 1, 1, 1, 2, 2, 7, 7]), (-39040/9, [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]), (154624/3, [1, 1, 1, 1, 2, 3, 3, 10]), (-163200, [1, 1, 1, 1, 2, 3, 4, 9]), (44128, [1, 1, 1, 1, 2, 3, 5, 8]), (-113920/7, [1, 1, 1, 1, 2, 3, 6, 7]), (-119220, [1, 1, 1, 1, 2, 4, 4, 8]), (-632832/7, [1, 1, 1, 1, 2, 4, 5, 7]), (-51040, [1, 1, 1, 1, 2, 4, 6, 6]), (158976/5, [1, 1, 1, 1, 2, 5, 5, 6]), (-40320, [1, 1, 1, 1, 2, 16]), (-465920/9, [1, 1, 1, 1, 3, 3, 3, 9]), (-488840/3, [1, 1, 1, 1, 3, 3, 4, 8]), (-194560/3, [1, 1, 1, 1, 3, 3, 5, 7]), (-202240/3, [1, 1, 1, 1, 3, 3, 6, 6]), (-923360/7, [1, 1, 1, 1, 3, 4, 4, 7]), (-187520, [1, 1, 1, 1, 3, 4, 5, 6])]

def node96SumData_sector1_chunk7 : RawPoly ℕ := [(-4096, [1, 1, 1, 1, 3, 5, 5, 5]), (-24320, [1, 1, 1, 1, 3, 15]), (-33180, [1, 1, 1, 1, 4, 4, 4, 6]), (-58128, [1, 1, 1, 1, 4, 4, 5, 5]), (-251520, [1, 1, 1, 1, 4, 14]), (31872, [1, 1, 1, 1, 5, 13]), (-163040, [1, 1, 1, 1, 6, 12]), (-2152320/7, [1, 1, 1, 1, 7, 11]), (-257784, [1, 1, 1, 1, 8, 10]), (-146240, [1, 1, 1, 1, 9, 9]), (-144, [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]), (-6480, [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]), (-976, [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]), (-16344, [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]), (58016/3, [1, 1, 1, 2, 2, 2, 2, 3, 3, 5]), (1880, [1, 1, 1, 2, 2, 2, 2, 3, 4, 4]), (61440, [1, 1, 1, 2, 2, 2, 2, 11]), (160480/9, [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]), (137216, [1, 1, 1, 2, 2, 2, 3, 10]), (-13120, [1, 1, 1, 2, 2, 2, 4, 9]), (57732, [1, 1, 1, 2, 2, 2, 5, 8]), (437760/7, [1, 1, 1, 2, 2, 2, 6, 7]), (47360/9, [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]), (272000, [1, 1, 1, 2, 2, 3, 3, 9])]

def node96SumData_sector1_chunk8 : RawPoly ℕ := [(151620, [1, 1, 1, 2, 2, 3, 4, 8]), (2052352/7, [1, 1, 1, 2, 2, 3, 5, 7]), (125760, [1, 1, 1, 2, 2, 3, 6, 6]), (-572520/7, [1, 1, 1, 2, 2, 4, 4, 7]), (7488, [1, 1, 1, 2, 2, 4, 5, 6]), (100608/5, [1, 1, 1, 2, 2, 5, 5, 5]), (-12000, [1, 1, 1, 2, 2, 15]), (832880/9, [1, 1, 1, 2, 3, 3, 3, 8]), (355520/7, [1, 1, 1, 2, 3, 3, 4, 7]), (539392/3, [1, 1, 1, 2, 3, 3, 5, 6]), (-103000, [1, 1, 1, 2, 3, 4, 4, 6]), (365888/5, [1, 1, 1, 2, 3, 4, 5, 5]), (-390400, [1, 1, 1, 2, 3, 14]), (-87904, [1, 1, 1, 2, 4, 4, 4, 5]), (578400, [1, 1, 1, 2, 4, 13]), (-128416, [1, 1, 1, 2, 5, 12]), (59520/11, [1, 1, 1, 2, 6, 11]), (865920/7, [1, 1, 1, 2, 7, 10]), (123920, [1, 1, 1, 2, 8, 9]), (112640/9, [1, 1, 1, 3, 3, 3, 3, 7]), (-785920/27, [1, 1, 1, 3, 3, 3, 4, 6]), (123904/9, [1, 1, 1, 3, 3, 3, 5, 5]), (-166768/3, [1, 1, 1, 3, 3, 4, 4, 5]), (780800/3, [1, 1, 1, 3, 3, 13])]

def node96SumData_sector1_chunk9 : RawPoly ℕ := [(-41420/3, [1, 1, 1, 3, 4, 4, 4, 4]), (-739040/3, [1, 1, 1, 3, 4, 12]), (-212224, [1, 1, 1, 3, 5, 11]), (-36736, [1, 1, 1, 3, 6, 10]), (-705280/7, [1, 1, 1, 3, 7, 9]), (-57000, [1, 1, 1, 3, 8, 8]), (-256080, [1, 1, 1, 4, 4, 11]), (-260928, [1, 1, 1, 4, 5, 10]), (-1134400/3, [1, 1, 1, 4, 6, 9]), (-2518080/7, [1, 1, 1, 4, 7, 8]), (-66304/5, [1, 1, 1, 5, 5, 9]), (-74448, [1, 1, 1, 5, 6, 8]), (-240384/7, [1, 1, 1, 5, 7, 7]), (-418560/7, [1, 1, 1, 6, 6, 7]), (59520, [1, 1, 1, 19]), (-1296, [1, 1, 2, 2, 2, 2, 2, 2, 2, 6]), (-3728, [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]), (-5376, [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]), (-4304, [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]), (-51840, [1, 1, 2, 2, 2, 2, 2, 10]), (90560/27, [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]), (-49120/3, [1, 1, 2, 2, 2, 2, 3, 9]), (-115140, [1, 1, 2, 2, 2, 2, 4, 8]), (-478272/7, [1, 1, 2, 2, 2, 2, 5, 7])]

def node96SumData_sector1_chunk10 : RawPoly ℕ := [(-25440, [1, 1, 2, 2, 2, 2, 6, 6]), (120820, [1, 1, 2, 2, 2, 3, 3, 8]), (88800/7, [1, 1, 2, 2, 2, 3, 4, 7]), (79680, [1, 1, 2, 2, 2, 3, 5, 6]), (-68760, [1, 1, 2, 2, 2, 4, 4, 6]), (-198912/5, [1, 1, 2, 2, 2, 4, 5, 5]), (-139200, [1, 1, 2, 2, 2, 14]), (9508480/63, [1, 1, 2, 2, 3, 3, 3, 7]), (146880, [1, 1, 2, 2, 3, 3, 4, 6]), (496128/5, [1, 1, 2, 2, 3, 3, 5, 5]), (20856, [1, 1, 2, 2, 3, 4, 4, 5]), (817920, [1, 1, 2, 2, 3, 13]), (-12300, [1, 1, 2, 2, 4, 4, 4, 4]), (-446640, [1, 1, 2, 2, 4, 12]), (2237760/11, [1, 1, 2, 2, 5, 11]), (36864, [1, 1, 2, 2, 6, 10]), (583360/7, [1, 1, 2, 2, 7, 9]), (31590, [1, 1, 2, 2, 8, 8]), (2613760/27, [1, 1, 2, 3, 3, 3, 3, 6]), (482432/3, [1, 1, 2, 3, 3, 3, 4, 5]), (260/3, [1, 1, 2, 3, 3, 4, 4, 4]), (-49120/3, [1, 1, 2, 3, 3, 12]), (2913600/11, [1, 1, 2, 3, 4, 11]), (694656, [1, 1, 2, 3, 5, 10])]

def node96SumData_sector1_chunk11 : RawPoly ℕ := [(2049280/3, [1, 1, 2, 3, 6, 9]), (654480, [1, 1, 2, 3, 7, 8]), (-202176, [1, 1, 2, 4, 4, 10]), (-118656, [1, 1, 2, 4, 5, 9]), (-199920, [1, 1, 2, 4, 6, 8]), (-748800/7, [1, 1, 2, 4, 7, 7]), (680112/5, [1, 1, 2, 5, 5, 8]), (1305600/7, [1, 1, 2, 5, 6, 7]), (17280, [1, 1, 2, 6, 6, 6]), (-76800, [1, 1, 2, 18]), (94720/9, [1, 1, 3, 3, 3, 3, 3, 5]), (5120, [1, 1, 3, 3, 3, 3, 4, 4]), (713600/9, [1, 1, 3, 3, 3, 11]), (219776, [1, 1, 3, 3, 4, 10]), (317184, [1, 1, 3, 3, 5, 9]), (245040, [1, 1, 3, 3, 6, 8]), (835200/7, [1, 1, 3, 3, 7, 7]), (-141840, [1, 1, 3, 4, 4, 9]), (48600, [1, 1, 3, 4, 5, 8]), (-48000, [1, 1, 3, 4, 6, 7]), (580992/5, [1, 1, 3, 5, 5, 7]), (91520, [1, 1, 3, 5, 6, 6]), (-48960, [1, 1, 3, 17]), (-90030, [1, 1, 4, 4, 4, 8])]

def node96SumData_sector1_chunk12 : RawPoly ℕ := [(-1063296/7, [1, 1, 4, 4, 5, 7]), (-65760, [1, 1, 4, 4, 6, 6]), (-118848/5, [1, 1, 4, 5, 5, 6]), (72000, [1, 1, 4, 16]), (16896/5, [1, 1, 5, 5, 5, 5]), (-24960, [1, 1, 5, 15]), (-153600, [1, 1, 6, 14]), (2108160/7, [1, 1, 7, 13]), (-150600, [1, 1, 8, 12]), (-389120/11, [1, 1, 9, 11]), (34560, [1, 1, 10, 10]), (-2368, [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]), (-1424/3, [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]), (-24960, [1, 2, 2, 2, 2, 2, 2, 9]), (-48972, [1, 2, 2, 2, 2, 2, 3, 8]), (-563280/7, [1, 2, 2, 2, 2, 2, 4, 7]), (-42048, [1, 2, 2, 2, 2, 2, 5, 6]), (-48320/7, [1, 2, 2, 2, 2, 3, 3, 7]), (-108960, [1, 2, 2, 2, 2, 3, 4, 6]), (-90144/5, [1, 2, 2, 2, 2, 3, 5, 5]), (-100392, [1, 2, 2, 2, 2, 4, 4, 5]), (55680, [1, 2, 2, 2, 2, 13]), (395200/9, [1, 2, 2, 2, 3, 3, 3, 6]), (15808, [1, 2, 2, 2, 3, 3, 4, 5])]

def node96SumData_sector1_chunk13 : RawPoly ℕ := [(-28260, [1, 2, 2, 2, 3, 4, 4, 4]), (-395360, [1, 2, 2, 2, 3, 12]), (-951360/11, [1, 2, 2, 2, 4, 11]), (-328512, [1, 2, 2, 2, 5, 10]), (-311360, [1, 2, 2, 2, 6, 9]), (-2256180/7, [1, 2, 2, 2, 7, 8]), (298880/9, [1, 2, 2, 3, 3, 3, 3, 5]), (22680, [1, 2, 2, 3, 3, 3, 4, 4]), (3531360/11, [1, 2, 2, 3, 3, 11]), (-108288, [1, 2, 2, 3, 4, 10]), (222272, [1, 2, 2, 3, 5, 9]), (144960, [1, 2, 2, 3, 6, 8]), (678240/7, [1, 2, 2, 3, 7, 7]), (-317040, [1, 2, 2, 4, 4, 9]), (-342450, [1, 2, 2, 4, 5, 8]), (-2268960/7, [1, 2, 2, 4, 6, 7]), (-169056/5, [1, 2, 2, 5, 5, 7]), (-45792, [1, 2, 2, 5, 6, 6]), (58320, [1, 2, 2, 17]), (11520, [1, 2, 3, 3, 3, 3, 3, 4]), (2520448/9, [1, 2, 3, 3, 3, 10]), (376640, [1, 2, 3, 3, 4, 9]), (461408, [1, 2, 3, 3, 5, 8]), (3116160/7, [1, 2, 3, 3, 6, 7])]

def node96SumData_sector1_chunk14 : RawPoly ℕ := [(-49380, [1, 2, 3, 4, 4, 8]), (1330176/7, [1, 2, 3, 4, 5, 7]), (14080, [1, 2, 3, 4, 6, 6]), (149376, [1, 2, 3, 5, 5, 6]), (-63360, [1, 2, 3, 16]), (-81780, [1, 2, 4, 4, 4, 7]), (-147120, [1, 2, 4, 4, 5, 6]), (192, [1, 2, 4, 5, 5, 5]), (33600, [1, 2, 4, 15]), (-195840, [1, 2, 5, 14]), (409920, [1, 2, 6, 13]), (-2329440/7, [1, 2, 7, 12]), (1340640/11, [1, 2, 8, 11]), (-20480, [1, 2, 9, 10]), (657920/9, [1, 3, 3, 3, 3, 9]), (1005280/9, [1, 3, 3, 3, 4, 8]), (7808000/63, [1, 3, 3, 3, 5, 7]), (732160/9, [1, 3, 3, 3, 6, 6]), (233360/7, [1, 3, 3, 4, 4, 7]), (161216, [1, 3, 3, 4, 5, 6]), (111616/5, [1, 3, 3, 5, 5, 5]), (90240, [1, 3, 3, 15]), (-25120, [1, 3, 4, 4, 4, 6]), (105216/5, [1, 3, 4, 4, 5, 5])]

def node96SumData_sector1_chunk15 : RawPoly ℕ := [(13440, [1, 3, 4, 14]), (627456, [1, 3, 5, 13]), (142080, [1, 3, 6, 12]), (36384000/77, [1, 3, 7, 11]), (559488, [1, 3, 8, 10]), (302720, [1, 3, 9, 9]), (-15750, [1, 4, 4, 4, 4, 5]), (88920, [1, 4, 4, 13]), (-261936, [1, 4, 5, 12]), (-890880/11, [1, 4, 6, 11]), (-132480, [1, 4, 7, 10]), (-182720, [1, 4, 8, 9]), (4484736/55, [1, 5, 5, 11]), (130560, [1, 5, 6, 10]), (980480/7, [1, 5, 7, 9]), (68616, [1, 5, 8, 8]), (39040, [1, 6, 6, 9]), (514560/7, [1, 6, 7, 8]), (82560/7, [1, 7, 7, 7]), (-41280, [1, 21]), (-336, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]), (-3024, [2, 2, 2, 2, 2, 2, 2, 8]), (-111600/7, [2, 2, 2, 2, 2, 2, 3, 7]), (-10128, [2, 2, 2, 2, 2, 2, 4, 6])]

def node96SumData_sector1_chunk16 : RawPoly ℕ := [(-3024, [2, 2, 2, 2, 2, 2, 5, 5]), (-22576, [2, 2, 2, 2, 2, 3, 3, 6]), (-37128, [2, 2, 2, 2, 2, 3, 4, 5]), (-5088, [2, 2, 2, 2, 2, 4, 4, 4]), (-45240, [2, 2, 2, 2, 2, 12]), (-18080/3, [2, 2, 2, 2, 3, 3, 3, 5]), (-13000, [2, 2, 2, 2, 3, 3, 4, 4]), (-373440/11, [2, 2, 2, 2, 3, 11]), (-166800, [2, 2, 2, 2, 4, 10]), (-143424, [2, 2, 2, 2, 5, 9]), (-132540, [2, 2, 2, 2, 6, 8]), (-533280/7, [2, 2, 2, 2, 7, 7]), (52160/27, [2, 2, 2, 3, 3, 3, 3, 4]), (-75456, [2, 2, 2, 3, 3, 10]), (-654400/3, [2, 2, 2, 3, 4, 9]), (-126792, [2, 2, 2, 3, 5, 8]), (-997440/7, [2, 2, 2, 3, 6, 7]), (-125940, [2, 2, 2, 4, 4, 8]), (-1487904/7, [2, 2, 2, 4, 5, 7]), (-77760, [2, 2, 2, 4, 6, 6]), (-249792/5, [2, 2, 2, 5, 5, 6]), (11520, [2, 2, 2, 16]), (160640/3, [2, 2, 3, 3, 3, 9]), (3300, [2, 2, 3, 3, 4, 8])]

def node96SumData_sector1_chunk17 : RawPoly ℕ := [(326528/7, [2, 2, 3, 3, 5, 7]), (9280, [2, 2, 3, 3, 6, 6]), (-563880/7, [2, 2, 3, 4, 4, 7]), (-118560, [2, 2, 3, 4, 5, 6]), (1536/5, [2, 2, 3, 5, 5, 5]), (-79680, [2, 2, 3, 15]), (-32100, [2, 2, 4, 4, 4, 6]), (-361512/5, [2, 2, 4, 4, 5, 5]), (-218880, [2, 2, 4, 14]), (-78336, [2, 2, 5, 13]), (-429120, [2, 2, 6, 12]), (-2640960/11, [2, 2, 7, 11]), (-436284, [2, 2, 8, 10]), (-223200, [2, 2, 9, 9]), (281600/9, [2, 3, 3, 3, 3, 8]), (1163200/21, [2, 3, 3, 3, 4, 7]), (677120/9, [2, 3, 3, 3, 5, 6]), (-3880, [2, 3, 3, 4, 4, 6]), (228928/5, [2, 3, 3, 4, 5, 5]), (-12800, [2, 3, 3, 14]), (-35956, [2, 3, 4, 4, 4, 5]), (212640, [2, 3, 4, 13]), (-164416, [2, 3, 5, 12]), (1973760/11, [2, 3, 6, 11])]

def node96SumData_sector1_chunk18 : RawPoly ℕ := [(531840/7, [2, 3, 7, 10]), (121760, [2, 3, 8, 9]), (-2460, [2, 4, 4, 4, 4, 4]), (-241140, [2, 4, 4, 12]), (-125568, [2, 4, 5, 11]), (-307488, [2, 4, 6, 10]), (-324480, [2, 4, 7, 9]), (-158400, [2, 4, 8, 8]), (-337536/5, [2, 5, 5, 10]), (-126976, [2, 5, 6, 9]), (-841392/7, [2, 5, 7, 8]), (-68640, [2, 6, 6, 8]), (-462720/7, [2, 6, 7, 7]), (74880, [2, 20]), (35840/9, [3, 3, 3, 3, 3, 7]), (578560/27, [3, 3, 3, 3, 4, 6]), (81920/9, [3, 3, 3, 3, 5, 5]), (250160/9, [3, 3, 3, 4, 4, 5]), (792320/9, [3, 3, 3, 13]), (-2380/3, [3, 3, 4, 4, 4, 4]), (52640/3, [3, 3, 4, 12]), (2045312/11, [3, 3, 5, 11]), (192384, [3, 3, 6, 10]), (1464320/7, [3, 3, 7, 9])]

def node96SumData_sector1_chunk19 : RawPoly ℕ := [(101040, [3, 3, 8, 8]), (304320/11, [3, 4, 4, 11]), (90432, [3, 4, 5, 10]), (184960/3, [3, 4, 6, 9]), (439680/7, [3, 4, 7, 8]), (458752/5, [3, 5, 5, 9]), (147936, [3, 5, 6, 8]), (495744/7, [3, 5, 7, 7]), (418560/7, [3, 6, 6, 7]), (-72960, [3, 19]), (-35268, [4, 4, 4, 10]), (-75520, [4, 4, 5, 9]), (-67440, [4, 4, 6, 8]), (-226080/7, [4, 4, 7, 7]), (-86328/5, [4, 5, 5, 8]), (-311424/7, [4, 5, 6, 7]), (-8640, [4, 6, 6, 6]), (38400, [4, 18]), (24192/5, [5, 5, 5, 7]), (22656/5, [5, 5, 6, 6]), (-8640, [5, 17]), (-28800, [8, 14]), (78080, [9, 13]), (-83040, [10, 12])]

def node96SumData_sector1_chunk20 : RawPoly ℕ := [(368640/11, [11, 11])]

def node96SumData_sector1 : RawPoly ℕ := [node96SumData_sector1_chunk0, node96SumData_sector1_chunk1, node96SumData_sector1_chunk2, node96SumData_sector1_chunk3, node96SumData_sector1_chunk4, node96SumData_sector1_chunk5, node96SumData_sector1_chunk6, node96SumData_sector1_chunk7, node96SumData_sector1_chunk8, node96SumData_sector1_chunk9, node96SumData_sector1_chunk10, node96SumData_sector1_chunk11, node96SumData_sector1_chunk12, node96SumData_sector1_chunk13, node96SumData_sector1_chunk14, node96SumData_sector1_chunk15, node96SumData_sector1_chunk16, node96SumData_sector1_chunk17, node96SumData_sector1_chunk18, node96SumData_sector1_chunk19, node96SumData_sector1_chunk20].flatten

def node96SumData_sector2 : RawPoly ℕ := [].flatten

def node96SumData : SectorVector := [(-2, node96SumData_sector0), (0, node96SumData_sector1), (2, node96SumData_sector2)]

def node96OutputGroups : List (List SectorVector) := [node96SumGroup0Outputs, node96SumGroup1Outputs, node96SumGroup2Outputs]

theorem node96SumData_check : zipMany 100000 [node96SumGroup0Data, node96SumGroup1Data, node96SumGroup2Data] = node96SumData := by decide +kernel

theorem node96SumData_value : evaluate node96SumData =
    ((node96OutputGroups.flatten).map evaluate).sum := by
  rw [← node96SumData_check, evaluate_zipMany]
  simp only [node96OutputGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, add_zero,
    node96SumGroup0_value, node96SumGroup1_value, node96SumGroup2_value]

theorem node96Outputs_identity : node96Pieces.map Prod.snd = node96OutputGroups.flatten := rfl

theorem node96Pieces_sum : evaluate (node96Pieces.flatMap Prod.snd) = evaluate node96SumData := by
  rw [evaluate_piece_outputs, node96Outputs_identity, ← node96SumData_value]
end VOA.Classification.COne.OrbC2h
