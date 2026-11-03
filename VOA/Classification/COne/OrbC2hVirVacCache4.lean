import VOA.Classification.COne.OrbC2hVirVacCache3
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac64Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 4, 4]), (2, [1, 1, 2, 2, 3, 4]), (4, [1, 1, 2, 9]), (8, [1, 1, 4, 7]), (1, [1, 2, 2, 2, 3, 3]), (3, [1, 2, 2, 8]), (10, [1, 2, 3, 7]), (7, [1, 2, 4, 6]), (4, [1, 3, 4, 5]), (2, [1, 4, 4, 4]), (36, [1, 12]), (6, [2, 2, 3, 6]), (4, [2, 3, 3, 5]), (2, [2, 3, 4, 4]), (24, [2, 11]), (14, [3, 10]), (10, [4, 9]), (6, [5, 8]), (10, [6, 7])]

def vVac64Data : SectorVector := [(0, vVac64Data_sector0)]

theorem vVac64_check : neutralDirectS omR (-(2:ℤ)) vVac32Data = vVac64Data := by decide +kernel

theorem vVac64_value : evaluate vVac64Data = virWord (V2m 4 four_ge_one) [2, 4, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [4, 4] _ _ _ vVac32_value vVac64_check

def vVac65Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 9]), (1, [1, 2, 2, 8]), (1, [1, 2, 3, 7]), (1, [1, 2, 4, 6]), (1/2, [1, 2, 5, 5]), (9, [1, 12]), (8, [2, 11]), (7, [3, 10]), (7, [4, 9]), (7, [5, 8]), (7, [6, 7])]

def vVac65Data : SectorVector := [(0, vVac65Data_sector0)]

theorem vVac65_check : neutralDirectS omR (-(2:ℤ)) vVac33Data = vVac65Data := by decide +kernel

theorem vVac65_value : evaluate vVac65Data = virWord (V2m 4 four_ge_one) [2, 9] (evaluate vacuumData) :=
  virWord_cached_step 2 [9] _ _ _ vVac33_value vVac65_check

def vVac66Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 4]), (1, [1, 1, 2, 2, 3, 4]), (1, [1, 1, 2, 3, 3, 3]), (8, [1, 1, 3, 8]), (3, [1, 1, 4, 7]), (1/4, [1, 2, 2, 2, 2, 4]), (1, [1, 2, 2, 2, 3, 3]), (4, [1, 2, 2, 8]), (9, [1, 2, 3, 7]), (2, [1, 2, 4, 6]), (4, [1, 3, 3, 6]), (3, [1, 3, 4, 5]), (32, [1, 12]), (1/4, [2, 2, 2, 2, 2, 3]), (3, [2, 2, 2, 7]), (4, [2, 2, 3, 6]), (1, [2, 2, 4, 5]), (1, [2, 3, 3, 5]), (21, [2, 11]), (12, [3, 10]), (5, [4, 9]), (8, [5, 8]), (12, [6, 7])]

def vVac66Data : SectorVector := [(0, vVac66Data_sector0)]

theorem vVac66_check : neutralDirectS omR (-(3:ℤ)) vVac20Data = vVac66Data := by decide +kernel

theorem vVac66_value : evaluate vVac66Data = virWord (V2m 4 four_ge_one) [3, 3, 4] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 4] _ _ _ vVac20_value vVac66_check

def vVac67Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 8]), (1/2, [1, 2, 2, 8]), (1, [1, 2, 3, 7]), (1, [1, 3, 3, 6]), (1, [1, 3, 4, 5]), (8, [1, 12]), (1/2, [2, 2, 2, 7]), (1/2, [2, 2, 3, 6]), (1/2, [2, 2, 4, 5]), (7, [2, 11]), (6, [3, 10]), (5, [4, 9]), (5, [5, 8]), (5, [6, 7])]

def vVac67Data : SectorVector := [(0, vVac67Data_sector0)]

theorem vVac67_check : neutralDirectS omR (-(3:ℤ)) vVac21Data = vVac67Data := by decide +kernel

theorem vVac67_value : evaluate vVac67Data = virWord (V2m 4 four_ge_one) [3, 8] (evaluate vacuumData) :=
  virWord_cached_step 3 [8] _ _ _ vVac21_value vVac67_check

def vVac68Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 7]), (1, [1, 2, 3, 7]), (1, [1, 2, 4, 6]), (1, [1, 3, 4, 5]), (1/2, [1, 4, 4, 4]), (7, [1, 12]), (1, [2, 2, 3, 6]), (1, [2, 3, 3, 5]), (1/2, [2, 3, 4, 4]), (6, [2, 11]), (5, [3, 10]), (4, [4, 9]), (3, [5, 8]), (3, [6, 7])]

def vVac68Data : SectorVector := [(0, vVac68Data_sector0)]

theorem vVac68_check : neutralDirectS omR (-(4:ℤ)) vVac17Data = vVac68Data := by decide +kernel

theorem vVac68_value : evaluate vVac68Data = virWord (V2m 4 four_ge_one) [4, 7] (evaluate vacuumData) :=
  virWord_cached_step 4 [7] _ _ _ vVac17_value vVac68_check

def vVac69Data_sector0 : RawPoly ℕ := [(1, [1, 1, 5, 6]), (1, [1, 2, 4, 6]), (1, [1, 2, 5, 5]), (1/2, [1, 3, 3, 6]), (1, [1, 3, 4, 5]), (6, [1, 12]), (1, [2, 2, 4, 5]), (1/2, [2, 3, 3, 5]), (1, [2, 3, 4, 4]), (5, [2, 11]), (1/2, [3, 3, 3, 4]), (4, [3, 10]), (3, [4, 9]), (2, [5, 8]), (1, [6, 7])]

def vVac69Data : SectorVector := [(0, vVac69Data_sector0)]

theorem vVac69_check : neutralDirectS omR (-(5:ℤ)) vVac10Data = vVac69Data := by decide +kernel

theorem vVac69_value : evaluate vVac69Data = virWord (V2m 4 four_ge_one) [5, 6] (evaluate vacuumData) :=
  virWord_cached_step 5 [6] _ _ _ vVac10_value vVac69_check

def vVac70Data_sector0 : RawPoly ℕ := [(1, [1, 12]), (1, [2, 11]), (1, [3, 10]), (1, [4, 9]), (1, [5, 8]), (1, [6, 7])]

def vVac70Data : SectorVector := [(0, vVac70Data_sector0)]

theorem vVac70_check : neutralDirectS omR (-(12:ℤ)) vacuumData = vVac70Data := by decide +kernel

theorem vVac70_value : evaluate vVac70Data = virWord (V2m 4 four_ge_one) [12] (evaluate vacuumData) :=
  virWord_cached_step 12 [] _ _ _ (by rfl) vVac70_check

def vVac71Data_sector0 : RawPoly ℕ := [(1/128, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (21/32, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (105/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (245/16, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (525/8, [1, 1, 1, 1, 1, 1, 1, 7]), (1575/8, [1, 1, 1, 1, 1, 1, 3, 5]), (105, [1, 1, 1, 1, 1, 3, 3, 3]), (2205/4, [1, 1, 1, 1, 1, 9]), (2205/2, [1, 1, 1, 1, 3, 7]), (1827/4, [1, 1, 1, 1, 5, 5]), (1995/2, [1, 1, 1, 3, 3, 5]), (6615/2, [1, 1, 1, 11]), (140, [1, 1, 3, 3, 3, 3]), (8085/2, [1, 1, 3, 9]), (3150, [1, 1, 5, 7]), (1785, [1, 3, 3, 7]), (1512, [1, 3, 5, 5]), (10395, [1, 13]), (315, [3, 3, 3, 5]), (5670, [3, 11]), (4725, [5, 9]), (2250, [7, 7])]

def vVac71Data : SectorVector := [(0, vVac71Data_sector0)]

theorem vVac71_check : neutralDirectS omR (-(1:ℤ)) vVac40Data = vVac71Data := by decide +kernel

theorem vVac71_value : evaluate vVac71Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 1, 1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 1, 1, 1] _ _ _ vVac40_value vVac71_check

def vVac72Data_sector0_chunk0 : RawPoly ℕ := [(1/32, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1/64, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (15/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (5/8, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (25/16, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (5/8, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (75/4, [1, 1, 1, 1, 1, 1, 1, 7]), (10, [1, 1, 1, 1, 1, 1, 2, 6]), (165/4, [1, 1, 1, 1, 1, 1, 3, 5]), (5, [1, 1, 1, 1, 1, 1, 4, 4]), (15/4, [1, 1, 1, 1, 1, 2, 2, 5]), (15, [1, 1, 1, 1, 1, 2, 3, 4]), (35/2, [1, 1, 1, 1, 1, 3, 3, 3]), (525/2, [1, 1, 1, 1, 1, 9]), (5, [1, 1, 1, 1, 2, 2, 3, 3]), (120, [1, 1, 1, 1, 2, 8]), (825/2, [1, 1, 1, 1, 3, 7]), (120, [1, 1, 1, 1, 4, 6]), (315/2, [1, 1, 1, 1, 5, 5]), (75/4, [1, 1, 1, 2, 2, 7]), (120, [1, 1, 1, 2, 3, 6]), (60, [1, 1, 1, 2, 4, 5]), (585/2, [1, 1, 1, 3, 3, 5]), (60, [1, 1, 1, 3, 4, 4])]

def vVac72Data_sector0_chunk1 : RawPoly ℕ := [(4725/2, [1, 1, 1, 11]), (105/4, [1, 1, 2, 2, 3, 5]), (50, [1, 1, 2, 3, 3, 4]), (960, [1, 1, 2, 10]), (35, [1, 1, 3, 3, 3, 3]), (4935/2, [1, 1, 3, 9]), (960, [1, 1, 4, 8]), (1800, [1, 1, 5, 7]), (480, [1, 1, 6, 6]), (5, [1, 2, 2, 3, 3, 3]), (105/2, [1, 2, 2, 9]), (480, [1, 2, 3, 8]), (150, [1, 2, 4, 7]), (240, [1, 2, 5, 6]), (885, [1, 3, 3, 7]), (480, [1, 3, 4, 6]), (702, [1, 3, 5, 5]), (120, [1, 4, 4, 5]), (10395, [1, 13]), (30, [2, 2, 3, 7]), (27/2, [2, 2, 5, 5]), (80, [2, 3, 3, 6]), (90, [2, 3, 4, 5]), (3840, [2, 12])]

def vVac72Data_sector0_chunk2 : RawPoly ℕ := [(135, [3, 3, 3, 5]), (40, [3, 3, 4, 4]), (5670, [3, 11]), (3840, [4, 10]), (4725, [5, 9]), (3840, [6, 8]), (2250, [7, 7])]

def vVac72Data_sector0 : RawPoly ℕ := [vVac72Data_sector0_chunk0, vVac72Data_sector0_chunk1, vVac72Data_sector0_chunk2].flatten

def vVac72Data : SectorVector := [(0, vVac72Data_sector0)]

theorem vVac72_check : neutralDirectS omR (-(1:ℤ)) vVac41Data = vVac72Data := by decide +kernel

theorem vVac72_value : evaluate vVac72Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 1, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 1, 3] _ _ _ vVac41_value vVac72_check

def vVac73Data_sector0_chunk0 : RawPoly ℕ := [(1/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (1/8, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (33/16, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (5/2, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (5, [1, 1, 1, 1, 1, 1, 1, 7]), (26, [1, 1, 1, 1, 1, 1, 2, 6]), (4, [1, 1, 1, 1, 1, 1, 3, 5]), (13, [1, 1, 1, 1, 1, 1, 4, 4]), (15, [1, 1, 1, 1, 1, 2, 2, 5]), (99/2, [1, 1, 1, 1, 1, 2, 3, 4]), (105, [1, 1, 1, 1, 1, 9]), (20, [1, 1, 1, 1, 2, 2, 3, 3]), (228, [1, 1, 1, 1, 2, 8]), (90, [1, 1, 1, 1, 3, 7]), (228, [1, 1, 1, 1, 4, 6]), (21, [1, 1, 1, 1, 5, 5]), (75, [1, 1, 1, 2, 2, 7]), (312, [1, 1, 1, 2, 3, 6]), (198, [1, 1, 1, 2, 4, 5]), (22, [1, 1, 1, 3, 3, 5]), (156, [1, 1, 1, 3, 4, 4]), (1260, [1, 1, 1, 11]), (105, [1, 1, 2, 2, 3, 5]), (165, [1, 1, 2, 3, 3, 4])]

def vVac73Data_sector0_chunk1 : RawPoly ℕ := [(1152, [1, 1, 2, 10]), (840, [1, 1, 3, 9]), (1152, [1, 1, 4, 8]), (390, [1, 1, 5, 7]), (576, [1, 1, 6, 6]), (20, [1, 2, 2, 3, 3, 3]), (210, [1, 2, 2, 9]), (912, [1, 2, 3, 8]), (495, [1, 2, 4, 7]), (624, [1, 2, 5, 6]), (160, [1, 3, 3, 7]), (912, [1, 3, 4, 6]), (78, [1, 3, 5, 5]), (312, [1, 4, 4, 5]), (6930, [1, 13]), (120, [2, 2, 3, 7]), (54, [2, 2, 5, 5]), (208, [2, 3, 3, 6]), (297, [2, 3, 4, 5]), (1920, [2, 12]), (8, [3, 3, 3, 5]), (104, [3, 3, 4, 4]), (2520, [3, 11]), (1920, [4, 10])]

def vVac73Data_sector0_chunk2 : RawPoly ℕ := [(1470, [5, 9]), (1920, [6, 8]), (600, [7, 7])]

def vVac73Data_sector0 : RawPoly ℕ := [vVac73Data_sector0_chunk0, vVac73Data_sector0_chunk1, vVac73Data_sector0_chunk2].flatten

def vVac73Data : SectorVector := [(0, vVac73Data_sector0)]

theorem vVac73_check : neutralDirectS omR (-(1:ℤ)) vVac42Data = vVac73Data := by decide +kernel

theorem vVac73_value : evaluate vVac73Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 2, 2] _ _ _ vVac42_value vVac73_check

def vVac74Data_sector0_chunk0 : RawPoly ℕ := [(1/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 5]), (1/16, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (1/32, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (5/2, [1, 1, 1, 1, 1, 1, 1, 7]), (2, [1, 1, 1, 1, 1, 1, 2, 6]), (7/2, [1, 1, 1, 1, 1, 1, 3, 5]), (1, [1, 1, 1, 1, 1, 1, 4, 4]), (3/2, [1, 1, 1, 1, 1, 2, 3, 4]), (3/4, [1, 1, 1, 1, 1, 3, 3, 3]), (105/2, [1, 1, 1, 1, 1, 9]), (36, [1, 1, 1, 1, 2, 8]), (135/2, [1, 1, 1, 1, 3, 7]), (36, [1, 1, 1, 1, 4, 6]), (24, [1, 1, 1, 1, 5, 5]), (24, [1, 1, 1, 2, 3, 6]), (6, [1, 1, 1, 2, 4, 5]), (32, [1, 1, 1, 3, 3, 5]), (12, [1, 1, 1, 3, 4, 4]), (630, [1, 1, 1, 11]), (5, [1, 1, 2, 3, 3, 4]), (384, [1, 1, 2, 10]), (5/2, [1, 1, 3, 3, 3, 3]), (630, [1, 1, 3, 9]), (384, [1, 1, 4, 8])]

def vVac74Data_sector0_chunk1 : RawPoly ℕ := [(465, [1, 1, 5, 7]), (192, [1, 1, 6, 6]), (144, [1, 2, 3, 8]), (15, [1, 2, 4, 7]), (48, [1, 2, 5, 6]), (355/2, [1, 3, 3, 7]), (144, [1, 3, 4, 6]), (129, [1, 3, 5, 5]), (24, [1, 4, 4, 5]), (3465, [1, 13]), (16, [2, 3, 3, 6]), (9, [2, 3, 4, 5]), (1920, [2, 12]), (41/2, [3, 3, 3, 5]), (8, [3, 3, 4, 4]), (2205, [3, 11]), (1920, [4, 10]), (1995, [5, 9]), (1920, [6, 8]), (975, [7, 7])]

def vVac74Data_sector0 : RawPoly ℕ := [vVac74Data_sector0_chunk0, vVac74Data_sector0_chunk1].flatten

def vVac74Data : SectorVector := [(0, vVac74Data_sector0)]

theorem vVac74_check : neutralDirectS omR (-(1:ℤ)) vVac43Data = vVac74Data := by decide +kernel

theorem vVac74_value : evaluate vVac74Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 5] _ _ _ vVac43_value vVac74_check

def vVac75Data_sector0_chunk0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 1, 2, 4]), (1/8, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (1/2, [1, 1, 1, 1, 1, 1, 1, 7]), (27/8, [1, 1, 1, 1, 1, 1, 2, 6]), (1/4, [1, 1, 1, 1, 1, 1, 3, 5]), (13/8, [1, 1, 1, 1, 1, 1, 4, 4]), (9/4, [1, 1, 1, 1, 1, 2, 2, 5]), (6, [1, 1, 1, 1, 1, 2, 3, 4]), (21, [1, 1, 1, 1, 1, 9]), (9/4, [1, 1, 1, 1, 2, 2, 3, 3]), (99/2, [1, 1, 1, 1, 2, 8]), (33/2, [1, 1, 1, 1, 3, 7]), (93/2, [1, 1, 1, 1, 4, 6]), (9/2, [1, 1, 1, 1, 5, 5]), (45/2, [1, 1, 1, 2, 2, 7]), (129/2, [1, 1, 1, 2, 3, 6]), (48, [1, 1, 1, 2, 4, 5]), (3, [1, 1, 1, 3, 3, 5]), (63/2, [1, 1, 1, 3, 4, 4]), (378, [1, 1, 1, 11]), (51/2, [1, 1, 2, 2, 3, 5]), (34, [1, 1, 2, 3, 3, 4]), (408, [1, 1, 2, 10]), (273, [1, 1, 3, 9])]

def vVac75Data_sector0_chunk1 : RawPoly ℕ := [(372, [1, 1, 4, 8]), (165, [1, 1, 5, 7]), (180, [1, 1, 6, 6]), (4, [1, 2, 2, 3, 3, 3]), (105, [1, 2, 2, 9]), (294, [1, 2, 3, 8]), (210, [1, 2, 4, 7]), (225, [1, 2, 5, 6]), (46, [1, 3, 3, 7]), (282, [1, 3, 4, 6]), (24, [1, 3, 5, 5]), (111, [1, 4, 4, 5]), (2772, [1, 13]), (60, [2, 2, 3, 7]), (27, [2, 2, 5, 5]), (75, [2, 3, 3, 6]), (126, [2, 3, 4, 5]), (1440, [2, 12]), (2, [3, 3, 3, 5]), (37, [3, 3, 4, 4]), (1386, [3, 11]), (1248, [4, 10]), (1092, [5, 9]), (1152, [6, 8])]

def vVac75Data_sector0_chunk2 : RawPoly ℕ := [(510, [7, 7])]

def vVac75Data_sector0 : RawPoly ℕ := [vVac75Data_sector0_chunk0, vVac75Data_sector0_chunk1, vVac75Data_sector0_chunk2].flatten

def vVac75Data : SectorVector := [(0, vVac75Data_sector0)]

theorem vVac75_check : neutralDirectS omR (-(1:ℤ)) vVac44Data = vVac75Data := by decide +kernel

theorem vVac75_value : evaluate vVac75Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 2, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 2, 4] _ _ _ vVac44_value vVac75_check

def vVac76Data_sector0_chunk0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 1, 3, 3]), (1/8, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (3/8, [1, 1, 1, 1, 1, 1, 1, 7]), (1/32, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (1/4, [1, 1, 1, 1, 1, 1, 2, 6]), (37/8, [1, 1, 1, 1, 1, 1, 3, 5]), (9/4, [1, 1, 1, 1, 1, 2, 2, 5]), (3, [1, 1, 1, 1, 1, 2, 3, 4]), (3, [1, 1, 1, 1, 1, 3, 3, 3]), (63/4, [1, 1, 1, 1, 1, 9]), (3/2, [1, 1, 1, 1, 2, 2, 2, 4]), (9/4, [1, 1, 1, 1, 2, 2, 3, 3]), (9, [1, 1, 1, 1, 2, 8]), (111/2, [1, 1, 1, 1, 3, 7]), (3, [1, 1, 1, 1, 4, 6]), (117/4, [1, 1, 1, 1, 5, 5]), (3/8, [1, 1, 1, 2, 2, 2, 2, 3]), (45/2, [1, 1, 1, 2, 2, 7]), (27, [1, 1, 1, 2, 3, 6]), (36, [1, 1, 1, 2, 4, 5]), (135/2, [1, 1, 1, 3, 3, 5]), (12, [1, 1, 1, 3, 4, 4]), (567/2, [1, 1, 1, 11]), (12, [1, 1, 2, 2, 2, 6])]

def vVac76Data_sector0_chunk1 : RawPoly ℕ := [(51/2, [1, 1, 2, 2, 3, 5]), (18, [1, 1, 2, 2, 4, 4]), (24, [1, 1, 2, 3, 3, 4]), (144, [1, 1, 2, 10]), (10, [1, 1, 3, 3, 3, 3]), (777/2, [1, 1, 3, 9]), (72, [1, 1, 4, 8]), (360, [1, 1, 5, 7]), (24, [1, 1, 6, 6]), (3/4, [1, 2, 2, 2, 2, 5]), (6, [1, 2, 2, 2, 3, 4]), (4, [1, 2, 2, 3, 3, 3]), (105, [1, 2, 2, 9]), (132, [1, 2, 3, 8]), (180, [1, 2, 4, 7]), (150, [1, 2, 5, 6]), (237, [1, 3, 3, 7]), (108, [1, 3, 4, 6]), (228, [1, 3, 5, 5]), (72, [1, 4, 4, 5]), (2079, [1, 13]), (1/4, [2, 2, 2, 2, 3, 3]), (48, [2, 2, 2, 8]), (60, [2, 2, 3, 7])]

def vVac76Data_sector0_chunk2 : RawPoly ℕ := [(144, [2, 2, 4, 6]), (27, [2, 2, 5, 5]), (50, [2, 3, 3, 6]), (108, [2, 3, 4, 5]), (48, [2, 4, 4, 4]), (960, [2, 12]), (55, [3, 3, 3, 5]), (24, [3, 3, 4, 4]), (882, [3, 11]), (576, [4, 10]), (609, [5, 9]), (384, [6, 8]), (270, [7, 7])]

def vVac76Data_sector0 : RawPoly ℕ := [vVac76Data_sector0_chunk0, vVac76Data_sector0_chunk1, vVac76Data_sector0_chunk2].flatten

def vVac76Data : SectorVector := [(0, vVac76Data_sector0)]

theorem vVac76_check : neutralDirectS omR (-(1:ℤ)) vVac45Data = vVac76Data := by decide +kernel

theorem vVac76_value : evaluate vVac76Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 3, 3] _ _ _ vVac45_value vVac76_check

def vVac77Data_sector0_chunk0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 7]), (1/8, [1, 1, 1, 1, 1, 1, 2, 6]), (1/8, [1, 1, 1, 1, 1, 1, 3, 5]), (1/16, [1, 1, 1, 1, 1, 1, 4, 4]), (21/4, [1, 1, 1, 1, 1, 9]), (9/2, [1, 1, 1, 1, 2, 8]), (6, [1, 1, 1, 1, 3, 7]), (9/2, [1, 1, 1, 1, 4, 6]), (9/4, [1, 1, 1, 1, 5, 5]), (3/2, [1, 1, 1, 2, 3, 6]), (3/2, [1, 1, 1, 3, 3, 5]), (3/4, [1, 1, 1, 3, 4, 4]), (189/2, [1, 1, 1, 11]), (72, [1, 1, 2, 10]), (189/2, [1, 1, 3, 9]), (72, [1, 1, 4, 8]), (75, [1, 1, 5, 7]), (36, [1, 1, 6, 6]), (18, [1, 2, 3, 8]), (3, [1, 2, 5, 6]), (19, [1, 3, 3, 7]), (18, [1, 3, 4, 6]), (12, [1, 3, 5, 5]), (3/2, [1, 4, 4, 5])]

def vVac77Data_sector0_chunk1 : RawPoly ℕ := [(693, [1, 13]), (1, [2, 3, 3, 6]), (480, [2, 12]), (1, [3, 3, 3, 5]), (1/2, [3, 3, 4, 4]), (504, [3, 11]), (480, [4, 10]), (483, [5, 9]), (480, [6, 8]), (240, [7, 7])]

def vVac77Data_sector0 : RawPoly ℕ := [vVac77Data_sector0_chunk0, vVac77Data_sector0_chunk1].flatten

def vVac77Data : SectorVector := [(0, vVac77Data_sector0)]

theorem vVac77_check : neutralDirectS omR (-(1:ℤ)) vVac46Data = vVac77Data := by decide +kernel

theorem vVac77_value : evaluate vVac77Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 7] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 7] _ _ _ vVac46_value vVac77_check

def vVac78Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 1, 2, 2, 3]), (1/8, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (3/2, [1, 1, 1, 1, 1, 1, 2, 6]), (1/2, [1, 1, 1, 1, 1, 1, 3, 5]), (17/4, [1, 1, 1, 1, 1, 2, 2, 5]), (19/4, [1, 1, 1, 1, 1, 2, 3, 4]), (9/2, [1, 1, 1, 1, 1, 9]), (33/8, [1, 1, 1, 1, 2, 2, 2, 4]), (4, [1, 1, 1, 1, 2, 2, 3, 3]), (77/2, [1, 1, 1, 1, 2, 8]), (11, [1, 1, 1, 1, 3, 7]), (27/2, [1, 1, 1, 1, 4, 6]), (7, [1, 1, 1, 1, 5, 5]), (3/2, [1, 1, 1, 2, 2, 2, 2, 3]), (40, [1, 1, 1, 2, 2, 7]), (46, [1, 1, 1, 2, 3, 6]), (53, [1, 1, 1, 2, 4, 5]), (6, [1, 1, 1, 3, 3, 5]), (14, [1, 1, 1, 3, 4, 4]), (162, [1, 1, 1, 11]), (18, [1, 1, 2, 2, 2, 6]), (37, [1, 1, 2, 2, 3, 5]), (27, [1, 1, 2, 2, 4, 4]), (30, [1, 1, 2, 3, 3, 4])]

def vVac78Data_sector0_chunk1 : RawPoly ℕ := [(368, [1, 1, 2, 10]), (134, [1, 1, 3, 9]), (200, [1, 1, 4, 8]), (142, [1, 1, 5, 7]), (72, [1, 1, 6, 6]), (3, [1, 2, 2, 2, 2, 5]), (33/2, [1, 2, 2, 2, 3, 4]), (6, [1, 2, 2, 3, 3, 3]), (175, [1, 2, 2, 9]), (226, [1, 2, 3, 8]), (245, [1, 2, 4, 7]), (188, [1, 2, 5, 6]), (44, [1, 3, 3, 7]), (126, [1, 3, 4, 6]), (40, [1, 3, 5, 5]), (76, [1, 4, 4, 5]), (1782, [1, 13]), (1, [2, 2, 2, 2, 3, 3]), (12, [2, 2, 2, 8]), (50, [2, 2, 3, 7]), (36, [2, 2, 4, 6]), (15, [2, 2, 5, 5]), (36, [2, 3, 3, 6]), (67, [2, 3, 4, 5])]

def vVac78Data_sector0_chunk2 : RawPoly ℕ := [(12, [2, 4, 4, 4]), (800, [2, 12]), (4, [3, 3, 3, 5]), (12, [3, 3, 4, 4]), (576, [3, 11]), (608, [4, 10]), (502, [5, 9]), (512, [6, 8]), (260, [7, 7])]

def vVac78Data_sector0 : RawPoly ℕ := [vVac78Data_sector0_chunk0, vVac78Data_sector0_chunk1, vVac78Data_sector0_chunk2].flatten

def vVac78Data : SectorVector := [(0, vVac78Data_sector0)]

theorem vVac78_check : neutralDirectS omR (-(1:ℤ)) vVac47Data = vVac78Data := by decide +kernel

theorem vVac78_value : evaluate vVac78Data = virWord (V2m 4 four_ge_one) [1, 1, 2, 2, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 2, 2, 3] _ _ _ vVac47_value vVac78_check

def vVac79Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 2, 6]), (1/4, [1, 1, 1, 1, 1, 2, 2, 5]), (1/4, [1, 1, 1, 1, 1, 2, 3, 4]), (3/2, [1, 1, 1, 1, 1, 9]), (29/4, [1, 1, 1, 1, 2, 8]), (1, [1, 1, 1, 1, 3, 7]), (3, [1, 1, 1, 1, 4, 6]), (1/2, [1, 1, 1, 1, 5, 5]), (5, [1, 1, 1, 2, 2, 7]), (7, [1, 1, 1, 2, 3, 6]), (7, [1, 1, 1, 2, 4, 5]), (2, [1, 1, 1, 3, 4, 4]), (54, [1, 1, 1, 11]), (2, [1, 1, 2, 2, 3, 5]), (2, [1, 1, 2, 3, 3, 4]), (88, [1, 1, 2, 10]), (40, [1, 1, 3, 9]), (58, [1, 1, 4, 8]), (32, [1, 1, 5, 7]), (24, [1, 1, 6, 6]), (35, [1, 2, 2, 9]), (53, [1, 2, 3, 8]), (55, [1, 2, 4, 7]), (46, [1, 2, 5, 6])]

def vVac79Data_sector0_chunk1 : RawPoly ℕ := [(4, [1, 3, 3, 7]), (36, [1, 3, 4, 6]), (2, [1, 3, 5, 5]), (20, [1, 4, 4, 5]), (594, [1, 13]), (10, [2, 2, 3, 7]), (3, [2, 2, 5, 5]), (10, [2, 3, 3, 6]), (17, [2, 3, 4, 5]), (400, [2, 12]), (4, [3, 3, 4, 4]), (360, [3, 11]), (352, [4, 10]), (326, [5, 9]), (328, [6, 8]), (160, [7, 7])]

def vVac79Data_sector0 : RawPoly ℕ := [vVac79Data_sector0_chunk0, vVac79Data_sector0_chunk1].flatten

def vVac79Data : SectorVector := [(0, vVac79Data_sector0)]

theorem vVac79_check : neutralDirectS omR (-(1:ℤ)) vVac48Data = vVac79Data := by decide +kernel

theorem vVac79_value : evaluate vVac79Data = virWord (V2m 4 four_ge_one) [1, 1, 2, 6] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 2, 6] _ _ _ vVac48_value vVac79_check
end VOA.Classification.COne.OrbC2h
