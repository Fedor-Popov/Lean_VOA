import VOA.Classification.COne.OrbC2hVirVacCache1
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac32Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 4]), (2, [1, 2, 3, 4]), (4, [1, 9]), (1, [2, 2, 3, 3]), (3, [2, 8]), (2, [3, 7]), (1, [4, 6])]

def vVac32Data : SectorVector := [(0, vVac32Data_sector0)]

theorem vVac32_check : neutralDirectS omR (-(4:ℤ)) vVac4Data = vVac32Data := by decide +kernel

theorem vVac32_value : evaluate vVac32Data = virWord (V2m 4 four_ge_one) [4, 4] (evaluate vacuumData) :=
  virWord_cached_step 4 [4] _ _ _ vVac4_value vVac32_check

def vVac33Data_sector0 : RawPoly ℕ := [(1, [1, 9]), (1, [2, 8]), (1, [3, 7]), (1, [4, 6]), (1/2, [5, 5])]

def vVac33Data : SectorVector := [(0, vVac33Data_sector0)]

theorem vVac33_check : neutralDirectS omR (-(9:ℤ)) vacuumData = vVac33Data := by decide +kernel

theorem vVac33_value : evaluate vVac33Data = virWord (V2m 4 four_ge_one) [9] (evaluate vacuumData) :=
  virWord_cached_step 9 [] _ _ _ (by rfl) vVac33_check

def vVac34Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 4]), (1, [1, 1, 2, 2, 2, 3]), (8, [1, 1, 2, 7]), (2, [1, 1, 4, 5]), (6, [1, 2, 2, 6]), (6, [1, 2, 3, 5]), (3, [1, 2, 4, 4]), (28, [1, 10]), (1, [2, 2, 3, 4]), (18, [2, 9]), (10, [3, 8]), (12, [4, 7]), (12, [5, 6])]

def vVac34Data : SectorVector := [(0, vVac34Data_sector0)]

theorem vVac34_check : neutralDirectS omR (-(2:ℤ)) vVac15Data = vVac34Data := by decide +kernel

theorem vVac34_value : evaluate vVac34Data = virWord (V2m 4 four_ge_one) [2, 2, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 4] _ _ _ vVac15_value vVac34_check

def vVac35Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 3]), (1, [1, 1, 2, 2, 2, 3]), (3, [1, 1, 2, 7]), (6, [1, 1, 3, 6]), (1/4, [1, 2, 2, 2, 2, 2]), (5, [1, 2, 2, 6]), (5, [1, 2, 3, 5]), (2, [1, 3, 3, 4]), (21, [1, 10]), (2, [2, 2, 2, 5]), (1, [2, 2, 3, 4]), (12, [2, 9]), (5, [3, 8]), (3, [4, 7]), (7, [5, 6])]

def vVac35Data : SectorVector := [(0, vVac35Data_sector0)]

theorem vVac35_check : neutralDirectS omR (-(2:ℤ)) vVac16Data = vVac35Data := by decide +kernel

theorem vVac35_value : evaluate vVac35Data = virWord (V2m 4 four_ge_one) [2, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 3] _ _ _ vVac16_value vVac35_check

def vVac36Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 7]), (1, [1, 2, 2, 6]), (1, [1, 2, 3, 5]), (1/2, [1, 2, 4, 4]), (7, [1, 10]), (6, [2, 9]), (5, [3, 8]), (5, [4, 7]), (5, [5, 6])]

def vVac36Data : SectorVector := [(0, vVac36Data_sector0)]

theorem vVac36_check : neutralDirectS omR (-(2:ℤ)) vVac17Data = vVac36Data := by decide +kernel

theorem vVac36_value : evaluate vVac36Data = virWord (V2m 4 four_ge_one) [2, 7] (evaluate vacuumData) :=
  virWord_cached_step 2 [7] _ _ _ vVac17_value vVac36_check

def vVac37Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 6]), (1/2, [1, 2, 2, 6]), (1, [1, 2, 3, 5]), (1, [1, 3, 3, 4]), (6, [1, 10]), (1/2, [2, 2, 2, 5]), (1/2, [2, 2, 3, 4]), (5, [2, 9]), (4, [3, 8]), (3, [4, 7]), (3, [5, 6])]

def vVac37Data : SectorVector := [(0, vVac37Data_sector0)]

theorem vVac37_check : neutralDirectS omR (-(3:ℤ)) vVac10Data = vVac37Data := by decide +kernel

theorem vVac37_value : evaluate vVac37Data = virWord (V2m 4 four_ge_one) [3, 6] (evaluate vacuumData) :=
  virWord_cached_step 3 [6] _ _ _ vVac10_value vVac37_check

def vVac38Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 5]), (1, [1, 2, 3, 5]), (1, [1, 2, 4, 4]), (1/2, [1, 3, 3, 4]), (5, [1, 10]), (1, [2, 2, 3, 4]), (1/2, [2, 3, 3, 3]), (4, [2, 9]), (3, [3, 8]), (2, [4, 7]), (1, [5, 6])]

def vVac38Data : SectorVector := [(0, vVac38Data_sector0)]

theorem vVac38_check : neutralDirectS omR (-(4:ℤ)) vVac8Data = vVac38Data := by decide +kernel

theorem vVac38_value : evaluate vVac38Data = virWord (V2m 4 four_ge_one) [4, 5] (evaluate vacuumData) :=
  virWord_cached_step 4 [5] _ _ _ vVac8_value vVac38_check

def vVac39Data_sector0 : RawPoly ℕ := [(1, [1, 10]), (1, [2, 9]), (1, [3, 8]), (1, [4, 7]), (1, [5, 6])]

def vVac39Data : SectorVector := [(0, vVac39Data_sector0)]

theorem vVac39_check : neutralDirectS omR (-(10:ℤ)) vacuumData = vVac39Data := by decide +kernel

theorem vVac39_value : evaluate vVac39Data = virWord (V2m 4 four_ge_one) [10] (evaluate vacuumData) :=
  virWord_cached_step 10 [] _ _ _ (by rfl) vVac39_check

def vVac40Data_sector0 : RawPoly ℕ := [(1/64, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (15/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (15/2, [1, 1, 1, 1, 1, 1, 1, 5]), (55/4, [1, 1, 1, 1, 1, 1, 3, 3]), (225/4, [1, 1, 1, 1, 1, 7]), (495/4, [1, 1, 1, 1, 3, 5]), (45, [1, 1, 1, 3, 3, 3]), (315, [1, 1, 1, 9]), (405, [1, 1, 3, 7]), (171, [1, 1, 5, 5]), (195, [1, 3, 3, 5]), (945, [1, 11]), (10, [3, 3, 3, 3]), (525, [3, 9]), (450, [5, 7])]

def vVac40Data : SectorVector := [(0, vVac40Data_sector0)]

theorem vVac40_check : neutralDirectS omR (-(1:ℤ)) vVac22Data = vVac40Data := by decide +kernel

theorem vVac40_value : evaluate vVac40Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 1, 1] _ _ _ vVac22_value vVac40_check

def vVac41Data_sector0_chunk0 : RawPoly ℕ := [(1/16, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3]), (1/32, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (3/2, [1, 1, 1, 1, 1, 1, 1, 5]), (1, [1, 1, 1, 1, 1, 1, 2, 4]), (2, [1, 1, 1, 1, 1, 1, 3, 3]), (3/4, [1, 1, 1, 1, 1, 2, 2, 3]), (45/2, [1, 1, 1, 1, 1, 7]), (12, [1, 1, 1, 1, 2, 6]), (75/2, [1, 1, 1, 1, 3, 5]), (6, [1, 1, 1, 1, 4, 4]), (3, [1, 1, 1, 2, 2, 5]), (12, [1, 1, 1, 2, 3, 4]), (11, [1, 1, 1, 3, 3, 3]), (210, [1, 1, 1, 9]), (5/2, [1, 1, 2, 2, 3, 3]), (96, [1, 1, 2, 8]), (225, [1, 1, 3, 7]), (96, [1, 1, 4, 6]), (90, [1, 1, 5, 5]), (15/2, [1, 2, 2, 7]), (48, [1, 2, 3, 6]), (24, [1, 2, 4, 5]), (87, [1, 3, 3, 5]), (24, [1, 3, 4, 4])]

def vVac41Data_sector0_chunk1 : RawPoly ℕ := [(945, [1, 11]), (9/2, [2, 2, 3, 5]), (8, [2, 3, 3, 4]), (384, [2, 10]), (4, [3, 3, 3, 3]), (525, [3, 9]), (384, [4, 8]), (450, [5, 7]), (192, [6, 6])]

def vVac41Data_sector0 : RawPoly ℕ := [vVac41Data_sector0_chunk0, vVac41Data_sector0_chunk1].flatten

def vVac41Data : SectorVector := [(0, vVac41Data_sector0)]

theorem vVac41_check : neutralDirectS omR (-(1:ℤ)) vVac23Data = vVac41Data := by decide +kernel

theorem vVac41_value : evaluate vVac41Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 3] _ _ _ vVac23_value vVac41_check

def vVac42Data_sector0_chunk0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2]), (1/4, [1, 1, 1, 1, 1, 1, 1, 5]), (25/8, [1, 1, 1, 1, 1, 1, 2, 4]), (3, [1, 1, 1, 1, 1, 2, 2, 3]), (15/2, [1, 1, 1, 1, 1, 7]), (27, [1, 1, 1, 1, 2, 6]), (9/2, [1, 1, 1, 1, 3, 5]), (27/2, [1, 1, 1, 1, 4, 4]), (12, [1, 1, 1, 2, 2, 5]), (75/2, [1, 1, 1, 2, 3, 4]), (105, [1, 1, 1, 9]), (10, [1, 1, 2, 2, 3, 3]), (132, [1, 1, 2, 8]), (60, [1, 1, 3, 7]), (132, [1, 1, 4, 6]), (15, [1, 1, 5, 5]), (30, [1, 2, 2, 7]), (108, [1, 2, 3, 6]), (75, [1, 2, 4, 5]), (8, [1, 3, 3, 5]), (54, [1, 3, 4, 4]), (630, [1, 11]), (18, [2, 2, 3, 5]), (25, [2, 3, 3, 4])]

def vVac42Data_sector0_chunk1 : RawPoly ℕ := [(192, [2, 10]), (210, [3, 9]), (192, [4, 8]), (120, [5, 7]), (96, [6, 6])]

def vVac42Data_sector0 : RawPoly ℕ := [vVac42Data_sector0_chunk0, vVac42Data_sector0_chunk1].flatten

def vVac42Data : SectorVector := [(0, vVac42Data_sector0)]

theorem vVac42_check : neutralDirectS omR (-(1:ℤ)) vVac24Data = vVac42Data := by decide +kernel

theorem vVac42_value : evaluate vVac42Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 2, 2] _ _ _ vVac24_value vVac42_check

def vVac43Data_sector0_chunk0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 5]), (1/8, [1, 1, 1, 1, 1, 1, 2, 4]), (1/16, [1, 1, 1, 1, 1, 1, 3, 3]), (15/4, [1, 1, 1, 1, 1, 7]), (3, [1, 1, 1, 1, 2, 6]), (9/2, [1, 1, 1, 1, 3, 5]), (3/2, [1, 1, 1, 1, 4, 4]), (3/2, [1, 1, 1, 2, 3, 4]), (3/4, [1, 1, 1, 3, 3, 3]), (105/2, [1, 1, 1, 9]), (36, [1, 1, 2, 8]), (105/2, [1, 1, 3, 7]), (36, [1, 1, 4, 6]), (21, [1, 1, 5, 5]), (12, [1, 2, 3, 6]), (3, [1, 2, 4, 5]), (29/2, [1, 3, 3, 5]), (6, [1, 3, 4, 4]), (315, [1, 11]), (1, [2, 3, 3, 4]), (192, [2, 10]), (1/2, [3, 3, 3, 3]), (210, [3, 9]), (192, [4, 8])]

def vVac43Data_sector0_chunk1 : RawPoly ℕ := [(195, [5, 7]), (96, [6, 6])]

def vVac43Data_sector0 : RawPoly ℕ := [vVac43Data_sector0_chunk0, vVac43Data_sector0_chunk1].flatten

def vVac43Data : SectorVector := [(0, vVac43Data_sector0)]

theorem vVac43_check : neutralDirectS omR (-(1:ℤ)) vVac25Data = vVac43Data := by decide +kernel

theorem vVac43_value : evaluate vVac43Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 5] _ _ _ vVac25_value vVac43_check

def vVac44Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 2, 4]), (1/4, [1, 1, 1, 1, 1, 2, 2, 3]), (1, [1, 1, 1, 1, 1, 7]), (19/4, [1, 1, 1, 1, 2, 6]), (1/2, [1, 1, 1, 1, 3, 5]), (9/4, [1, 1, 1, 1, 4, 4]), (3, [1, 1, 1, 2, 2, 5]), (7, [1, 1, 1, 2, 3, 4]), (28, [1, 1, 1, 9]), (2, [1, 1, 2, 2, 3, 3]), (42, [1, 1, 2, 8]), (18, [1, 1, 3, 7]), (38, [1, 1, 4, 6]), (6, [1, 1, 5, 5]), (15, [1, 2, 2, 7]), (35, [1, 2, 3, 6]), (30, [1, 2, 4, 5]), (2, [1, 3, 3, 5]), (17, [1, 3, 4, 4]), (252, [1, 11]), (9, [2, 2, 3, 5]), (10, [2, 3, 3, 4]), (144, [2, 10]), (126, [3, 9])]

def vVac44Data_sector0_chunk1 : RawPoly ℕ := [(120, [4, 8]), (102, [5, 7]), (56, [6, 6])]

def vVac44Data_sector0 : RawPoly ℕ := [vVac44Data_sector0_chunk0, vVac44Data_sector0_chunk1].flatten

def vVac44Data : SectorVector := [(0, vVac44Data_sector0)]

theorem vVac44_check : neutralDirectS omR (-(1:ℤ)) vVac26Data = vVac44Data := by decide +kernel

theorem vVac44_value : evaluate vVac44Data = virWord (V2m 4 four_ge_one) [1, 1, 2, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 2, 4] _ _ _ vVac26_value vVac44_check

def vVac45Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 3, 3]), (1/4, [1, 1, 1, 1, 1, 2, 2, 3]), (3/4, [1, 1, 1, 1, 1, 7]), (1/16, [1, 1, 1, 1, 2, 2, 2, 2]), (1/2, [1, 1, 1, 1, 2, 6]), (25/4, [1, 1, 1, 1, 3, 5]), (3, [1, 1, 1, 2, 2, 5]), (4, [1, 1, 1, 2, 3, 4]), (3, [1, 1, 1, 3, 3, 3]), (21, [1, 1, 1, 9]), (2, [1, 1, 2, 2, 2, 4]), (2, [1, 1, 2, 2, 3, 3]), (12, [1, 1, 2, 8]), (41, [1, 1, 3, 7]), (4, [1, 1, 4, 6]), (21, [1, 1, 5, 5]), (1/4, [1, 2, 2, 2, 2, 3]), (15, [1, 2, 2, 7]), (18, [1, 2, 3, 6]), (24, [1, 2, 4, 5]), (31, [1, 3, 3, 5]), (8, [1, 3, 4, 4]), (189, [1, 11]), (8, [2, 2, 2, 6])]

def vVac45Data_sector0_chunk1 : RawPoly ℕ := [(9, [2, 2, 3, 5]), (12, [2, 2, 4, 4]), (8, [2, 3, 3, 4]), (96, [2, 10]), (2, [3, 3, 3, 3]), (77, [3, 9]), (48, [4, 8]), (54, [5, 7]), (16, [6, 6])]

def vVac45Data_sector0 : RawPoly ℕ := [vVac45Data_sector0_chunk0, vVac45Data_sector0_chunk1].flatten

def vVac45Data : SectorVector := [(0, vVac45Data_sector0)]

theorem vVac45_check : neutralDirectS omR (-(1:ℤ)) vVac27Data = vVac45Data := by decide +kernel

theorem vVac45_value : evaluate vVac45Data = virWord (V2m 4 four_ge_one) [1, 1, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 3, 3] _ _ _ vVac27_value vVac45_check

def vVac46Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 7]), (1/4, [1, 1, 1, 1, 2, 6]), (1/4, [1, 1, 1, 1, 3, 5]), (1/8, [1, 1, 1, 1, 4, 4]), (7, [1, 1, 1, 9]), (6, [1, 1, 2, 8]), (7, [1, 1, 3, 7]), (6, [1, 1, 4, 6]), (3, [1, 1, 5, 5]), (1, [1, 2, 3, 6]), (1, [1, 3, 3, 5]), (1/2, [1, 3, 4, 4]), (63, [1, 11]), (48, [2, 10]), (49, [3, 9]), (48, [4, 8]), (48, [5, 7]), (24, [6, 6])]

def vVac46Data : SectorVector := [(0, vVac46Data_sector0)]

theorem vVac46_check : neutralDirectS omR (-(1:ℤ)) vVac28Data = vVac46Data := by decide +kernel

theorem vVac46_value : evaluate vVac46Data = virWord (V2m 4 four_ge_one) [1, 1, 7] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 7] _ _ _ vVac28_value vVac46_check

def vVac47Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 1, 2, 2, 3]), (1/4, [1, 1, 1, 1, 2, 2, 2, 2]), (3, [1, 1, 1, 1, 2, 6]), (1, [1, 1, 1, 1, 3, 5]), (11/2, [1, 1, 1, 2, 2, 5]), (11/2, [1, 1, 1, 2, 3, 4]), (9, [1, 1, 1, 9]), (17/4, [1, 1, 2, 2, 2, 4]), (3, [1, 1, 2, 2, 3, 3]), (41, [1, 1, 2, 8]), (12, [1, 1, 3, 7]), (15, [1, 1, 4, 6]), (8, [1, 1, 5, 5]), (1, [1, 2, 2, 2, 2, 3]), (25, [1, 2, 2, 7]), (24, [1, 2, 3, 6]), (29, [1, 2, 4, 5]), (4, [1, 3, 3, 5]), (6, [1, 3, 4, 4]), (162, [1, 11]), (2, [2, 2, 2, 6]), (5, [2, 2, 3, 5]), (3, [2, 2, 4, 4]), (3, [2, 3, 3, 4])]

def vVac47Data_sector0_chunk1 : RawPoly ℕ := [(80, [2, 10]), (46, [3, 9]), (56, [4, 8]), (52, [5, 7]), (24, [6, 6])]

def vVac47Data_sector0 : RawPoly ℕ := [vVac47Data_sector0_chunk0, vVac47Data_sector0_chunk1].flatten

def vVac47Data : SectorVector := [(0, vVac47Data_sector0)]

theorem vVac47_check : neutralDirectS omR (-(1:ℤ)) vVac29Data = vVac47Data := by decide +kernel

theorem vVac47_value : evaluate vVac47Data = virWord (V2m 4 four_ge_one) [1, 2, 2, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 2, 3] _ _ _ vVac29_value vVac47_check
end VOA.Classification.COne.OrbC2h
