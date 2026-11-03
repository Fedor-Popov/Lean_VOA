import VOA.Classification.COne.OrbC2hVirVacCache0
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac16Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 3]), (1, [1, 2, 2, 3]), (3, [1, 7]), (1/4, [2, 2, 2, 2]), (2, [2, 6]), (1, [3, 5])]

def vVac16Data : SectorVector := [(0, vVac16Data_sector0)]

theorem vVac16_check : neutralDirectS omR (-(3:ℤ)) vVac3Data = vVac16Data := by decide +kernel

theorem vVac16_value : evaluate vVac16Data = virWord (V2m 4 four_ge_one) [3, 3] (evaluate vacuumData) :=
  virWord_cached_step 3 [3] _ _ _ vVac3_value vVac16_check

def vVac17Data_sector0 : RawPoly ℕ := [(1, [1, 7]), (1, [2, 6]), (1, [3, 5]), (1/2, [4, 4])]

def vVac17Data : SectorVector := [(0, vVac17Data_sector0)]

theorem vVac17_check : neutralDirectS omR (-(7:ℤ)) vacuumData = vVac17Data := by decide +kernel

theorem vVac17_value : evaluate vVac17Data = virWord (V2m 4 four_ge_one) [7] (evaluate vacuumData) :=
  virWord_cached_step 7 [] _ _ _ (by rfl) vVac17_check

def vVac18Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 2]), (6, [1, 1, 2, 5]), (3, [1, 2, 2, 4]), (10, [1, 8]), (4, [2, 7]), (4, [4, 5])]

def vVac18Data : SectorVector := [(0, vVac18Data_sector0)]

theorem vVac18_check : neutralDirectS omR (-(2:ℤ)) vVac7Data = vVac18Data := by decide +kernel

theorem vVac18_value : evaluate vVac18Data = virWord (V2m 4 four_ge_one) [2, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2] _ _ _ vVac7_value vVac18_check

def vVac19Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 5]), (1, [1, 2, 2, 4]), (1/2, [1, 2, 3, 3]), (5, [1, 8]), (4, [2, 7]), (3, [3, 6]), (3, [4, 5])]

def vVac19Data : SectorVector := [(0, vVac19Data_sector0)]

theorem vVac19_check : neutralDirectS omR (-(2:ℤ)) vVac8Data = vVac19Data := by decide +kernel

theorem vVac19_value : evaluate vVac19Data = virWord (V2m 4 four_ge_one) [2, 5] (evaluate vacuumData) :=
  virWord_cached_step 2 [5] _ _ _ vVac8_value vVac19_check

def vVac20Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 4]), (1/2, [1, 2, 2, 4]), (1, [1, 2, 3, 3]), (4, [1, 8]), (1/2, [2, 2, 2, 3]), (3, [2, 7]), (2, [3, 6]), (1, [4, 5])]

def vVac20Data : SectorVector := [(0, vVac20Data_sector0)]

theorem vVac20_check : neutralDirectS omR (-(3:ℤ)) vVac4Data = vVac20Data := by decide +kernel

theorem vVac20_value : evaluate vVac20Data = virWord (V2m 4 four_ge_one) [3, 4] (evaluate vacuumData) :=
  virWord_cached_step 3 [4] _ _ _ vVac4_value vVac20_check

def vVac21Data_sector0 : RawPoly ℕ := [(1, [1, 8]), (1, [2, 7]), (1, [3, 6]), (1, [4, 5])]

def vVac21Data : SectorVector := [(0, vVac21Data_sector0)]

theorem vVac21_check : neutralDirectS omR (-(8:ℤ)) vacuumData = vVac21Data := by decide +kernel

theorem vVac21_value : evaluate vVac21Data = virWord (V2m 4 four_ge_one) [8] (evaluate vacuumData) :=
  virWord_cached_step 8 [] _ _ _ (by rfl) vVac21_check

def vVac22Data_sector0 : RawPoly ℕ := [(1/32, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), (5/4, [1, 1, 1, 1, 1, 1, 1, 3]), (15/2, [1, 1, 1, 1, 1, 5]), (10, [1, 1, 1, 1, 3, 3]), (75/2, [1, 1, 1, 7]), (105/2, [1, 1, 3, 5]), (10, [1, 3, 3, 3]), (105, [1, 9]), (60, [3, 7]), (27, [5, 5])]

def vVac22Data : SectorVector := [(0, vVac22Data_sector0)]

theorem vVac22_check : neutralDirectS omR (-(1:ℤ)) vVac11Data = vVac22Data := by decide +kernel

theorem vVac22_value : evaluate vVac22Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1, 1] _ _ _ vVac11_value vVac22_check

def vVac23Data_sector0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1, 1, 3]), (1/16, [1, 1, 1, 1, 1, 1, 2, 2]), (9/4, [1, 1, 1, 1, 1, 5]), (3/2, [1, 1, 1, 1, 2, 4]), (9/4, [1, 1, 1, 1, 3, 3]), (3/4, [1, 1, 1, 2, 2, 3]), (45/2, [1, 1, 1, 7]), (12, [1, 1, 2, 6]), (51/2, [1, 1, 3, 5]), (6, [1, 1, 4, 4]), (3/2, [1, 2, 2, 5]), (6, [1, 2, 3, 4]), (4, [1, 3, 3, 3]), (105, [1, 9]), (1/2, [2, 2, 3, 3]), (48, [2, 8]), (60, [3, 7]), (48, [4, 6]), (27, [5, 5])]

def vVac23Data : SectorVector := [(0, vVac23Data_sector0)]

theorem vVac23_check : neutralDirectS omR (-(1:ℤ)) vVac12Data = vVac23Data := by decide +kernel

theorem vVac23_value : evaluate vVac23Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 3] _ _ _ vVac12_value vVac23_check

def vVac24Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 2, 2]), (1/2, [1, 1, 1, 1, 1, 5]), (17/4, [1, 1, 1, 1, 2, 4]), (3, [1, 1, 1, 2, 2, 3]), (10, [1, 1, 1, 7]), (20, [1, 1, 2, 6]), (4, [1, 1, 3, 5]), (10, [1, 1, 4, 4]), (6, [1, 2, 2, 5]), (17, [1, 2, 3, 4]), (70, [1, 9]), (2, [2, 2, 3, 3]), (24, [2, 8]), (20, [3, 7]), (24, [4, 6]), (6, [5, 5])]

def vVac24Data : SectorVector := [(0, vVac24Data_sector0)]

theorem vVac24_check : neutralDirectS omR (-(1:ℤ)) vVac13Data = vVac24Data := by decide +kernel

theorem vVac24_value : evaluate vVac24Data = virWord (V2m 4 four_ge_one) [1, 1, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 2, 2] _ _ _ vVac13_value vVac24_check

def vVac25Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 5]), (1/4, [1, 1, 1, 1, 2, 4]), (1/8, [1, 1, 1, 1, 3, 3]), (5, [1, 1, 1, 7]), (4, [1, 1, 2, 6]), (5, [1, 1, 3, 5]), (2, [1, 1, 4, 4]), (1, [1, 2, 3, 4]), (1/2, [1, 3, 3, 3]), (35, [1, 9]), (24, [2, 8]), (25, [3, 7]), (24, [4, 6]), (12, [5, 5])]

def vVac25Data : SectorVector := [(0, vVac25Data_sector0)]

theorem vVac25_check : neutralDirectS omR (-(1:ℤ)) vVac14Data = vVac25Data := by decide +kernel

theorem vVac25_value : evaluate vVac25Data = virWord (V2m 4 four_ge_one) [1, 1, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 5] _ _ _ vVac14_value vVac25_check

def vVac26Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 2, 4]), (1/2, [1, 1, 1, 2, 2, 3]), (2, [1, 1, 1, 7]), (11/2, [1, 1, 2, 6]), (1, [1, 1, 3, 5]), (5/2, [1, 1, 4, 4]), (3, [1, 2, 2, 5]), (6, [1, 2, 3, 4]), (28, [1, 9]), (1, [2, 2, 3, 3]), (18, [2, 8]), (14, [3, 7]), (14, [4, 6]), (6, [5, 5])]

def vVac26Data : SectorVector := [(0, vVac26Data_sector0)]

theorem vVac26_check : neutralDirectS omR (-(1:ℤ)) vVac15Data = vVac26Data := by decide +kernel

theorem vVac26_value : evaluate vVac26Data = virWord (V2m 4 four_ge_one) [1, 2, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 4] _ _ _ vVac15_value vVac26_check

def vVac27Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 3, 3]), (1/2, [1, 1, 1, 2, 2, 3]), (3/2, [1, 1, 1, 7]), (1/8, [1, 1, 2, 2, 2, 2]), (1, [1, 1, 2, 6]), (13/2, [1, 1, 3, 5]), (3, [1, 2, 2, 5]), (4, [1, 2, 3, 4]), (2, [1, 3, 3, 3]), (21, [1, 9]), (2, [2, 2, 2, 4]), (1, [2, 2, 3, 3]), (12, [2, 8]), (8, [3, 7]), (4, [4, 6]), (3, [5, 5])]

def vVac27Data : SectorVector := [(0, vVac27Data_sector0)]

theorem vVac27_check : neutralDirectS omR (-(1:ℤ)) vVac16Data = vVac27Data := by decide +kernel

theorem vVac27_value : evaluate vVac27Data = virWord (V2m 4 four_ge_one) [1, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [3, 3] _ _ _ vVac16_value vVac27_check

def vVac28Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 7]), (1/2, [1, 1, 2, 6]), (1/2, [1, 1, 3, 5]), (1/4, [1, 1, 4, 4]), (7, [1, 9]), (6, [2, 8]), (6, [3, 7]), (6, [4, 6]), (3, [5, 5])]

def vVac28Data : SectorVector := [(0, vVac28Data_sector0)]

theorem vVac28_check : neutralDirectS omR (-(1:ℤ)) vVac17Data = vVac28Data := by decide +kernel

theorem vVac28_value : evaluate vVac28Data = virWord (V2m 4 four_ge_one) [1, 7] (evaluate vacuumData) :=
  virWord_cached_step 1 [7] _ _ _ vVac17_value vVac28_check

def vVac29Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 3]), (1/2, [1, 1, 2, 2, 2, 2]), (6, [1, 1, 2, 6]), (2, [1, 1, 3, 5]), (5, [1, 2, 2, 5]), (3, [1, 2, 3, 4]), (18, [1, 9]), (1/2, [2, 2, 2, 4]), (10, [2, 8]), (4, [3, 7]), (6, [4, 6]), (4, [5, 5])]

def vVac29Data : SectorVector := [(0, vVac29Data_sector0)]

theorem vVac29_check : neutralDirectS omR (-(2:ℤ)) vVac9Data = vVac29Data := by decide +kernel

theorem vVac29_value : evaluate vVac29Data = virWord (V2m 4 four_ge_one) [2, 2, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 3] _ _ _ vVac9_value vVac29_check

def vVac30Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 6]), (1, [1, 2, 2, 5]), (1, [1, 2, 3, 4]), (6, [1, 9]), (5, [2, 8]), (4, [3, 7]), (4, [4, 6]), (2, [5, 5])]

def vVac30Data : SectorVector := [(0, vVac30Data_sector0)]

theorem vVac30_check : neutralDirectS omR (-(2:ℤ)) vVac10Data = vVac30Data := by decide +kernel

theorem vVac30_value : evaluate vVac30Data = virWord (V2m 4 four_ge_one) [2, 6] (evaluate vacuumData) :=
  virWord_cached_step 2 [6] _ _ _ vVac10_value vVac30_check

def vVac31Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 5]), (1/2, [1, 2, 2, 5]), (1, [1, 2, 3, 4]), (1/2, [1, 3, 3, 3]), (5, [1, 9]), (1/2, [2, 2, 2, 4]), (1/4, [2, 2, 3, 3]), (4, [2, 8]), (3, [3, 7]), (2, [4, 6]), (1, [5, 5])]

def vVac31Data : SectorVector := [(0, vVac31Data_sector0)]

theorem vVac31_check : neutralDirectS omR (-(3:ℤ)) vVac8Data = vVac31Data := by decide +kernel

theorem vVac31_value : evaluate vVac31Data = virWord (V2m 4 four_ge_one) [3, 5] (evaluate vacuumData) :=
  virWord_cached_step 3 [5] _ _ _ vVac8_value vVac31_check
end VOA.Classification.COne.OrbC2h
