import VOA.Classification.COne.OrbC2hVirCached
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac0Data_sector0 : RawPoly ℕ := [(1/2, [1, 1])]

def vVac0Data : SectorVector := [(0, vVac0Data_sector0)]

theorem vVac0_check : neutralDirectS omR (-(1:ℤ)) vacuumData = vVac0Data := by decide +kernel

theorem vVac0_value : evaluate vVac0Data = virWord (V2m 4 four_ge_one) [1] (evaluate vacuumData) :=
  virWord_cached_step 1 [] _ _ _ (by rfl) vVac0_check

def vVac1Data_sector0 : RawPoly ℕ := [(1, [1, 2])]

def vVac1Data : SectorVector := [(0, vVac1Data_sector0)]

theorem vVac1_check : neutralDirectS omR (-(2:ℤ)) vacuumData = vVac1Data := by decide +kernel

theorem vVac1_value : evaluate vVac1Data = virWord (V2m 4 four_ge_one) [2] (evaluate vacuumData) :=
  virWord_cached_step 2 [] _ _ _ (by rfl) vVac1_check

def vVac2Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1]), (1, [1, 3])]

def vVac2Data : SectorVector := [(0, vVac2Data_sector0)]

theorem vVac2_check : neutralDirectS omR (-(1:ℤ)) vVac0Data = vVac2Data := by decide +kernel

theorem vVac2_value : evaluate vVac2Data = virWord (V2m 4 four_ge_one) [1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1] _ _ _ vVac0_value vVac2_check

def vVac3Data_sector0 : RawPoly ℕ := [(1, [1, 3]), (1/2, [2, 2])]

def vVac3Data : SectorVector := [(0, vVac3Data_sector0)]

theorem vVac3_check : neutralDirectS omR (-(3:ℤ)) vacuumData = vVac3Data := by decide +kernel

theorem vVac3_value : evaluate vVac3Data = virWord (V2m 4 four_ge_one) [3] (evaluate vacuumData) :=
  virWord_cached_step 3 [] _ _ _ (by rfl) vVac3_check

def vVac4Data_sector0 : RawPoly ℕ := [(1, [1, 4]), (1, [2, 3])]

def vVac4Data : SectorVector := [(0, vVac4Data_sector0)]

theorem vVac4_check : neutralDirectS omR (-(4:ℤ)) vacuumData = vVac4Data := by decide +kernel

theorem vVac4_value : evaluate vVac4Data = virWord (V2m 4 four_ge_one) [4] (evaluate vacuumData) :=
  virWord_cached_step 4 [] _ _ _ (by rfl) vVac4_check

def vVac5Data_sector0 : RawPoly ℕ := [(1/8, [1, 1, 1, 1, 1, 1]), (3/2, [1, 1, 1, 3]), (3, [1, 5]), (1, [3, 3])]

def vVac5Data : SectorVector := [(0, vVac5Data_sector0)]

theorem vVac5_check : neutralDirectS omR (-(1:ℤ)) vVac2Data = vVac5Data := by decide +kernel

theorem vVac5_value : evaluate vVac5Data = virWord (V2m 4 four_ge_one) [1, 1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1] _ _ _ vVac2_value vVac5_check

def vVac6Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 3]), (1/4, [1, 1, 2, 2]), (3, [1, 5]), (2, [2, 4]), (1, [3, 3])]

def vVac6Data : SectorVector := [(0, vVac6Data_sector0)]

theorem vVac6_check : neutralDirectS omR (-(1:ℤ)) vVac3Data = vVac6Data := by decide +kernel

theorem vVac6_value : evaluate vVac6Data = virWord (V2m 4 four_ge_one) [1, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [3] _ _ _ vVac3_value vVac6_check

def vVac7Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 2]), (2, [1, 5]), (1, [2, 4])]

def vVac7Data : SectorVector := [(0, vVac7Data_sector0)]

theorem vVac7_check : neutralDirectS omR (-(2:ℤ)) vVac1Data = vVac7Data := by decide +kernel

theorem vVac7_value : evaluate vVac7Data = virWord (V2m 4 four_ge_one) [2, 2] (evaluate vacuumData) :=
  virWord_cached_step 2 [2] _ _ _ vVac1_value vVac7_check

def vVac8Data_sector0 : RawPoly ℕ := [(1, [1, 5]), (1, [2, 4]), (1/2, [3, 3])]

def vVac8Data : SectorVector := [(0, vVac8Data_sector0)]

theorem vVac8_check : neutralDirectS omR (-(5:ℤ)) vacuumData = vVac8Data := by decide +kernel

theorem vVac8_value : evaluate vVac8Data = virWord (V2m 4 four_ge_one) [5] (evaluate vacuumData) :=
  virWord_cached_step 5 [] _ _ _ (by rfl) vVac8_check

def vVac9Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 3]), (1/2, [1, 2, 2, 2]), (3, [1, 6]), (2, [2, 5]), (1, [3, 4])]

def vVac9Data : SectorVector := [(0, vVac9Data_sector0)]

theorem vVac9_check : neutralDirectS omR (-(2:ℤ)) vVac3Data = vVac9Data := by decide +kernel

theorem vVac9_value : evaluate vVac9Data = virWord (V2m 4 four_ge_one) [2, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [3] _ _ _ vVac3_value vVac9_check

def vVac10Data_sector0 : RawPoly ℕ := [(1, [1, 6]), (1, [2, 5]), (1, [3, 4])]

def vVac10Data : SectorVector := [(0, vVac10Data_sector0)]

theorem vVac10_check : neutralDirectS omR (-(6:ℤ)) vacuumData = vVac10Data := by decide +kernel

theorem vVac10_value : evaluate vVac10Data = virWord (V2m 4 four_ge_one) [6] (evaluate vacuumData) :=
  virWord_cached_step 6 [] _ _ _ (by rfl) vVac10_check

def vVac11Data_sector0 : RawPoly ℕ := [(1/16, [1, 1, 1, 1, 1, 1, 1, 1]), (3/2, [1, 1, 1, 1, 1, 3]), (6, [1, 1, 1, 5]), (5, [1, 1, 3, 3]), (15, [1, 7]), (9, [3, 5])]

def vVac11Data : SectorVector := [(0, vVac11Data_sector0)]

theorem vVac11_check : neutralDirectS omR (-(1:ℤ)) vVac5Data = vVac11Data := by decide +kernel

theorem vVac11_value : evaluate vVac11Data = virWord (V2m 4 four_ge_one) [1, 1, 1, 1] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 1, 1] _ _ _ vVac5_value vVac11_check

def vVac12Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 3]), (1/8, [1, 1, 1, 1, 2, 2]), (3, [1, 1, 1, 5]), (2, [1, 1, 2, 4]), (2, [1, 1, 3, 3]), (1/2, [1, 2, 2, 3]), (15, [1, 7]), (8, [2, 6]), (9, [3, 5]), (4, [4, 4])]

def vVac12Data : SectorVector := [(0, vVac12Data_sector0)]

theorem vVac12_check : neutralDirectS omR (-(1:ℤ)) vVac6Data = vVac12Data := by decide +kernel

theorem vVac12_value : evaluate vVac12Data = virWord (V2m 4 four_ge_one) [1, 1, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 3] _ _ _ vVac6_value vVac12_check

def vVac13Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 2, 2]), (1, [1, 1, 1, 5]), (9/2, [1, 1, 2, 4]), (2, [1, 2, 2, 3]), (10, [1, 7]), (4, [2, 6]), (2, [3, 5]), (2, [4, 4])]

def vVac13Data : SectorVector := [(0, vVac13Data_sector0)]

theorem vVac13_check : neutralDirectS omR (-(1:ℤ)) vVac7Data = vVac13Data := by decide +kernel

theorem vVac13_value : evaluate vVac13Data = virWord (V2m 4 four_ge_one) [1, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 2] _ _ _ vVac7_value vVac13_check

def vVac14Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 5]), (1/2, [1, 1, 2, 4]), (1/4, [1, 1, 3, 3]), (5, [1, 7]), (4, [2, 6]), (4, [3, 5]), (2, [4, 4])]

def vVac14Data : SectorVector := [(0, vVac14Data_sector0)]

theorem vVac14_check : neutralDirectS omR (-(1:ℤ)) vVac8Data = vVac14Data := by decide +kernel

theorem vVac14_value : evaluate vVac14Data = virWord (V2m 4 four_ge_one) [1, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [5] _ _ _ vVac8_value vVac14_check

def vVac15Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 4]), (1, [1, 2, 2, 3]), (4, [1, 7]), (3, [2, 6]), (2, [3, 5]), (1, [4, 4])]

def vVac15Data : SectorVector := [(0, vVac15Data_sector0)]

theorem vVac15_check : neutralDirectS omR (-(2:ℤ)) vVac4Data = vVac15Data := by decide +kernel

theorem vVac15_value : evaluate vVac15Data = virWord (V2m 4 four_ge_one) [2, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [4] _ _ _ vVac4_value vVac15_check
end VOA.Classification.COne.OrbC2h
