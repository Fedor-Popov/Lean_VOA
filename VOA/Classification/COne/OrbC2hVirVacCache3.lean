import VOA.Classification.COne.OrbC2hVirVacCache2
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac48Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 2, 6]), (1/2, [1, 1, 1, 2, 2, 5]), (1/2, [1, 1, 1, 2, 3, 4]), (3, [1, 1, 1, 9]), (17/2, [1, 1, 2, 8]), (2, [1, 1, 3, 7]), (4, [1, 1, 4, 6]), (1, [1, 1, 5, 5]), (5, [1, 2, 2, 7]), (6, [1, 2, 3, 6]), (7, [1, 2, 4, 5]), (2, [1, 3, 4, 4]), (54, [1, 11]), (1, [2, 2, 3, 5]), (1, [2, 3, 3, 4]), (40, [2, 10]), (34, [3, 9]), (34, [4, 8]), (32, [5, 7]), (16, [6, 6])]

def vVac48Data : SectorVector := [(0, vVac48Data_sector0)]

theorem vVac48_check : neutralDirectS omR (-(1:ℤ)) vVac30Data = vVac48Data := by decide +kernel

theorem vVac48_value : evaluate vVac48Data = virWord (V2m 4 four_ge_one) [1, 2, 6] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 6] _ _ _ vVac30_value vVac48_check

def vVac49Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 3, 5]), (1/4, [1, 1, 1, 2, 2, 5]), (1/2, [1, 1, 1, 2, 3, 4]), (1/4, [1, 1, 1, 3, 3, 3]), (5/2, [1, 1, 1, 9]), (1/4, [1, 1, 2, 2, 2, 4]), (1/8, [1, 1, 2, 2, 3, 3]), (2, [1, 1, 2, 8]), (13/2, [1, 1, 3, 7]), (1, [1, 1, 4, 6]), (7/2, [1, 1, 5, 5]), (5/2, [1, 2, 2, 7]), (4, [1, 2, 3, 6]), (5, [1, 2, 4, 5]), (13/2, [1, 3, 3, 5]), (2, [1, 3, 4, 4]), (45, [1, 11]), (2, [2, 2, 2, 6]), (2, [2, 2, 3, 5]), (3, [2, 2, 4, 4]), (2, [2, 3, 3, 4]), (32, [2, 10]), (1/2, [3, 3, 3, 3]), (26, [3, 9])]

def vVac49Data_sector0_chunk1 : RawPoly ℕ := [(20, [4, 8]), (19, [5, 7]), (8, [6, 6])]

def vVac49Data_sector0 : RawPoly ℕ := [vVac49Data_sector0_chunk0, vVac49Data_sector0_chunk1].flatten

def vVac49Data : SectorVector := [(0, vVac49Data_sector0)]

theorem vVac49_check : neutralDirectS omR (-(1:ℤ)) vVac31Data = vVac49Data := by decide +kernel

theorem vVac49_value : evaluate vVac49Data = virWord (V2m 4 four_ge_one) [1, 3, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [3, 5] _ _ _ vVac31_value vVac49_check

def vVac50Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 4, 4]), (1, [1, 1, 1, 2, 3, 4]), (2, [1, 1, 1, 9]), (1/2, [1, 1, 2, 2, 3, 3]), (3/2, [1, 1, 2, 8]), (1, [1, 1, 3, 7]), (17/2, [1, 1, 4, 6]), (8, [1, 2, 3, 6]), (6, [1, 2, 4, 5]), (6, [1, 3, 4, 4]), (36, [1, 11]), (6, [2, 2, 3, 5]), (6, [2, 3, 3, 4]), (24, [2, 10]), (18, [3, 9]), (12, [4, 8]), (6, [5, 7]), (4, [6, 6])]

def vVac50Data : SectorVector := [(0, vVac50Data_sector0)]

theorem vVac50_check : neutralDirectS omR (-(1:ℤ)) vVac32Data = vVac50Data := by decide +kernel

theorem vVac50_value : evaluate vVac50Data = virWord (V2m 4 four_ge_one) [1, 4, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [4, 4] _ _ _ vVac32_value vVac50_check

def vVac51Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 9]), (1/2, [1, 1, 2, 8]), (1/2, [1, 1, 3, 7]), (1/2, [1, 1, 4, 6]), (1/4, [1, 1, 5, 5]), (9, [1, 11]), (8, [2, 10]), (8, [3, 9]), (8, [4, 8]), (8, [5, 7]), (4, [6, 6])]

def vVac51Data : SectorVector := [(0, vVac51Data_sector0)]

theorem vVac51_check : neutralDirectS omR (-(1:ℤ)) vVac33Data = vVac51Data := by decide +kernel

theorem vVac51_value : evaluate vVac51Data = virWord (V2m 4 four_ge_one) [1, 9] (evaluate vacuumData) :=
  virWord_cached_step 1 [9] _ _ _ vVac33_value vVac51_check

def vVac52Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 2, 2]), (12, [1, 1, 1, 2, 2, 5]), (6, [1, 1, 2, 2, 2, 4]), (40, [1, 1, 2, 8]), (12, [1, 1, 5, 5]), (16, [1, 2, 2, 7]), (28, [1, 2, 4, 5]), (80, [1, 11]), (3, [2, 2, 4, 4]), (28, [2, 10]), (30, [4, 8]), (24, [5, 7])]

def vVac52Data : SectorVector := [(0, vVac52Data_sector0)]

theorem vVac52_check : neutralDirectS omR (-(2:ℤ)) vVac18Data = vVac52Data := by decide +kernel

theorem vVac52_value : evaluate vVac52Data = virWord (V2m 4 four_ge_one) [2, 2, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2, 2] _ _ _ vVac18_value vVac52_check

def vVac53Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 5]), (1, [1, 1, 2, 2, 2, 4]), (1/2, [1, 1, 2, 2, 3, 3]), (10, [1, 1, 2, 8]), (2, [1, 1, 5, 5]), (8, [1, 2, 2, 7]), (6, [1, 2, 3, 6]), (9, [1, 2, 4, 5]), (1, [1, 3, 3, 5]), (40, [1, 11]), (1, [2, 2, 4, 4]), (1/2, [2, 3, 3, 4]), (28, [2, 10]), (18, [3, 9]), (20, [4, 8]), (20, [5, 7]), (9, [6, 6])]

def vVac53Data : SectorVector := [(0, vVac53Data_sector0)]

theorem vVac53_check : neutralDirectS omR (-(2:ℤ)) vVac19Data = vVac53Data := by decide +kernel

theorem vVac53_value : evaluate vVac53Data = virWord (V2m 4 four_ge_one) [2, 2, 5] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 5] _ _ _ vVac19_value vVac53_check

def vVac54Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 4]), (1/2, [1, 1, 2, 2, 2, 4]), (1, [1, 1, 2, 2, 3, 3]), (4, [1, 1, 2, 8]), (4, [1, 1, 3, 7]), (3, [1, 1, 4, 6]), (1/2, [1, 2, 2, 2, 2, 3]), (5, [1, 2, 2, 7]), (8, [1, 2, 3, 6]), (3, [1, 2, 4, 5]), (2, [1, 3, 3, 5]), (2, [1, 3, 4, 4]), (32, [1, 11]), (3/2, [2, 2, 2, 6]), (3, [2, 2, 3, 5]), (1/2, [2, 2, 4, 4]), (1, [2, 3, 3, 4]), (21, [2, 10]), (12, [3, 9]), (9, [4, 8]), (10, [5, 7]), (6, [6, 6])]

def vVac54Data : SectorVector := [(0, vVac54Data_sector0)]

theorem vVac54_check : neutralDirectS omR (-(2:ℤ)) vVac20Data = vVac54Data := by decide +kernel

theorem vVac54_value : evaluate vVac54Data = virWord (V2m 4 four_ge_one) [2, 3, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 4] _ _ _ vVac20_value vVac54_check

def vVac55Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 8]), (1, [1, 2, 2, 7]), (1, [1, 2, 3, 6]), (1, [1, 2, 4, 5]), (8, [1, 11]), (7, [2, 10]), (6, [3, 9]), (6, [4, 8]), (6, [5, 7]), (3, [6, 6])]

def vVac55Data : SectorVector := [(0, vVac55Data_sector0)]

theorem vVac55_check : neutralDirectS omR (-(2:ℤ)) vVac21Data = vVac55Data := by decide +kernel

theorem vVac55_value : evaluate vVac55Data = virWord (V2m 4 four_ge_one) [2, 8] (evaluate vacuumData) :=
  virWord_cached_step 2 [8] _ _ _ vVac21_value vVac55_check

def vVac56Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 3]), (3/2, [1, 1, 2, 2, 3, 3]), (9, [1, 1, 3, 7]), (3/4, [1, 2, 2, 2, 2, 3]), (9/2, [1, 2, 2, 7]), (6, [1, 2, 3, 6]), (3, [1, 3, 3, 5]), (21, [1, 11]), (1/8, [2, 2, 2, 2, 2, 2]), (3, [2, 2, 2, 6]), (3/2, [2, 2, 3, 5]), (12, [2, 10]), (5, [3, 9]), (6, [5, 7]), (4, [6, 6])]

def vVac56Data : SectorVector := [(0, vVac56Data_sector0)]

theorem vVac56_check : neutralDirectS omR (-(3:ℤ)) vVac16Data = vVac56Data := by decide +kernel

theorem vVac56_value : evaluate vVac56Data = virWord (V2m 4 four_ge_one) [3, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 3] _ _ _ vVac16_value vVac56_check

def vVac57Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 7]), (1/2, [1, 2, 2, 7]), (1, [1, 2, 3, 6]), (1, [1, 3, 3, 5]), (1/2, [1, 3, 4, 4]), (7, [1, 11]), (1/2, [2, 2, 2, 6]), (1/2, [2, 2, 3, 5]), (1/4, [2, 2, 4, 4]), (6, [2, 10]), (5, [3, 9]), (4, [4, 8]), (4, [5, 7]), (2, [6, 6])]

def vVac57Data : SectorVector := [(0, vVac57Data_sector0)]

theorem vVac57_check : neutralDirectS omR (-(3:ℤ)) vVac17Data = vVac57Data := by decide +kernel

theorem vVac57_value : evaluate vVac57Data = virWord (V2m 4 four_ge_one) [3, 7] (evaluate vacuumData) :=
  virWord_cached_step 3 [7] _ _ _ vVac17_value vVac57_check

def vVac58Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 6]), (1, [1, 2, 3, 6]), (1, [1, 2, 4, 5]), (1, [1, 3, 4, 4]), (6, [1, 11]), (1, [2, 2, 3, 5]), (1, [2, 3, 3, 4]), (5, [2, 10]), (4, [3, 9]), (3, [4, 8]), (2, [5, 7]), (1, [6, 6])]

def vVac58Data : SectorVector := [(0, vVac58Data_sector0)]

theorem vVac58_check : neutralDirectS omR (-(4:ℤ)) vVac10Data = vVac58Data := by decide +kernel

theorem vVac58_value : evaluate vVac58Data = virWord (V2m 4 four_ge_one) [4, 6] (evaluate vacuumData) :=
  virWord_cached_step 4 [6] _ _ _ vVac10_value vVac58_check

def vVac59Data_sector0 : RawPoly ℕ := [(1, [1, 1, 5, 5]), (2, [1, 2, 4, 5]), (1, [1, 3, 3, 5]), (5, [1, 11]), (1, [2, 2, 4, 4]), (1, [2, 3, 3, 4]), (4, [2, 10]), (1/4, [3, 3, 3, 3]), (3, [3, 9]), (2, [4, 8]), (1, [5, 7])]

def vVac59Data : SectorVector := [(0, vVac59Data_sector0)]

theorem vVac59_check : neutralDirectS omR (-(5:ℤ)) vVac8Data = vVac59Data := by decide +kernel

theorem vVac59_value : evaluate vVac59Data = virWord (V2m 4 four_ge_one) [5, 5] (evaluate vacuumData) :=
  virWord_cached_step 5 [5] _ _ _ vVac8_value vVac59_check

def vVac60Data_sector0 : RawPoly ℕ := [(1, [1, 11]), (1, [2, 10]), (1, [3, 9]), (1, [4, 8]), (1, [5, 7]), (1/2, [6, 6])]

def vVac60Data : SectorVector := [(0, vVac60Data_sector0)]

theorem vVac60_check : neutralDirectS omR (-(11:ℤ)) vacuumData = vVac60Data := by decide +kernel

theorem vVac60_value : evaluate vVac60Data = virWord (V2m 4 four_ge_one) [11] (evaluate vacuumData) :=
  virWord_cached_step 11 [] _ _ _ (by rfl) vVac60_check

def vVac61Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 2, 3]), (1/2, [1, 1, 1, 2, 2, 2, 2, 2]), (9, [1, 1, 1, 2, 2, 6]), (6, [1, 1, 1, 2, 3, 5]), (9, [1, 1, 2, 2, 2, 5]), (6, [1, 1, 2, 2, 3, 4]), (54, [1, 1, 2, 9]), (10, [1, 1, 3, 8]), (18, [1, 1, 5, 6]), (3/2, [1, 2, 2, 2, 2, 4]), (35, [1, 2, 2, 8]), (16, [1, 2, 3, 7]), (27, [1, 2, 4, 6]), (24, [1, 2, 5, 5]), (10, [1, 3, 4, 5]), (162, [1, 12]), (2, [2, 2, 2, 7]), (8, [2, 2, 4, 5]), (3, [2, 3, 4, 4]), (80, [2, 11]), (28, [3, 10]), (54, [4, 9]), (60, [5, 8]), (36, [6, 7])]

def vVac61Data : SectorVector := [(0, vVac61Data_sector0)]

theorem vVac61_check : neutralDirectS omR (-(2:ℤ)) vVac29Data = vVac61Data := by decide +kernel

theorem vVac61_value : evaluate vVac61Data = virWord (V2m 4 four_ge_one) [2, 2, 2, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2, 3] _ _ _ vVac29_value vVac61_check

def vVac62Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 6]), (1, [1, 1, 2, 2, 2, 5]), (1, [1, 1, 2, 2, 3, 4]), (12, [1, 1, 2, 9]), (2, [1, 1, 5, 6]), (10, [1, 2, 2, 8]), (8, [1, 2, 3, 7]), (9, [1, 2, 4, 6]), (6, [1, 2, 5, 5]), (2, [1, 3, 4, 5]), (54, [1, 12]), (1, [2, 2, 4, 5]), (1, [2, 3, 4, 4]), (40, [2, 11]), (28, [3, 10]), (30, [4, 9]), (30, [5, 8]), (28, [6, 7])]

def vVac62Data : SectorVector := [(0, vVac62Data_sector0)]

theorem vVac62_check : neutralDirectS omR (-(2:ℤ)) vVac30Data = vVac62Data := by decide +kernel

theorem vVac62_value : evaluate vVac62Data = virWord (V2m 4 four_ge_one) [2, 2, 6] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 6] _ _ _ vVac30_value vVac62_check

def vVac63Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 5]), (1/2, [1, 1, 2, 2, 2, 5]), (1, [1, 1, 2, 2, 3, 4]), (1/2, [1, 1, 2, 3, 3, 3]), (5, [1, 1, 2, 9]), (5, [1, 1, 3, 8]), (3, [1, 1, 5, 6]), (1/2, [1, 2, 2, 2, 2, 4]), (1/4, [1, 2, 2, 2, 3, 3]), (13/2, [1, 2, 2, 8]), (7, [1, 2, 3, 7]), (5, [1, 2, 4, 6]), (3, [1, 2, 5, 5]), (9/2, [1, 3, 3, 6]), (4, [1, 3, 4, 5]), (45, [1, 12]), (2, [2, 2, 2, 7]), (3/2, [2, 2, 3, 6]), (7/2, [2, 2, 4, 5]), (1, [2, 3, 3, 5]), (1, [2, 3, 4, 4]), (32, [2, 11]), (1/2, [3, 3, 3, 4]), (21, [3, 10])]

def vVac63Data_sector0_chunk1 : RawPoly ℕ := [(17, [4, 9]), (18, [5, 8]), (17, [6, 7])]

def vVac63Data_sector0 : RawPoly ℕ := [vVac63Data_sector0_chunk0, vVac63Data_sector0_chunk1].flatten

def vVac63Data : SectorVector := [(0, vVac63Data_sector0)]

theorem vVac63_check : neutralDirectS omR (-(2:ℤ)) vVac31Data = vVac63Data := by decide +kernel

theorem vVac63_value : evaluate vVac63Data = virWord (V2m 4 four_ge_one) [2, 3, 5] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 5] _ _ _ vVac31_value vVac63_check
end VOA.Classification.COne.OrbC2h
