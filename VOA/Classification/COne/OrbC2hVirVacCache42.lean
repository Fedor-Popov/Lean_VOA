import VOA.Classification.COne.OrbC2hVirVacCache41
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async true
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac672Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 8, 12]), (1, [1, 2, 7, 12]), (1, [1, 2, 8, 11]), (1, [1, 3, 6, 12]), (1, [1, 3, 8, 10]), (1, [1, 4, 5, 12]), (1, [1, 4, 8, 9]), (1, [1, 5, 8, 8]), (1, [1, 6, 7, 8]), (12, [1, 21]), (1, [2, 2, 7, 11]), (1, [2, 3, 6, 11]), (1, [2, 3, 7, 10]), (1, [2, 4, 5, 11]), (1, [2, 4, 7, 9]), (1, [2, 5, 7, 8]), (1, [2, 6, 7, 7]), (11, [2, 20]), (1, [3, 3, 6, 10]), (1, [3, 4, 5, 10]), (1, [3, 4, 6, 9]), (1, [3, 5, 6, 8]), (1, [3, 6, 6, 7]), (10, [3, 19])]

def vVac672Data_sector0_chunk1 : RawPoly ℕ := [(1, [4, 4, 5, 9]), (1, [4, 5, 5, 8]), (1, [4, 5, 6, 7]), (9, [4, 18]), (8, [5, 17]), (7, [6, 16]), (6, [7, 15]), (5, [8, 14]), (4, [9, 13]), (4, [10, 12]), (2, [11, 11])]

def vVac672Data_sector0 : RawPoly ℕ := [vVac672Data_sector0_chunk0, vVac672Data_sector0_chunk1].flatten

def vVac672Data : SectorVector := [(0, vVac672Data_sector0)]

theorem vVac672_check : neutralDirectS omR (-(8:ℤ)) vVac70Data = vVac672Data := by decide +kernel

theorem vVac672_value : evaluate vVac672Data = virWord (V2m 4 four_ge_one) [8, 12] (evaluate vacuumData) :=
  virWord_cached_step 8 [12] _ _ _ vVac70_value vVac672_check

def vVac673Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 9, 11]), (1, [1, 2, 8, 11]), (1, [1, 2, 9, 10]), (1, [1, 3, 7, 11]), (1, [1, 3, 9, 9]), (1, [1, 4, 6, 11]), (1, [1, 4, 8, 9]), (1/2, [1, 5, 5, 11]), (1, [1, 5, 7, 9]), (1/2, [1, 6, 6, 9]), (11, [1, 21]), (1, [2, 2, 8, 10]), (1, [2, 3, 7, 10]), (1, [2, 3, 8, 9]), (1, [2, 4, 6, 10]), (1, [2, 4, 8, 8]), (1/2, [2, 5, 5, 10]), (1, [2, 5, 7, 8]), (1/2, [2, 6, 6, 8]), (10, [2, 20]), (1, [3, 3, 7, 9]), (1, [3, 4, 6, 9]), (1, [3, 4, 7, 8]), (1/2, [3, 5, 5, 9])]

def vVac673Data_sector0_chunk1 : RawPoly ℕ := [(1, [3, 5, 7, 7]), (1/2, [3, 6, 6, 7]), (9, [3, 19]), (1, [4, 4, 6, 8]), (1/2, [4, 5, 5, 8]), (1, [4, 5, 6, 7]), (1/2, [4, 6, 6, 6]), (8, [4, 18]), (1/2, [5, 5, 5, 7]), (1/4, [5, 5, 6, 6]), (7, [5, 17]), (6, [6, 16]), (5, [7, 15]), (4, [8, 14]), (3, [9, 13]), (2, [10, 12]), (1, [11, 11])]

def vVac673Data_sector0 : RawPoly ℕ := [vVac673Data_sector0_chunk0, vVac673Data_sector0_chunk1].flatten

def vVac673Data : SectorVector := [(0, vVac673Data_sector0)]

theorem vVac673_check : neutralDirectS omR (-(9:ℤ)) vVac60Data = vVac673Data := by decide +kernel

theorem vVac673_value : evaluate vVac673Data = virWord (V2m 4 four_ge_one) [9, 11] (evaluate vacuumData) :=
  virWord_cached_step 9 [11] _ _ _ vVac60_value vVac673_check

def vVac674Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 10, 10]), (2, [1, 2, 9, 10]), (2, [1, 3, 8, 10]), (2, [1, 4, 7, 10]), (2, [1, 5, 6, 10]), (10, [1, 21]), (1, [2, 2, 9, 9]), (2, [2, 3, 8, 9]), (2, [2, 4, 7, 9]), (2, [2, 5, 6, 9]), (9, [2, 20]), (1, [3, 3, 8, 8]), (2, [3, 4, 7, 8]), (2, [3, 5, 6, 8]), (8, [3, 19]), (1, [4, 4, 7, 7]), (2, [4, 5, 6, 7]), (7, [4, 18]), (1, [5, 5, 6, 6]), (6, [5, 17]), (5, [6, 16]), (4, [7, 15]), (3, [8, 14]), (2, [9, 13])]

def vVac674Data_sector0_chunk1 : RawPoly ℕ := [(1, [10, 12])]

def vVac674Data_sector0 : RawPoly ℕ := [vVac674Data_sector0_chunk0, vVac674Data_sector0_chunk1].flatten

def vVac674Data : SectorVector := [(0, vVac674Data_sector0)]

theorem vVac674_check : neutralDirectS omR (-(10:ℤ)) vVac39Data = vVac674Data := by decide +kernel

theorem vVac674_value : evaluate vVac674Data = virWord (V2m 4 four_ge_one) [10, 10] (evaluate vacuumData) :=
  virWord_cached_step 10 [10] _ _ _ vVac39_value vVac674_check

def vVac675Data_sector0 : RawPoly ℕ := [(1, [1, 21]), (1, [2, 20]), (1, [3, 19]), (1, [4, 18]), (1, [5, 17]), (1, [6, 16]), (1, [7, 15]), (1, [8, 14]), (1, [9, 13]), (1, [10, 12]), (1/2, [11, 11])]

def vVac675Data : SectorVector := [(0, vVac675Data_sector0)]

theorem vVac675_check : neutralDirectS omR (-(21:ℤ)) vacuumData = vVac675Data := by decide +kernel

theorem vVac675_value : evaluate vVac675Data = virWord (V2m 4 four_ge_one) [21] (evaluate vacuumData) :=
  virWord_cached_step 21 [] _ _ _ (by rfl) vVac675_check
end VOA.Classification.COne.OrbC2h
