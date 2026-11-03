import VOA.Classification.COne.OrbC2hVirVacCache9
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac160Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 9]), (1, [1, 1, 2, 2, 2, 8]), (1, [1, 1, 2, 2, 3, 7]), (1, [1, 1, 2, 2, 4, 6]), (1/2, [1, 1, 2, 2, 5, 5]), (18, [1, 1, 2, 12]), (2, [1, 1, 5, 9]), (16, [1, 2, 2, 11]), (14, [1, 2, 3, 10]), (15, [1, 2, 4, 9]), (16, [1, 2, 5, 8]), (14, [1, 2, 6, 7]), (2, [1, 3, 5, 7]), (2, [1, 4, 5, 6]), (1, [1, 5, 5, 5]), (108, [1, 15]), (1, [2, 2, 4, 8]), (1, [2, 3, 4, 7]), (1, [2, 4, 4, 6]), (1/2, [2, 4, 5, 5]), (88, [2, 14]), (70, [3, 13]), (72, [4, 12]), (72, [5, 11])]

def vVac160Data_sector0_chunk1 : RawPoly ℕ := [(70, [6, 10]), (70, [7, 9]), (35, [8, 8])]

def vVac160Data_sector0 : RawPoly ℕ := [vVac160Data_sector0_chunk0, vVac160Data_sector0_chunk1].flatten

def vVac160Data : SectorVector := [(0, vVac160Data_sector0)]

theorem vVac160_check : neutralDirectS omR (-(2:ℤ)) vVac65Data = vVac160Data := by decide +kernel

theorem vVac160_value : evaluate vVac160Data = virWord (V2m 4 four_ge_one) [2, 2, 9] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 9] _ _ _ vVac65_value vVac160_check

def vVac161Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 3, 3, 4]), (1, [1, 1, 1, 2, 2, 2, 3, 4]), (1, [1, 1, 1, 2, 2, 3, 3, 3]), (8, [1, 1, 1, 2, 3, 8]), (3, [1, 1, 1, 2, 4, 7]), (4, [1, 1, 1, 3, 3, 7]), (6, [1, 1, 1, 3, 4, 6]), (1/4, [1, 1, 2, 2, 2, 2, 2, 4]), (1, [1, 1, 2, 2, 2, 2, 3, 3]), (4, [1, 1, 2, 2, 2, 8]), (13, [1, 1, 2, 2, 3, 7]), (5, [1, 1, 2, 2, 4, 6]), (13, [1, 1, 2, 3, 3, 6]), (7, [1, 1, 2, 3, 4, 5]), (32, [1, 1, 2, 12]), (2, [1, 1, 3, 3, 3, 5]), (3, [1, 1, 3, 3, 4, 4]), (64, [1, 1, 3, 11]), (21, [1, 1, 4, 10]), (24, [1, 1, 6, 8]), (12, [1, 1, 7, 7]), (1/4, [1, 2, 2, 2, 2, 2, 2, 3]), (4, [1, 2, 2, 2, 2, 7]), (10, [1, 2, 2, 2, 3, 6])]

def vVac161Data_sector0_chunk1 : RawPoly ℕ := [(3, [1, 2, 2, 2, 4, 5]), (7, [1, 2, 2, 3, 3, 5]), (2, [1, 2, 2, 3, 4, 4]), (53, [1, 2, 2, 11]), (2, [1, 2, 3, 3, 3, 4]), (75, [1, 2, 3, 10]), (17, [1, 2, 4, 9]), (24, [1, 2, 5, 8]), (47, [1, 2, 6, 7]), (24, [1, 3, 3, 9]), (31, [1, 3, 4, 8]), (30, [1, 3, 5, 7]), (24, [1, 3, 6, 6]), (6, [1, 4, 4, 7]), (13, [1, 4, 5, 6]), (384, [1, 15]), (3/4, [2, 2, 2, 2, 2, 6]), (5/2, [2, 2, 2, 2, 3, 5]), (1/4, [2, 2, 2, 2, 4, 4]), (1, [2, 2, 2, 3, 3, 4]), (21, [2, 2, 2, 10]), (24, [2, 2, 3, 9]), (9, [2, 2, 4, 8]), (22, [2, 2, 5, 7])]

def vVac161Data_sector0_chunk2 : RawPoly ℕ := [(12, [2, 2, 6, 6]), (5, [2, 3, 3, 8]), (9, [2, 3, 4, 7]), (22, [2, 3, 5, 6]), (2, [2, 4, 4, 6]), (4, [2, 4, 5, 5]), (231, [2, 14]), (4, [3, 3, 4, 6]), (2, [3, 3, 5, 5]), (3, [3, 4, 4, 5]), (120, [3, 13]), (77, [4, 12]), (106, [5, 11]), (120, [6, 10]), (92, [7, 9]), (40, [8, 8])]

def vVac161Data_sector0 : RawPoly ℕ := [vVac161Data_sector0_chunk0, vVac161Data_sector0_chunk1, vVac161Data_sector0_chunk2].flatten

def vVac161Data : SectorVector := [(0, vVac161Data_sector0)]

theorem vVac161_check : neutralDirectS omR (-(2:ℤ)) vVac66Data = vVac161Data := by decide +kernel

theorem vVac161_value : evaluate vVac161Data = virWord (V2m 4 four_ge_one) [2, 3, 3, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 3, 4] _ _ _ vVac66_value vVac161_check

def vVac162Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 8]), (1/2, [1, 1, 2, 2, 2, 8]), (1, [1, 1, 2, 2, 3, 7]), (1, [1, 1, 2, 3, 3, 6]), (1, [1, 1, 2, 3, 4, 5]), (8, [1, 1, 2, 12]), (8, [1, 1, 3, 11]), (3, [1, 1, 6, 8]), (1/2, [1, 2, 2, 2, 2, 7]), (1/2, [1, 2, 2, 2, 3, 6]), (1/2, [1, 2, 2, 2, 4, 5]), (11, [1, 2, 2, 11]), (13, [1, 2, 3, 10]), (5, [1, 2, 4, 9]), (7, [1, 2, 5, 8]), (8, [1, 2, 6, 7]), (6, [1, 3, 3, 9]), (7, [1, 3, 4, 8]), (6, [1, 3, 5, 7]), (6, [1, 3, 6, 6]), (3, [1, 4, 5, 6]), (96, [1, 15]), (7/2, [2, 2, 2, 10]), (3, [2, 2, 3, 9])]

def vVac162Data_sector0_chunk1 : RawPoly ℕ := [(3, [2, 2, 4, 8]), (5, [2, 2, 5, 7]), (3/2, [2, 2, 6, 6]), (1, [2, 3, 4, 7]), (2, [2, 3, 5, 6]), (2, [2, 4, 5, 5]), (77, [2, 14]), (1, [3, 3, 4, 6]), (1, [3, 4, 4, 5]), (60, [3, 13]), (53, [4, 12]), (54, [5, 11]), (53, [6, 10]), (50, [7, 9]), (25, [8, 8])]

def vVac162Data_sector0 : RawPoly ℕ := [vVac162Data_sector0_chunk0, vVac162Data_sector0_chunk1].flatten

def vVac162Data : SectorVector := [(0, vVac162Data_sector0)]

theorem vVac162_check : neutralDirectS omR (-(2:ℤ)) vVac67Data = vVac162Data := by decide +kernel

theorem vVac162_value : evaluate vVac162Data = virWord (V2m 4 four_ge_one) [2, 3, 8] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 8] _ _ _ vVac67_value vVac162_check

def vVac163Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 4, 7]), (1, [1, 1, 2, 2, 3, 7]), (1, [1, 1, 2, 2, 4, 6]), (1, [1, 1, 2, 3, 4, 5]), (1/2, [1, 1, 2, 4, 4, 4]), (7, [1, 1, 2, 12]), (7, [1, 1, 4, 10]), (4, [1, 1, 7, 7]), (1, [1, 2, 2, 2, 3, 6]), (1, [1, 2, 2, 3, 3, 5]), (1/2, [1, 2, 2, 3, 4, 4]), (6, [1, 2, 2, 11]), (12, [1, 2, 3, 10]), (10, [1, 2, 4, 9]), (3, [1, 2, 5, 8]), (10, [1, 2, 6, 7]), (5, [1, 3, 4, 8]), (6, [1, 3, 5, 7]), (8, [1, 4, 4, 7]), (5, [1, 4, 5, 6]), (84, [1, 15]), (6, [2, 2, 3, 9]), (3, [2, 2, 6, 6]), (5, [2, 3, 3, 8])]

def vVac163Data_sector0_chunk1 : RawPoly ℕ := [(5, [2, 3, 4, 7]), (10, [2, 3, 5, 6]), (5/2, [2, 4, 4, 6]), (66, [2, 14]), (2, [3, 3, 5, 5]), (2, [3, 4, 4, 5]), (50, [3, 13]), (1/2, [4, 4, 4, 4]), (43, [4, 12]), (36, [5, 11]), (36, [6, 10]), (34, [7, 9]), (15, [8, 8])]

def vVac163Data_sector0 : RawPoly ℕ := [vVac163Data_sector0_chunk0, vVac163Data_sector0_chunk1].flatten

def vVac163Data : SectorVector := [(0, vVac163Data_sector0)]

theorem vVac163_check : neutralDirectS omR (-(2:ℤ)) vVac68Data = vVac163Data := by decide +kernel

theorem vVac163_value : evaluate vVac163Data = virWord (V2m 4 four_ge_one) [2, 4, 7] (evaluate vacuumData) :=
  virWord_cached_step 2 [4, 7] _ _ _ vVac68_value vVac163_check

def vVac164Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 5, 6]), (1, [1, 1, 2, 2, 4, 6]), (1, [1, 1, 2, 2, 5, 5]), (1/2, [1, 1, 2, 3, 3, 6]), (1, [1, 1, 2, 3, 4, 5]), (6, [1, 1, 2, 12]), (6, [1, 1, 5, 9]), (5, [1, 1, 6, 8]), (1, [1, 2, 2, 2, 4, 5]), (1/2, [1, 2, 2, 3, 3, 5]), (1, [1, 2, 2, 3, 4, 4]), (5, [1, 2, 2, 11]), (1/2, [1, 2, 3, 3, 3, 4]), (4, [1, 2, 3, 10]), (9, [1, 2, 4, 9]), (12, [1, 2, 5, 8]), (5, [1, 2, 6, 7]), (3, [1, 3, 3, 9]), (5, [1, 3, 4, 8]), (4, [1, 3, 5, 7]), (3, [1, 3, 6, 6]), (7, [1, 4, 5, 6]), (2, [1, 5, 5, 5]), (72, [1, 15])]

def vVac164Data_sector0_chunk1 : RawPoly ℕ := [(5, [2, 2, 4, 8]), (4, [2, 2, 5, 7]), (5/2, [2, 3, 3, 8]), (8, [2, 3, 4, 7]), (3, [2, 3, 5, 6]), (4, [2, 4, 4, 6]), (5, [2, 4, 5, 5]), (55, [2, 14]), (2, [3, 3, 3, 7]), (5, [3, 3, 4, 6]), (1, [3, 3, 5, 5]), (3, [3, 4, 4, 5]), (40, [3, 13]), (33, [4, 12]), (26, [5, 11]), (19, [6, 10]), (18, [7, 9]), (10, [8, 8])]

def vVac164Data_sector0 : RawPoly ℕ := [vVac164Data_sector0_chunk0, vVac164Data_sector0_chunk1].flatten

def vVac164Data : SectorVector := [(0, vVac164Data_sector0)]

theorem vVac164_check : neutralDirectS omR (-(2:ℤ)) vVac69Data = vVac164Data := by decide +kernel

theorem vVac164_value : evaluate vVac164Data = virWord (V2m 4 four_ge_one) [2, 5, 6] (evaluate vacuumData) :=
  virWord_cached_step 2 [5, 6] _ _ _ vVac69_value vVac164_check

def vVac165Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 12]), (1, [1, 2, 2, 11]), (1, [1, 2, 3, 10]), (1, [1, 2, 4, 9]), (1, [1, 2, 5, 8]), (1, [1, 2, 6, 7]), (12, [1, 15]), (11, [2, 14]), (10, [3, 13]), (10, [4, 12]), (10, [5, 11]), (10, [6, 10]), (10, [7, 9]), (5, [8, 8])]

def vVac165Data : SectorVector := [(0, vVac165Data_sector0)]

theorem vVac165_check : neutralDirectS omR (-(2:ℤ)) vVac70Data = vVac165Data := by decide +kernel

theorem vVac165_value : evaluate vVac165Data = virWord (V2m 4 four_ge_one) [2, 12] (evaluate vacuumData) :=
  virWord_cached_step 2 [12] _ _ _ vVac70_value vVac165_check

def vVac166Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 3, 3, 3, 3]), (2, [1, 1, 1, 2, 2, 3, 3, 3]), (18, [1, 1, 1, 3, 3, 7]), (3/2, [1, 1, 2, 2, 2, 2, 3, 3]), (18, [1, 1, 2, 2, 3, 7]), (12, [1, 1, 2, 3, 3, 6]), (6, [1, 1, 3, 3, 3, 5]), (84, [1, 1, 3, 11]), (27, [1, 1, 7, 7]), (1/2, [1, 2, 2, 2, 2, 2, 2, 3]), (9/2, [1, 2, 2, 2, 2, 7]), (12, [1, 2, 2, 2, 3, 6]), (6, [1, 2, 2, 3, 3, 5]), (42, [1, 2, 2, 11]), (48, [1, 2, 3, 10]), (36, [1, 2, 6, 7]), (20, [1, 3, 3, 9]), (42, [1, 3, 5, 7]), (16, [1, 3, 6, 6]), (231, [1, 15]), (1/16, [2, 2, 2, 2, 2, 2, 2, 2]), (3, [2, 2, 2, 2, 2, 6]), (3/2, [2, 2, 2, 2, 3, 5]), (24, [2, 2, 2, 10])]

def vVac166Data_sector0_chunk1 : RawPoly ℕ := [(10, [2, 2, 3, 9]), (12, [2, 2, 5, 7]), (20, [2, 2, 6, 6]), (12, [2, 3, 5, 6]), (120, [2, 14]), (3, [3, 3, 5, 5]), (45, [3, 13]), (63, [5, 11]), (72, [6, 10]), (45, [7, 9])]

def vVac166Data_sector0 : RawPoly ℕ := [vVac166Data_sector0_chunk0, vVac166Data_sector0_chunk1].flatten

def vVac166Data : SectorVector := [(0, vVac166Data_sector0)]

theorem vVac166_check : neutralDirectS omR (-(3:ℤ)) vVac56Data = vVac166Data := by decide +kernel

theorem vVac166_value : evaluate vVac166Data = virWord (V2m 4 four_ge_one) [3, 3, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 3, 3] _ _ _ vVac56_value vVac166_check

def vVac167Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 7]), (1, [1, 1, 2, 2, 3, 7]), (1, [1, 1, 2, 3, 3, 6]), (1, [1, 1, 3, 3, 3, 5]), (1/2, [1, 1, 3, 3, 4, 4]), (14, [1, 1, 3, 11]), (3, [1, 1, 7, 7]), (1/4, [1, 2, 2, 2, 2, 7]), (1, [1, 2, 2, 2, 3, 6]), (1, [1, 2, 2, 3, 3, 5]), (1/2, [1, 2, 2, 3, 4, 4]), (7, [1, 2, 2, 11]), (12, [1, 2, 3, 10]), (5, [1, 2, 6, 7]), (10, [1, 3, 3, 9]), (8, [1, 3, 4, 8]), (12, [1, 3, 5, 7]), (4, [1, 3, 6, 6]), (3/2, [1, 4, 4, 7]), (77, [1, 15]), (1/4, [2, 2, 2, 2, 2, 6]), (1/4, [2, 2, 2, 2, 3, 5]), (1/8, [2, 2, 2, 2, 4, 4]), (6, [2, 2, 2, 10])]

def vVac167Data_sector0_chunk1 : RawPoly ℕ := [(5, [2, 2, 3, 9]), (4, [2, 2, 4, 8]), (4, [2, 2, 5, 7]), (4, [2, 2, 6, 6]), (3, [2, 3, 5, 6]), (1, [2, 4, 4, 6]), (60, [2, 14]), (1, [3, 3, 5, 5]), (1/2, [3, 4, 4, 5]), (45, [3, 13]), (32, [4, 12]), (35, [5, 11]), (36, [6, 10]), (35, [7, 9]), (16, [8, 8])]

def vVac167Data_sector0 : RawPoly ℕ := [vVac167Data_sector0_chunk0, vVac167Data_sector0_chunk1].flatten

def vVac167Data : SectorVector := [(0, vVac167Data_sector0)]

theorem vVac167_check : neutralDirectS omR (-(3:ℤ)) vVac57Data = vVac167Data := by decide +kernel

theorem vVac167_value : evaluate vVac167Data = virWord (V2m 4 four_ge_one) [3, 3, 7] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 7] _ _ _ vVac57_value vVac167_check

def vVac168Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 4, 6]), (1/2, [1, 1, 2, 2, 4, 6]), (1, [1, 1, 2, 3, 3, 6]), (1, [1, 1, 2, 3, 4, 5]), (1, [1, 1, 3, 3, 4, 4]), (6, [1, 1, 3, 11]), (6, [1, 1, 4, 10]), (4, [1, 1, 6, 8]), (1/2, [1, 2, 2, 2, 3, 6]), (1/2, [1, 2, 2, 2, 4, 5]), (1, [1, 2, 2, 3, 3, 5]), (1/2, [1, 2, 2, 3, 4, 4]), (3, [1, 2, 2, 11]), (1, [1, 2, 3, 3, 3, 4]), (11, [1, 2, 3, 10]), (5, [1, 2, 4, 9]), (4, [1, 2, 5, 8]), (3, [1, 2, 6, 7]), (4, [1, 3, 3, 9]), (11, [1, 3, 4, 8]), (2, [1, 3, 5, 7]), (3, [1, 3, 6, 6]), (3, [1, 4, 4, 7]), (4, [1, 4, 5, 6])]

def vVac168Data_sector0_chunk1 : RawPoly ℕ := [(66, [1, 15]), (1/2, [2, 2, 2, 2, 3, 5]), (1/2, [2, 2, 2, 3, 3, 4]), (5/2, [2, 2, 2, 10]), (7, [2, 2, 3, 9]), (3/2, [2, 2, 4, 8]), (4, [2, 2, 5, 7]), (1/2, [2, 2, 6, 6]), (4, [2, 3, 3, 8]), (6, [2, 3, 4, 7]), (5, [2, 3, 5, 6]), (1, [2, 4, 5, 5]), (50, [2, 14]), (2, [3, 3, 4, 6]), (1, [3, 4, 4, 5]), (36, [3, 13]), (24, [4, 12]), (20, [5, 11]), (22, [6, 10]), (22, [7, 9]), (12, [8, 8])]

def vVac168Data_sector0 : RawPoly ℕ := [vVac168Data_sector0_chunk0, vVac168Data_sector0_chunk1].flatten

def vVac168Data : SectorVector := [(0, vVac168Data_sector0)]

theorem vVac168_check : neutralDirectS omR (-(3:ℤ)) vVac58Data = vVac168Data := by decide +kernel

theorem vVac168_value : evaluate vVac168Data = virWord (V2m 4 four_ge_one) [3, 4, 6] (evaluate vacuumData) :=
  virWord_cached_step 3 [4, 6] _ _ _ vVac58_value vVac168_check

def vVac169Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 5, 5]), (1/2, [1, 1, 2, 2, 5, 5]), (2, [1, 1, 2, 3, 4, 5]), (1, [1, 1, 3, 3, 3, 5]), (5, [1, 1, 3, 11]), (10, [1, 1, 5, 9]), (1, [1, 2, 2, 2, 4, 5]), (1/2, [1, 2, 2, 3, 3, 5]), (1, [1, 2, 2, 3, 4, 4]), (5/2, [1, 2, 2, 11]), (1, [1, 2, 3, 3, 3, 4]), (4, [1, 2, 3, 10]), (10, [1, 2, 4, 9]), (8, [1, 2, 5, 8]), (1/4, [1, 3, 3, 3, 3, 3]), (8, [1, 3, 3, 9]), (2, [1, 3, 4, 8]), (7, [1, 3, 5, 7]), (4, [1, 4, 5, 6]), (2, [1, 5, 5, 5]), (55, [1, 15]), (1/2, [2, 2, 2, 2, 4, 4]), (1/2, [2, 2, 2, 3, 3, 4]), (2, [2, 2, 2, 10])]

def vVac169Data_sector0_chunk1 : RawPoly ℕ := [(1/8, [2, 2, 3, 3, 3, 3]), (3/2, [2, 2, 3, 9]), (9, [2, 2, 4, 8]), (1/2, [2, 2, 5, 7]), (4, [2, 3, 3, 8]), (6, [2, 3, 4, 7]), (4, [2, 4, 4, 6]), (2, [2, 4, 5, 5]), (40, [2, 14]), (3, [3, 3, 3, 7]), (2, [3, 3, 4, 6]), (1, [3, 3, 5, 5]), (27, [3, 13]), (16, [4, 12]), (12, [5, 11]), (8, [6, 10]), (14, [7, 9]), (8, [8, 8])]

def vVac169Data_sector0 : RawPoly ℕ := [vVac169Data_sector0_chunk0, vVac169Data_sector0_chunk1].flatten

def vVac169Data : SectorVector := [(0, vVac169Data_sector0)]

theorem vVac169_check : neutralDirectS omR (-(3:ℤ)) vVac59Data = vVac169Data := by decide +kernel

theorem vVac169_value : evaluate vVac169Data = virWord (V2m 4 four_ge_one) [3, 5, 5] (evaluate vacuumData) :=
  virWord_cached_step 3 [5, 5] _ _ _ vVac59_value vVac169_check

def vVac170Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 11]), (1/2, [1, 2, 2, 11]), (1, [1, 2, 3, 10]), (1, [1, 3, 3, 9]), (1, [1, 3, 4, 8]), (1, [1, 3, 5, 7]), (1/2, [1, 3, 6, 6]), (11, [1, 15]), (1/2, [2, 2, 2, 10]), (1/2, [2, 2, 3, 9]), (1/2, [2, 2, 4, 8]), (1/2, [2, 2, 5, 7]), (1/4, [2, 2, 6, 6]), (10, [2, 14]), (9, [3, 13]), (8, [4, 12]), (8, [5, 11]), (8, [6, 10]), (8, [7, 9]), (4, [8, 8])]

def vVac170Data : SectorVector := [(0, vVac170Data_sector0)]

theorem vVac170_check : neutralDirectS omR (-(3:ℤ)) vVac60Data = vVac170Data := by decide +kernel

theorem vVac170_value : evaluate vVac170Data = virWord (V2m 4 four_ge_one) [3, 11] (evaluate vacuumData) :=
  virWord_cached_step 3 [11] _ _ _ vVac60_value vVac170_check

def vVac171Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 4, 4, 5]), (2, [1, 1, 2, 3, 4, 5]), (1, [1, 1, 2, 4, 4, 4]), (1/2, [1, 1, 3, 3, 4, 4]), (10, [1, 1, 4, 10]), (4, [1, 1, 5, 9]), (1, [1, 2, 2, 3, 3, 5]), (2, [1, 2, 2, 3, 4, 4]), (1, [1, 2, 3, 3, 3, 4]), (10, [1, 2, 3, 10]), (12, [1, 2, 4, 9]), (3, [1, 2, 5, 8]), (2, [1, 3, 3, 9]), (6, [1, 3, 4, 8]), (2, [1, 3, 5, 7]), (4, [1, 4, 4, 7]), (3, [1, 4, 5, 6]), (50, [1, 15]), (1, [2, 2, 2, 3, 3, 4]), (1/2, [2, 2, 3, 3, 3, 3]), (8, [2, 2, 3, 9]), (3, [2, 2, 4, 8]), (15/2, [2, 3, 3, 8]), (6, [2, 3, 4, 7])]

def vVac171Data_sector0_chunk1 : RawPoly ℕ := [(2, [2, 3, 5, 6]), (1, [2, 4, 4, 6]), (36, [2, 14]), (1, [3, 3, 3, 7]), (1/2, [3, 3, 4, 6]), (24, [3, 13]), (14, [4, 12]), (6, [5, 11]), (10, [6, 10]), (16, [7, 9]), (9, [8, 8])]

def vVac171Data_sector0 : RawPoly ℕ := [vVac171Data_sector0_chunk0, vVac171Data_sector0_chunk1].flatten

def vVac171Data : SectorVector := [(0, vVac171Data_sector0)]

theorem vVac171_check : neutralDirectS omR (-(4:ℤ)) vVac38Data = vVac171Data := by decide +kernel

theorem vVac171_value : evaluate vVac171Data = virWord (V2m 4 four_ge_one) [4, 4, 5] (evaluate vacuumData) :=
  virWord_cached_step 4 [4, 5] _ _ _ vVac38_value vVac171_check

def vVac172Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 10]), (1, [1, 2, 3, 10]), (1, [1, 2, 4, 9]), (1, [1, 3, 4, 8]), (1, [1, 4, 4, 7]), (1, [1, 4, 5, 6]), (10, [1, 15]), (1, [2, 2, 3, 9]), (1, [2, 3, 3, 8]), (1, [2, 3, 4, 7]), (1, [2, 3, 5, 6]), (9, [2, 14]), (8, [3, 13]), (7, [4, 12]), (6, [5, 11]), (6, [6, 10]), (6, [7, 9]), (3, [8, 8])]

def vVac172Data : SectorVector := [(0, vVac172Data_sector0)]

theorem vVac172_check : neutralDirectS omR (-(4:ℤ)) vVac39Data = vVac172Data := by decide +kernel

theorem vVac172_value : evaluate vVac172Data = virWord (V2m 4 four_ge_one) [4, 10] (evaluate vacuumData) :=
  virWord_cached_step 4 [10] _ _ _ vVac39_value vVac172_check

def vVac173Data_sector0 : RawPoly ℕ := [(1, [1, 1, 5, 9]), (1, [1, 2, 4, 9]), (1, [1, 2, 5, 8]), (1/2, [1, 3, 3, 9]), (1, [1, 3, 5, 7]), (1, [1, 4, 5, 6]), (1/2, [1, 5, 5, 5]), (9, [1, 15]), (1, [2, 2, 4, 8]), (1/2, [2, 3, 3, 8]), (1, [2, 3, 4, 7]), (1, [2, 4, 4, 6]), (1/2, [2, 4, 5, 5]), (8, [2, 14]), (1/2, [3, 3, 3, 7]), (1/2, [3, 3, 4, 6]), (1/4, [3, 3, 5, 5]), (7, [3, 13]), (6, [4, 12]), (5, [5, 11]), (4, [6, 10]), (4, [7, 9]), (2, [8, 8])]

def vVac173Data : SectorVector := [(0, vVac173Data_sector0)]

theorem vVac173_check : neutralDirectS omR (-(5:ℤ)) vVac33Data = vVac173Data := by decide +kernel

theorem vVac173_value : evaluate vVac173Data = virWord (V2m 4 four_ge_one) [5, 9] (evaluate vacuumData) :=
  virWord_cached_step 5 [9] _ _ _ vVac33_value vVac173_check

def vVac174Data_sector0 : RawPoly ℕ := [(1, [1, 1, 6, 8]), (1, [1, 2, 5, 8]), (1, [1, 2, 6, 7]), (1, [1, 3, 4, 8]), (1, [1, 3, 6, 6]), (1, [1, 4, 5, 6]), (8, [1, 15]), (1, [2, 2, 5, 7]), (1, [2, 3, 4, 7]), (1, [2, 3, 5, 6]), (1, [2, 4, 5, 5]), (7, [2, 14]), (1, [3, 3, 4, 6]), (1, [3, 4, 4, 5]), (6, [3, 13]), (5, [4, 12]), (4, [5, 11]), (3, [6, 10]), (2, [7, 9]), (1, [8, 8])]

def vVac174Data : SectorVector := [(0, vVac174Data_sector0)]

theorem vVac174_check : neutralDirectS omR (-(6:ℤ)) vVac21Data = vVac174Data := by decide +kernel

theorem vVac174_value : evaluate vVac174Data = virWord (V2m 4 four_ge_one) [6, 8] (evaluate vacuumData) :=
  virWord_cached_step 6 [8] _ _ _ vVac21_value vVac174_check

def vVac175Data_sector0 : RawPoly ℕ := [(1, [1, 1, 7, 7]), (2, [1, 2, 6, 7]), (2, [1, 3, 5, 7]), (1, [1, 4, 4, 7]), (7, [1, 15]), (1, [2, 2, 6, 6]), (2, [2, 3, 5, 6]), (1, [2, 4, 4, 6]), (6, [2, 14]), (1, [3, 3, 5, 5]), (1, [3, 4, 4, 5]), (5, [3, 13]), (1/4, [4, 4, 4, 4]), (4, [4, 12]), (3, [5, 11]), (2, [6, 10]), (1, [7, 9])]

def vVac175Data : SectorVector := [(0, vVac175Data_sector0)]

theorem vVac175_check : neutralDirectS omR (-(7:ℤ)) vVac17Data = vVac175Data := by decide +kernel

theorem vVac175_value : evaluate vVac175Data = virWord (V2m 4 four_ge_one) [7, 7] (evaluate vacuumData) :=
  virWord_cached_step 7 [7] _ _ _ vVac17_value vVac175_check
end VOA.Classification.COne.OrbC2h
