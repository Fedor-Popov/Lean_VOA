import VOA.Classification.COne.OrbC2hVirVacCache16
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async true
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac272Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 6, 7]), (1, [1, 1, 2, 2, 5, 7]), (1, [1, 1, 2, 2, 6, 6]), (1, [1, 1, 2, 3, 4, 7]), (1, [1, 1, 2, 3, 5, 6]), (1/2, [1, 1, 2, 4, 4, 6]), (7, [1, 1, 2, 14]), (7, [1, 1, 6, 10]), (6, [1, 1, 7, 9]), (1, [1, 2, 2, 2, 5, 6]), (1, [1, 2, 2, 3, 4, 6]), (1, [1, 2, 2, 3, 5, 5]), (1/2, [1, 2, 2, 4, 4, 5]), (6, [1, 2, 2, 13]), (1, [1, 2, 3, 3, 4, 5]), (1/2, [1, 2, 3, 4, 4, 4]), (5, [1, 2, 3, 12]), (4, [1, 2, 4, 11]), (10, [1, 2, 5, 10]), (14, [1, 2, 6, 9]), (6, [1, 2, 7, 8]), (7, [1, 3, 4, 10]), (6, [1, 3, 5, 9]), (5, [1, 3, 6, 8])]

def vVac272Data_sector0_chunk1 : RawPoly ℕ := [(4, [1, 3, 7, 7]), (3, [1, 4, 4, 9]), (9, [1, 4, 6, 7]), (2, [1, 5, 5, 7]), (5, [1, 5, 6, 6]), (98, [1, 17]), (6, [2, 2, 5, 9]), (5, [2, 2, 6, 8]), (6, [2, 3, 4, 9]), (10, [2, 3, 5, 8]), (4, [2, 3, 6, 7]), (5/2, [2, 4, 4, 8]), (5, [2, 4, 5, 7]), (4, [2, 4, 6, 6]), (7, [2, 5, 5, 6]), (78, [2, 16]), (5, [3, 3, 4, 8]), (4, [3, 3, 5, 7]), (7, [3, 4, 4, 7]), (9, [3, 4, 5, 6]), (2, [3, 5, 5, 5]), (60, [3, 15]), (2, [4, 4, 4, 6]), (1, [4, 4, 5, 5])]

def vVac272Data_sector0_chunk2 : RawPoly ℕ := [(51, [4, 14]), (42, [5, 13]), (33, [6, 12]), (24, [7, 11]), (22, [8, 10]), (12, [9, 9])]

def vVac272Data_sector0 : RawPoly ℕ := [vVac272Data_sector0_chunk0, vVac272Data_sector0_chunk1, vVac272Data_sector0_chunk2].flatten

def vVac272Data : SectorVector := [(0, vVac272Data_sector0)]

theorem vVac272_check : neutralDirectS omR (-(2:ℤ)) vVac120Data = vVac272Data := by decide +kernel

theorem vVac272_value : evaluate vVac272Data = virWord (V2m 4 four_ge_one) [2, 6, 7] (evaluate vacuumData) :=
  virWord_cached_step 2 [6, 7] _ _ _ vVac120_value vVac272_check

def vVac273Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 14]), (1, [1, 2, 2, 13]), (1, [1, 2, 3, 12]), (1, [1, 2, 4, 11]), (1, [1, 2, 5, 10]), (1, [1, 2, 6, 9]), (1, [1, 2, 7, 8]), (14, [1, 17]), (13, [2, 16]), (12, [3, 15]), (12, [4, 14]), (12, [5, 13]), (12, [6, 12]), (12, [7, 11]), (12, [8, 10]), (6, [9, 9])]

def vVac273Data : SectorVector := [(0, vVac273Data_sector0)]

theorem vVac273_check : neutralDirectS omR (-(2:ℤ)) vVac121Data = vVac273Data := by decide +kernel

theorem vVac273_value : evaluate vVac273Data = virWord (V2m 4 four_ge_one) [2, 14] (evaluate vacuumData) :=
  virWord_cached_step 2 [14] _ _ _ vVac121_value vVac273_check

def vVac274Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 3, 3, 3, 5]), (3/2, [1, 1, 1, 2, 2, 3, 3, 5]), (1, [1, 1, 1, 2, 3, 3, 3, 4]), (1/2, [1, 1, 1, 3, 3, 3, 3, 3]), (15, [1, 1, 1, 3, 3, 9]), (9, [1, 1, 1, 3, 5, 7]), (3/4, [1, 1, 2, 2, 2, 2, 3, 5]), (3/2, [1, 1, 2, 2, 2, 3, 3, 4]), (3/4, [1, 1, 2, 2, 3, 3, 3, 3]), (15, [1, 1, 2, 2, 3, 9]), (9/2, [1, 1, 2, 2, 5, 7]), (12, [1, 1, 2, 3, 3, 8]), (9, [1, 1, 2, 3, 4, 7]), (6, [1, 1, 2, 3, 5, 6]), (27/2, [1, 1, 3, 3, 3, 7]), (6, [1, 1, 3, 3, 4, 6]), (6, [1, 1, 3, 3, 5, 5]), (135, [1, 1, 3, 13]), (21, [1, 1, 5, 11]), (45, [1, 1, 7, 9]), (1/8, [1, 2, 2, 2, 2, 2, 2, 5]), (3/4, [1, 2, 2, 2, 2, 2, 3, 4]), (3/8, [1, 2, 2, 2, 2, 3, 3, 3]), (15/4, [1, 2, 2, 2, 2, 9])]

def vVac274Data_sector0_chunk1 : RawPoly ℕ := [(12, [1, 2, 2, 2, 3, 8]), (9/2, [1, 2, 2, 2, 4, 7]), (3, [1, 2, 2, 2, 5, 6]), (45/4, [1, 2, 2, 3, 3, 7]), (12, [1, 2, 2, 3, 4, 6]), (9/2, [1, 2, 2, 3, 5, 5]), (135/2, [1, 2, 2, 13]), (3, [1, 2, 3, 3, 3, 6]), (3, [1, 2, 3, 3, 4, 5]), (96, [1, 2, 3, 12]), (21, [1, 2, 4, 11]), (12, [1, 2, 5, 10]), (30, [1, 2, 6, 9]), (36, [1, 2, 7, 8]), (3/2, [1, 3, 3, 3, 3, 5]), (147/2, [1, 3, 3, 11]), (36, [1, 3, 4, 10]), (65, [1, 3, 5, 9]), (48, [1, 3, 6, 8]), (54, [1, 3, 7, 7]), (18, [1, 4, 6, 7]), (15, [1, 5, 5, 7]), (4, [1, 5, 6, 6]), (585, [1, 17])]

def vVac274Data_sector0_chunk2 : RawPoly ℕ := [(1/8, [2, 2, 2, 2, 2, 2, 2, 4]), (1/16, [2, 2, 2, 2, 2, 2, 3, 3]), (3, [2, 2, 2, 2, 2, 8]), (9/4, [2, 2, 2, 2, 3, 7]), (9/2, [2, 2, 2, 2, 4, 6]), (3/4, [2, 2, 2, 2, 5, 5]), (3/2, [2, 2, 2, 3, 3, 6]), (3/2, [2, 2, 2, 3, 4, 5]), (48, [2, 2, 2, 12]), (3/4, [2, 2, 3, 3, 3, 5]), (63/2, [2, 2, 3, 11]), (30, [2, 2, 4, 10]), (45/2, [2, 2, 5, 9]), (48, [2, 2, 6, 8]), (27/2, [2, 2, 7, 7]), (6, [2, 3, 3, 10]), (5, [2, 3, 4, 9]), (12, [2, 3, 5, 8]), (18, [2, 3, 6, 7]), (6, [2, 4, 5, 7]), (16, [2, 4, 6, 6]), (6, [2, 5, 5, 6]), (384, [2, 16]), (5/2, [3, 3, 3, 9])]

def vVac274Data_sector0_chunk3 : RawPoly ℕ := [(12, [3, 3, 5, 7]), (2, [3, 3, 6, 6]), (6, [3, 4, 5, 6]), (3, [3, 5, 5, 5]), (231, [3, 15]), (120, [4, 14]), (180, [5, 13]), (192, [6, 12]), (189, [7, 11]), (144, [8, 10]), (75, [9, 9])]

def vVac274Data_sector0 : RawPoly ℕ := [vVac274Data_sector0_chunk0, vVac274Data_sector0_chunk1, vVac274Data_sector0_chunk2, vVac274Data_sector0_chunk3].flatten

def vVac274Data : SectorVector := [(0, vVac274Data_sector0)]

theorem vVac274_check : neutralDirectS omR (-(3:ℤ)) vVac98Data = vVac274Data := by decide +kernel

theorem vVac274_value : evaluate vVac274Data = virWord (V2m 4 four_ge_one) [3, 3, 3, 5] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 3, 5] _ _ _ vVac98_value vVac274_check

def vVac275Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 3, 3, 4, 4]), (1, [1, 1, 1, 2, 2, 3, 4, 4]), (2, [1, 1, 1, 2, 3, 3, 3, 4]), (4, [1, 1, 1, 3, 3, 9]), (16, [1, 1, 1, 3, 4, 8]), (3, [1, 1, 1, 4, 4, 7]), (1/4, [1, 1, 2, 2, 2, 2, 4, 4]), (2, [1, 1, 2, 2, 2, 3, 3, 4]), (1, [1, 1, 2, 2, 3, 3, 3, 3]), (4, [1, 1, 2, 2, 3, 9]), (8, [1, 1, 2, 2, 4, 8]), (19, [1, 1, 2, 3, 3, 8]), (18, [1, 1, 2, 3, 4, 7]), (2, [1, 1, 2, 4, 4, 6]), (2, [1, 1, 3, 3, 3, 7]), (9, [1, 1, 3, 3, 4, 6]), (5, [1, 1, 3, 4, 4, 5]), (72, [1, 1, 3, 13]), (64, [1, 1, 4, 12]), (12, [1, 1, 7, 9]), (32, [1, 1, 8, 8]), (1/2, [1, 2, 2, 2, 2, 2, 3, 4]), (1, [1, 2, 2, 2, 2, 3, 3, 3]), (1, [1, 2, 2, 2, 2, 9])]

def vVac275Data_sector0_chunk1 : RawPoly ℕ := [(11, [1, 2, 2, 2, 3, 8]), (6, [1, 2, 2, 2, 4, 7]), (17, [1, 2, 2, 3, 3, 7]), (9, [1, 2, 2, 3, 4, 6]), (2, [1, 2, 2, 4, 4, 5]), (36, [1, 2, 2, 13]), (8, [1, 2, 3, 3, 3, 6]), (6, [1, 2, 3, 3, 4, 5]), (112, [1, 2, 3, 12]), (42, [1, 2, 4, 11]), (8, [1, 2, 6, 9]), (57, [1, 2, 7, 8]), (28, [1, 3, 3, 11]), (36, [1, 3, 4, 10]), (12, [1, 3, 5, 9]), (52, [1, 3, 6, 8]), (18, [1, 3, 7, 7]), (10, [1, 4, 4, 9]), (32, [1, 4, 5, 8]), (27, [1, 4, 6, 7]), (468, [1, 17]), (1/4, [2, 2, 2, 2, 2, 2, 3, 3]), (3/4, [2, 2, 2, 2, 2, 8]), (13/2, [2, 2, 2, 2, 3, 7])]

def vVac275Data_sector0_chunk2 : RawPoly ℕ := [(1/4, [2, 2, 2, 2, 4, 6]), (6, [2, 2, 2, 3, 3, 6]), (2, [2, 2, 2, 3, 4, 5]), (24, [2, 2, 2, 12]), (1, [2, 2, 3, 3, 3, 5]), (56, [2, 2, 3, 11]), (6, [2, 2, 4, 10]), (4, [2, 2, 5, 9]), (16, [2, 2, 6, 8]), (24, [2, 2, 7, 7]), (24, [2, 3, 3, 10]), (10, [2, 3, 4, 9]), (19, [2, 3, 5, 8]), (52, [2, 3, 6, 7]), (12, [2, 4, 5, 7]), (2, [2, 4, 6, 6]), (288, [2, 16]), (2, [3, 3, 5, 7]), (8, [3, 3, 6, 6]), (9, [3, 4, 5, 6]), (154, [3, 15]), (2, [4, 4, 5, 5]), (60, [4, 14]), (72, [5, 13])]

def vVac275Data_sector0_chunk3 : RawPoly ℕ := [(128, [6, 12]), (126, [7, 11]), (84, [8, 10]), (20, [9, 9])]

def vVac275Data_sector0 : RawPoly ℕ := [vVac275Data_sector0_chunk0, vVac275Data_sector0_chunk1, vVac275Data_sector0_chunk2, vVac275Data_sector0_chunk3].flatten

def vVac275Data : SectorVector := [(0, vVac275Data_sector0)]

theorem vVac275_check : neutralDirectS omR (-(3:ℤ)) vVac99Data = vVac275Data := by decide +kernel

theorem vVac275_value : evaluate vVac275Data = virWord (V2m 4 four_ge_one) [3, 3, 4, 4] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 4, 4] _ _ _ vVac99_value vVac275_check

def vVac276Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 9]), (1, [1, 1, 2, 2, 3, 9]), (1, [1, 1, 2, 3, 3, 8]), (1, [1, 1, 3, 3, 3, 7]), (1, [1, 1, 3, 3, 4, 6]), (1/2, [1, 1, 3, 3, 5, 5]), (18, [1, 1, 3, 13]), (3, [1, 1, 7, 9]), (1/4, [1, 2, 2, 2, 2, 9]), (1, [1, 2, 2, 2, 3, 8]), (1, [1, 2, 2, 3, 3, 7]), (1, [1, 2, 2, 3, 4, 6]), (1/2, [1, 2, 2, 3, 5, 5]), (9, [1, 2, 2, 13]), (16, [1, 2, 3, 12]), (2, [1, 2, 6, 9]), (3, [1, 2, 7, 8]), (14, [1, 3, 3, 11]), (12, [1, 3, 4, 10]), (13, [1, 3, 5, 9]), (12, [1, 3, 6, 8]), (9, [1, 3, 7, 7]), (3, [1, 4, 6, 7]), (3/2, [1, 5, 5, 7])]

def vVac276Data_sector0_chunk1 : RawPoly ℕ := [(117, [1, 17]), (1/4, [2, 2, 2, 2, 2, 8]), (1/4, [2, 2, 2, 2, 3, 7]), (1/4, [2, 2, 2, 2, 4, 6]), (1/8, [2, 2, 2, 2, 5, 5]), (8, [2, 2, 2, 12]), (7, [2, 2, 3, 11]), (6, [2, 2, 4, 10]), (6, [2, 2, 5, 9]), (8, [2, 2, 6, 8]), (3, [2, 2, 7, 7]), (1, [2, 3, 5, 8]), (2, [2, 3, 6, 7]), (2, [2, 4, 6, 6]), (1, [2, 5, 5, 6]), (96, [2, 16]), (1, [3, 3, 5, 7]), (1, [3, 4, 5, 6]), (1/2, [3, 5, 5, 5]), (77, [3, 15]), (60, [4, 14]), (63, [5, 13]), (64, [6, 12]), (63, [7, 11])]

def vVac276Data_sector0_chunk2 : RawPoly ℕ := [(60, [8, 10]), (30, [9, 9])]

def vVac276Data_sector0 : RawPoly ℕ := [vVac276Data_sector0_chunk0, vVac276Data_sector0_chunk1, vVac276Data_sector0_chunk2].flatten

def vVac276Data : SectorVector := [(0, vVac276Data_sector0)]

theorem vVac276_check : neutralDirectS omR (-(3:ℤ)) vVac100Data = vVac276Data := by decide +kernel

theorem vVac276_value : evaluate vVac276Data = virWord (V2m 4 four_ge_one) [3, 3, 9] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 9] _ _ _ vVac100_value vVac276_check

def vVac277Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 4, 8]), (1/2, [1, 1, 2, 2, 4, 8]), (1, [1, 1, 2, 3, 3, 8]), (1, [1, 1, 2, 3, 4, 7]), (1, [1, 1, 3, 3, 4, 6]), (1, [1, 1, 3, 4, 4, 5]), (8, [1, 1, 3, 13]), (8, [1, 1, 4, 12]), (4, [1, 1, 8, 8]), (1/2, [1, 2, 2, 2, 3, 8]), (1/2, [1, 2, 2, 2, 4, 7]), (1, [1, 2, 2, 3, 3, 7]), (1/2, [1, 2, 2, 3, 4, 6]), (1/2, [1, 2, 2, 4, 4, 5]), (4, [1, 2, 2, 13]), (1, [1, 2, 3, 3, 3, 6]), (1, [1, 2, 3, 3, 4, 5]), (15, [1, 2, 3, 12]), (7, [1, 2, 4, 11]), (7, [1, 2, 7, 8]), (6, [1, 3, 3, 11]), (11, [1, 3, 4, 10]), (4, [1, 3, 5, 9]), (10, [1, 3, 6, 8])]

def vVac277Data_sector0_chunk1 : RawPoly ℕ := [(2, [1, 3, 7, 7]), (5, [1, 4, 4, 9]), (10, [1, 4, 5, 8]), (5, [1, 4, 6, 7]), (104, [1, 17]), (1/2, [2, 2, 2, 2, 3, 7]), (1/2, [2, 2, 2, 3, 3, 6]), (1/2, [2, 2, 2, 3, 4, 5]), (7/2, [2, 2, 2, 12]), (10, [2, 2, 3, 11]), (5/2, [2, 2, 4, 10]), (2, [2, 2, 5, 9]), (2, [2, 2, 6, 8]), (4, [2, 2, 7, 7]), (6, [2, 3, 3, 10]), (5, [2, 3, 4, 9]), (5, [2, 3, 5, 8]), (10, [2, 3, 6, 7]), (4, [2, 4, 5, 7]), (84, [2, 16]), (2, [3, 3, 6, 6]), (3, [3, 4, 5, 6]), (66, [3, 15]), (1, [4, 4, 5, 5])]

def vVac277Data_sector0_chunk2 : RawPoly ℕ := [(50, [4, 14]), (44, [5, 13]), (46, [6, 12]), (46, [7, 11]), (44, [8, 10]), (20, [9, 9])]

def vVac277Data_sector0 : RawPoly ℕ := [vVac277Data_sector0_chunk0, vVac277Data_sector0_chunk1, vVac277Data_sector0_chunk2].flatten

def vVac277Data : SectorVector := [(0, vVac277Data_sector0)]

theorem vVac277_check : neutralDirectS omR (-(3:ℤ)) vVac101Data = vVac277Data := by decide +kernel

theorem vVac277_value : evaluate vVac277Data = virWord (V2m 4 four_ge_one) [3, 4, 8] (evaluate vacuumData) :=
  virWord_cached_step 3 [4, 8] _ _ _ vVac101_value vVac277_check

def vVac278Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 5, 7]), (1/2, [1, 1, 2, 2, 5, 7]), (1, [1, 1, 2, 3, 4, 7]), (1, [1, 1, 2, 3, 5, 6]), (1/2, [1, 1, 3, 3, 3, 7]), (1, [1, 1, 3, 3, 5, 5]), (1/2, [1, 1, 3, 4, 4, 5]), (7, [1, 1, 3, 13]), (7, [1, 1, 5, 11]), (5, [1, 1, 7, 9]), (1/2, [1, 2, 2, 2, 4, 7]), (1/2, [1, 2, 2, 2, 5, 6]), (1/4, [1, 2, 2, 3, 3, 7]), (1, [1, 2, 2, 3, 4, 6]), (1/2, [1, 2, 2, 3, 5, 5]), (1/4, [1, 2, 2, 4, 4, 5]), (7/2, [1, 2, 2, 13]), (1/2, [1, 2, 3, 3, 3, 6]), (1, [1, 2, 3, 3, 4, 5]), (1/2, [1, 2, 3, 4, 4, 4]), (6, [1, 2, 3, 12]), (7, [1, 2, 4, 11]), (6, [1, 2, 5, 10]), (5, [1, 2, 6, 9])]

def vVac278Data_sector0_chunk1 : RawPoly ℕ := [(4, [1, 2, 7, 8]), (1/2, [1, 3, 3, 3, 3, 5]), (1/4, [1, 3, 3, 3, 4, 4]), (17/2, [1, 3, 3, 11]), (4, [1, 3, 4, 10]), (13, [1, 3, 5, 9]), (2, [1, 3, 6, 8]), (4, [1, 3, 7, 7]), (5/2, [1, 4, 4, 9]), (4, [1, 4, 5, 8]), (2, [1, 4, 6, 7]), (5, [1, 5, 5, 7]), (2, [1, 5, 6, 6]), (91, [1, 17]), (1/2, [2, 2, 2, 2, 4, 6]), (1/4, [2, 2, 2, 3, 3, 6]), (1/2, [2, 2, 2, 3, 4, 5]), (1/4, [2, 2, 2, 4, 4, 4]), (3, [2, 2, 2, 12]), (1/4, [2, 2, 3, 3, 3, 5]), (1/8, [2, 2, 3, 3, 4, 4]), (5/2, [2, 2, 3, 11]), (8, [2, 2, 4, 10]), (3/2, [2, 2, 5, 9])]

def vVac278Data_sector0_chunk2 : RawPoly ℕ := [(5, [2, 2, 6, 8]), (1/2, [2, 2, 7, 7]), (3, [2, 3, 3, 10]), (5, [2, 3, 4, 9]), (4, [2, 3, 5, 8]), (3, [2, 3, 6, 7]), (6, [2, 4, 4, 8]), (4, [2, 4, 5, 7]), (4, [2, 4, 6, 6]), (1, [2, 5, 5, 6]), (72, [2, 16]), (5/2, [3, 3, 3, 9]), (2, [3, 3, 4, 8]), (5, [3, 3, 5, 7]), (1, [3, 3, 6, 6]), (3/2, [3, 4, 4, 7]), (2, [3, 4, 5, 6]), (1, [3, 5, 5, 5]), (55, [3, 15]), (1, [4, 4, 4, 6]), (1/2, [4, 4, 5, 5]), (40, [4, 14]), (34, [5, 13]), (28, [6, 12])]

def vVac278Data_sector0_chunk3 : RawPoly ℕ := [(29, [7, 11]), (28, [8, 10]), (15, [9, 9])]

def vVac278Data_sector0 : RawPoly ℕ := [vVac278Data_sector0_chunk0, vVac278Data_sector0_chunk1, vVac278Data_sector0_chunk2, vVac278Data_sector0_chunk3].flatten

def vVac278Data : SectorVector := [(0, vVac278Data_sector0)]

theorem vVac278_check : neutralDirectS omR (-(3:ℤ)) vVac102Data = vVac278Data := by decide +kernel

theorem vVac278_value : evaluate vVac278Data = virWord (V2m 4 four_ge_one) [3, 5, 7] (evaluate vacuumData) :=
  virWord_cached_step 3 [5, 7] _ _ _ vVac102_value vVac278_check

def vVac279Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 6, 6]), (1/2, [1, 1, 2, 2, 6, 6]), (2, [1, 1, 2, 3, 5, 6]), (2, [1, 1, 3, 3, 4, 6]), (6, [1, 1, 3, 13]), (12, [1, 1, 6, 10]), (1, [1, 2, 2, 2, 5, 6]), (1, [1, 2, 2, 3, 4, 6]), (1, [1, 2, 2, 3, 5, 5]), (3, [1, 2, 2, 13]), (2, [1, 2, 3, 3, 4, 5]), (5, [1, 2, 3, 12]), (12, [1, 2, 5, 10]), (10, [1, 2, 6, 9]), (1, [1, 3, 3, 3, 4, 4]), (4, [1, 3, 3, 11]), (15, [1, 3, 4, 10]), (2, [1, 3, 5, 9]), (9, [1, 3, 6, 8]), (6, [1, 4, 6, 7]), (6, [1, 5, 6, 6]), (78, [1, 17]), (1/2, [2, 2, 2, 2, 5, 5]), (1, [2, 2, 2, 3, 4, 5])]

def vVac279Data_sector0_chunk1 : RawPoly ℕ := [(5/2, [2, 2, 2, 12]), (1/2, [2, 2, 3, 3, 4, 4]), (2, [2, 2, 3, 11]), (3/2, [2, 2, 4, 10]), (11, [2, 2, 5, 9]), (1/2, [2, 2, 6, 8]), (10, [2, 3, 4, 9]), (8, [2, 3, 5, 8]), (6, [2, 4, 5, 7]), (6, [2, 5, 5, 6]), (60, [2, 16]), (8, [3, 3, 4, 8]), (6, [3, 4, 4, 7]), (6, [3, 4, 5, 6]), (44, [3, 15]), (30, [4, 14]), (24, [5, 13]), (18, [6, 12]), (12, [7, 11]), (18, [8, 10]), (10, [9, 9])]

def vVac279Data_sector0 : RawPoly ℕ := [vVac279Data_sector0_chunk0, vVac279Data_sector0_chunk1].flatten

def vVac279Data : SectorVector := [(0, vVac279Data_sector0)]

theorem vVac279_check : neutralDirectS omR (-(3:ℤ)) vVac103Data = vVac279Data := by decide +kernel

theorem vVac279_value : evaluate vVac279Data = virWord (V2m 4 four_ge_one) [3, 6, 6] (evaluate vacuumData) :=
  virWord_cached_step 3 [6, 6] _ _ _ vVac103_value vVac279_check

def vVac280Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 13]), (1/2, [1, 2, 2, 13]), (1, [1, 2, 3, 12]), (1, [1, 3, 3, 11]), (1, [1, 3, 4, 10]), (1, [1, 3, 5, 9]), (1, [1, 3, 6, 8]), (1/2, [1, 3, 7, 7]), (13, [1, 17]), (1/2, [2, 2, 2, 12]), (1/2, [2, 2, 3, 11]), (1/2, [2, 2, 4, 10]), (1/2, [2, 2, 5, 9]), (1/2, [2, 2, 6, 8]), (1/4, [2, 2, 7, 7]), (12, [2, 16]), (11, [3, 15]), (10, [4, 14]), (10, [5, 13]), (10, [6, 12]), (10, [7, 11]), (10, [8, 10]), (5, [9, 9])]

def vVac280Data : SectorVector := [(0, vVac280Data_sector0)]

theorem vVac280_check : neutralDirectS omR (-(3:ℤ)) vVac104Data = vVac280Data := by decide +kernel

theorem vVac280_value : evaluate vVac280Data = virWord (V2m 4 four_ge_one) [3, 13] (evaluate vacuumData) :=
  virWord_cached_step 3 [13] _ _ _ vVac104_value vVac280_check

def vVac281Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 4, 4, 7]), (2, [1, 1, 2, 3, 4, 7]), (1, [1, 1, 2, 4, 4, 6]), (1, [1, 1, 3, 4, 4, 5]), (1/2, [1, 1, 4, 4, 4, 4]), (14, [1, 1, 4, 12]), (4, [1, 1, 7, 9]), (1, [1, 2, 2, 3, 3, 7]), (2, [1, 2, 2, 3, 4, 6]), (2, [1, 2, 3, 3, 4, 5]), (1, [1, 2, 3, 4, 4, 4]), (14, [1, 2, 3, 12]), (12, [1, 2, 4, 11]), (4, [1, 2, 6, 9]), (3, [1, 2, 7, 8]), (10, [1, 3, 4, 10]), (4, [1, 3, 5, 9]), (2, [1, 3, 7, 7]), (10, [1, 4, 4, 9]), (6, [1, 4, 5, 8]), (7, [1, 4, 6, 7]), (84, [1, 17]), (1, [2, 2, 2, 3, 3, 6]), (1, [2, 2, 3, 3, 3, 5])]

def vVac281Data_sector0_chunk1 : RawPoly ℕ := [(1/2, [2, 2, 3, 3, 4, 4]), (12, [2, 2, 3, 11]), (3, [2, 2, 6, 8]), (10, [2, 3, 3, 10]), (8, [2, 3, 4, 9]), (9, [2, 3, 5, 8]), (8, [2, 3, 6, 7]), (3/2, [2, 4, 4, 8]), (1, [2, 4, 6, 6]), (66, [2, 16]), (2, [3, 3, 5, 7]), (1, [3, 4, 4, 7]), (1, [3, 4, 5, 6]), (50, [3, 15]), (1/2, [4, 4, 4, 6]), (36, [4, 14]), (24, [5, 13]), (28, [6, 12]), (30, [7, 11]), (30, [8, 10]), (16, [9, 9])]

def vVac281Data_sector0 : RawPoly ℕ := [vVac281Data_sector0_chunk0, vVac281Data_sector0_chunk1].flatten

def vVac281Data : SectorVector := [(0, vVac281Data_sector0)]

theorem vVac281_check : neutralDirectS omR (-(4:ℤ)) vVac68Data = vVac281Data := by decide +kernel

theorem vVac281_value : evaluate vVac281Data = virWord (V2m 4 four_ge_one) [4, 4, 7] (evaluate vacuumData) :=
  virWord_cached_step 4 [4, 7] _ _ _ vVac68_value vVac281_check

def vVac282Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 4, 5, 6]), (1, [1, 1, 2, 3, 5, 6]), (1, [1, 1, 2, 4, 4, 6]), (1, [1, 1, 2, 4, 5, 5]), (1/2, [1, 1, 3, 3, 4, 6]), (1, [1, 1, 3, 4, 4, 5]), (6, [1, 1, 4, 12]), (6, [1, 1, 5, 11]), (5, [1, 1, 6, 10]), (1, [1, 2, 2, 3, 4, 6]), (1, [1, 2, 2, 3, 5, 5]), (1, [1, 2, 2, 4, 4, 5]), (1/2, [1, 2, 3, 3, 3, 6]), (3/2, [1, 2, 3, 3, 4, 5]), (1, [1, 2, 3, 4, 4, 4]), (6, [1, 2, 3, 12]), (11, [1, 2, 4, 11]), (10, [1, 2, 5, 10]), (4, [1, 2, 6, 9]), (1/2, [1, 3, 3, 3, 4, 4]), (3, [1, 3, 3, 11]), (9, [1, 3, 4, 10]), (4, [1, 3, 5, 9]), (3, [1, 3, 6, 8])]

def vVac282Data_sector0_chunk1 : RawPoly ℕ := [(3, [1, 4, 4, 9]), (5, [1, 4, 5, 8]), (3, [1, 4, 6, 7]), (2, [1, 5, 5, 7]), (2, [1, 5, 6, 6]), (72, [1, 17]), (1, [2, 2, 2, 3, 4, 5]), (1/2, [2, 2, 3, 3, 3, 5]), (1, [2, 2, 3, 3, 4, 4]), (5, [2, 2, 3, 11]), (5, [2, 2, 4, 10]), (4, [2, 2, 5, 9]), (1/2, [2, 3, 3, 3, 3, 4]), (13/2, [2, 3, 3, 10]), (11, [2, 3, 4, 9]), (5, [2, 3, 5, 8]), (1, [2, 3, 6, 7]), (3, [2, 4, 4, 8]), (4, [2, 4, 5, 7]), (1, [2, 4, 6, 6]), (1, [2, 5, 5, 6]), (55, [2, 16]), (2, [3, 3, 3, 9]), (9/2, [3, 3, 4, 8])]

def vVac282Data_sector0_chunk2 : RawPoly ℕ := [(1, [3, 3, 5, 7]), (1/2, [3, 3, 6, 6]), (2, [3, 4, 4, 7]), (1, [3, 4, 5, 6]), (40, [3, 15]), (27, [4, 14]), (16, [5, 13]), (13, [6, 12]), (16, [7, 11]), (22, [8, 10]), (12, [9, 9])]

def vVac282Data_sector0 : RawPoly ℕ := [vVac282Data_sector0_chunk0, vVac282Data_sector0_chunk1, vVac282Data_sector0_chunk2].flatten

def vVac282Data : SectorVector := [(0, vVac282Data_sector0)]

theorem vVac282_check : neutralDirectS omR (-(4:ℤ)) vVac69Data = vVac282Data := by decide +kernel

theorem vVac282_value : evaluate vVac282Data = virWord (V2m 4 four_ge_one) [4, 5, 6] (evaluate vacuumData) :=
  virWord_cached_step 4 [5, 6] _ _ _ vVac69_value vVac282_check

def vVac283Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 12]), (1, [1, 2, 3, 12]), (1, [1, 2, 4, 11]), (1, [1, 3, 4, 10]), (1, [1, 4, 4, 9]), (1, [1, 4, 5, 8]), (1, [1, 4, 6, 7]), (12, [1, 17]), (1, [2, 2, 3, 11]), (1, [2, 3, 3, 10]), (1, [2, 3, 4, 9]), (1, [2, 3, 5, 8]), (1, [2, 3, 6, 7]), (11, [2, 16]), (10, [3, 15]), (9, [4, 14]), (8, [5, 13]), (8, [6, 12]), (8, [7, 11]), (8, [8, 10]), (4, [9, 9])]

def vVac283Data : SectorVector := [(0, vVac283Data_sector0)]

theorem vVac283_check : neutralDirectS omR (-(4:ℤ)) vVac70Data = vVac283Data := by decide +kernel

theorem vVac283_value : evaluate vVac283Data = virWord (V2m 4 four_ge_one) [4, 12] (evaluate vacuumData) :=
  virWord_cached_step 4 [12] _ _ _ vVac70_value vVac283_check

def vVac284Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 5, 5, 5]), (3, [1, 1, 2, 4, 5, 5]), (3/2, [1, 1, 3, 3, 5, 5]), (15, [1, 1, 5, 11]), (3, [1, 2, 2, 4, 4, 5]), (3, [1, 2, 3, 3, 4, 5]), (15, [1, 2, 4, 11]), (12, [1, 2, 5, 10]), (3/4, [1, 3, 3, 3, 3, 5]), (15/2, [1, 3, 3, 11]), (9, [1, 3, 5, 9]), (6, [1, 4, 5, 8]), (3, [1, 5, 5, 7]), (55, [1, 17]), (1, [2, 2, 2, 4, 4, 4]), (3/2, [2, 2, 3, 3, 4, 4]), (12, [2, 2, 4, 10]), (3/4, [2, 3, 3, 3, 3, 4]), (6, [2, 3, 3, 10]), (9, [2, 3, 4, 9]), (6, [2, 4, 4, 8]), (3, [2, 4, 5, 7]), (40, [2, 16]), (1/8, [3, 3, 3, 3, 3, 3])]

def vVac284Data_sector0_chunk1 : RawPoly ℕ := [(9/2, [3, 3, 3, 9]), (3, [3, 3, 4, 8]), (3/2, [3, 3, 5, 7]), (27, [3, 15]), (16, [4, 14]), (7, [5, 13]), (10, [7, 11]), (16, [8, 10]), (9, [9, 9])]

def vVac284Data_sector0 : RawPoly ℕ := [vVac284Data_sector0_chunk0, vVac284Data_sector0_chunk1].flatten

def vVac284Data : SectorVector := [(0, vVac284Data_sector0)]

theorem vVac284_check : neutralDirectS omR (-(5:ℤ)) vVac59Data = vVac284Data := by decide +kernel

theorem vVac284_value : evaluate vVac284Data = virWord (V2m 4 four_ge_one) [5, 5, 5] (evaluate vacuumData) :=
  virWord_cached_step 5 [5, 5] _ _ _ vVac59_value vVac284_check

def vVac285Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 5, 11]), (1, [1, 2, 4, 11]), (1, [1, 2, 5, 10]), (1/2, [1, 3, 3, 11]), (1, [1, 3, 5, 9]), (1, [1, 4, 5, 8]), (1, [1, 5, 5, 7]), (1/2, [1, 5, 6, 6]), (11, [1, 17]), (1, [2, 2, 4, 10]), (1/2, [2, 3, 3, 10]), (1, [2, 3, 4, 9]), (1, [2, 4, 4, 8]), (1, [2, 4, 5, 7]), (1/2, [2, 4, 6, 6]), (10, [2, 16]), (1/2, [3, 3, 3, 9]), (1/2, [3, 3, 4, 8]), (1/2, [3, 3, 5, 7]), (1/4, [3, 3, 6, 6]), (9, [3, 15]), (8, [4, 14]), (7, [5, 13]), (6, [6, 12])]

def vVac285Data_sector0_chunk1 : RawPoly ℕ := [(6, [7, 11]), (6, [8, 10]), (3, [9, 9])]

def vVac285Data_sector0 : RawPoly ℕ := [vVac285Data_sector0_chunk0, vVac285Data_sector0_chunk1].flatten

def vVac285Data : SectorVector := [(0, vVac285Data_sector0)]

theorem vVac285_check : neutralDirectS omR (-(5:ℤ)) vVac60Data = vVac285Data := by decide +kernel

theorem vVac285_value : evaluate vVac285Data = virWord (V2m 4 four_ge_one) [5, 11] (evaluate vacuumData) :=
  virWord_cached_step 5 [11] _ _ _ vVac60_value vVac285_check

def vVac286Data_sector0 : RawPoly ℕ := [(1, [1, 1, 6, 10]), (1, [1, 2, 5, 10]), (1, [1, 2, 6, 9]), (1, [1, 3, 4, 10]), (1, [1, 3, 6, 8]), (1, [1, 4, 6, 7]), (1, [1, 5, 6, 6]), (10, [1, 17]), (1, [2, 2, 5, 9]), (1, [2, 3, 4, 9]), (1, [2, 3, 5, 8]), (1, [2, 4, 5, 7]), (1, [2, 5, 5, 6]), (9, [2, 16]), (1, [3, 3, 4, 8]), (1, [3, 4, 4, 7]), (1, [3, 4, 5, 6]), (8, [3, 15]), (7, [4, 14]), (6, [5, 13]), (5, [6, 12]), (4, [7, 11]), (4, [8, 10]), (2, [9, 9])]

def vVac286Data : SectorVector := [(0, vVac286Data_sector0)]

theorem vVac286_check : neutralDirectS omR (-(6:ℤ)) vVac39Data = vVac286Data := by decide +kernel

theorem vVac286_value : evaluate vVac286Data = virWord (V2m 4 four_ge_one) [6, 10] (evaluate vacuumData) :=
  virWord_cached_step 6 [10] _ _ _ vVac39_value vVac286_check

def vVac287Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 7, 9]), (1, [1, 2, 6, 9]), (1, [1, 2, 7, 8]), (1, [1, 3, 5, 9]), (1, [1, 3, 7, 7]), (1/2, [1, 4, 4, 9]), (1, [1, 4, 6, 7]), (1/2, [1, 5, 5, 7]), (9, [1, 17]), (1, [2, 2, 6, 8]), (1, [2, 3, 5, 8]), (1, [2, 3, 6, 7]), (1/2, [2, 4, 4, 8]), (1, [2, 4, 6, 6]), (1/2, [2, 5, 5, 6]), (8, [2, 16]), (1, [3, 3, 5, 7]), (1/2, [3, 4, 4, 7]), (1, [3, 4, 5, 6]), (1/2, [3, 5, 5, 5]), (7, [3, 15]), (1/2, [4, 4, 4, 6]), (1/4, [4, 4, 5, 5]), (6, [4, 14])]

def vVac287Data_sector0_chunk1 : RawPoly ℕ := [(5, [5, 13]), (4, [6, 12]), (3, [7, 11]), (2, [8, 10]), (1, [9, 9])]

def vVac287Data_sector0 : RawPoly ℕ := [vVac287Data_sector0_chunk0, vVac287Data_sector0_chunk1].flatten

def vVac287Data : SectorVector := [(0, vVac287Data_sector0)]

theorem vVac287_check : neutralDirectS omR (-(7:ℤ)) vVac33Data = vVac287Data := by decide +kernel

theorem vVac287_value : evaluate vVac287Data = virWord (V2m 4 four_ge_one) [7, 9] (evaluate vacuumData) :=
  virWord_cached_step 7 [9] _ _ _ vVac33_value vVac287_check
end VOA.Classification.COne.OrbC2h
