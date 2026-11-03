import VOA.Classification.COne.OrbC2hVirVacCache5
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac96Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 4, 5]), (1, [1, 1, 2, 2, 3, 5]), (1, [1, 1, 2, 2, 4, 4]), (1/2, [1, 1, 2, 3, 3, 4]), (5, [1, 1, 2, 10]), (5, [1, 1, 4, 8]), (4, [1, 1, 5, 7]), (1, [1, 2, 2, 2, 3, 4]), (1/2, [1, 2, 2, 3, 3, 3]), (4, [1, 2, 2, 9]), (8, [1, 2, 3, 8]), (10, [1, 2, 4, 7]), (4, [1, 2, 5, 6]), (2, [1, 3, 3, 7]), (3, [1, 3, 4, 6]), (2, [1, 3, 5, 5]), (4, [1, 4, 4, 5]), (50, [1, 13]), (4, [2, 2, 3, 7]), (3, [2, 2, 4, 6]), (9/2, [2, 3, 3, 6]), (5, [2, 3, 4, 5]), (1, [2, 4, 4, 4]), (36, [2, 12])]

def vVac96Data_sector0_chunk1 : RawPoly ℕ := [(1, [3, 3, 3, 5]), (1/2, [3, 3, 4, 4]), (24, [3, 11]), (19, [4, 10]), (14, [5, 9]), (14, [6, 8]), (8, [7, 7])]

def vVac96Data_sector0 : RawPoly ℕ := [vVac96Data_sector0_chunk0, vVac96Data_sector0_chunk1].flatten

def vVac96Data : SectorVector := [(0, vVac96Data_sector0)]

theorem vVac96_check : neutralDirectS omR (-(2:ℤ)) vVac38Data = vVac96Data := by decide +kernel

theorem vVac96_value : evaluate vVac96Data = virWord (V2m 4 four_ge_one) [2, 4, 5] (evaluate vacuumData) :=
  virWord_cached_step 2 [4, 5] _ _ _ vVac38_value vVac96_check

def vVac97Data_sector0 : RawPoly ℕ := [(1, [1, 1, 2, 10]), (1, [1, 2, 2, 9]), (1, [1, 2, 3, 8]), (1, [1, 2, 4, 7]), (1, [1, 2, 5, 6]), (10, [1, 13]), (9, [2, 12]), (8, [3, 11]), (8, [4, 10]), (8, [5, 9]), (8, [6, 8]), (4, [7, 7])]

def vVac97Data : SectorVector := [(0, vVac97Data_sector0)]

theorem vVac97_check : neutralDirectS omR (-(2:ℤ)) vVac39Data = vVac97Data := by decide +kernel

theorem vVac97_value : evaluate vVac97Data = virWord (V2m 4 four_ge_one) [2, 10] (evaluate vacuumData) :=
  virWord_cached_step 2 [10] _ _ _ vVac39_value vVac97_check

def vVac98Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 3, 5]), (1, [1, 1, 2, 2, 3, 5]), (1, [1, 1, 2, 3, 3, 4]), (1/2, [1, 1, 3, 3, 3, 3]), (10, [1, 1, 3, 9]), (3, [1, 1, 5, 7]), (1/4, [1, 2, 2, 2, 2, 5]), (1, [1, 2, 2, 2, 3, 4]), (1/2, [1, 2, 2, 3, 3, 3]), (5, [1, 2, 2, 9]), (8, [1, 2, 3, 8]), (3, [1, 2, 4, 7]), (2, [1, 2, 5, 6]), (15/2, [1, 3, 3, 7]), (4, [1, 3, 4, 6]), (3, [1, 3, 5, 5]), (45, [1, 13]), (1/4, [2, 2, 2, 2, 2, 4]), (1/8, [2, 2, 2, 2, 3, 3]), (4, [2, 2, 2, 8]), (3, [2, 2, 3, 7]), (4, [2, 2, 4, 6]), (1, [2, 2, 5, 5]), (1, [2, 3, 3, 6])]

def vVac98Data_sector0_chunk1 : RawPoly ℕ := [(1, [2, 3, 4, 5]), (32, [2, 12]), (1/2, [3, 3, 3, 5]), (21, [3, 11]), (12, [4, 10]), (15, [5, 9]), (16, [6, 8]), (9, [7, 7])]

def vVac98Data_sector0 : RawPoly ℕ := [vVac98Data_sector0_chunk0, vVac98Data_sector0_chunk1].flatten

def vVac98Data : SectorVector := [(0, vVac98Data_sector0)]

theorem vVac98_check : neutralDirectS omR (-(3:ℤ)) vVac31Data = vVac98Data := by decide +kernel

theorem vVac98_value : evaluate vVac98Data = virWord (V2m 4 four_ge_one) [3, 3, 5] (evaluate vacuumData) :=
  virWord_cached_step 3 [3, 5] _ _ _ vVac31_value vVac98_check

def vVac99Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 3, 4, 4]), (1/2, [1, 1, 2, 2, 4, 4]), (2, [1, 1, 2, 3, 3, 4]), (4, [1, 1, 3, 9]), (8, [1, 1, 4, 8]), (1, [1, 2, 2, 2, 3, 4]), (1, [1, 2, 2, 3, 3, 3]), (2, [1, 2, 2, 9]), (11, [1, 2, 3, 8]), (6, [1, 2, 4, 7]), (2, [1, 3, 3, 7]), (5, [1, 3, 4, 6]), (2, [1, 4, 4, 5]), (36, [1, 13]), (1/2, [2, 2, 2, 2, 3, 3]), (3/2, [2, 2, 2, 8]), (7, [2, 2, 3, 7]), (1/2, [2, 2, 4, 6]), (4, [2, 3, 3, 6]), (2, [2, 3, 4, 5]), (24, [2, 12]), (14, [3, 11]), (6, [4, 10]), (4, [5, 9])]

def vVac99Data_sector0_chunk1 : RawPoly ℕ := [(10, [6, 8]), (6, [7, 7])]

def vVac99Data_sector0 : RawPoly ℕ := [vVac99Data_sector0_chunk0, vVac99Data_sector0_chunk1].flatten

def vVac99Data : SectorVector := [(0, vVac99Data_sector0)]

theorem vVac99_check : neutralDirectS omR (-(3:ℤ)) vVac32Data = vVac99Data := by decide +kernel

theorem vVac99_value : evaluate vVac99Data = virWord (V2m 4 four_ge_one) [3, 4, 4] (evaluate vacuumData) :=
  virWord_cached_step 3 [4, 4] _ _ _ vVac32_value vVac99_check

def vVac100Data_sector0 : RawPoly ℕ := [(1, [1, 1, 3, 9]), (1/2, [1, 2, 2, 9]), (1, [1, 2, 3, 8]), (1, [1, 3, 3, 7]), (1, [1, 3, 4, 6]), (1/2, [1, 3, 5, 5]), (9, [1, 13]), (1/2, [2, 2, 2, 8]), (1/2, [2, 2, 3, 7]), (1/2, [2, 2, 4, 6]), (1/4, [2, 2, 5, 5]), (8, [2, 12]), (7, [3, 11]), (6, [4, 10]), (6, [5, 9]), (6, [6, 8]), (3, [7, 7])]

def vVac100Data : SectorVector := [(0, vVac100Data_sector0)]

theorem vVac100_check : neutralDirectS omR (-(3:ℤ)) vVac33Data = vVac100Data := by decide +kernel

theorem vVac100_value : evaluate vVac100Data = virWord (V2m 4 four_ge_one) [3, 9] (evaluate vacuumData) :=
  virWord_cached_step 3 [9] _ _ _ vVac33_value vVac100_check

def vVac101Data_sector0 : RawPoly ℕ := [(1, [1, 1, 4, 8]), (1, [1, 2, 3, 8]), (1, [1, 2, 4, 7]), (1, [1, 3, 4, 6]), (1, [1, 4, 4, 5]), (8, [1, 13]), (1, [2, 2, 3, 7]), (1, [2, 3, 3, 6]), (1, [2, 3, 4, 5]), (7, [2, 12]), (6, [3, 11]), (5, [4, 10]), (4, [5, 9]), (4, [6, 8]), (2, [7, 7])]

def vVac101Data : SectorVector := [(0, vVac101Data_sector0)]

theorem vVac101_check : neutralDirectS omR (-(4:ℤ)) vVac21Data = vVac101Data := by decide +kernel

theorem vVac101_value : evaluate vVac101Data = virWord (V2m 4 four_ge_one) [4, 8] (evaluate vacuumData) :=
  virWord_cached_step 4 [8] _ _ _ vVac21_value vVac101_check

def vVac102Data_sector0 : RawPoly ℕ := [(1, [1, 1, 5, 7]), (1, [1, 2, 4, 7]), (1, [1, 2, 5, 6]), (1/2, [1, 3, 3, 7]), (1, [1, 3, 5, 5]), (1/2, [1, 4, 4, 5]), (7, [1, 13]), (1, [2, 2, 4, 6]), (1/2, [2, 3, 3, 6]), (1, [2, 3, 4, 5]), (1/2, [2, 4, 4, 4]), (6, [2, 12]), (1/2, [3, 3, 3, 5]), (1/4, [3, 3, 4, 4]), (5, [3, 11]), (4, [4, 10]), (3, [5, 9]), (2, [6, 8]), (1, [7, 7])]

def vVac102Data : SectorVector := [(0, vVac102Data_sector0)]

theorem vVac102_check : neutralDirectS omR (-(5:ℤ)) vVac17Data = vVac102Data := by decide +kernel

theorem vVac102_value : evaluate vVac102Data = virWord (V2m 4 four_ge_one) [5, 7] (evaluate vacuumData) :=
  virWord_cached_step 5 [7] _ _ _ vVac17_value vVac102_check

def vVac103Data_sector0 : RawPoly ℕ := [(1, [1, 1, 6, 6]), (2, [1, 2, 5, 6]), (2, [1, 3, 4, 6]), (6, [1, 13]), (1, [2, 2, 5, 5]), (2, [2, 3, 4, 5]), (5, [2, 12]), (1, [3, 3, 4, 4]), (4, [3, 11]), (3, [4, 10]), (2, [5, 9]), (1, [6, 8])]

def vVac103Data : SectorVector := [(0, vVac103Data_sector0)]

theorem vVac103_check : neutralDirectS omR (-(6:ℤ)) vVac10Data = vVac103Data := by decide +kernel

theorem vVac103_value : evaluate vVac103Data = virWord (V2m 4 four_ge_one) [6, 6] (evaluate vacuumData) :=
  virWord_cached_step 6 [6] _ _ _ vVac10_value vVac103_check

def vVac104Data_sector0 : RawPoly ℕ := [(1, [1, 13]), (1, [2, 12]), (1, [3, 11]), (1, [4, 10]), (1, [5, 9]), (1, [6, 8]), (1/2, [7, 7])]

def vVac104Data : SectorVector := [(0, vVac104Data_sector0)]

theorem vVac104_check : neutralDirectS omR (-(13:ℤ)) vacuumData = vVac104Data := by decide +kernel

theorem vVac104_value : evaluate vVac104Data = virWord (V2m 4 four_ge_one) [13] (evaluate vacuumData) :=
  virWord_cached_step 13 [] _ _ _ (by rfl) vVac104_check

def vVac105Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2]), (20, [1, 1, 1, 1, 2, 2, 2, 5]), (10, [1, 1, 1, 2, 2, 2, 2, 4]), (100, [1, 1, 1, 2, 2, 8]), (60, [1, 1, 1, 2, 5, 5]), (40, [1, 1, 2, 2, 2, 7]), (100, [1, 1, 2, 2, 4, 5]), (400, [1, 1, 2, 11]), (200, [1, 1, 5, 8]), (15, [1, 2, 2, 2, 4, 4]), (140, [1, 2, 2, 10]), (250, [1, 2, 4, 8]), (200, [1, 2, 5, 7]), (80, [1, 4, 5, 5]), (880, [1, 14]), (40, [2, 2, 4, 7]), (40, [2, 4, 4, 5]), (280, [2, 13]), (320, [4, 11]), (224, [5, 10]), (240, [7, 8])]

def vVac105Data : SectorVector := [(0, vVac105Data_sector0)]

theorem vVac105_check : neutralDirectS omR (-(2:ℤ)) vVac52Data = vVac105Data := by decide +kernel

theorem vVac105_value : evaluate vVac105Data = virWord (V2m 4 four_ge_one) [2, 2, 2, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2, 2, 2] _ _ _ vVac52_value vVac105_check

def vVac106Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 2, 5]), (1, [1, 1, 1, 2, 2, 2, 2, 4]), (1/2, [1, 1, 1, 2, 2, 2, 3, 3]), (15, [1, 1, 1, 2, 2, 8]), (6, [1, 1, 1, 2, 5, 5]), (12, [1, 1, 2, 2, 2, 7]), (9, [1, 1, 2, 2, 3, 6]), (18, [1, 1, 2, 2, 4, 5]), (3, [1, 1, 2, 3, 3, 5]), (120, [1, 1, 2, 11]), (40, [1, 1, 5, 8]), (3, [1, 2, 2, 2, 4, 4]), (3/2, [1, 2, 2, 3, 3, 4]), (84, [1, 2, 2, 10]), (54, [1, 2, 3, 9]), (85, [1, 2, 4, 8]), (88, [1, 2, 5, 7]), (27, [1, 2, 6, 6]), (5, [1, 3, 3, 8]), (18, [1, 3, 5, 6]), (22, [1, 4, 5, 5]), (440, [1, 14]), (16, [2, 2, 4, 7]), (2, [2, 3, 3, 7])]

def vVac106Data_sector0_chunk1 : RawPoly ℕ := [(9, [2, 3, 4, 6]), (13, [2, 4, 4, 5]), (280, [2, 13]), (2, [3, 3, 4, 5]), (162, [3, 12]), (200, [4, 11]), (196, [5, 10]), (162, [6, 9]), (180, [7, 8])]

def vVac106Data_sector0 : RawPoly ℕ := [vVac106Data_sector0_chunk0, vVac106Data_sector0_chunk1].flatten

def vVac106Data : SectorVector := [(0, vVac106Data_sector0)]

theorem vVac106_check : neutralDirectS omR (-(2:ℤ)) vVac53Data = vVac106Data := by decide +kernel

theorem vVac106_value : evaluate vVac106Data = virWord (V2m 4 four_ge_one) [2, 2, 2, 5] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2, 5] _ _ _ vVac53_value vVac106_check

def vVac107Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 3, 4]), (1/2, [1, 1, 1, 2, 2, 2, 2, 4]), (1, [1, 1, 1, 2, 2, 2, 3, 3]), (4, [1, 1, 1, 2, 2, 8]), (8, [1, 1, 1, 2, 3, 7]), (6, [1, 1, 1, 2, 4, 6]), (2, [1, 1, 1, 3, 4, 5]), (1/2, [1, 1, 2, 2, 2, 2, 2, 3]), (7, [1, 1, 2, 2, 2, 7]), (14, [1, 1, 2, 2, 3, 6]), (6, [1, 1, 2, 2, 4, 5]), (6, [1, 1, 2, 3, 3, 5]), (5, [1, 1, 2, 3, 4, 4]), (64, [1, 1, 2, 11]), (28, [1, 1, 3, 10]), (18, [1, 1, 4, 9]), (8, [1, 1, 5, 8]), (24, [1, 1, 6, 7]), (3, [1, 2, 2, 2, 2, 6]), (7, [1, 2, 2, 2, 3, 5]), (3/2, [1, 2, 2, 2, 4, 4]), (3, [1, 2, 2, 3, 3, 4]), (56, [1, 2, 2, 10]), (60, [1, 2, 3, 9])]

def vVac107Data_sector0_chunk1 : RawPoly ℕ := [(32, [1, 2, 4, 8]), (42, [1, 2, 5, 7]), (30, [1, 2, 6, 6]), (10, [1, 3, 3, 8]), (24, [1, 3, 4, 7]), (28, [1, 3, 5, 6]), (12, [1, 4, 4, 6]), (6, [1, 4, 5, 5]), (352, [1, 14]), (1/2, [2, 2, 2, 2, 3, 4]), (9, [2, 2, 2, 9]), (15, [2, 2, 3, 8]), (9, [2, 2, 4, 7]), (18, [2, 2, 5, 6]), (4, [2, 3, 3, 7]), (14, [2, 3, 4, 6]), (12, [2, 3, 5, 5]), (5, [2, 4, 4, 5]), (210, [2, 13]), (4, [3, 3, 4, 5]), (2, [3, 4, 4, 4]), (108, [3, 12]), (104, [4, 11]), (112, [5, 10])]

def vVac107Data_sector0_chunk2 : RawPoly ℕ := [(108, [6, 9]), (86, [7, 8])]

def vVac107Data_sector0 : RawPoly ℕ := [vVac107Data_sector0_chunk0, vVac107Data_sector0_chunk1, vVac107Data_sector0_chunk2].flatten

def vVac107Data : SectorVector := [(0, vVac107Data_sector0)]

theorem vVac107_check : neutralDirectS omR (-(2:ℤ)) vVac54Data = vVac107Data := by decide +kernel

theorem vVac107_value : evaluate vVac107Data = virWord (V2m 4 four_ge_one) [2, 2, 3, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 3, 4] _ _ _ vVac54_value vVac107_check

def vVac108Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 8]), (1, [1, 1, 2, 2, 2, 7]), (1, [1, 1, 2, 2, 3, 6]), (1, [1, 1, 2, 2, 4, 5]), (16, [1, 1, 2, 11]), (2, [1, 1, 5, 8]), (14, [1, 2, 2, 10]), (12, [1, 2, 3, 9]), (13, [1, 2, 4, 8]), (14, [1, 2, 5, 7]), (6, [1, 2, 6, 6]), (2, [1, 3, 5, 6]), (2, [1, 4, 5, 5]), (88, [1, 14]), (1, [2, 2, 4, 7]), (1, [2, 3, 4, 6]), (1, [2, 4, 4, 5]), (70, [2, 13]), (54, [3, 12]), (56, [4, 11]), (56, [5, 10]), (54, [6, 9]), (54, [7, 8])]

def vVac108Data : SectorVector := [(0, vVac108Data_sector0)]

theorem vVac108_check : neutralDirectS omR (-(2:ℤ)) vVac55Data = vVac108Data := by decide +kernel

theorem vVac108_value : evaluate vVac108Data = virWord (V2m 4 four_ge_one) [2, 2, 8] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 8] _ _ _ vVac55_value vVac108_check

def vVac109Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 3, 3, 3]), (3/2, [1, 1, 1, 2, 2, 2, 3, 3]), (9, [1, 1, 1, 2, 3, 7]), (9, [1, 1, 1, 3, 3, 6]), (3/4, [1, 1, 2, 2, 2, 2, 2, 3]), (9/2, [1, 1, 2, 2, 2, 7]), (15, [1, 1, 2, 2, 3, 6]), (9, [1, 1, 2, 3, 3, 5]), (21, [1, 1, 2, 11]), (3, [1, 1, 3, 3, 3, 4]), (63, [1, 1, 3, 10]), (27, [1, 1, 6, 7]), (1/8, [1, 2, 2, 2, 2, 2, 2, 2]), (21/4, [1, 2, 2, 2, 2, 6]), (15/2, [1, 2, 2, 2, 3, 5]), (3, [1, 2, 2, 3, 3, 4]), (87/2, [1, 2, 2, 10]), (41, [1, 2, 3, 9]), (24, [1, 2, 5, 7]), (22, [1, 2, 6, 6]), (15, [1, 3, 3, 8]), (18, [1, 3, 4, 7]), (30, [1, 3, 5, 6]), (231, [1, 14])]

def vVac109Data_sector0_chunk1 : RawPoly ℕ := [(3/2, [2, 2, 2, 2, 2, 5]), (3/4, [2, 2, 2, 2, 3, 4]), (18, [2, 2, 2, 9]), (15/2, [2, 2, 3, 8]), (9/2, [2, 2, 4, 7]), (45/2, [2, 2, 5, 6]), (6, [2, 3, 4, 6]), (6, [2, 3, 5, 5]), (120, [2, 13]), (3, [3, 3, 4, 5]), (45, [3, 12]), (21, [4, 11]), (66, [5, 10]), (63, [6, 9]), (30, [7, 8])]

def vVac109Data_sector0 : RawPoly ℕ := [vVac109Data_sector0_chunk0, vVac109Data_sector0_chunk1].flatten

def vVac109Data : SectorVector := [(0, vVac109Data_sector0)]

theorem vVac109_check : neutralDirectS omR (-(2:ℤ)) vVac56Data = vVac109Data := by decide +kernel

theorem vVac109_value : evaluate vVac109Data = virWord (V2m 4 four_ge_one) [2, 3, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 3, 3] _ _ _ vVac56_value vVac109_check

def vVac110Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 7]), (1/2, [1, 1, 2, 2, 2, 7]), (1, [1, 1, 2, 2, 3, 6]), (1, [1, 1, 2, 3, 3, 5]), (1/2, [1, 1, 2, 3, 4, 4]), (7, [1, 1, 2, 11]), (7, [1, 1, 3, 10]), (3, [1, 1, 6, 7]), (1/2, [1, 2, 2, 2, 2, 6]), (1/2, [1, 2, 2, 2, 3, 5]), (1/4, [1, 2, 2, 2, 4, 4]), (19/2, [1, 2, 2, 10]), (11, [1, 2, 3, 9]), (4, [1, 2, 4, 8]), (6, [1, 2, 5, 7]), (5, [1, 2, 6, 6]), (5, [1, 3, 3, 8]), (6, [1, 3, 4, 7]), (8, [1, 3, 5, 6]), (3/2, [1, 4, 4, 6]), (77, [1, 14]), (3, [2, 2, 2, 9]), (5/2, [2, 2, 3, 8]), (5/2, [2, 2, 4, 7])]

def vVac110Data_sector0_chunk1 : RawPoly ℕ := [(9/2, [2, 2, 5, 6]), (1, [2, 3, 4, 6]), (2, [2, 3, 5, 5]), (1, [2, 4, 4, 5]), (60, [2, 13]), (1, [3, 3, 4, 5]), (1/2, [3, 4, 4, 4]), (45, [3, 12]), (39, [4, 11]), (40, [5, 10]), (39, [6, 9]), (36, [7, 8])]

def vVac110Data_sector0 : RawPoly ℕ := [vVac110Data_sector0_chunk0, vVac110Data_sector0_chunk1].flatten

def vVac110Data : SectorVector := [(0, vVac110Data_sector0)]

theorem vVac110_check : neutralDirectS omR (-(2:ℤ)) vVac57Data = vVac110Data := by decide +kernel

theorem vVac110_value : evaluate vVac110Data = virWord (V2m 4 four_ge_one) [2, 3, 7] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 7] _ _ _ vVac57_value vVac110_check

def vVac111Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 4, 6]), (1, [1, 1, 2, 2, 3, 6]), (1, [1, 1, 2, 2, 4, 5]), (1, [1, 1, 2, 3, 4, 4]), (6, [1, 1, 2, 11]), (6, [1, 1, 4, 9]), (4, [1, 1, 6, 7]), (1, [1, 2, 2, 2, 3, 5]), (1, [1, 2, 2, 3, 3, 4]), (5, [1, 2, 2, 10]), (10, [1, 2, 3, 9]), (8, [1, 2, 4, 8]), (6, [1, 2, 5, 7]), (4, [1, 2, 6, 6]), (8, [1, 3, 4, 7]), (2, [1, 3, 5, 6]), (5, [1, 4, 4, 6]), (2, [1, 4, 5, 5]), (66, [1, 14]), (5, [2, 2, 3, 8]), (3, [2, 2, 5, 6]), (4, [2, 3, 3, 7]), (7, [2, 3, 4, 6]), (4, [2, 3, 5, 5])]

def vVac111Data_sector0_chunk1 : RawPoly ℕ := [(1, [2, 4, 4, 5]), (50, [2, 13]), (2, [3, 3, 4, 5]), (1, [3, 4, 4, 4]), (36, [3, 12]), (30, [4, 11]), (24, [5, 10]), (24, [6, 9]), (22, [7, 8])]

def vVac111Data_sector0 : RawPoly ℕ := [vVac111Data_sector0_chunk0, vVac111Data_sector0_chunk1].flatten

def vVac111Data : SectorVector := [(0, vVac111Data_sector0)]

theorem vVac111_check : neutralDirectS omR (-(2:ℤ)) vVac58Data = vVac111Data := by decide +kernel

theorem vVac111_value : evaluate vVac111Data = virWord (V2m 4 four_ge_one) [2, 4, 6] (evaluate vacuumData) :=
  virWord_cached_step 2 [4, 6] _ _ _ vVac58_value vVac111_check
end VOA.Classification.COne.OrbC2h
