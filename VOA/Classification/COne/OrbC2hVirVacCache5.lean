import VOA.Classification.COne.OrbC2hVirVacCache4
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vVac80Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 3, 5]), (1/8, [1, 1, 1, 1, 1, 2, 2, 5]), (1/4, [1, 1, 1, 1, 1, 2, 3, 4]), (1/8, [1, 1, 1, 1, 1, 3, 3, 3]), (5/4, [1, 1, 1, 1, 1, 9]), (1/8, [1, 1, 1, 1, 2, 2, 2, 4]), (1/16, [1, 1, 1, 1, 2, 2, 3, 3]), (1, [1, 1, 1, 1, 2, 8]), (23/4, [1, 1, 1, 1, 3, 7]), (1/2, [1, 1, 1, 1, 4, 6]), (13/4, [1, 1, 1, 1, 5, 5]), (5/2, [1, 1, 1, 2, 2, 7]), (4, [1, 1, 1, 2, 3, 6]), (5, [1, 1, 1, 2, 4, 5]), (15/2, [1, 1, 1, 3, 3, 5]), (2, [1, 1, 1, 3, 4, 4]), (45, [1, 1, 1, 11]), (2, [1, 1, 2, 2, 2, 6]), (5/2, [1, 1, 2, 2, 3, 5]), (3, [1, 1, 2, 2, 4, 4]), (3, [1, 1, 2, 3, 3, 4]), (32, [1, 1, 2, 10]), (1, [1, 1, 3, 3, 3, 3]), (66, [1, 1, 3, 9])]

def vVac80Data_sector0_chunk1 : RawPoly ℕ := [(20, [1, 1, 4, 8]), (64, [1, 1, 5, 7]), (8, [1, 1, 6, 6]), (1/2, [1, 2, 2, 2, 3, 4]), (1/4, [1, 2, 2, 3, 3, 3]), (35/2, [1, 2, 2, 9]), (28, [1, 2, 3, 8]), (35, [1, 2, 4, 7]), (32, [1, 2, 5, 6]), (91/2, [1, 3, 3, 7]), (26, [1, 3, 4, 6]), (46, [1, 3, 5, 5]), (16, [1, 4, 4, 5]), (495, [1, 13]), (12, [2, 2, 2, 8]), (25/2, [2, 2, 3, 7]), (36, [2, 2, 4, 6]), (6, [2, 2, 5, 5]), (12, [2, 3, 3, 6]), (25, [2, 3, 4, 5]), (12, [2, 4, 4, 4]), (320, [2, 12]), (25/2, [3, 3, 3, 5]), (6, [3, 3, 4, 4])]

def vVac80Data_sector0_chunk2 : RawPoly ℕ := [(279, [3, 11]), (224, [4, 10]), (211, [5, 9]), (176, [6, 8]), (95, [7, 7])]

def vVac80Data_sector0 : RawPoly ℕ := [vVac80Data_sector0_chunk0, vVac80Data_sector0_chunk1, vVac80Data_sector0_chunk2].flatten

def vVac80Data : SectorVector := [(0, vVac80Data_sector0)]

theorem vVac80_check : neutralDirectS omR (-(1:ℤ)) vVac49Data = vVac80Data := by decide +kernel

theorem vVac80_value : evaluate vVac80Data = virWord (V2m 4 four_ge_one) [1, 1, 3, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 3, 5] _ _ _ vVac49_value vVac80_check

def vVac81Data_sector0_chunk0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 1, 4, 4]), (1/2, [1, 1, 1, 1, 1, 2, 3, 4]), (1, [1, 1, 1, 1, 1, 9]), (1/4, [1, 1, 1, 1, 2, 2, 3, 3]), (3/4, [1, 1, 1, 1, 2, 8]), (1/2, [1, 1, 1, 1, 3, 7]), (33/4, [1, 1, 1, 1, 4, 6]), (8, [1, 1, 1, 2, 3, 6]), (6, [1, 1, 1, 2, 4, 5]), (7, [1, 1, 1, 3, 4, 4]), (36, [1, 1, 1, 11]), (6, [1, 1, 2, 2, 3, 5]), (8, [1, 1, 2, 3, 3, 4]), (24, [1, 1, 2, 10]), (22, [1, 1, 3, 9]), (60, [1, 1, 4, 8]), (6, [1, 1, 5, 7]), (36, [1, 1, 6, 6]), (1, [1, 2, 2, 3, 3, 3]), (51, [1, 2, 3, 8]), (30, [1, 2, 4, 7]), (48, [1, 2, 5, 6]), (2, [1, 3, 3, 7]), (81, [1, 3, 4, 6])]

def vVac81Data_sector0_chunk1 : RawPoly ℕ := [(30, [1, 4, 4, 5]), (396, [1, 13]), (30, [2, 2, 3, 7]), (18, [2, 2, 5, 5]), (32, [2, 3, 3, 6]), (66, [2, 3, 4, 5]), (240, [2, 12]), (18, [3, 3, 4, 4]), (198, [3, 11]), (144, [4, 10]), (96, [5, 9]), (96, [6, 8]), (30, [7, 7])]

def vVac81Data_sector0 : RawPoly ℕ := [vVac81Data_sector0_chunk0, vVac81Data_sector0_chunk1].flatten

def vVac81Data : SectorVector := [(0, vVac81Data_sector0)]

theorem vVac81_check : neutralDirectS omR (-(1:ℤ)) vVac50Data = vVac81Data := by decide +kernel

theorem vVac81_value : evaluate vVac81Data = virWord (V2m 4 four_ge_one) [1, 1, 4, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 4, 4] _ _ _ vVac50_value vVac81_check

def vVac82Data_sector0 : RawPoly ℕ := [(1/4, [1, 1, 1, 1, 1, 9]), (1/4, [1, 1, 1, 1, 2, 8]), (1/4, [1, 1, 1, 1, 3, 7]), (1/4, [1, 1, 1, 1, 4, 6]), (1/8, [1, 1, 1, 1, 5, 5]), (9, [1, 1, 1, 11]), (8, [1, 1, 2, 10]), (9, [1, 1, 3, 9]), (8, [1, 1, 4, 8]), (8, [1, 1, 5, 7]), (4, [1, 1, 6, 6]), (1, [1, 2, 3, 8]), (1, [1, 3, 3, 7]), (1, [1, 3, 4, 6]), (1/2, [1, 3, 5, 5]), (99, [1, 13]), (80, [2, 12]), (81, [3, 11]), (80, [4, 10]), (80, [5, 9]), (80, [6, 8]), (40, [7, 7])]

def vVac82Data : SectorVector := [(0, vVac82Data_sector0)]

theorem vVac82_check : neutralDirectS omR (-(1:ℤ)) vVac51Data = vVac82Data := by decide +kernel

theorem vVac82_value : evaluate vVac82Data = virWord (V2m 4 four_ge_one) [1, 1, 9] (evaluate vacuumData) :=
  virWord_cached_step 1 [1, 9] _ _ _ vVac51_value vVac82_check

def vVac83Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]), (6, [1, 1, 1, 1, 1, 2, 2, 5]), (11, [1, 1, 1, 1, 2, 2, 2, 4]), (20, [1, 1, 1, 1, 2, 8]), (6, [1, 1, 1, 1, 5, 5]), (4, [1, 1, 1, 2, 2, 2, 2, 3]), (68, [1, 1, 1, 2, 2, 7]), (62, [1, 1, 1, 2, 4, 5]), (40, [1, 1, 1, 11]), (24, [1, 1, 2, 2, 2, 6]), (36, [1, 1, 2, 2, 3, 5]), (75/2, [1, 1, 2, 2, 4, 4]), (334, [1, 1, 2, 10]), (95, [1, 1, 4, 8]), (132, [1, 1, 5, 7]), (12, [1, 2, 2, 2, 3, 4]), (112, [1, 2, 2, 9]), (80, [1, 2, 3, 8]), (204, [1, 2, 4, 7]), (112, [1, 2, 5, 6]), (24, [1, 3, 5, 5]), (56, [1, 4, 4, 5]), (880, [1, 13]), (16, [2, 2, 3, 7])]

def vVac83Data_sector0_chunk1 : RawPoly ℕ := [(24, [2, 2, 4, 6]), (28, [2, 3, 4, 5]), (12, [2, 4, 4, 4]), (280, [2, 12]), (80, [3, 11]), (296, [4, 10]), (168, [5, 9]), (120, [6, 8]), (120, [7, 7])]

def vVac83Data_sector0 : RawPoly ℕ := [vVac83Data_sector0_chunk0, vVac83Data_sector0_chunk1].flatten

def vVac83Data : SectorVector := [(0, vVac83Data_sector0)]

theorem vVac83_check : neutralDirectS omR (-(1:ℤ)) vVac52Data = vVac83Data := by decide +kernel

theorem vVac83_value : evaluate vVac83Data = virWord (V2m 4 four_ge_one) [1, 2, 2, 2, 2] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 2, 2, 2] _ _ _ vVac52_value vVac83_check

def vVac84Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 1, 2, 2, 5]), (1/2, [1, 1, 1, 1, 2, 2, 2, 4]), (1/4, [1, 1, 1, 1, 2, 2, 3, 3]), (5, [1, 1, 1, 1, 2, 8]), (1, [1, 1, 1, 1, 5, 5]), (9, [1, 1, 1, 2, 2, 7]), (3, [1, 1, 1, 2, 3, 6]), (17/2, [1, 1, 1, 2, 4, 5]), (1/2, [1, 1, 1, 3, 3, 5]), (20, [1, 1, 1, 11]), (4, [1, 1, 2, 2, 2, 6]), (6, [1, 1, 2, 2, 3, 5]), (13/2, [1, 1, 2, 2, 4, 4]), (9/4, [1, 1, 2, 3, 3, 4]), (94, [1, 1, 2, 10]), (9, [1, 1, 3, 9]), (30, [1, 1, 4, 8]), (30, [1, 1, 5, 7]), (9/2, [1, 1, 6, 6]), (2, [1, 2, 2, 2, 3, 4]), (1, [1, 2, 2, 3, 3, 3]), (56, [1, 2, 2, 9]), (56, [1, 2, 3, 8]), (77, [1, 2, 4, 7])]

def vVac84Data_sector0_chunk1 : RawPoly ℕ := [(54, [1, 2, 5, 6]), (5, [1, 3, 3, 7]), (12, [1, 3, 4, 6]), (10, [1, 3, 5, 5]), (18, [1, 4, 4, 5]), (440, [1, 13]), (8, [2, 2, 3, 7]), (8, [2, 2, 4, 6]), (8, [2, 3, 3, 6]), (12, [2, 3, 4, 5]), (4, [2, 4, 4, 4]), (280, [2, 12]), (1, [3, 3, 3, 5]), (1, [3, 3, 4, 4]), (202, [3, 11]), (216, [4, 10]), (194, [5, 9]), (188, [6, 8]), (100, [7, 7])]

def vVac84Data_sector0 : RawPoly ℕ := [vVac84Data_sector0_chunk0, vVac84Data_sector0_chunk1].flatten

def vVac84Data : SectorVector := [(0, vVac84Data_sector0)]

theorem vVac84_check : neutralDirectS omR (-(1:ℤ)) vVac53Data = vVac84Data := by decide +kernel

theorem vVac84_value : evaluate vVac84Data = virWord (V2m 4 four_ge_one) [1, 2, 2, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 2, 5] _ _ _ vVac53_value vVac84_check

def vVac85Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 1, 2, 3, 4]), (1/4, [1, 1, 1, 1, 2, 2, 2, 4]), (1/2, [1, 1, 1, 1, 2, 2, 3, 3]), (2, [1, 1, 1, 1, 2, 8]), (2, [1, 1, 1, 1, 3, 7]), (3/2, [1, 1, 1, 1, 4, 6]), (1/4, [1, 1, 1, 2, 2, 2, 2, 3]), (5/2, [1, 1, 1, 2, 2, 7]), (8, [1, 1, 1, 2, 3, 6]), (9/2, [1, 1, 1, 2, 4, 5]), (1, [1, 1, 1, 3, 3, 5]), (3, [1, 1, 1, 3, 4, 4]), (16, [1, 1, 1, 11]), (11/4, [1, 1, 2, 2, 2, 6]), (15/2, [1, 1, 2, 2, 3, 5]), (13/4, [1, 1, 2, 2, 4, 4]), (15/2, [1, 1, 2, 3, 3, 4]), (85/2, [1, 1, 2, 10]), (34, [1, 1, 3, 9]), (61/2, [1, 1, 4, 8]), (17, [1, 1, 5, 7]), (15, [1, 1, 6, 6]), (3/2, [1, 2, 2, 2, 2, 5]), (5, [1, 2, 2, 2, 3, 4])]

def vVac85Data_sector0_chunk1 : RawPoly ℕ := [(2, [1, 2, 2, 3, 3, 3]), (35, [1, 2, 2, 9]), (56, [1, 2, 3, 8]), (35, [1, 2, 4, 7]), (36, [1, 2, 5, 6]), (18, [1, 3, 3, 7]), (38, [1, 3, 4, 6]), (12, [1, 3, 5, 5]), (12, [1, 4, 4, 5]), (352, [1, 13]), (1/2, [2, 2, 2, 2, 3, 3]), (9, [2, 2, 2, 8]), (20, [2, 2, 3, 7]), (13, [2, 2, 4, 6]), (9, [2, 2, 5, 5]), (12, [2, 3, 3, 6]), (21, [2, 3, 4, 5]), (2, [2, 4, 4, 4]), (210, [2, 12]), (2, [3, 3, 3, 5]), (4, [3, 3, 4, 4]), (140, [3, 11]), (114, [4, 10]), (106, [5, 9])]

def vVac85Data_sector0_chunk2 : RawPoly ℕ := [(108, [6, 8]), (50, [7, 7])]

def vVac85Data_sector0 : RawPoly ℕ := [vVac85Data_sector0_chunk0, vVac85Data_sector0_chunk1, vVac85Data_sector0_chunk2].flatten

def vVac85Data : SectorVector := [(0, vVac85Data_sector0)]

theorem vVac85_check : neutralDirectS omR (-(1:ℤ)) vVac54Data = vVac85Data := by decide +kernel

theorem vVac85_value : evaluate vVac85Data = virWord (V2m 4 four_ge_one) [1, 2, 3, 4] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 3, 4] _ _ _ vVac54_value vVac85_check

def vVac86Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 2, 8]), (1/2, [1, 1, 1, 2, 2, 7]), (1/2, [1, 1, 1, 2, 3, 6]), (1/2, [1, 1, 1, 2, 4, 5]), (4, [1, 1, 1, 11]), (23/2, [1, 1, 2, 10]), (3, [1, 1, 3, 9]), (5, [1, 1, 4, 8]), (3, [1, 1, 5, 7]), (3/2, [1, 1, 6, 6]), (7, [1, 2, 2, 9]), (8, [1, 2, 3, 8]), (9, [1, 2, 4, 7]), (7, [1, 2, 5, 6]), (2, [1, 3, 4, 6]), (2, [1, 4, 4, 5]), (88, [1, 13]), (1, [2, 2, 3, 7]), (1, [2, 3, 3, 6]), (1, [2, 3, 4, 5]), (70, [2, 12]), (62, [3, 11]), (62, [4, 10]), (60, [5, 9])]

def vVac86Data_sector0_chunk1 : RawPoly ℕ := [(60, [6, 8]), (30, [7, 7])]

def vVac86Data_sector0 : RawPoly ℕ := [vVac86Data_sector0_chunk0, vVac86Data_sector0_chunk1].flatten

def vVac86Data : SectorVector := [(0, vVac86Data_sector0)]

theorem vVac86_check : neutralDirectS omR (-(1:ℤ)) vVac55Data = vVac86Data := by decide +kernel

theorem vVac86_value : evaluate vVac86Data = virWord (V2m 4 four_ge_one) [1, 2, 8] (evaluate vacuumData) :=
  virWord_cached_step 1 [2, 8] _ _ _ vVac55_value vVac86_check

def vVac87Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 1, 3, 3, 3]), (3/4, [1, 1, 1, 1, 2, 2, 3, 3]), (9/2, [1, 1, 1, 1, 3, 7]), (3/8, [1, 1, 1, 2, 2, 2, 2, 3]), (9/4, [1, 1, 1, 2, 2, 7]), (3, [1, 1, 1, 2, 3, 6]), (21/2, [1, 1, 1, 3, 3, 5]), (21/2, [1, 1, 1, 11]), (1/16, [1, 1, 2, 2, 2, 2, 2, 2]), (3/2, [1, 1, 2, 2, 2, 6]), (39/4, [1, 1, 2, 2, 3, 5]), (6, [1, 1, 2, 3, 3, 4]), (6, [1, 1, 2, 10]), (3, [1, 1, 3, 3, 3, 3]), (131/2, [1, 1, 3, 9]), (30, [1, 1, 5, 7]), (2, [1, 1, 6, 6]), (9/4, [1, 2, 2, 2, 2, 5]), (6, [1, 2, 2, 2, 3, 4]), (3, [1, 2, 2, 3, 3, 3]), (63/2, [1, 2, 2, 9]), (36, [1, 2, 3, 8]), (18, [1, 2, 4, 7]), (18, [1, 2, 5, 6])]

def vVac87Data_sector0_chunk1 : RawPoly ℕ := [(33, [1, 3, 3, 7]), (12, [1, 3, 4, 6]), (18, [1, 3, 5, 5]), (231, [1, 13]), (3/2, [2, 2, 2, 2, 2, 4]), (3/4, [2, 2, 2, 2, 3, 3]), (18, [2, 2, 2, 8]), (12, [2, 2, 3, 7]), (18, [2, 2, 4, 6]), (9/2, [2, 2, 5, 5]), (6, [2, 3, 3, 6]), (6, [2, 3, 4, 5]), (120, [2, 12]), (3, [3, 3, 3, 5]), (66, [3, 11]), (24, [4, 10]), (57, [5, 9]), (48, [6, 8]), (30, [7, 7])]

def vVac87Data_sector0 : RawPoly ℕ := [vVac87Data_sector0_chunk0, vVac87Data_sector0_chunk1].flatten

def vVac87Data : SectorVector := [(0, vVac87Data_sector0)]

theorem vVac87_check : neutralDirectS omR (-(1:ℤ)) vVac56Data = vVac87Data := by decide +kernel

theorem vVac87_value : evaluate vVac87Data = virWord (V2m 4 four_ge_one) [1, 3, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 1 [3, 3, 3] _ _ _ vVac56_value vVac87_check

def vVac88Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 3, 7]), (1/4, [1, 1, 1, 2, 2, 7]), (1/2, [1, 1, 1, 2, 3, 6]), (1/2, [1, 1, 1, 3, 3, 5]), (1/4, [1, 1, 1, 3, 4, 4]), (7/2, [1, 1, 1, 11]), (1/4, [1, 1, 2, 2, 2, 6]), (1/4, [1, 1, 2, 2, 3, 5]), (1/8, [1, 1, 2, 2, 4, 4]), (3, [1, 1, 2, 10]), (19/2, [1, 1, 3, 9]), (2, [1, 1, 4, 8]), (5, [1, 1, 5, 7]), (1, [1, 1, 6, 6]), (7/2, [1, 2, 2, 9]), (6, [1, 2, 3, 8]), (2, [1, 2, 4, 7]), (3, [1, 2, 5, 6]), (7, [1, 3, 3, 7]), (6, [1, 3, 4, 6]), (6, [1, 3, 5, 5]), (3/2, [1, 4, 4, 5]), (77, [1, 13]), (3, [2, 2, 2, 8])]

def vVac88Data_sector0_chunk1 : RawPoly ℕ := [(3, [2, 2, 3, 7]), (5, [2, 2, 4, 6]), (3/2, [2, 2, 5, 5]), (1, [2, 3, 3, 6]), (2, [2, 3, 4, 5]), (1, [2, 4, 4, 4]), (60, [2, 12]), (1, [3, 3, 3, 5]), (1/2, [3, 3, 4, 4]), (52, [3, 11]), (44, [4, 10]), (43, [5, 9]), (40, [6, 8]), (20, [7, 7])]

def vVac88Data_sector0 : RawPoly ℕ := [vVac88Data_sector0_chunk0, vVac88Data_sector0_chunk1].flatten

def vVac88Data : SectorVector := [(0, vVac88Data_sector0)]

theorem vVac88_check : neutralDirectS omR (-(1:ℤ)) vVac57Data = vVac88Data := by decide +kernel

theorem vVac88_value : evaluate vVac88Data = virWord (V2m 4 four_ge_one) [1, 3, 7] (evaluate vacuumData) :=
  virWord_cached_step 1 [3, 7] _ _ _ vVac57_value vVac88_check

def vVac89Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 4, 6]), (1/2, [1, 1, 1, 2, 3, 6]), (1/2, [1, 1, 1, 2, 4, 5]), (1/2, [1, 1, 1, 3, 4, 4]), (3, [1, 1, 1, 11]), (1/2, [1, 1, 2, 2, 3, 5]), (1/2, [1, 1, 2, 3, 3, 4]), (5/2, [1, 1, 2, 10]), (2, [1, 1, 3, 9]), (15/2, [1, 1, 4, 8]), (1, [1, 1, 5, 7]), (9/2, [1, 1, 6, 6]), (6, [1, 2, 3, 8]), (5, [1, 2, 4, 7]), (7, [1, 2, 5, 6]), (12, [1, 3, 4, 6]), (5, [1, 4, 4, 5]), (66, [1, 13]), (5, [2, 2, 3, 7]), (3, [2, 2, 5, 5]), (5, [2, 3, 3, 6]), (11, [2, 3, 4, 5]), (50, [2, 12]), (3, [3, 3, 4, 4])]

def vVac89Data_sector0_chunk1 : RawPoly ℕ := [(42, [3, 11]), (34, [4, 10]), (26, [5, 9]), (24, [6, 8]), (10, [7, 7])]

def vVac89Data_sector0 : RawPoly ℕ := [vVac89Data_sector0_chunk0, vVac89Data_sector0_chunk1].flatten

def vVac89Data : SectorVector := [(0, vVac89Data_sector0)]

theorem vVac89_check : neutralDirectS omR (-(1:ℤ)) vVac58Data = vVac89Data := by decide +kernel

theorem vVac89_value : evaluate vVac89Data = virWord (V2m 4 four_ge_one) [1, 4, 6] (evaluate vacuumData) :=
  virWord_cached_step 1 [4, 6] _ _ _ vVac58_value vVac89_check

def vVac90Data_sector0_chunk0 : RawPoly ℕ := [(1/2, [1, 1, 1, 1, 5, 5]), (1, [1, 1, 1, 2, 4, 5]), (1/2, [1, 1, 1, 3, 3, 5]), (5/2, [1, 1, 1, 11]), (1/2, [1, 1, 2, 2, 4, 4]), (1/2, [1, 1, 2, 3, 3, 4]), (2, [1, 1, 2, 10]), (1/8, [1, 1, 3, 3, 3, 3]), (3/2, [1, 1, 3, 9]), (1, [1, 1, 4, 8]), (21/2, [1, 1, 5, 7]), (10, [1, 2, 4, 7]), (8, [1, 2, 5, 6]), (5, [1, 3, 3, 7]), (8, [1, 3, 5, 5]), (4, [1, 4, 4, 5]), (55, [1, 13]), (8, [2, 2, 4, 6]), (4, [2, 3, 3, 6]), (8, [2, 3, 4, 5]), (4, [2, 4, 4, 4]), (40, [2, 12]), (4, [3, 3, 3, 5]), (2, [3, 3, 4, 4])]

def vVac90Data_sector0_chunk1 : RawPoly ℕ := [(32, [3, 11]), (24, [4, 10]), (16, [5, 9]), (8, [6, 8]), (5, [7, 7])]

def vVac90Data_sector0 : RawPoly ℕ := [vVac90Data_sector0_chunk0, vVac90Data_sector0_chunk1].flatten

def vVac90Data : SectorVector := [(0, vVac90Data_sector0)]

theorem vVac90_check : neutralDirectS omR (-(1:ℤ)) vVac59Data = vVac90Data := by decide +kernel

theorem vVac90_value : evaluate vVac90Data = virWord (V2m 4 four_ge_one) [1, 5, 5] (evaluate vacuumData) :=
  virWord_cached_step 1 [5, 5] _ _ _ vVac59_value vVac90_check

def vVac91Data_sector0 : RawPoly ℕ := [(1/2, [1, 1, 1, 11]), (1/2, [1, 1, 2, 10]), (1/2, [1, 1, 3, 9]), (1/2, [1, 1, 4, 8]), (1/2, [1, 1, 5, 7]), (1/4, [1, 1, 6, 6]), (11, [1, 13]), (10, [2, 12]), (10, [3, 11]), (10, [4, 10]), (10, [5, 9]), (10, [6, 8]), (5, [7, 7])]

def vVac91Data : SectorVector := [(0, vVac91Data_sector0)]

theorem vVac91_check : neutralDirectS omR (-(1:ℤ)) vVac60Data = vVac91Data := by decide +kernel

theorem vVac91_value : evaluate vVac91Data = virWord (V2m 4 four_ge_one) [1, 11] (evaluate vacuumData) :=
  virWord_cached_step 1 [11] _ _ _ vVac60_value vVac91_check

def vVac92Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 2, 4]), (1, [1, 1, 1, 2, 2, 2, 2, 3]), (12, [1, 1, 1, 2, 2, 7]), (6, [1, 1, 1, 2, 4, 5]), (9, [1, 1, 2, 2, 2, 6]), (12, [1, 1, 2, 2, 3, 5]), (6, [1, 1, 2, 2, 4, 4]), (84, [1, 1, 2, 10]), (10, [1, 1, 4, 8]), (24, [1, 1, 5, 7]), (3, [1, 2, 2, 2, 3, 4]), (54, [1, 2, 2, 9]), (40, [1, 2, 3, 8]), (52, [1, 2, 4, 7]), (54, [1, 2, 5, 6]), (12, [1, 3, 5, 5]), (10, [1, 4, 4, 5]), (280, [1, 13]), (4, [2, 2, 3, 7]), (9, [2, 2, 4, 6]), (10, [2, 3, 4, 5]), (3, [2, 4, 4, 4]), (162, [2, 12]), (80, [3, 11])]

def vVac92Data_sector0_chunk1 : RawPoly ℕ := [(112, [4, 10]), (108, [5, 9]), (90, [6, 8]), (48, [7, 7])]

def vVac92Data_sector0 : RawPoly ℕ := [vVac92Data_sector0_chunk0, vVac92Data_sector0_chunk1].flatten

def vVac92Data : SectorVector := [(0, vVac92Data_sector0)]

theorem vVac92_check : neutralDirectS omR (-(2:ℤ)) vVac34Data = vVac92Data := by decide +kernel

theorem vVac92_value : evaluate vVac92Data = virWord (V2m 4 four_ge_one) [2, 2, 2, 4] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 2, 4] _ _ _ vVac34_value vVac92_check

def vVac93Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 1, 2, 2, 3, 3]), (1, [1, 1, 1, 2, 2, 2, 2, 3]), (3, [1, 1, 1, 2, 2, 7]), (12, [1, 1, 1, 2, 3, 6]), (2, [1, 1, 1, 3, 3, 5]), (1/4, [1, 1, 2, 2, 2, 2, 2, 2]), (8, [1, 1, 2, 2, 2, 6]), (11, [1, 1, 2, 2, 3, 5]), (5, [1, 1, 2, 3, 3, 4]), (42, [1, 1, 2, 10]), (36, [1, 1, 3, 9]), (6, [1, 1, 5, 7]), (18, [1, 1, 6, 6]), (9/2, [1, 2, 2, 2, 2, 5]), (3, [1, 2, 2, 2, 3, 4]), (42, [1, 2, 2, 9]), (30, [1, 2, 3, 8]), (9, [1, 2, 4, 7]), (42, [1, 2, 5, 6]), (8, [1, 3, 3, 7]), (24, [1, 3, 4, 6]), (10, [1, 3, 5, 5]), (210, [1, 13]), (1/4, [2, 2, 2, 2, 2, 4])]

def vVac93Data_sector0_chunk1 : RawPoly ℕ := [(10, [2, 2, 2, 8]), (4, [2, 2, 3, 7]), (8, [2, 2, 4, 6]), (12, [2, 2, 5, 5]), (9, [2, 3, 4, 5]), (108, [2, 12]), (2, [3, 3, 4, 4]), (40, [3, 11]), (42, [4, 10]), (66, [5, 9]), (50, [6, 8]), (12, [7, 7])]

def vVac93Data_sector0 : RawPoly ℕ := [vVac93Data_sector0_chunk0, vVac93Data_sector0_chunk1].flatten

def vVac93Data : SectorVector := [(0, vVac93Data_sector0)]

theorem vVac93_check : neutralDirectS omR (-(2:ℤ)) vVac35Data = vVac93Data := by decide +kernel

theorem vVac93_value : evaluate vVac93Data = virWord (V2m 4 four_ge_one) [2, 2, 3, 3] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 3, 3] _ _ _ vVac35_value vVac93_check

def vVac94Data_sector0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 2, 7]), (1, [1, 1, 2, 2, 2, 6]), (1, [1, 1, 2, 2, 3, 5]), (1/2, [1, 1, 2, 2, 4, 4]), (14, [1, 1, 2, 10]), (2, [1, 1, 5, 7]), (12, [1, 2, 2, 9]), (10, [1, 2, 3, 8]), (11, [1, 2, 4, 7]), (12, [1, 2, 5, 6]), (2, [1, 3, 5, 5]), (1, [1, 4, 4, 5]), (70, [1, 13]), (1, [2, 2, 4, 6]), (1, [2, 3, 4, 5]), (1/2, [2, 4, 4, 4]), (54, [2, 12]), (40, [3, 11]), (42, [4, 10]), (42, [5, 9]), (40, [6, 8]), (20, [7, 7])]

def vVac94Data : SectorVector := [(0, vVac94Data_sector0)]

theorem vVac94_check : neutralDirectS omR (-(2:ℤ)) vVac36Data = vVac94Data := by decide +kernel

theorem vVac94_value : evaluate vVac94Data = virWord (V2m 4 four_ge_one) [2, 2, 7] (evaluate vacuumData) :=
  virWord_cached_step 2 [2, 7] _ _ _ vVac36_value vVac94_check

def vVac95Data_sector0_chunk0 : RawPoly ℕ := [(1, [1, 1, 1, 2, 3, 6]), (1/2, [1, 1, 2, 2, 2, 6]), (1, [1, 1, 2, 2, 3, 5]), (1, [1, 1, 2, 3, 3, 4]), (6, [1, 1, 2, 10]), (6, [1, 1, 3, 9]), (3, [1, 1, 6, 6]), (1/2, [1, 2, 2, 2, 2, 5]), (1/2, [1, 2, 2, 2, 3, 4]), (8, [1, 2, 2, 9]), (9, [1, 2, 3, 8]), (3, [1, 2, 4, 7]), (8, [1, 2, 5, 6]), (4, [1, 3, 3, 7]), (8, [1, 3, 4, 6]), (2, [1, 3, 5, 5]), (60, [1, 13]), (5/2, [2, 2, 2, 8]), (2, [2, 2, 3, 7]), (2, [2, 2, 4, 6]), (3, [2, 2, 5, 5]), (3, [2, 3, 4, 5]), (45, [2, 12]), (1, [3, 3, 4, 4])]

def vVac95Data_sector0_chunk1 : RawPoly ℕ := [(32, [3, 11]), (27, [4, 10]), (28, [5, 9]), (27, [6, 8]), (12, [7, 7])]

def vVac95Data_sector0 : RawPoly ℕ := [vVac95Data_sector0_chunk0, vVac95Data_sector0_chunk1].flatten

def vVac95Data : SectorVector := [(0, vVac95Data_sector0)]

theorem vVac95_check : neutralDirectS omR (-(2:ℤ)) vVac37Data = vVac95Data := by decide +kernel

theorem vVac95_value : evaluate vVac95Data = virWord (V2m 4 four_ge_one) [2, 3, 6] (evaluate vacuumData) :=
  virWord_cached_step 2 [3, 6] _ _ _ vVac37_value vVac95_check
end VOA.Classification.COne.OrbC2h
