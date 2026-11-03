/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFast3

/-! # Fast W(2) Zhu recurrence: exact homogeneous cube -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

def omegaParts3FastExpectedQ : List (ℕ × SparseRational.Poly ℕ) :=
  [(6,
    [([0, 0, 0, 0, 0, 0], (1 / 512)),
     ([0, 0, 0, 0, 1], (3 / 256)),
     ([0, 0, 0, 2], (3 / 32)),
     ([0, 0, 1, 1], (3 / 128)),
     ([0, 0, 3], (3 / 16)),
     ([0, 1, 2], (3 / 16)),
     ([0, 4], (3 / 4)),
     ([1, 1, 1], (1 / 64)),
     ([1, 3], (3 / 8)),
     ([2, 2], (1 / 4)),
     ([5], 2)]),
   (5,
    [([0, 0, 0, 1], (1 / 8)),
     ([0, 0, 2], (1 / 4)),
     ([0, 1, 1], (1 / 4)),
     ([0, 3], (3 / 2)),
     ([1, 2], 1),
     ([4], 4)]),
   (4, [([0, 0, 0, 0], (1 / 16)), ([0, 0, 1], (1 / 4)),
     ([0, 2], 1), ([1, 1], (1 / 4)), ([3], 2)]),
   (5, [([0, 0, 0, 1], (1 / 16)), ([0, 0, 2], (1 / 8)),
     ([0, 1, 1], (1 / 8)), ([0, 3], 1), ([1, 2], (3 / 4)), ([4], 3)]),
   (4, [([0, 2], 2), ([1, 1], 1), ([3], 6)]),
   (3, [([0, 1], (3 / 2)), ([2], 3)]),
   (4, [([0, 0, 0, 0], (1 / 32)), ([0, 0, 1], (1 / 8)),
     ([0, 2], (1 / 2)), ([1, 1], (1 / 8)), ([3], 1)]),
   (3, [([0, 1], 1), ([2], 2)]),
   (2, [([0, 0], (1 / 2)), ([1], 1)]),
   (5, []), (4, []), (3, []), (4, []), (3, []), (2, []),
   (3, []), (2, []), (1, []), (4, []), (3, []), (2, []),
   (3, []), (2, []), (1, []), (2, []), (1, []), (0, [])]

set_option maxHeartbeats 4000000 in
-- This stores the homogeneous cube once, so all later powers start from a bounded ledger.
set_option maxRecDepth 100000 in
theorem zhuOmegaParts3FastSparseQ_eq_expected :
    zhuOmegaPartsFastSparseQ 3 = omegaParts3FastExpectedQ := by
  norm_num (config := { maxSteps := 2000000 })
    [zhuOmegaPartsFastSparseQ, zhuOmegaPartFastSparseQ, omegaParts3FastExpectedQ,
     vacuumSparseQ, virActSparseQ, virVacuumSparseQ, virShiftRawQ, mulSparseQ,
     bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord, insertVar,
     insertSorted, compareWord, List.range_succ, List.range_zero,
     List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
     Function.comp_apply]

#print axioms zhuOmegaParts3FastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
