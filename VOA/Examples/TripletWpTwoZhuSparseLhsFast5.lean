/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFast4

/-! # Fast W(2) Zhu recurrence: fifth power -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 10000000 in
-- Starting from the stored homogeneous cube, this checks only the two final Virasoro steps.
set_option maxRecDepth 100000 in
theorem omegaPower5FastSparseQ_eq_expected :
    omegaPowerFastSparseQ 5 = omegaPower5ExpectedQ := by
  rw [omegaPowerFastSparseQ, zhuOmegaPartsFastSparseQ,
    zhuOmegaPartsFastSparseQ, zhuOmegaParts3FastSparseQ_eq_expected]
  norm_num (config := { maxSteps := 5000000 })
    [omegaParts3FastExpectedQ, zhuOmegaPartFastSparseQ, omegaPower5ExpectedQ,
     flattenGradedSparseQ, virActSparseQ, virVacuumSparseQ, virShiftRawQ,
     mulSparseQ, bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord,
     insertVar, insertSorted, compareWord, List.range_succ, List.range_zero,
     List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
     Function.comp_apply]

#print axioms omegaPower5FastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
