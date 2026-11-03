/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFast

/-! # Fast W(2) Zhu recurrence: square -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 2000000 in
-- The direct Virasoro recurrence avoids expanding the generic omega field.
set_option maxRecDepth 100000 in
theorem omegaPower2FastSparseQ_eq_expected :
    omegaPowerFastSparseQ 2 = omegaPower2ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [omegaPowerFastSparseQ, zhuOmegaPartsFastSparseQ, zhuOmegaPartFastSparseQ,
     omegaPower2ExpectedQ, flattenGradedSparseQ, vacuumSparseQ, virActSparseQ,
     virVacuumSparseQ, virShiftRawQ, mulSparseQ, bindQ, sumQ, addQ, scaleQ,
     normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
     List.range_succ, List.range_zero, List.map_cons, List.map_nil,
     List.flatMap_cons, List.flatMap_nil, Function.comp_apply]

#print axioms omegaPower2FastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
