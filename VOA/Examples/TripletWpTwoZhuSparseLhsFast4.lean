/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFastGraded3

/-! # Fast W(2) Zhu recurrence: fourth power -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 6000000 in
-- The homogeneous cube ledger leaves only nine nonzero parents for this step.
set_option maxRecDepth 100000 in
theorem omegaPower4FastSparseQ_eq_expected :
    omegaPowerFastSparseQ 4 = omegaPower4ExpectedQ := by
  rw [omegaPowerFastSparseQ, zhuOmegaPartsFastSparseQ,
    zhuOmegaParts3FastSparseQ_eq_expected]
  norm_num (config := { maxSteps := 3000000 })
    [omegaParts3FastExpectedQ, zhuOmegaPartFastSparseQ, omegaPower4ExpectedQ,
     flattenGradedSparseQ, virActSparseQ, virVacuumSparseQ, virShiftRawQ,
     mulSparseQ, bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord,
     insertVar, insertSorted, compareWord, List.range_succ, List.range_zero,
     List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
     Function.comp_apply]

#print axioms omegaPower4FastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
