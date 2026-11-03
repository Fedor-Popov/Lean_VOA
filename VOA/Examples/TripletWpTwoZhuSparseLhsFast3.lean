/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFast2

/-! # Fast W(2) Zhu recurrence: cube -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 4000000 in
-- Twenty-seven direct Virasoro branches are checked without generic field expansion.
set_option maxRecDepth 100000 in
theorem omegaPower3FastSparseQ_eq_expected :
    omegaPowerFastSparseQ 3 = omegaPower3ExpectedQ := by
  norm_num (config := { maxSteps := 2000000 })
    [omegaPowerFastSparseQ, zhuOmegaPartsFastSparseQ, zhuOmegaPartFastSparseQ,
     omegaPower3ExpectedQ, flattenGradedSparseQ, vacuumSparseQ, virActSparseQ,
     virVacuumSparseQ, virShiftRawQ, mulSparseQ, bindQ, sumQ, addQ, scaleQ,
     normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
     List.range_succ, List.range_zero, List.map_cons, List.map_nil,
     List.flatMap_cons, List.flatMap_nil, Function.comp_apply]

#print axioms omegaPower3FastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
