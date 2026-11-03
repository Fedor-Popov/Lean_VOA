/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhs02

/-! # Staged sparse check of the W(2) Zhu polynomial: the cubic power -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
-- This stage replays all twenty-seven branches of the corrected Zhu--omega recurrence.
theorem omegaPower3SparseQ_eq_expected :
    flattenGradedSparseQ (zhuOmegaPartsSparseQ 3) = omegaPower3ExpectedQ := by
  norm_num (config := { maxSteps := 4000000 })
    [omegaPower3ExpectedQ, zhuOmegaPartsSparseQ, zhuOmegaPartSparseQ,
     flattenGradedSparseQ, omegaSparseQ, vacuumSparseQ, voaModeActSparseQ,
     zhuStateActSparseQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
     intIccListQ, natRangeQ, Int.toNat, Function.comp_apply,
     aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
     annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
     normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

#print axioms omegaPower3SparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
