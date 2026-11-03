/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoZhuSparseCompute

/-!
# Staged sparse check of the W(2) Zhu polynomial: powers zero through two

These are closed exact-rational checks.  The displayed expected ledgers are discovery data; the
proofs replay the corrected coefficient/mode recurrence in Lean's kernel.
-/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

theorem omegaPower0SparseQ_eq_expected :
    flattenGradedSparseQ (zhuOmegaPartsSparseQ 0) = omegaPower0ExpectedQ := by
  norm_num [omegaPower0ExpectedQ, zhuOmegaPartsSparseQ, flattenGradedSparseQ,
    vacuumSparseQ, sumQ, normalizeQ, insertQ, sortWord, insertVar, insertSorted,
    compareWord]

theorem omegaPower1SparseQ_eq_expected :
    flattenGradedSparseQ (zhuOmegaPartsSparseQ 1) = omegaPower1ExpectedQ := by
  norm_num (config := { maxSteps := 2000000 })
    [omegaPower1ExpectedQ, zhuOmegaPartsSparseQ, zhuOmegaPartSparseQ,
     flattenGradedSparseQ, omegaSparseQ, vacuumSparseQ, voaModeActSparseQ,
     zhuStateActSparseQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
     intIccListQ, natRangeQ, Int.toNat, Function.comp_apply,
     aFieldActSparseQ, aFieldActMonomialQ,
     aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
     bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord, insertVar,
     insertSorted, compareWord]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
-- The depth-two branch expansion deliberately replays the complete bounded current recurrence.
theorem omegaPower2SparseQ_eq_expected :
    flattenGradedSparseQ (zhuOmegaPartsSparseQ 2) = omegaPower2ExpectedQ := by
  norm_num (config := { maxSteps := 2000000 })
    [omegaPower2ExpectedQ, zhuOmegaPartsSparseQ, zhuOmegaPartSparseQ,
     flattenGradedSparseQ, omegaSparseQ, vacuumSparseQ, voaModeActSparseQ,
     zhuStateActSparseQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
     intIccListQ, natRangeQ, Int.toNat, Function.comp_apply,
     aFieldActSparseQ, aFieldActMonomialQ,
     aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
     bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord, insertVar,
     insertSorted, compareWord]

section AxiomAudit
#print axioms omegaPower0SparseQ_eq_expected
#print axioms omegaPower1SparseQ_eq_expected
#print axioms omegaPower2SparseQ_eq_expected
end AxiomAudit

end VOA.LatGen.WpTwoZhuSparseLhs
