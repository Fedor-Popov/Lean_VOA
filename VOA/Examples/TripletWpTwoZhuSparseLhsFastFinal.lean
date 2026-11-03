/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhsFast5

/-! # Fast W(2) Zhu recurrence: the factored polynomial

This final layer combines the four independently certified Virasoro powers.  It contains
no field expansion: after rewriting by the power certificates, only exact rational sparse
polynomial arithmetic remains.
-/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxHeartbeats 2000000 in
-- Rewriting the four certified powers leaves a finite exact rational normalization.
set_option maxRecDepth 100000 in
theorem fTwoFastSparseQ_eq_expected :
    fTwoFastSparseQ = fTwoExpectedQ := by
  rw [fTwoFastSparseQ, omegaPower5FastSparseQ_eq_expected,
    omegaPower4FastSparseQ_eq_expected, omegaPower3FastSparseQ_eq_expected,
    omegaPower2FastSparseQ_eq_expected]
  norm_num (config := { maxSteps := 1000000 })
    [fTwoExpectedQ, omegaPower5ExpectedQ, omegaPower4ExpectedQ,
     omegaPower3ExpectedQ, omegaPower2ExpectedQ, sumQ, addQ, scaleQ,
     normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

#print axioms fTwoFastSparseQ_eq_expected

end VOA.LatGen.WpTwoZhuSparseLhs
