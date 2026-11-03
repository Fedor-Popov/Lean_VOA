/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL2Tail
import VOA.Examples.TripletWpTwoZhuSparseL22CollectB

/-! # Specialized translation certificate for the L(-5) Zhu ledger entry -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
-- The seven-coordinate translation computation is finite but reduction-intensive.
theorem certificateL5VirVacSparseQ_eq_expected :
    evalVirVacLedger certificateL5Ledger = rhsL5ExpectedQ := by
  simp only [evalVirVacLedger, certificateL5Ledger, List.map_cons, List.map_nil,
    ZhuStateDesc.weight, ZhuStateDesc.eval]
  change sumQ [
    scaleQ (221 / 128) (virVacCircleSparseQ 5 0 vacuumSparseQ)] =
      rhsL5ExpectedQ
  norm_num (config := { maxSteps := 1000000 })
    [rhsL5ExpectedQ, virVacCircleSparseQ, virVacModeSparseQ,
    virVacModeCoefficientQ, virModeSparseQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, vacuumSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.certificateL5VirVacSparseQ_eq_expected
end AxiomAudit
