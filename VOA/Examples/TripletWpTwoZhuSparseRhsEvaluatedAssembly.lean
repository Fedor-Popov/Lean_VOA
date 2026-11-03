/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHEvaluatedAssembly
import VOA.Examples.TripletWpTwoZhuSparseL2Tail
import VOA.Examples.TripletWpTwoZhuSparseL3Tail
import VOA.Examples.TripletWpTwoZhuSparseL4
import VOA.Examples.TripletWpTwoZhuSparseL22CollectB
import VOA.Examples.TripletWpTwoZhuSparseRhsVirFamilies

/-! # Evaluated assembly of the complete sparse Zhu-certificate RHS -/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open VOA.SparseRational
open VOA.LatGen.WpTwoZhuSparseCompute

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
-- Merge the seven independently certified RHS families without replaying their field actions.
theorem fTwoExpectedQ_eq_sum_rhs_families :
    fTwoExpectedQ = sumQ [rhsqExpectedQ, rhsL2ExpectedQ, rhsL3ExpectedQ,
      rhsL4ExpectedQ, rhsL22ExpectedQ, rhsL5ExpectedQ, rhsHExpectedQ] := by
  norm_num (config := { maxSteps := 1000000 })
    [fTwoExpectedQ, rhsqExpectedQ, rhsL2ExpectedQ, rhsL3ExpectedQ,
    rhsL4ExpectedQ, rhsL22ExpectedQ, rhsL5ExpectedQ, rhsHExpectedQ,
    sumQ, addQ, compareWord]

/-- Assemble the screened term and all six circle families from an evaluated H-family input. -/
theorem eval_certificateRhsSparseQ_eq_expected_of_H
    (hH : evalZhuSparseQ (evalCircleLedger certificateHLedger) =
      evalZhuSparseQ rhsHExpectedQ) :
    evalZhuSparseQ certificateRhsSparseQ = evalZhuSparseQ fTwoExpectedQ := by
  rw [certificateRhsSparseQ, evalZhuSparseQ_sumQ,
    fTwoExpectedQ_eq_sum_rhs_families, evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [congrArg evalZhuSparseQ certificateQPartSparseQ_eq_expected,
    congrArg evalZhuSparseQ certificateL2SparseQ_eq_expected,
    congrArg evalZhuSparseQ certificateL3SparseQ_eq_expected,
    congrArg evalZhuSparseQ certificateL4SparseQ_eq_expected,
    congrArg evalZhuSparseQ certificateL22SparseQ_eq_expected,
    congrArg evalZhuSparseQ certificateL5VirVacSparseQ_eq_expected,
    hH]

/-- Complete RHS assembly with the single still-parametric mode-zero H input. -/
theorem eval_certificateRhsSparseQ_eq_expected_of_mode0
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    evalZhuSparseQ certificateRhsSparseQ = evalZhuSparseQ fTwoExpectedQ :=
  eval_certificateRhsSparseQ_eq_expected_of_H
    (eval_certificateHLedger_eq_expected_of_mode0 h0)

#print axioms fTwoExpectedQ_eq_sum_rhs_families
#print axioms eval_certificateRhsSparseQ_eq_expected_of_H
#print axioms eval_certificateRhsSparseQ_eq_expected_of_mode0

end VOA.LatGen.WpTwoZhuSparseSemantics
