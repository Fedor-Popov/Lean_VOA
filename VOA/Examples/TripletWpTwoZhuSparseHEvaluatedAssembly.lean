/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseSemantics
import VOA.Examples.TripletWpTwoZhuSparseHMode1Collect
import VOA.Examples.TripletWpTwoZhuSparseHMode23Collect

/-! # Evaluated assembly of the H-left Zhu-circle family -/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open VOA.SparseRational
open VOA.LatGen.WpTwoZhuSparseCompute

/-- The one-entry typed H ledger expands structurally into its four Zhu-circle modes. -/
theorem evalCircleLedger_certificateHLedger_eq_modes :
    evalCircleLedger certificateHLedger = sumQ [hEntryModeSparseQ 0,
      hEntryModeSparseQ 1, hEntryModeSparseQ 2, hEntryModeSparseQ 3] := by
  simp only [evalCircleLedger, certificateHLedger, List.map_cons, List.map_nil,
    ZhuCircleDesc.eval, ZhuStateDesc.weight, ZhuStateDesc.eval,
    sumQ, addQ_nil_right]
  rw [circleSparseQ, scaleQ_sumQ (-4725 / 2048) (by norm_num)]
  norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_nil]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  unfold hEntryModeSparseQ
  have hneg : (-(4725 / 2048) : ℚ) = (-4725 : ℚ) / 2048 := by norm_num
  rw [hneg]
  simp only [sumQ, addQ_nil_right]

/-- The four audited mode ledgers merge to the advertised H-family coordinate. -/
theorem rhsHExpectedQ_eq_sum_modes :
    rhsHExpectedQ = sumQ [hEntry0Mode0ExpectedQ, hEntry0Mode1ExpectedQ,
      hEntry0Mode2ExpectedQ, hEntry0Mode3ExpectedQ] := by
  norm_num (config := { maxSteps := 1000000 })
    [rhsHExpectedQ, hEntry0Mode0ExpectedQ, hEntry0Mode1ExpectedQ,
    hEntry0Mode2ExpectedQ, hEntry0Mode3ExpectedQ,
    sumQ, addQ, compareWord]

/-- Parametric terminal H-family assembly.  The only pending input is the evaluated mode-zero
certificate; modes one through three are already exact coordinate theorems. -/
theorem eval_certificateHLedger_eq_expected_of_mode0
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    evalZhuSparseQ (evalCircleLedger certificateHLedger) =
      evalZhuSparseQ rhsHExpectedQ := by
  rw [evalCircleLedger_certificateHLedger_eq_modes,
    evalZhuSparseQ_sumQ, rhsHExpectedQ_eq_sum_modes,
    evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [h0, congrArg evalZhuSparseQ hEntryMode1_eq,
    congrArg evalZhuSparseQ hEntryMode2_eq,
    congrArg evalZhuSparseQ hEntryMode3_eq]

#print axioms eval_certificateHLedger_eq_expected_of_mode0

end VOA.LatGen.WpTwoZhuSparseSemantics
