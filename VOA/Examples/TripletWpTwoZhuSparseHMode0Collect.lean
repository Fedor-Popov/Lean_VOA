/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0CollectBase
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosBCSemantics

/-! # Evaluated collection of the lowest H-left Zhu-circle mode

The negative outer modes are exact sparse equalities.  The nonnegative modes are assembled
from three right-state blocks after applying the linear sparse evaluator.  This is the precise
state-level boundary needed by the intrinsic Zhu certificate.
-/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

/-- The complete cubic branch agrees with its canonical coordinate after evaluation. -/
theorem eval_hEntryMode0Part0_eq_expected :
    evalZhuSparseQ (hEntryModePartSparseQ 0 0) =
      evalZhuSparseQ hEntry0Mode0Part0ExpectedQ := by
  rw [hEntryMode0Part0_eq_outer_sum, evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hMode0Part0OuterNeg7_eq, hMode0Part0OuterNeg6_eq,
    hMode0Part0OuterNeg5_eq, hMode0Part0OuterNeg4_eq,
    hMode0Part0OuterNeg3_eq, hMode0Part0OuterNeg2_eq,
    hMode0Part0OuterNeg1_eq,
    eval_hMode0Part0Outer0_eq_expected,
    eval_hMode0Part0Outer1_eq_expected,
    eval_hMode0Part0Outer2_eq_expected,
    eval_hMode0Part0Outer3_eq_expected,
    eval_hMode0Part0Outer4_eq_expected,
    eval_hMode0Part0Outer5_eq_expected,
    eval_hMode0Part0Outer6_eq_expected,
    eval_hMode0Part0Outer7_eq_expected,
    eval_hMode0Part0Outer8_eq_expected,
    eval_hMode0Part0Outer9_eq_expected]
  have hmerge := congrArg evalZhuSparseQ hEntry0Mode0Part0ExpectedQ_eq_outer_sum
  rw [evalZhuSparseQ_sumQ] at hmerge
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    using hmerge

/-- The full lowest H-ledger mode agrees with its canonical coordinate after evaluation. -/
theorem eval_hEntryMode0_eq_expected :
    evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ := by
  rw [hEntryMode_split 0 (by norm_num), evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [eval_hEntryMode0Part0_eq_expected,
    hEntryMode0Part1_eq, hEntryMode0Part2_eq]
  have hmerge := congrArg evalZhuSparseQ hEntry0Mode0ExpectedQ_eq_parts
  rw [evalZhuSparseQ_sumQ] at hmerge
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    using hmerge

end VOA.LatGen.WpTwoZhuSparseSemantics

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseSemantics.eval_hEntryMode0Part0_eq_expected
#print axioms VOA.LatGen.WpTwoZhuSparseSemantics.eval_hEntryMode0_eq_expected
end AxiomAudit
