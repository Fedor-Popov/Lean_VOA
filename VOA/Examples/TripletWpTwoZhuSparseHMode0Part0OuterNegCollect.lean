/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNegD

/-! # Collected negative outer-mode endpoint for the lowest cubic H branch -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational

/-- All seven negative outer modes have independently certified canonical outputs. -/
theorem hMode0Part0Outer_negative_eq :
    sumQ [hMode0Part0OuterSparseQ (-7), hMode0Part0OuterSparseQ (-6),
      hMode0Part0OuterSparseQ (-5), hMode0Part0OuterSparseQ (-4),
      hMode0Part0OuterSparseQ (-3), hMode0Part0OuterSparseQ (-2),
      hMode0Part0OuterSparseQ (-1)] =
    sumQ [hMode0Part0OuterN7ExpectedQ, hMode0Part0OuterN6ExpectedQ,
      hMode0Part0OuterN5ExpectedQ, hMode0Part0OuterN4ExpectedQ,
      hMode0Part0OuterN3ExpectedQ, hMode0Part0OuterN2ExpectedQ,
      hMode0Part0OuterN1ExpectedQ] := by
  rw [hMode0Part0OuterNeg7_eq, hMode0Part0OuterNeg6_eq,
    hMode0Part0OuterNeg5_eq, hMode0Part0OuterNeg4_eq,
    hMode0Part0OuterNeg3_eq, hMode0Part0OuterNeg2_eq,
    hMode0Part0OuterNeg1_eq]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0Outer_negative_eq
end AxiomAudit
