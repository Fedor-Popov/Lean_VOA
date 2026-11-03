/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNegCollect
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterBlockSemantics
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part1
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part2

/-! # Structural and exact-ledger staging for the lowest H-left mode -/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

private theorem scaleQ_scaleQ_nonzero (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : SparseRational.Poly ℕ) :
    scaleQ a (scaleQ b P) = scaleQ (a * b) P := by
  simp [scaleQ, ha, hb, mul_ne_zero ha hb, List.map_map, Function.comp_def]
  intro w c _
  ring

/-- The cubic left monomial expands into the seventeen outer current modes `-7, …, 9`. -/
theorem hEntryMode0Part0_eq_outer_sum :
    hEntryModePartSparseQ 0 0 = sumQ
      [hMode0Part0OuterSparseQ (-7), hMode0Part0OuterSparseQ (-6),
       hMode0Part0OuterSparseQ (-5), hMode0Part0OuterSparseQ (-4),
       hMode0Part0OuterSparseQ (-3), hMode0Part0OuterSparseQ (-2),
       hMode0Part0OuterSparseQ (-1), hMode0Part0OuterSparseQ 0,
       hMode0Part0OuterSparseQ 1, hMode0Part0OuterSparseQ 2,
       hMode0Part0OuterSparseQ 3, hMode0Part0OuterSparseQ 4,
       hMode0Part0OuterSparseQ 5, hMode0Part0OuterSparseQ 6,
       hMode0Part0OuterSparseQ 7, hMode0Part0OuterSparseQ 8,
       hMode0Part0OuterSparseQ 9] := by
  unfold hEntryModePartSparseQ voaModeActSparseQ zhuStateActSparseQ bindQ
  norm_num [hLeftPartSparseQ, sumQ]
  rw [aWordActSparseQ]
  norm_num only [aWordWeightQ, Int.reduceNeg, Int.reduceAdd]
  rw [max_eq_right (by norm_num : (-1 : ℤ) ≤ 9)]
  change scaleQ (-(4725 / 2048)) (scaleQ 1 (scaleQ (1 / 6)
      (sumSparseIcc (-7) 9 fun m =>
        if 0 ≤ m then
          aFieldActSparseQ 0 m
            (aWordActSparseQ [0, 0] (1 - m) 6 l3hExpectedQ)
        else
          aWordActSparseQ [0, 0] (1 - m) (7 + m).toNat
            (aFieldActSparseQ 0 m l3hExpectedQ)))) = _
  have hscale (P : SparseRational.Poly ℕ) :
      scaleQ (-(4725 / 2048)) (scaleQ 1 (scaleQ (1 / 6) P)) =
        scaleQ (-(1575 / 4096)) P := by
    rw [scaleQ_scaleQ_nonzero 1 (1 / 6) (by norm_num) (by norm_num),
      scaleQ_scaleQ_nonzero (-(4725 / 2048)) (1 * (1 / 6))
        (by norm_num) (by norm_num)]
    norm_num
  unfold sumSparseIcc
  rw [scaleQ_sumQ (1 / 6) (by norm_num),
    scaleQ_sumQ 1 (by norm_num),
    scaleQ_sumQ (-(4725 / 2048)) (by norm_num)]
  norm_num [intIccListQ, natRangeQ, hMode0Part0OuterSparseQ,
    Function.comp_apply, Int.toNat, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, sumQ]
  simp only [hscale]

theorem hEntry0Mode0Part0ExpectedQ_eq_outer_sum :
    sumQ [hMode0Part0OuterN7ExpectedQ, hMode0Part0OuterN6ExpectedQ,
      hMode0Part0OuterN5ExpectedQ, hMode0Part0OuterN4ExpectedQ,
      hMode0Part0OuterN3ExpectedQ, hMode0Part0OuterN2ExpectedQ,
      hMode0Part0OuterN1ExpectedQ, hMode0Part0Outer0ExpectedQ,
      hMode0Part0Outer1ExpectedQ, hMode0Part0Outer2ExpectedQ,
      hMode0Part0Outer3ExpectedQ, hMode0Part0Outer4ExpectedQ,
      hMode0Part0Outer5ExpectedQ, hMode0Part0Outer6ExpectedQ,
      hMode0Part0Outer7ExpectedQ, hMode0Part0Outer8ExpectedQ,
      hMode0Part0Outer9ExpectedQ] = hEntry0Mode0Part0ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [hMode0Part0OuterN7ExpectedQ, hMode0Part0OuterN6ExpectedQ,
    hMode0Part0OuterN5ExpectedQ, hMode0Part0OuterN4ExpectedQ,
    hMode0Part0OuterN3ExpectedQ, hMode0Part0OuterN2ExpectedQ,
    hMode0Part0OuterN1ExpectedQ, hMode0Part0Outer0ExpectedQ,
    hMode0Part0Outer1ExpectedQ, hMode0Part0Outer2ExpectedQ,
    hMode0Part0Outer3ExpectedQ, hMode0Part0Outer4ExpectedQ,
    hMode0Part0Outer5ExpectedQ, hMode0Part0Outer6ExpectedQ,
    hMode0Part0Outer7ExpectedQ, hMode0Part0Outer8ExpectedQ,
    hMode0Part0Outer9ExpectedQ, hEntry0Mode0Part0ExpectedQ,
    sumQ, addQ, compareWord]

theorem hEntry0Mode0ExpectedQ_eq_parts :
    sumQ [hEntry0Mode0Part0ExpectedQ, hEntry0Mode0Part1ExpectedQ,
      hEntry0Mode0Part2ExpectedQ] = hEntry0Mode0ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [hEntry0Mode0Part0ExpectedQ, hEntry0Mode0Part1ExpectedQ,
    hEntry0Mode0Part2ExpectedQ, hEntry0Mode0ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseSemantics

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseSemantics.hEntryMode0Part0_eq_outer_sum
#print axioms VOA.LatGen.WpTwoZhuSparseSemantics.hEntry0Mode0Part0ExpectedQ_eq_outer_sum
#print axioms VOA.LatGen.WpTwoZhuSparseSemantics.hEntry0Mode0ExpectedQ_eq_parts
end AxiomAudit
