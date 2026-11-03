/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesB0SecondB
import VOA.Examples.TripletWpTwoZhuSparseL22ModeB4Collect

/-! # Collection of the second L22 circle and the complete two-circle family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

theorem l22CircleBMode0_eq :
    l22CircleBModeSparseQ 0 = l22Entry1Mode0ExpectedQ := by
  unfold l22CircleBModeSparseQ
  norm_num only [Nat.choose]
  have scaleQ_one (P : SparseRational.Poly ℕ) : scaleQ 1 P = P := by
    simp [scaleQ]
  rw [scaleQ_one]
  rw [vir22ModeSparseQ, scaleQ_addQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num),
    scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ
      (sumQ [l22BMode0FirstSparseQ (-10), l22BMode0FirstSparseQ (-9), l22BMode0FirstSparseQ (-8), l22BMode0FirstSparseQ (-7), l22BMode0FirstSparseQ (-6), l22BMode0FirstSparseQ (-5), l22BMode0FirstSparseQ (-4), l22BMode0FirstSparseQ (-3), l22BMode0FirstSparseQ (-2)])
      (sumQ [l22BMode0SecondSparseQ (-1), l22BMode0SecondSparseQ (0), l22BMode0SecondSparseQ (1), l22BMode0SecondSparseQ (2), l22BMode0SecondSparseQ (3), l22BMode0SecondSparseQ (4), l22BMode0SecondSparseQ (5)]) = l22Entry1Mode0ExpectedQ
  rw [l22BMode0FirstNeg10_eq,
    l22BMode0FirstNeg9_eq,
    l22BMode0FirstNeg8_eq,
    l22BMode0FirstNeg7_eq,
    l22BMode0FirstNeg6_eq,
    l22BMode0FirstNeg5_eq,
    l22BMode0FirstNeg4_eq,
    l22BMode0FirstNeg3_eq,
    l22BMode0FirstNeg2_eq,
    l22BMode0SecondNeg1_eq,
    l22BMode0Second0_eq,
    l22BMode0Second1_eq,
    l22BMode0Second2_eq,
    l22BMode0Second3_eq,
    l22BMode0Second4_eq,
    l22BMode0Second5_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l22BMode0FirstNeg10ExpectedQ,
    l22BMode0FirstNeg9ExpectedQ,
    l22BMode0FirstNeg8ExpectedQ,
    l22BMode0FirstNeg7ExpectedQ,
    l22BMode0FirstNeg6ExpectedQ,
    l22BMode0FirstNeg5ExpectedQ,
    l22BMode0FirstNeg4ExpectedQ,
    l22BMode0FirstNeg3ExpectedQ,
    l22BMode0FirstNeg2ExpectedQ,
    l22BMode0SecondNeg1ExpectedQ,
    l22BMode0Second0ExpectedQ,
    l22BMode0Second1ExpectedQ,
    l22BMode0Second2ExpectedQ,
    l22BMode0Second3ExpectedQ,
    l22BMode0Second4ExpectedQ,
    l22BMode0Second5ExpectedQ, l22Entry1Mode0ExpectedQ, sumQ, addQ, compareWord]

/-- The second specialized L22 ledger circle agrees with its canonical coordinate. -/
theorem l22CircleB_eq_expected :
    scaleQ (1669 / 128)
      (vir22CircleSparseQ 5 (reifyVirWordSparseQ [3, 2])) =
        l22CircleBExpectedQ := by
  rw [vir22CircleSparseQ, scaleQ_sumQ (1669 / 128) (by norm_num)]
  norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_nil]
  change sumQ [l22CircleBModeSparseQ 0, l22CircleBModeSparseQ 1,
    l22CircleBModeSparseQ 2, l22CircleBModeSparseQ 3,
    l22CircleBModeSparseQ 4] = l22CircleBExpectedQ
  rw [l22CircleBMode0_eq, l22CircleBMode1_eq, l22CircleBMode2_eq,
    l22CircleBMode3_eq, l22CircleBMode4_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l22Entry1Mode0ExpectedQ, l22Entry1Mode1ExpectedQ,
    l22Entry1Mode2ExpectedQ, l22Entry1Mode3ExpectedQ,
    l22Entry1Mode4ExpectedQ, l22CircleBExpectedQ,
    sumQ, addQ, compareWord]

/-- The two L(-2)^2-left ledger entries reconstruct their family coordinate. -/
theorem certificateL22SparseQ_eq_expected :
    evalVir22Ledger certificateL22Ledger = rhsL22ExpectedQ := by
  simp only [evalVir22Ledger, certificateL22Ledger, List.map_cons, List.map_nil,
    ZhuStateDesc.weight, ZhuStateDesc.eval]
  change sumQ [
    scaleQ (3417 / 256)
      (vir22CircleSparseQ 3 (reifyVirWordSparseQ [3])),
    scaleQ (1669 / 128)
      (vir22CircleSparseQ 5 (reifyVirWordSparseQ [3, 2]))] =
        rhsL22ExpectedQ
  rw [l22CircleA_eq_expected, l22CircleB_eq_expected]
  norm_num (config := { maxSteps := 1000000 })
    [l22CircleAExpectedQ, l22CircleBExpectedQ, rhsL22ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.certificateL22SparseQ_eq_expected
end AxiomAudit
