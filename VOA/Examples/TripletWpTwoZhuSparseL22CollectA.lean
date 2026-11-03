/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesA0Second

/-! # Collection of the first `L(-2)^2 1` normal-product circle certificate -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxRecDepth 100000

theorem l22CircleAMode0_eq :
    l22CircleAModeSparseQ 0 = l22CircleAMode0ExpectedQ := by
  unfold l22CircleAModeSparseQ
  norm_num only [Nat.choose]
  have scaleQ_one (P : SparseRational.Poly ℕ) : scaleQ 1 P = P := by
    simp [scaleQ]
  rw [scaleQ_one]
  rw [vir22ModeSparseQ, scaleQ_addQ (3417 / 256) (by norm_num),
    scaleQ_sumQ (3417 / 256) (by norm_num),
    scaleQ_sumQ (3417 / 256) (by norm_num)]
  norm_num only [intIccListQ, natRangeQ, Int.toNat, List.map_cons,
    List.map_nil, Function.comp_apply]
  change addQ
      (sumQ [l22AMode0FirstSparseQ (-8), l22AMode0FirstSparseQ (-7),
        l22AMode0FirstSparseQ (-6), l22AMode0FirstSparseQ (-5),
        l22AMode0FirstSparseQ (-4), l22AMode0FirstSparseQ (-3),
        l22AMode0FirstSparseQ (-2)])
      (sumQ [l22AMode0SecondSparseQ (-1), l22AMode0SecondSparseQ 0,
        l22AMode0SecondSparseQ 1, l22AMode0SecondSparseQ 2,
        l22AMode0SecondSparseQ 3]) = l22CircleAMode0ExpectedQ
  rw [l22AMode0FirstNeg8_eq, l22AMode0FirstNeg7_eq,
    l22AMode0FirstNeg6_eq, l22AMode0FirstNeg5_eq,
    l22AMode0FirstNeg4_eq, l22AMode0FirstNeg3_eq,
    l22AMode0FirstNeg2_eq, l22AMode0SecondNeg1_eq,
    l22AMode0Second0_eq, l22AMode0Second1_eq,
    l22AMode0Second2_eq, l22AMode0Second3_eq]
  norm_num (config := { maxSteps := 500000 })
    [l22AMode0FirstNeg8ExpectedQ, l22AMode0FirstNeg7ExpectedQ,
    l22AMode0FirstNeg6ExpectedQ, l22AMode0FirstNeg5ExpectedQ,
    l22AMode0FirstNeg4ExpectedQ, l22AMode0FirstNeg3ExpectedQ,
    l22AMode0FirstNeg2ExpectedQ, l22AMode0SecondNeg1ExpectedQ,
    l22AMode0Second0ExpectedQ, l22AMode0Second1ExpectedQ,
    l22AMode0Second2ExpectedQ, l22AMode0Second3ExpectedQ,
    l22CircleAMode0ExpectedQ, sumQ, addQ, compareWord]

/-- The first specialized L22 ledger circle agrees with its canonical 52 coordinates. -/
theorem l22CircleA_eq_expected :
    scaleQ (3417 / 256)
      (vir22CircleSparseQ 3 (reifyVirWordSparseQ [3])) = l22CircleAExpectedQ := by
  rw [vir22CircleSparseQ, scaleQ_sumQ (3417 / 256) (by norm_num)]
  norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_nil]
  change sumQ [l22CircleAModeSparseQ 0, l22CircleAModeSparseQ 1,
    l22CircleAModeSparseQ 2, l22CircleAModeSparseQ 3,
    l22CircleAModeSparseQ 4] = l22CircleAExpectedQ
  rw [l22CircleAMode0_eq, l22CircleAMode1_eq, l22CircleAMode2_eq,
    l22CircleAMode3_eq, l22CircleAMode4_eq]
  norm_num (config := { maxSteps := 500000 })
    [l22CircleAMode0ExpectedQ, l22CircleAMode1ExpectedQ,
    l22CircleAMode2ExpectedQ, l22CircleAMode3ExpectedQ,
    l22CircleAMode4ExpectedQ, l22CircleAExpectedQ, sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleA_eq_expected
end AxiomAudit
