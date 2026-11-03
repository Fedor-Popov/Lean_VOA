/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHBase

/-! # Outer-mode split of the cubic H branch at Zhu mode two -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

/-- One summand of the outermost `aWordActSparseQ [0,0,0]` mode expansion.  The three
scalings are intentionally left nested so collection follows definitionally from
`scaleQ_sumQ`. -/
def hMode2Part0OuterSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (-4725 / 2048) (scaleQ 3 (scaleQ (1 / 6)
    (if 0 ≤ m then
      aFieldActSparseQ 0 m
        (aWordActSparseQ [0, 0] (-1 - m) 6 l3hExpectedQ)
    else
      aWordActSparseQ [0, 0] (-1 - m) (7 + m).toNat
        (aFieldActSparseQ 0 m l3hExpectedQ))))

def hMode2Part0OuterNeg7ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 6], -14175 / 256), ([1, 5], -14175 / 256),
   ([2, 4], -14175 / 256), ([3, 3], -14175 / 512)]
def hMode2Part0OuterNeg6ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 5], -23625 / 512), ([0, 1, 4], -23625 / 512),
   ([0, 2, 3], -23625 / 512), ([7], -23625 / 128)]
def hMode2Part0OuterNeg5ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 4], -4725 / 256), ([0, 0, 1, 3], -4725 / 256),
   ([0, 0, 2, 2], -4725 / 512), ([0, 1, 4], -4725 / 256),
   ([0, 6], -4725 / 32), ([1, 1, 3], -4725 / 256),
   ([1, 2, 2], -4725 / 512), ([7], -4725 / 32)]
def hMode2Part0OuterNeg4ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 3], -4725 / 2048),
   ([0, 0, 0, 1, 2], -4725 / 2048), ([0, 0, 1, 3], -4725 / 512),
   ([0, 0, 5], -14175 / 512), ([0, 1, 1, 2], -4725 / 512),
   ([0, 2, 3], -4725 / 512), ([0, 6], -4725 / 64),
   ([1, 2, 2], -4725 / 512), ([1, 5], -4725 / 128),
   ([7], -14175 / 128)]
def hMode2Part0OuterNeg3ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 2], -1575 / 2048),
   ([0, 0, 0, 0, 1, 1], -1575 / 4096),
   ([0, 0, 0, 1, 2], -4725 / 1024), ([0, 0, 0, 4], -1575 / 128),
   ([0, 0, 1, 1, 1], -4725 / 2048), ([0, 0, 2, 2], -1575 / 256),
   ([0, 0, 5], -4725 / 128), ([0, 1, 1, 2], -1575 / 512),
   ([0, 1, 4], -4725 / 128), ([0, 2, 3], -4725 / 512),
   ([0, 6], -4725 / 64), ([1, 1, 3], -4725 / 1024),
   ([2, 4], -1575 / 64), ([7], -4725 / 32)]
def hMode2Part0OuterNeg2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 1], -1575 / 1024),
   ([0, 0, 0, 1, 2], -4725 / 2048), ([0, 0, 0, 4], -1575 / 128),
   ([0, 0, 1, 1, 1], -4725 / 2048), ([0, 0, 1, 3], -14175 / 512),
   ([0, 0, 5], -14175 / 512), ([0, 1, 1, 2], -1575 / 512),
   ([0, 1, 4], -23625 / 512), ([0, 2, 3], -4725 / 256),
   ([0, 6], -4725 / 32), ([1, 1, 3], -4725 / 512),
   ([1, 5], -4725 / 128), ([2, 4], -1575 / 64),
   ([3, 3], -4725 / 128), ([7], -23625 / 128)]
def hMode2Part0OuterNeg1ExpectedQ : SparseRational.Poly ℕ := []
def hMode2Part0Outer0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 2], -1575 / 2048),
   ([0, 0, 0, 0, 1, 1], -1575 / 1024),
   ([0, 0, 0, 0, 3], -4725 / 2048),
   ([0, 0, 0, 1, 2], -14175 / 2048), ([0, 0, 0, 4], -4725 / 256),
   ([0, 0, 1, 1, 1], -4725 / 2048), ([0, 0, 1, 3], -4725 / 256),
   ([0, 0, 2, 2], -1575 / 256), ([0, 0, 5], -23625 / 512),
   ([0, 1, 1, 2], -1575 / 512), ([0, 1, 4], -14175 / 512),
   ([0, 2, 3], -4725 / 256), ([0, 6], -14175 / 256)]
def hMode2Part0Outer1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 1], -4725 / 2048),
   ([0, 0, 0, 1, 2], -4725 / 1024),
   ([0, 0, 1, 1, 1], -14175 / 2048), ([0, 0, 1, 3], -14175 / 512),
   ([0, 1, 1, 2], -4725 / 256), ([0, 1, 4], -14175 / 256),
   ([1, 1, 3], -14175 / 512), ([1, 2, 2], -4725 / 512),
   ([1, 5], -14175 / 256)]
def hMode2Part0Outer2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 2], -1575 / 2048),
   ([0, 0, 0, 1, 2], -14175 / 2048), ([0, 0, 2, 2], -1575 / 64),
   ([0, 1, 1, 2], -4725 / 512), ([0, 2, 3], -14175 / 256),
   ([1, 2, 2], -14175 / 512), ([2, 4], -14175 / 256)]
def hMode2Part0Outer3ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 3], -4725 / 2048), ([0, 0, 1, 3], -4725 / 128),
   ([0, 2, 3], -33075 / 512), ([1, 1, 3], -23625 / 1024),
   ([3, 3], -4725 / 64)]
def hMode2Part0Outer4ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 4], -7875 / 256), ([0, 1, 4], -51975 / 512),
   ([2, 4], -20475 / 256)]
def hMode2Part0Outer5ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 5], -23625 / 256), ([1, 5], -23625 / 256)]
def hMode2Part0Outer6ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 6], -70875 / 256)]
def hMode2Part0Outer7ExpectedQ : SparseRational.Poly ℕ :=
  [([7], -99225 / 256)]

macro "close_h_mode2_part0_outer" : tactic => `(tactic|
  (unfold hMode2Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode2Part0OuterNeg7ExpectedQ, hMode2Part0OuterNeg6ExpectedQ,
    hMode2Part0OuterNeg5ExpectedQ, hMode2Part0OuterNeg4ExpectedQ,
    hMode2Part0OuterNeg3ExpectedQ, hMode2Part0OuterNeg2ExpectedQ,
    hMode2Part0OuterNeg1ExpectedQ, hMode2Part0Outer0ExpectedQ,
    hMode2Part0Outer1ExpectedQ, hMode2Part0Outer2ExpectedQ,
    hMode2Part0Outer3ExpectedQ, hMode2Part0Outer4ExpectedQ,
    hMode2Part0Outer5ExpectedQ, hMode2Part0Outer6ExpectedQ,
    hMode2Part0Outer7ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
