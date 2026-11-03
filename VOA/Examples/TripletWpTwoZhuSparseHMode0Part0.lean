/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHBase

/-! # Outer-mode staging for the H(-1)^3, lowest Zhu-circle mode -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

def hMode0Part0OuterSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (-1575 / 4096)
    (if 0 ≤ m then
      aFieldActSparseQ 0 m (aWordActSparseQ [0, 0] (1 - m) 6 l3hExpectedQ)
    else
      aWordActSparseQ [0, 0] (1 - m) ((7 : ℤ) + m).toNat
        (aFieldActSparseQ 0 m l3hExpectedQ))

-- 5 canonical terms; sorted and zero-free
def hMode0Part0OuterN7ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 8], (-4725 / 256)), ([1, 7], (-4725 / 256)), ([2, 6], (-4725 / 256)), ([3, 5], (-4725 / 256)),
    ([4, 4], (-4725 / 512))]

-- 5 canonical terms; sorted and zero-free
def hMode0Part0OuterN6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 7], (-7875 / 512)), ([0, 1, 6], (-7875 / 512)), ([0, 2, 5], (-7875 / 512)), ([0, 3, 4], (-7875 / 512)),
    ([9], (-7875 / 128))]

-- 10 canonical terms; sorted and zero-free
def hMode0Part0OuterN5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 6], (-1575 / 256)), ([0, 0, 1, 5], (-1575 / 256)), ([0, 0, 2, 4], (-1575 / 256)), ([0, 0, 3, 3], (-1575 / 512)),
    ([0, 1, 6], (-1575 / 256)), ([0, 8], (-1575 / 32)), ([1, 1, 5], (-1575 / 256)), ([1, 2, 4], (-1575 / 256)),
    ([1, 3, 3], (-1575 / 512)), ([9], (-1575 / 32))]

-- 13 canonical terms; sorted and zero-free
def hMode0Part0OuterN4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 5], (-1575 / 2048)), ([0, 0, 0, 1, 4], (-1575 / 2048)), ([0, 0, 0, 2, 3], (-1575 / 2048)), ([0, 0, 1, 5], (-1575 / 512)),
    ([0, 0, 7], (-4725 / 512)), ([0, 1, 1, 4], (-1575 / 512)), ([0, 1, 2, 3], (-1575 / 512)), ([0, 2, 5], (-1575 / 512)),
    ([0, 8], (-1575 / 64)), ([1, 2, 4], (-1575 / 512)), ([1, 7], (-1575 / 128)), ([2, 2, 3], (-1575 / 512)),
    ([9], (-4725 / 128))]

-- 18 canonical terms; sorted and zero-free
def hMode0Part0OuterN3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 4], (-525 / 2048)), ([0, 0, 0, 0, 1, 3], (-525 / 2048)), ([0, 0, 0, 0, 2, 2], (-525 / 4096)), ([0, 0, 0, 1, 4], (-1575 / 1024)),
    ([0, 0, 0, 6], (-525 / 128)), ([0, 0, 1, 1, 3], (-1575 / 1024)), ([0, 0, 1, 2, 2], (-1575 / 2048)), ([0, 0, 2, 4], (-525 / 256)),
    ([0, 0, 7], (-1575 / 128)), ([0, 1, 2, 3], (-525 / 256)), ([0, 1, 6], (-1575 / 128)), ([0, 2, 2, 2], (-525 / 512)),
    ([0, 3, 4], (-1575 / 512)), ([0, 8], (-1575 / 64)), ([1, 3, 3], (-1575 / 512)), ([2, 2, 3], (-1575 / 1024)),
    ([2, 6], (-525 / 64)), ([9], (-1575 / 32))]

-- 22 canonical terms; sorted and zero-free
def hMode0Part0OuterN2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 3], (-525 / 1024)), ([0, 0, 0, 1, 1, 2], (-525 / 1024)), ([0, 0, 0, 2, 3], (-1575 / 2048)), ([0, 0, 0, 6], (-525 / 128)),
    ([0, 0, 1, 1, 3], (-1575 / 2048)), ([0, 0, 1, 2, 2], (-1575 / 2048)), ([0, 0, 1, 5], (-1575 / 256)), ([0, 0, 3, 3], (-1575 / 512)),
    ([0, 0, 7], (-4725 / 512)), ([0, 1, 1, 1, 2], (-1575 / 2048)), ([0, 1, 2, 3], (-525 / 128)), ([0, 1, 6], (-1575 / 128)),
    ([0, 2, 5], (-1575 / 256)), ([0, 3, 4], (-1575 / 512)), ([0, 8], (-1575 / 32)), ([1, 1, 2, 2], (-525 / 512)),
    ([1, 1, 5], (-1575 / 512)), ([1, 2, 4], (-1575 / 512)), ([1, 7], (-1575 / 128)), ([2, 6], (-525 / 64)),
    ([3, 5], (-1575 / 128)), ([9], (-7875 / 128))]

-- 0 canonical terms; sorted and zero-free
def hMode0Part0OuterN1ExpectedQ : SparseRational.Poly ℕ :=
  []

-- 21 canonical terms; sorted and zero-free
def hMode0Part0Outer0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 1, 1], (-525 / 16384)), ([0, 0, 0, 0, 0, 1, 2], (-525 / 8192)), ([0, 0, 0, 0, 0, 4], (-525 / 2048)), ([0, 0, 0, 0, 1, 1, 1], (-1575 / 16384)),
    ([0, 0, 0, 0, 1, 3], (-3675 / 4096)), ([0, 0, 0, 0, 5], (-1575 / 2048)), ([0, 0, 0, 1, 1, 2], (-525 / 2048)), ([0, 0, 0, 1, 4], (-4725 / 2048)),
    ([0, 0, 0, 2, 3], (-1575 / 2048)), ([0, 0, 0, 6], (-1575 / 256)), ([0, 0, 1, 1, 3], (-4725 / 4096)), ([0, 0, 1, 2, 2], (-525 / 4096)),
    ([0, 0, 1, 5], (-7875 / 2048)), ([0, 0, 2, 4], (-525 / 256)), ([0, 0, 3, 3], (-1575 / 512)), ([0, 0, 7], (-7875 / 512)),
    ([0, 1, 2, 3], (-525 / 512)), ([0, 1, 6], (-1575 / 256)), ([0, 2, 5], (-1575 / 512)), ([0, 3, 4], (-1575 / 256)),
    ([0, 8], (-4725 / 256))]

-- 18 canonical terms; sorted and zero-free
def hMode0Part0Outer1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 1, 1], (-525 / 32768)), ([0, 0, 0, 0, 0, 1, 2], (-525 / 16384)), ([0, 0, 0, 0, 1, 1, 1], (-1575 / 32768)), ([0, 0, 0, 0, 1, 3], (-3675 / 8192)),
    ([0, 0, 0, 1, 1, 2], (-2625 / 4096)), ([0, 0, 0, 1, 4], (-4725 / 4096)), ([0, 0, 1, 1, 3], (-14175 / 8192)), ([0, 0, 1, 2, 2], (-6825 / 8192)),
    ([0, 0, 1, 5], (-26775 / 4096)), ([0, 1, 1, 1, 2], (-1575 / 2048)), ([0, 1, 1, 4], (-1575 / 512)), ([0, 1, 2, 3], (-2625 / 512)),
    ([0, 1, 6], (-7875 / 512)), ([1, 1, 2, 2], (-525 / 512)), ([1, 1, 5], (-1575 / 256)), ([1, 2, 4], (-1575 / 256)),
    ([1, 3, 3], (-1575 / 512)), ([1, 7], (-4725 / 256))]

-- 13 canonical terms; sorted and zero-free
def hMode0Part0Outer2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 2, 2], (-525 / 2048)), ([0, 0, 0, 1, 1, 2], (-525 / 1024)), ([0, 0, 0, 2, 3], (-1575 / 2048)), ([0, 0, 1, 2, 2], (-4725 / 2048)),
    ([0, 0, 2, 4], (-1575 / 256)), ([0, 1, 1, 1, 2], (-1575 / 2048)), ([0, 1, 2, 3], (-1575 / 256)), ([0, 2, 2, 2], (-525 / 256)),
    ([0, 2, 5], (-7875 / 512)), ([1, 1, 2, 2], (-525 / 512)), ([1, 2, 4], (-4725 / 512)), ([2, 2, 3], (-1575 / 256)),
    ([2, 6], (-4725 / 256))]

-- 9 canonical terms; sorted and zero-free
def hMode0Part0Outer3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 3], (-1575 / 2048)), ([0, 0, 0, 2, 3], (-1575 / 1024)), ([0, 0, 1, 1, 3], (-4725 / 2048)), ([0, 0, 3, 3], (-4725 / 512)),
    ([0, 1, 2, 3], (-1575 / 256)), ([0, 3, 4], (-4725 / 256)), ([1, 3, 3], (-4725 / 512)), ([2, 2, 3], (-1575 / 512)),
    ([3, 5], (-4725 / 256))]

-- 7 canonical terms; sorted and zero-free
def hMode0Part0Outer4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 4], (-525 / 2048)), ([0, 0, 0, 1, 4], (-4725 / 2048)), ([0, 0, 2, 4], (-525 / 64)), ([0, 1, 1, 4], (-1575 / 512)),
    ([0, 3, 4], (-4725 / 256)), ([1, 2, 4], (-4725 / 512)), ([4, 4], (-4725 / 256))]

-- 5 canonical terms; sorted and zero-free
def hMode0Part0Outer5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 5], (-1575 / 2048)), ([0, 0, 1, 5], (-1575 / 128)), ([0, 2, 5], (-11025 / 512)), ([1, 1, 5], (-7875 / 1024)),
    ([3, 5], (-1575 / 64))]

-- 3 canonical terms; sorted and zero-free
def hMode0Part0Outer6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 6], (-2625 / 256)), ([0, 1, 6], (-17325 / 512)), ([2, 6], (-6825 / 256))]

-- 2 canonical terms; sorted and zero-free
def hMode0Part0Outer7ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 7], (-7875 / 256)), ([1, 7], (-7875 / 256))]

-- 1 canonical terms; sorted and zero-free
def hMode0Part0Outer8ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 8], (-23625 / 256))]

-- 1 canonical terms; sorted and zero-free
def hMode0Part0Outer9ExpectedQ : SparseRational.Poly ℕ :=
  [    ([9], (-33075 / 256))]

/-- Close one source-expanded summand of the mode-zero cubic branch. -/
macro "close_h_mode0_part0_outer" : tactic => `(tactic|
  (unfold hMode0Part0OuterSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [hMode0Part0OuterN7ExpectedQ, hMode0Part0OuterN6ExpectedQ,
    hMode0Part0OuterN5ExpectedQ, hMode0Part0OuterN4ExpectedQ,
    hMode0Part0OuterN3ExpectedQ, hMode0Part0OuterN2ExpectedQ,
    hMode0Part0OuterN1ExpectedQ, hMode0Part0Outer0ExpectedQ,
    hMode0Part0Outer1ExpectedQ, hMode0Part0Outer2ExpectedQ,
    hMode0Part0Outer3ExpectedQ, hMode0Part0Outer4ExpectedQ,
    hMode0Part0Outer5ExpectedQ, hMode0Part0Outer6ExpectedQ,
    hMode0Part0Outer7ExpectedQ, hMode0Part0Outer8ExpectedQ,
    hMode0Part0Outer9ExpectedQ, l3hExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
