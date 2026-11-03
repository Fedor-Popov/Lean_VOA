/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0
import VOA.Examples.TripletWpTwoZhuSparseHRightBlocks

/-! # Three-block coordinates for the first nonnegative mode-zero cubic summands -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

/-- The contribution of one of the three audited right-state blocks to a nonnegative
outer summand of the mode-zero cubic branch. -/
def hMode0Part0OuterBlockSparseQ (m : ℤ) (k : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (-1575 / 4096)
    (aFieldActSparseQ 0 m
      (aWordActSparseQ [0, 0] (1 - m) 6 (l3hBlockSparseQ k)))

def hMode0Part0Outer0Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 0, 1, 1], -525 / 16384),
   ([0, 0, 0, 0, 0, 1, 2], -525 / 8192),
   ([0, 0, 0, 0, 0, 4], -525 / 2048),
   ([0, 0, 0, 0, 1, 1, 1], -1575 / 16384),
   ([0, 0, 0, 0, 1, 3], -525 / 1024),
   ([0, 0, 0, 0, 5], -1575 / 2048),
   ([0, 0, 0, 1, 4], -1575 / 1024),
   ([0, 0, 0, 2, 3], -1575 / 2048),
   ([0, 0, 1, 1, 3], -1575 / 2048)]

def hMode0Part0Outer0Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 3], -1575 / 4096),
   ([0, 0, 0, 1, 1, 2], -525 / 2048),
   ([0, 0, 0, 1, 4], -1575 / 2048),
   ([0, 0, 0, 6], -1575 / 256),
   ([0, 0, 1, 5], -1575 / 512),
   ([0, 0, 2, 4], -525 / 256),
   ([0, 0, 3, 3], -1575 / 512),
   ([0, 0, 7], -7875 / 512),
   ([0, 1, 2, 3], -525 / 512),
   ([0, 3, 4], -1575 / 512)]

def hMode0Part0Outer0Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 1, 1, 3], -1575 / 4096),
   ([0, 0, 1, 2, 2], -525 / 4096),
   ([0, 0, 1, 5], -1575 / 2048),
   ([0, 1, 6], -1575 / 256),
   ([0, 2, 5], -1575 / 512),
   ([0, 3, 4], -1575 / 512),
   ([0, 8], -4725 / 256)]

def hMode0Part0Outer1Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 0, 1, 1], -525 / 32768),
   ([0, 0, 0, 0, 0, 1, 2], -525 / 16384),
   ([0, 0, 0, 0, 1, 1, 1], -1575 / 32768),
   ([0, 0, 0, 0, 1, 3], -525 / 2048),
   ([0, 0, 0, 1, 1, 2], -525 / 1024),
   ([0, 0, 0, 1, 4], -1575 / 2048),
   ([0, 0, 1, 1, 3], -1575 / 1024),
   ([0, 0, 1, 2, 2], -1575 / 2048),
   ([0, 1, 1, 1, 2], -1575 / 2048)]

def hMode0Part0Outer1Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 3], -1575 / 8192),
   ([0, 0, 0, 1, 1, 2], -525 / 4096),
   ([0, 0, 0, 1, 4], -1575 / 4096),
   ([0, 0, 1, 5], -1575 / 256),
   ([0, 1, 1, 4], -1575 / 512),
   ([0, 1, 2, 3], -2625 / 512),
   ([0, 1, 6], -7875 / 512),
   ([1, 1, 2, 2], -525 / 512),
   ([1, 2, 4], -1575 / 512)]

def hMode0Part0Outer1Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 1, 1, 3], -1575 / 8192),
   ([0, 0, 1, 2, 2], -525 / 8192),
   ([0, 0, 1, 5], -1575 / 4096),
   ([1, 1, 5], -1575 / 256),
   ([1, 2, 4], -1575 / 512),
   ([1, 3, 3], -1575 / 512),
   ([1, 7], -4725 / 256)]

def hMode0Part0Outer2Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 2, 2], -525 / 2048),
   ([0, 0, 0, 1, 1, 2], -525 / 1024),
   ([0, 0, 0, 2, 3], -1575 / 2048),
   ([0, 0, 1, 2, 2], -4725 / 2048),
   ([0, 1, 1, 1, 2], -1575 / 2048)]

def hMode0Part0Outer2Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 2, 4], -1575 / 256),
   ([0, 1, 2, 3], -1575 / 256),
   ([0, 2, 2, 2], -525 / 256),
   ([0, 2, 5], -7875 / 512),
   ([1, 1, 2, 2], -525 / 512),
   ([1, 2, 4], -1575 / 512)]

def hMode0Part0Outer2Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([1, 2, 4], -1575 / 256),
   ([2, 2, 3], -1575 / 256),
   ([2, 6], -4725 / 256)]

def hMode0Part0Outer3Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 3], -1575 / 2048),
   ([0, 0, 0, 2, 3], -1575 / 1024),
   ([0, 0, 1, 1, 3], -4725 / 2048)]

def hMode0Part0Outer3Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 3, 3], -4725 / 512),
   ([0, 1, 2, 3], -1575 / 256),
   ([0, 3, 4], -4725 / 256)]

def hMode0Part0Outer3Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([1, 3, 3], -4725 / 512),
   ([2, 2, 3], -1575 / 512),
   ([3, 5], -4725 / 256)]

/-- Normalize one three-monomial right-state block under the fixed certificate budget. -/
macro "close_h_mode0_part0_outer_block" : tactic => `(tactic|
  (unfold hMode0Part0OuterBlockSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
