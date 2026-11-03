/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosABlocks

/-! # Right-state blocks for the later nonnegative mode-zero cubic summands -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

def hMode0Part0Outer4Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 4], -525 / 2048), ([0, 0, 0, 1, 4], -4725 / 2048)]
def hMode0Part0Outer4Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 2, 4], -525 / 64), ([0, 1, 1, 4], -1575 / 512),
   ([0, 3, 4], -7875 / 512)]
def hMode0Part0Outer4Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 3, 4], -1575 / 512), ([1, 2, 4], -4725 / 512),
   ([4, 4], -4725 / 256)]

def hMode0Part0Outer5Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 5], -1575 / 2048), ([0, 0, 1, 5], -1575 / 512),
   ([0, 2, 5], -1575 / 512), ([1, 1, 5], -1575 / 1024)]
def hMode0Part0Outer5Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 1, 5], -4725 / 512), ([0, 2, 5], -7875 / 512),
   ([3, 5], -1575 / 256)]
def hMode0Part0Outer5Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 2, 5], -1575 / 512), ([1, 1, 5], -1575 / 256),
   ([3, 5], -4725 / 256)]

def hMode0Part0Outer6Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 6], -525 / 128), ([0, 1, 6], -1575 / 128)]
def hMode0Part0Outer6Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 6], -1575 / 256), ([0, 1, 6], -7875 / 512),
   ([2, 6], -525 / 64)]
def hMode0Part0Outer6Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 1, 6], -1575 / 256), ([2, 6], -4725 / 256)]

def hMode0Part0Outer7Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 7], -7875 / 512)]
def hMode0Part0Outer7Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 7], -7875 / 512), ([1, 7], -1575 / 128)]
def hMode0Part0Outer7Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([1, 7], -4725 / 256)]

def hMode0Part0Outer8Block0ExpectedQ : SparseRational.Poly ℕ := []
def hMode0Part0Outer8Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 8], -4725 / 64)]
def hMode0Part0Outer8Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 8], -4725 / 256)]

def hMode0Part0Outer9Block0ExpectedQ : SparseRational.Poly ℕ := []
def hMode0Part0Outer9Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([9], -7875 / 128)]
def hMode0Part0Outer9Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([9], -17325 / 256)]

macro "close_h_mode0_part0_outer_block" : tactic => `(tactic|
  (unfold hMode0Part0OuterBlockSparseQ
   norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
    intIccListQ, natRangeQ, aFieldActSparseQ, aFieldActMonomialQ,
    aFieldModeQ, aFieldCoeffQ, annihilateRawQ, prependRawQ, scaleRawQ,
    bindQ, sumQ, addQ, scaleQ, normalizeQ, insertQ, sortWord, insertVar,
    insertSorted, compareWord, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, Int.toNat]))

end VOA.LatGen.WpTwoZhuSparseCompute
