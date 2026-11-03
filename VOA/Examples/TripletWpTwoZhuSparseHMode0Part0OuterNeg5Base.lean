/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterNegA
import VOA.Examples.TripletWpTwoZhuSparseHRightBlocks

/-! # Three-block staging for the difficult `m = -5` cubic H summand -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

def hMode0Part0Neg5InnerExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0], 8), ([1], 8)]

def hMode0Part0Neg5InnerBlock0ExpectedQ : SparseRational.Poly ℕ := []
def hMode0Part0OuterNeg5Block0ExpectedQ : SparseRational.Poly ℕ := []

def hMode0Part0Neg5InnerBlock1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0], 8)]
def hMode0Part0OuterNeg5Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 6], -1575 / 256), ([0, 0, 1, 5], -1575 / 256),
    ([0, 0, 2, 4], -1575 / 256), ([0, 0, 3, 3], -1575 / 512),
    ([0, 8], -1575 / 32)]

def hMode0Part0Neg5InnerBlock2ExpectedQ : SparseRational.Poly ℕ :=
  [([1], 8)]
def hMode0Part0OuterNeg5Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 1, 6], -1575 / 256), ([1, 1, 5], -1575 / 256),
    ([1, 2, 4], -1575 / 256), ([1, 3, 3], -1575 / 512),
    ([9], -1575 / 32)]

def hMode0Part0Neg5InnerBlockExpectedQ : ℕ → SparseRational.Poly ℕ
  | 0 => hMode0Part0Neg5InnerBlock0ExpectedQ
  | 1 => hMode0Part0Neg5InnerBlock1ExpectedQ
  | 2 => hMode0Part0Neg5InnerBlock2ExpectedQ
  | _ => []

def hMode0Part0OuterNeg5BlockSparseQ (k : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (-1575 / 4096)
    (aWordActSparseQ [0, 0] 6 2 (hMode0Part0Neg5InnerBlockExpectedQ k))

theorem hMode0Part0Neg5InnerBlock0_eq :
    aFieldActSparseQ 0 (-5) (l3hBlockSparseQ 0) =
      hMode0Part0Neg5InnerBlock0ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, hMode0Part0Neg5InnerBlock0ExpectedQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, Int.toNat]

theorem hMode0Part0Neg5InnerBlock1_eq :
    aFieldActSparseQ 0 (-5) (l3hBlockSparseQ 1) =
      hMode0Part0Neg5InnerBlock1ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, hMode0Part0Neg5InnerBlock1ExpectedQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, Int.toNat]

theorem hMode0Part0Neg5InnerBlock2_eq :
    aFieldActSparseQ 0 (-5) (l3hBlockSparseQ 2) =
      hMode0Part0Neg5InnerBlock2ExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hBlockSparseQ, hMode0Part0Neg5InnerBlock2ExpectedQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, Int.toNat]

/-- The three source blocks reduce the nine-term `L(-3)H` state to two terms. -/
theorem hMode0Part0Neg5_inner_eq_expected :
    aFieldActSparseQ 0 (-5) l3hExpectedQ =
      hMode0Part0Neg5InnerExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [l3hExpectedQ, hMode0Part0Neg5InnerExpectedQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, Int.toNat]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.hMode0Part0Neg5_inner_eq_expected
end AxiomAudit
