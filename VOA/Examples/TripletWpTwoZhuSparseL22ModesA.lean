/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22

/-! # Five mode certificates for the first `L(-2)^2 1` Zhu circle -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxRecDepth 100000

def l22CircleAModeSparseQ (i : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (3417 / 256) (scaleQ (Nat.choose 4 i)
    (vir22ModeSparseQ ((i : ℤ) - 2) 3 (reifyVirWordSparseQ [3])))

def l22CircleAMode0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 1, 1], 3417 / 16384),
   ([0, 0, 0, 1, 2], 3417 / 4096),
   ([0, 0, 0, 4], 10251 / 2048),
   ([0, 0, 1, 1, 1], 3417 / 8192),
   ([0, 0, 1, 3], 30753 / 2048),
   ([0, 0, 2, 2], 23919 / 4096),
   ([0, 0, 5], 44421 / 2048),
   ([0, 1, 1, 2], 51255 / 4096),
   ([0, 1, 4], 23919 / 512),
   ([0, 2, 3], 85425 / 2048),
   ([0, 6], 71757 / 512),
   ([1, 1, 1, 1], 3417 / 4096),
   ([1, 1, 3], 37587 / 2048),
   ([1, 2, 2], 10251 / 512),
   ([1, 5], 44421 / 512),
   ([2, 4], 37587 / 512),
   ([3, 3], 30753 / 1024),
   ([7], 187935 / 512)]

def l22CircleAMode1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 1], 3417 / 16384),
   ([0, 0, 0, 0, 2], 3417 / 8192),
   ([0, 0, 0, 1, 1], 3417 / 4096),
   ([0, 0, 0, 3], 10251 / 512),
   ([0, 0, 1, 2], 112761 / 2048),
   ([0, 0, 4], 37587 / 512),
   ([0, 1, 1, 1], 71757 / 4096),
   ([0, 1, 3], 37587 / 256),
   ([0, 2, 2], 37587 / 512),
   ([0, 5], 3417 / 8),
   ([1, 1, 2], 140097 / 2048),
   ([1, 4], 17085 / 64),
   ([2, 3], 3417 / 16),
   ([6], 140097 / 128)]

def l22CircleAMode2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 2], 30753 / 1024),
   ([0, 0, 1, 1], 92259 / 2048),
   ([0, 0, 3], 92259 / 1024),
   ([0, 1, 2], 92259 / 512),
   ([0, 4], 30753 / 64),
   ([1, 1, 1], 30753 / 1024),
   ([1, 3], 153765 / 512),
   ([2, 2], 30753 / 256),
   ([5], 153765 / 128)]

def l22CircleAMode3ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 1], 23919 / 1024),
   ([0, 0, 2], 23919 / 512),
   ([0, 1, 1], 23919 / 512),
   ([0, 3], 30753 / 128),
   ([1, 2], 37587 / 256),
   ([4], 37587 / 64)]

def l22CircleAMode4ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0], 3417 / 2048),
   ([0, 0, 1], 3417 / 512),
   ([0, 2], 23919 / 512),
   ([1, 1], 17085 / 1024),
   ([3], 58089 / 512)]



macro "close_l22_a_mode" : tactic => `(tactic|
  (unfold l22CircleAModeSparseQ
   rw [reifyVir3SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l22CircleAMode0ExpectedQ, l22CircleAMode1ExpectedQ,
    l22CircleAMode2ExpectedQ, l22CircleAMode3ExpectedQ,
    l22CircleAMode4ExpectedQ, vir3ExpectedQ,
    vir22ModeSparseQ, virModeSparseQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ,
    vacuumSparseQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ,
    natRangeQ, aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
theorem l22CircleAMode1_eq :
    l22CircleAModeSparseQ 1 = l22CircleAMode1ExpectedQ := by close_l22_a_mode
set_option maxHeartbeats 1000000 in
theorem l22CircleAMode3_eq :
    l22CircleAModeSparseQ 3 = l22CircleAMode3ExpectedQ := by close_l22_a_mode
set_option maxHeartbeats 1000000 in
theorem l22CircleAMode4_eq :
    l22CircleAModeSparseQ 4 = l22CircleAMode4ExpectedQ := by close_l22_a_mode

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22CircleAMode4_eq
end AxiomAudit
