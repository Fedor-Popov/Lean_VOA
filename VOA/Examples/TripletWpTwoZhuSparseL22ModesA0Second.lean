/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesA0First

/-! # Second normal-order half of the lowest first L22 Zhu-circle mode -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxRecDepth 100000

def l22AMode0SecondSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (3417 / 256)
    (virModeSparseQ (-5 - m) (3 - m).toNat
      (virModeSparseQ m 3 (reifyVirWordSparseQ [3])))

-- 10 canonical terms; sorted and zero-free
def l22AMode0SecondNeg1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 2, 2], (3417 / 2048)), ([0, 1, 1, 2], (3417 / 2048)), ([0, 2, 3], (10251 / 1024)), ([0, 6], (10251 / 512)),
    ([1, 1, 1, 1], (3417 / 8192)), ([1, 1, 3], (10251 / 2048)), ([1, 5], (3417 / 256)), ([2, 4], (3417 / 512)),
    ([3, 3], (30753 / 2048)), ([7], (10251 / 128))]
-- 9 canonical terms; sorted and zero-free
def l22AMode0Second0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 3], (10251 / 4096)), ([0, 1, 1, 2], (10251 / 4096)), ([0, 1, 4], (10251 / 1024)), ([0, 2, 3], (10251 / 2048)),
    ([0, 6], (10251 / 512)), ([1, 2, 2], (10251 / 2048)), ([1, 5], (10251 / 1024)), ([2, 4], (10251 / 512)),
    ([7], (30753 / 512))]
-- 10 canonical terms; sorted and zero-free
def l22AMode0Second1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 4], (3417 / 2048)), ([0, 0, 1, 3], (3417 / 2048)), ([0, 0, 2, 2], (3417 / 4096)), ([0, 0, 5], (17085 / 2048)),
    ([0, 1, 4], (3417 / 1024)), ([0, 6], (3417 / 256)), ([1, 1, 3], (3417 / 1024)), ([1, 2, 2], (3417 / 2048)),
    ([1, 5], (17085 / 1024)), ([7], (3417 / 128))]
-- 0 canonical terms; sorted and zero-free
def l22AMode0Second2ExpectedQ : SparseRational.Poly ℕ :=
  []
-- 5 canonical terms; sorted and zero-free
def l22AMode0Second3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 6], (-3417 / 256)), ([1, 5], (-3417 / 256)), ([2, 4], (-3417 / 256)), ([3, 3], (-3417 / 512)),
    ([7], (-23919 / 256))]

macro "close_l22_a0_second" : tactic => `(tactic|
  (unfold l22AMode0SecondSparseQ
   rw [reifyVir3SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l22AMode0SecondNeg1ExpectedQ, l22AMode0Second0ExpectedQ,
    l22AMode0Second1ExpectedQ, l22AMode0Second2ExpectedQ,
    l22AMode0Second3ExpectedQ, vir3ExpectedQ, virModeSparseQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, vacuumSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0SecondNeg1_eq :
    l22AMode0SecondSparseQ (-1) = l22AMode0SecondNeg1ExpectedQ := by
  close_l22_a0_second
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0Second0_eq :
    l22AMode0SecondSparseQ (0) = l22AMode0Second0ExpectedQ := by
  close_l22_a0_second
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0Second1_eq :
    l22AMode0SecondSparseQ (1) = l22AMode0Second1ExpectedQ := by
  close_l22_a0_second
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0Second2_eq :
    l22AMode0SecondSparseQ (2) = l22AMode0Second2ExpectedQ := by
  close_l22_a0_second
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0Second3_eq :
    l22AMode0SecondSparseQ (3) = l22AMode0Second3ExpectedQ := by
  close_l22_a0_second

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22AMode0Second3_eq
end AxiomAudit
