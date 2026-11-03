/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22ModesA2

/-! # First normal-order half of the lowest first L22 Zhu-circle mode -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxRecDepth 100000

def l22AMode0FirstSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (3417 / 256)
    (virModeSparseQ m (8 + m).toNat
      (virModeSparseQ (-5 - m) 3 (reifyVirWordSparseQ [3])))

-- 5 canonical terms; sorted and zero-free
def l22AMode0FirstNeg8ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 6], (-3417 / 256)), ([1, 5], (-3417 / 256)), ([2, 4], (-3417 / 256)), ([3, 3], (-3417 / 512)),
    ([7], (-23919 / 256))]
-- 0 canonical terms; sorted and zero-free
def l22AMode0FirstNeg7ExpectedQ : SparseRational.Poly ℕ :=
  []
-- 10 canonical terms; sorted and zero-free
def l22AMode0FirstNeg6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 4], (3417 / 2048)), ([0, 0, 1, 3], (3417 / 2048)), ([0, 0, 2, 2], (3417 / 4096)), ([0, 0, 5], (17085 / 2048)),
    ([0, 1, 4], (3417 / 1024)), ([0, 6], (3417 / 256)), ([1, 1, 3], (3417 / 1024)), ([1, 2, 2], (3417 / 2048)),
    ([1, 5], (17085 / 1024)), ([7], (3417 / 128))]
-- 9 canonical terms; sorted and zero-free
def l22AMode0FirstNeg5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 3], (10251 / 4096)), ([0, 1, 1, 2], (10251 / 4096)), ([0, 1, 4], (10251 / 1024)), ([0, 2, 3], (10251 / 2048)),
    ([0, 6], (10251 / 512)), ([1, 2, 2], (10251 / 2048)), ([1, 5], (10251 / 1024)), ([2, 4], (10251 / 512)),
    ([7], (30753 / 512))]
-- 10 canonical terms; sorted and zero-free
def l22AMode0FirstNeg4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 2, 2], (3417 / 2048)), ([0, 1, 1, 2], (3417 / 2048)), ([0, 2, 3], (10251 / 1024)), ([0, 6], (10251 / 512)),
    ([1, 1, 1, 1], (3417 / 8192)), ([1, 1, 3], (10251 / 2048)), ([1, 5], (3417 / 256)), ([2, 4], (3417 / 512)),
    ([3, 3], (30753 / 2048)), ([7], (10251 / 128))]
-- 17 canonical terms; sorted and zero-free
def l22AMode0FirstNeg3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 1], (3417 / 32768)), ([0, 0, 0, 1, 2], (3417 / 8192)), ([0, 0, 0, 4], (3417 / 4096)), ([0, 0, 1, 1, 1], (3417 / 16384)),
    ([0, 0, 1, 3], (23919 / 8192)), ([0, 0, 2, 2], (3417 / 8192)), ([0, 0, 5], (10251 / 4096)), ([0, 1, 1, 2], (3417 / 2048)),
    ([0, 1, 4], (17085 / 2048)), ([0, 2, 3], (10251 / 2048)), ([0, 6], (3417 / 128)), ([1, 1, 3], (3417 / 4096)),
    ([1, 2, 2], (10251 / 4096)), ([1, 5], (30753 / 2048)), ([2, 4], (10251 / 512)), ([3, 3], (3417 / 512)),
    ([7], (51255 / 512))]
-- 17 canonical terms; sorted and zero-free
def l22AMode0FirstNeg2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 1], (3417 / 32768)), ([0, 0, 0, 1, 2], (3417 / 8192)), ([0, 0, 0, 4], (3417 / 4096)), ([0, 0, 1, 1, 1], (3417 / 16384)),
    ([0, 0, 1, 3], (30753 / 8192)), ([0, 0, 2, 2], (3417 / 8192)), ([0, 0, 5], (10251 / 4096)), ([0, 1, 1, 2], (10251 / 4096)),
    ([0, 1, 4], (23919 / 2048)), ([0, 2, 3], (3417 / 512)), ([0, 6], (17085 / 512)), ([1, 1, 3], (3417 / 4096)),
    ([1, 2, 2], (17085 / 4096)), ([1, 5], (37587 / 2048)), ([2, 4], (3417 / 128)), ([3, 3], (3417 / 512)),
    ([7], (30753 / 256))]

macro "close_l22_a0_first" : tactic => `(tactic|
  (unfold l22AMode0FirstSparseQ
   rw [reifyVir3SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l22AMode0FirstNeg8ExpectedQ, l22AMode0FirstNeg7ExpectedQ,
    l22AMode0FirstNeg6ExpectedQ, l22AMode0FirstNeg5ExpectedQ,
    l22AMode0FirstNeg4ExpectedQ, l22AMode0FirstNeg3ExpectedQ,
    l22AMode0FirstNeg2ExpectedQ, vir3ExpectedQ, virModeSparseQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, vacuumSparseQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg8_eq :
    l22AMode0FirstSparseQ (-8) = l22AMode0FirstNeg8ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg7_eq :
    l22AMode0FirstSparseQ (-7) = l22AMode0FirstNeg7ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg6_eq :
    l22AMode0FirstSparseQ (-6) = l22AMode0FirstNeg6ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg5_eq :
    l22AMode0FirstSparseQ (-5) = l22AMode0FirstNeg5ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg4_eq :
    l22AMode0FirstSparseQ (-4) = l22AMode0FirstNeg4ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg3_eq :
    l22AMode0FirstSparseQ (-3) = l22AMode0FirstNeg3ExpectedQ := by
  close_l22_a0_first
set_option maxHeartbeats 1000000 in
-- One summand of the finite normal-order expansion.
theorem l22AMode0FirstNeg2_eq :
    l22AMode0FirstSparseQ (-2) = l22AMode0FirstNeg2ExpectedQ := by
  close_l22_a0_first

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l22AMode0FirstNeg2_eq
end AxiomAudit
