/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL3

/-! # Mode-split tail and collection for the L(-3) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l3Entry10ModeSparseQ (i : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (25 / 4) (scaleQ (Nat.choose 3 i)
    (virVacModeSparseQ 3 ((i : ℤ) - 2) 6
      (reifyVirWordSparseQ [2, 2, 2])))

-- 40 canonical terms; sorted and zero-free
def l3Entry10Mode0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 0, 2], (25 / 4096)), ([0, 0, 0, 0, 0, 0, 1, 1], (25 / 8192)), ([0, 0, 0, 0, 0, 0, 3], (75 / 4096)), ([0, 0, 0, 0, 0, 1, 2], (75 / 2048)),
    ([0, 0, 0, 0, 0, 4], (75 / 512)), ([0, 0, 0, 0, 1, 1, 1], (75 / 4096)), ([0, 0, 0, 0, 1, 3], (225 / 2048)), ([0, 0, 0, 0, 2, 2], (75 / 256)),
    ([0, 0, 0, 0, 5], (75 / 256)), ([0, 0, 0, 1, 1, 2], (225 / 1024)), ([0, 0, 0, 1, 4], (75 / 128)), ([0, 0, 0, 2, 3], (375 / 256)),
    ([0, 0, 0, 6], (225 / 64)), ([0, 0, 1, 1, 1, 1], (75 / 2048)), ([0, 0, 1, 1, 3], (525 / 1024)), ([0, 0, 1, 2, 2], (75 / 128)),
    ([0, 0, 1, 5], (75 / 64)), ([0, 0, 2, 4], (375 / 64)), ([0, 0, 3, 3], (225 / 128)), ([0, 0, 7], (75 / 8)),
    ([0, 1, 1, 1, 2], (175 / 512)), ([0, 1, 1, 4], (225 / 128)), ([0, 1, 2, 3], (375 / 128)), ([0, 1, 6], (225 / 32)),
    ([0, 2, 2, 2], (25 / 32)), ([0, 2, 5], (175 / 16)), ([0, 3, 4], (375 / 32)), ([0, 8], (375 / 8)),
    ([1, 1, 1, 1, 1], (25 / 1024)), ([1, 1, 1, 3], (375 / 512)), ([1, 1, 2, 2], (25 / 64)), ([1, 1, 5], (275 / 64)),
    ([1, 2, 4], (75 / 32)), ([1, 3, 3], (225 / 64)), ([1, 7], (75 / 4)), ([2, 2, 3], (75 / 32)),
    ([2, 6], (75 / 4)), ([3, 5], (225 / 8)), ([4, 4], (75 / 8)), ([9], 150)]
-- 29 canonical terms; sorted and zero-free
def l3Entry10Mode1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 0, 1], (75 / 8192)), ([0, 0, 0, 0, 0, 0, 2], (75 / 4096)), ([0, 0, 0, 0, 0, 1, 1], (225 / 4096)), ([0, 0, 0, 0, 0, 3], (225 / 1024)),
    ([0, 0, 0, 0, 1, 2], (1125 / 2048)), ([0, 0, 0, 0, 4], (225 / 512)), ([0, 0, 0, 1, 1, 1], (225 / 2048)), ([0, 0, 0, 1, 3], (225 / 128)),
    ([0, 0, 0, 2, 2], (225 / 256)), ([0, 0, 0, 5], (675 / 128)), ([0, 0, 1, 1, 2], (1125 / 1024)), ([0, 0, 1, 4], (675 / 128)),
    ([0, 0, 2, 3], (225 / 32)), ([0, 0, 6], (225 / 16)), ([0, 1, 1, 1, 1], (75 / 1024)), ([0, 1, 1, 3], (675 / 256)),
    ([0, 1, 2, 2], (375 / 128)), ([0, 1, 5], (1275 / 64)), ([0, 2, 4], (225 / 16)), ([0, 3, 3], (225 / 32)),
    ([0, 7], (1125 / 16)), ([1, 1, 1, 2], (75 / 512)), ([1, 1, 4], (225 / 128)), ([1, 2, 3], (225 / 32)),
    ([1, 6], (225 / 8)), ([2, 2, 2], (75 / 32)), ([2, 5], (375 / 8)), ([3, 4], (225 / 8)),
    ([8], 225)]
-- 0 canonical terms; sorted and zero-free
def l3Entry10Mode2ExpectedQ : SparseRational.Poly ℕ :=
  []
-- 14 canonical terms; sorted and zero-free
def l3Entry10Mode3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 1], (-75 / 1024)), ([0, 0, 0, 0, 2], (-75 / 512)), ([0, 0, 0, 1, 1], (-75 / 256)), ([0, 0, 0, 3], (-225 / 128)),
    ([0, 0, 1, 2], (-75 / 32)), ([0, 0, 4], (-75 / 16)), ([0, 1, 1, 1], (-75 / 256)), ([0, 1, 3], (-375 / 64)),
    ([0, 2, 2], (-75 / 32)), ([0, 5], (-375 / 16)), ([1, 1, 2], (-225 / 128)), ([1, 4], (-225 / 16)),
    ([2, 3], (-225 / 16)), ([6], -75)]

macro "close_l3_tail_mode" : tactic => `(tactic|
  (unfold l3Entry10ModeSparseQ
   rw [reifyZhuVir222SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l3Entry10Mode0ExpectedQ, l3Entry10Mode1ExpectedQ,
    l3Entry10Mode2ExpectedQ, l3Entry10Mode3ExpectedQ,
    virVacModeSparseQ, virVacModeCoefficientQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, zhuVir222ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- The largest mode is isolated from all collection work.
theorem l3Entry10Mode0_eq :
    l3Entry10ModeSparseQ 0 = l3Entry10Mode0ExpectedQ := by close_l3_tail_mode
set_option maxHeartbeats 1000000 in
-- Independent finite mode.
theorem l3Entry10Mode1_eq :
    l3Entry10ModeSparseQ 1 = l3Entry10Mode1ExpectedQ := by close_l3_tail_mode
set_option maxHeartbeats 1000000 in
-- Independent finite mode.
theorem l3Entry10Mode2_eq :
    l3Entry10ModeSparseQ 2 = l3Entry10Mode2ExpectedQ := by close_l3_tail_mode
set_option maxHeartbeats 1000000 in
-- Independent finite mode.
theorem l3Entry10Mode3_eq :
    l3Entry10ModeSparseQ 3 = l3Entry10Mode3ExpectedQ := by close_l3_tail_mode

theorem l3Entry10_eq : l3Entry10SparseQ = l3Entry10ExpectedQ := by
  unfold l3Entry10SparseQ
  rw [virVacCircleSparseQ, scaleQ_sumQ (25 / 4) (by norm_num)]
  norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_nil]
  change sumQ [l3Entry10ModeSparseQ 0, l3Entry10ModeSparseQ 1,
    l3Entry10ModeSparseQ 2, l3Entry10ModeSparseQ 3] = l3Entry10ExpectedQ
  rw [l3Entry10Mode0_eq, l3Entry10Mode1_eq, l3Entry10Mode2_eq,
    l3Entry10Mode3_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l3Entry10Mode0ExpectedQ, l3Entry10Mode1ExpectedQ,
    l3Entry10Mode2ExpectedQ, l3Entry10Mode3ExpectedQ,
    l3Entry10ExpectedQ, sumQ, addQ, compareWord]

/-- The eleven L(-3)-left ledger entries reconstruct their canonical family coordinate. -/
theorem certificateL3SparseQ_eq_expected :
    evalVirVacLedger certificateL3Ledger = rhsL3ExpectedQ := by
  simp only [evalVirVacLedger, certificateL3Ledger, List.map_cons, List.map_nil,
    ZhuStateDesc.weight, ZhuStateDesc.eval]
  change sumQ [l3Entry0SparseQ, l3Entry1SparseQ, l3Entry2SparseQ,
    l3Entry3SparseQ, l3Entry4SparseQ, l3Entry5SparseQ, l3Entry6SparseQ,
    l3Entry7SparseQ, l3Entry8SparseQ, l3Entry9SparseQ,
    l3Entry10SparseQ] = rhsL3ExpectedQ
  rw [l3Entry0_eq, l3Entry1_eq, l3Entry2_eq, l3Entry3_eq,
    l3Entry4_eq, l3Entry5_eq, l3Entry6_eq, l3Entry7_eq,
    l3Entry8_eq, l3Entry9_eq, l3Entry10_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l3Entry0ExpectedQ, l3Entry1ExpectedQ, l3Entry2ExpectedQ,
    l3Entry3ExpectedQ, l3Entry4ExpectedQ, l3Entry5ExpectedQ,
    l3Entry6ExpectedQ, l3Entry7ExpectedQ, l3Entry8ExpectedQ,
    l3Entry9ExpectedQ, l3Entry10ExpectedQ, rhsL3ExpectedQ,
    sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.certificateL3SparseQ_eq_expected
end AxiomAudit
