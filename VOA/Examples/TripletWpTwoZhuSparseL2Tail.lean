/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL2B

/-! # Mode-split tail and collection for the L(-2) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l2Entry14SparseQ : SparseRational.Poly ℕ :=
  scaleQ (1221 / 64)
    (virVacCircleSparseQ 2 7 (reifyVirWordSparseQ [3, 2, 2]))

def l2Entry14ModeSparseQ (i : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (1221 / 64) (scaleQ (Nat.choose 2 i)
    (virVacModeSparseQ 2 ((i : ℤ) - 2) 7
      (reifyVirWordSparseQ [3, 2, 2])))


-- 37 canonical terms; sorted and zero-free
def l2Entry14Mode0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 1, 1], (1221 / 65536)), ([0, 0, 0, 0, 0, 1, 2], (1221 / 16384)), ([0, 0, 0, 0, 0, 4], (1221 / 8192)), ([0, 0, 0, 0, 1, 1, 1], (1221 / 16384)),
    ([0, 0, 0, 0, 1, 3], (10989 / 16384)), ([0, 0, 0, 0, 2, 2], (1221 / 16384)), ([0, 0, 0, 0, 5], (3663 / 8192)), ([0, 0, 0, 1, 1, 2], (1221 / 2048)),
    ([0, 0, 0, 1, 4], (3663 / 2048)), ([0, 0, 0, 2, 3], (1221 / 1024)), ([0, 0, 0, 6], (1221 / 256)), ([0, 0, 1, 1, 1, 1], (1221 / 16384)),
    ([0, 0, 1, 1, 3], (8547 / 4096)), ([0, 0, 1, 2, 2], (6105 / 4096)), ([0, 0, 1, 5], (18315 / 2048)), ([0, 0, 2, 4], (1221 / 256)),
    ([0, 0, 3, 3], (3663 / 1024)), ([0, 0, 7], (6105 / 512)), ([0, 1, 1, 1, 2], (1221 / 4096)), ([0, 1, 1, 4], (6105 / 2048)),
    ([0, 1, 2, 3], (8547 / 1024)), ([0, 1, 6], (3663 / 128)), ([0, 2, 2, 2], (1221 / 1024)), ([0, 2, 5], (10989 / 512)),
    ([0, 3, 4], (3663 / 256)), ([0, 8], (10989 / 128)), ([1, 1, 1, 3], (1221 / 4096)), ([1, 1, 2, 2], (1221 / 4096)),
    ([1, 1, 5], (3663 / 2048)), ([1, 2, 4], (1221 / 256)), ([1, 3, 3], (1221 / 256)), ([1, 7], (6105 / 256)),
    ([2, 2, 3], (3663 / 512)), ([2, 6], (3663 / 64)), ([3, 5], (10989 / 256)), ([4, 4], (1221 / 128)),
    ([9], (8547 / 32))]

-- 29 canonical terms; sorted and zero-free
def l2Entry14Mode1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 0, 1], (1221 / 65536)), ([0, 0, 0, 0, 0, 0, 2], (1221 / 32768)), ([0, 0, 0, 0, 0, 1, 1], (3663 / 32768)), ([0, 0, 0, 0, 0, 3], (1221 / 2048)),
    ([0, 0, 0, 0, 1, 2], (20757 / 16384)), ([0, 0, 0, 0, 4], (6105 / 4096)), ([0, 0, 0, 1, 1, 1], (3663 / 16384)), ([0, 0, 0, 1, 3], (8547 / 2048)),
    ([0, 0, 0, 2, 2], (3663 / 2048)), ([0, 0, 0, 5], (13431 / 1024)), ([0, 0, 1, 1, 2], (23199 / 8192)), ([0, 0, 1, 4], (13431 / 1024)),
    ([0, 0, 2, 3], (8547 / 512)), ([0, 0, 6], (8547 / 256)), ([0, 1, 1, 1, 1], (1221 / 8192)), ([0, 1, 1, 3], (6105 / 1024)),
    ([0, 1, 2, 2], (8547 / 1024)), ([0, 1, 5], (23199 / 512)), ([0, 2, 4], (1221 / 32)), ([0, 3, 3], (1221 / 64)),
    ([0, 7], (10989 / 64)), ([1, 1, 1, 2], (3663 / 4096)), ([1, 1, 4], (6105 / 1024)), ([1, 2, 3], (1221 / 64)),
    ([1, 6], (8547 / 128)), ([2, 2, 2], (1221 / 256)), ([2, 5], (13431 / 128)), ([3, 4], (1221 / 16)),
    ([8], (8547 / 16))]

-- 20 canonical terms; sorted and zero-free
def l2Entry14Mode2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 2], (1221 / 8192)), ([0, 0, 0, 0, 1, 1], (6105 / 16384)), ([0, 0, 0, 0, 3], (3663 / 8192)), ([0, 0, 0, 1, 2], (3663 / 2048)),
    ([0, 0, 0, 4], (1221 / 256)), ([0, 0, 1, 1, 1], (3663 / 4096)), ([0, 0, 1, 3], (18315 / 2048)), ([0, 0, 2, 2], (3663 / 1024)),
    ([0, 0, 5], (6105 / 512)), ([0, 1, 1, 2], (10989 / 2048)), ([0, 1, 4], (6105 / 256)), ([0, 2, 3], (6105 / 256)),
    ([0, 6], (10989 / 128)), ([1, 1, 1, 1], (1221 / 4096)), ([1, 1, 3], (13431 / 2048)), ([1, 2, 2], (1221 / 256)),
    ([1, 5], (1221 / 32)), ([2, 4], (6105 / 128)), ([3, 3], (3663 / 128)), ([7], (8547 / 32))]


macro "close_l2_tail_mode" : tactic => `(tactic|
  (unfold l2Entry14ModeSparseQ
   rw [reifyZhuVir322SparseQ_eq_expected]
   norm_num (config := { maxSteps := 1000000 })
    [l2Entry14Mode0ExpectedQ, l2Entry14Mode1ExpectedQ,
    l2Entry14Mode2ExpectedQ, virVacModeSparseQ,
    virVacModeCoefficientQ, omegaSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, zhuVir322ExpectedQ, aWordActSparseQ,
    aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
theorem l2Entry14Mode0_eq :
    l2Entry14ModeSparseQ 0 = l2Entry14Mode0ExpectedQ := by
  close_l2_tail_mode
set_option maxHeartbeats 1000000 in
theorem l2Entry14Mode1_eq :
    l2Entry14ModeSparseQ 1 = l2Entry14Mode1ExpectedQ := by
  close_l2_tail_mode
set_option maxHeartbeats 1000000 in
theorem l2Entry14Mode2_eq :
    l2Entry14ModeSparseQ 2 = l2Entry14Mode2ExpectedQ := by
  close_l2_tail_mode

theorem l2Entry14_eq : l2Entry14SparseQ = l2Entry14ExpectedQ := by
  unfold l2Entry14SparseQ
  rw [virVacCircleSparseQ, scaleQ_sumQ (1221 / 64) (by norm_num)]
  norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_nil]
  change sumQ [l2Entry14ModeSparseQ 0, l2Entry14ModeSparseQ 1,
    l2Entry14ModeSparseQ 2] = l2Entry14ExpectedQ
  rw [l2Entry14Mode0_eq, l2Entry14Mode1_eq, l2Entry14Mode2_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l2Entry14Mode0ExpectedQ, l2Entry14Mode1ExpectedQ,
    l2Entry14Mode2ExpectedQ, l2Entry14ExpectedQ,
    sumQ, addQ, compareWord]

/-- The fifteen L(-2)-left ledger entries reconstruct their family coordinate. -/
theorem certificateL2SparseQ_eq_expected :
    evalVirVacLedger certificateL2Ledger = rhsL2ExpectedQ := by
  simp only [evalVirVacLedger, certificateL2Ledger, List.map_cons, List.map_nil,
    ZhuStateDesc.weight, ZhuStateDesc.eval]
  change sumQ [l2Entry0SparseQ, l2Entry1SparseQ, l2Entry2SparseQ,
    l2Entry3SparseQ, l2Entry4SparseQ, l2Entry5SparseQ, l2Entry6SparseQ,
    l2Entry7SparseQ, l2Entry8SparseQ, l2Entry9SparseQ, l2Entry10SparseQ,
    l2Entry11SparseQ, l2Entry12SparseQ, l2Entry13SparseQ,
    l2Entry14SparseQ] = rhsL2ExpectedQ
  rw [l2Entry0_eq, l2Entry1_eq, l2Entry2_eq, l2Entry3_eq,
    l2Entry4_eq, l2Entry5_eq, l2Entry6_eq, l2Entry7_eq,
    l2Entry8_eq, l2Entry9_eq, l2Entry10_eq, l2Entry11_eq,
    l2Entry12_eq, l2Entry13_eq, l2Entry14_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l2Entry0ExpectedQ, l2Entry1ExpectedQ, l2Entry2ExpectedQ,
    l2Entry3ExpectedQ, l2Entry4ExpectedQ, l2Entry5ExpectedQ,
    l2Entry6ExpectedQ, l2Entry7ExpectedQ, l2Entry8ExpectedQ,
    l2Entry9ExpectedQ, l2Entry10ExpectedQ, l2Entry11ExpectedQ,
    l2Entry12ExpectedQ, l2Entry13ExpectedQ, l2Entry14ExpectedQ,
    rhsL2ExpectedQ, sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.certificateL2SparseQ_eq_expected
end AxiomAudit
