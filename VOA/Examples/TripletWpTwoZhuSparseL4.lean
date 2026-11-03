/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseStates

/-! # Efficient single-Virasoro certificate for the L(-4) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxRecDepth 100000

def l4Entry0SparseQ : SparseRational.Poly ℕ :=
  scaleQ (2431 / 384) (virVacCircleSparseQ 4 0 (vacuumSparseQ))
def l4Entry1SparseQ : SparseRational.Poly ℕ :=
  scaleQ (48653 / 384) (virVacCircleSparseQ 4 2 (reifyVirWordSparseQ [2]))
def l4Entry2SparseQ : SparseRational.Poly ℕ :=
  scaleQ (157223 / 768) (virVacCircleSparseQ 4 3 (reifyVirWordSparseQ [3]))
def l4Entry3SparseQ : SparseRational.Poly ℕ :=
  scaleQ (2983 / 32) (virVacCircleSparseQ 4 4 (reifyVirWordSparseQ [4]))
def l4Entry4SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-401 / 64) (virVacCircleSparseQ 4 4 (reifyVirWordSparseQ [2, 2]))
def l4Entry5SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-1159 / 192) (virVacCircleSparseQ 4 5 (reifyVirWordSparseQ [5]))
def l4Entry6SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-2689 / 384) (virVacCircleSparseQ 4 5 (reifyVirWordSparseQ [3, 2]))

-- 6 canonical terms; sorted and zero-free
def l4Entry0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 2], (2431 / 384)), ([0, 3], (2431 / 512)), ([1, 1], (2431 / 768)), ([1, 2], (2431 / 512)),
    ([3], (2431 / 128)), ([4], (2431 / 128))]
-- 18 canonical terms; sorted and zero-free
def l4Entry1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 2], (48653 / 3072)), ([0, 0, 0, 3], (48653 / 4096)), ([0, 0, 1, 1], (48653 / 6144)), ([0, 0, 1, 2], (48653 / 4096)),
    ([0, 0, 3], (48653 / 1024)), ([0, 0, 4], (48653 / 1024)), ([0, 1], (48653 / 1536)), ([0, 1, 2], (48653 / 1536)),
    ([0, 1, 3], (48653 / 2048)), ([0, 4], (48653 / 384)), ([0, 5], (48653 / 512)), ([1, 1, 1], (48653 / 3072)),
    ([1, 1, 2], (48653 / 2048)), ([1, 3], (48653 / 512)), ([1, 4], (48653 / 512)), ([2], (48653 / 768)),
    ([5], (48653 / 192)), ([6], (48653 / 256))]
-- 21 canonical terms; sorted and zero-free
def l4Entry2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 2], (157223 / 3072)), ([0, 0, 1, 3], (157223 / 4096)), ([0, 1, 1, 1], (157223 / 6144)), ([0, 1, 1, 2], (157223 / 4096)),
    ([0, 1, 3], (157223 / 1024)), ([0, 1, 4], (157223 / 1024)), ([0, 2], (157223 / 1536)), ([0, 2, 2], (157223 / 1536)),
    ([0, 2, 3], (157223 / 2048)), ([0, 5], (157223 / 384)), ([0, 6], (157223 / 512)), ([1, 1], (157223 / 3072)),
    ([1, 1, 2], (157223 / 3072)), ([1, 2, 2], (157223 / 2048)), ([1, 4], (157223 / 768)), ([1, 5], (157223 / 1024)),
    ([2, 3], (157223 / 512)), ([2, 4], (157223 / 512)), ([3], (157223 / 512)), ([6], (157223 / 128)),
    ([7], (471669 / 512))]
-- 26 canonical terms; sorted and zero-free
def l4Entry3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 2, 2], (2983 / 128)), ([0, 0, 2, 3], (8949 / 512)), ([0, 1, 1, 2], (2983 / 128)), ([0, 1, 1, 3], (8949 / 1024)),
    ([0, 1, 2, 2], (8949 / 512)), ([0, 2, 3], (8949 / 64)), ([0, 2, 4], (8949 / 128)), ([0, 3], (8949 / 128)),
    ([0, 3, 3], (26847 / 512)), ([0, 6], (8949 / 32)), ([0, 7], (26847 / 128)), ([1, 1, 1, 1], (2983 / 512)),
    ([1, 1, 1, 2], (8949 / 1024)), ([1, 1, 3], (8949 / 128)), ([1, 1, 4], (8949 / 256)), ([1, 2], (8949 / 128)),
    ([1, 2, 3], (26847 / 512)), ([1, 5], (2983 / 16)), ([1, 6], (8949 / 64)), ([2, 4], (2983 / 32)),
    ([2, 5], (8949 / 128)), ([3, 3], (26847 / 128)), ([3, 4], (26847 / 128)), ([4], (8949 / 32)),
    ([7], (8949 / 8)), ([8], (26847 / 32))]
-- 47 canonical terms; sorted and zero-free
def l4Entry4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 2], (-401 / 4096)), ([0, 0, 0, 0, 0, 3], (-1203 / 16384)), ([0, 0, 0, 0, 1, 1], (-401 / 8192)), ([0, 0, 0, 0, 1, 2], (-1203 / 16384)),
    ([0, 0, 0, 0, 3], (-1203 / 4096)), ([0, 0, 0, 0, 4], (-1203 / 4096)), ([0, 0, 0, 1], (-401 / 1024)), ([0, 0, 0, 1, 2], (-401 / 1024)),
    ([0, 0, 0, 1, 3], (-1203 / 4096)), ([0, 0, 0, 4], (-401 / 256)), ([0, 0, 0, 5], (-1203 / 1024)), ([0, 0, 1, 1, 1], (-401 / 2048)),
    ([0, 0, 1, 1, 2], (-1203 / 4096)), ([0, 0, 1, 3], (-1203 / 1024)), ([0, 0, 1, 4], (-1203 / 1024)), ([0, 0, 2], (-401 / 512)),
    ([0, 0, 2, 2], (-401 / 256)), ([0, 0, 2, 3], (-1203 / 1024)), ([0, 0, 5], (-401 / 128)), ([0, 0, 6], (-1203 / 512)),
    ([0, 1, 1], (-401 / 512)), ([0, 1, 1, 2], (-1203 / 1024)), ([0, 1, 1, 3], (-1203 / 4096)), ([0, 1, 2, 2], (-1203 / 1024)),
    ([0, 1, 4], (-401 / 128)), ([0, 1, 5], (-1203 / 512)), ([0, 2, 3], (-2005 / 256)), ([0, 2, 4], (-1203 / 256)),
    ([0, 3], (-1203 / 256)), ([0, 3, 3], (-1203 / 512)), ([0, 6], (-1203 / 64)), ([0, 7], (-3609 / 256)),
    ([1, 1, 1, 1], (-401 / 2048)), ([1, 1, 1, 2], (-1203 / 4096)), ([1, 1, 3], (-2807 / 1024)), ([1, 1, 4], (-1203 / 1024)),
    ([1, 2], (-401 / 128)), ([1, 2, 3], (-1203 / 512)), ([1, 5], (-401 / 64)), ([1, 6], (-1203 / 256)),
    ([2, 4], (-401 / 64)), ([2, 5], (-1203 / 256)), ([3, 3], (-1203 / 128)), ([3, 4], (-1203 / 128)),
    ([4], (-401 / 32)), ([7], (-401 / 8)), ([8], (-1203 / 32))]
-- 28 canonical terms; sorted and zero-free
def l4Entry5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 2, 3], (-1159 / 768)), ([0, 0, 3, 3], (-1159 / 1024)), ([0, 1, 1, 3], (-1159 / 1536)), ([0, 1, 2, 2], (-1159 / 768)),
    ([0, 1, 2, 3], (-1159 / 512)), ([0, 2, 4], (-1159 / 192)), ([0, 3, 3], (-1159 / 256)), ([0, 3, 4], (-1159 / 128)),
    ([0, 4], (-1159 / 192)), ([0, 7], (-1159 / 48)), ([0, 8], (-1159 / 64)), ([1, 1, 1, 2], (-1159 / 1536)),
    ([1, 1, 2, 2], (-1159 / 1024)), ([1, 1, 4], (-1159 / 384)), ([1, 2, 3], (-1159 / 256)), ([1, 2, 4], (-1159 / 128)),
    ([1, 3], (-1159 / 192)), ([1, 6], (-1159 / 64)), ([1, 7], (-3477 / 256)), ([2, 2], (-1159 / 384)),
    ([2, 5], (-1159 / 96)), ([2, 6], (-1159 / 128)), ([3, 4], (-1159 / 48)), ([3, 5], (-1159 / 256)),
    ([4, 4], (-1159 / 64)), ([5], (-5795 / 192)), ([8], (-5795 / 48)), ([9], (-5795 / 64))]
-- 58 canonical terms; sorted and zero-free
def l4Entry6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 2], (-2689 / 12288)), ([0, 0, 0, 0, 1, 3], (-2689 / 16384)), ([0, 0, 0, 1, 1, 1], (-2689 / 24576)), ([0, 0, 0, 1, 1, 2], (-2689 / 16384)),
    ([0, 0, 0, 1, 3], (-2689 / 4096)), ([0, 0, 0, 1, 4], (-2689 / 4096)), ([0, 0, 0, 2], (-2689 / 6144)), ([0, 0, 0, 2, 2], (-2689 / 6144)),
    ([0, 0, 0, 2, 3], (-2689 / 8192)), ([0, 0, 0, 5], (-2689 / 1536)), ([0, 0, 0, 6], (-2689 / 2048)), ([0, 0, 1, 1], (-2689 / 4096)),
    ([0, 0, 1, 1, 2], (-2689 / 4096)), ([0, 0, 1, 1, 3], (-2689 / 8192)), ([0, 0, 1, 2, 2], (-2689 / 8192)), ([0, 0, 1, 4], (-2689 / 1024)),
    ([0, 0, 1, 5], (-8067 / 4096)), ([0, 0, 2, 3], (-18823 / 6144)), ([0, 0, 2, 4], (-2689 / 2048)), ([0, 0, 3], (-2689 / 2048)),
    ([0, 0, 3, 3], (-2689 / 2048)), ([0, 0, 6], (-2689 / 512)), ([0, 0, 7], (-8067 / 2048)), ([0, 1, 1, 1, 1], (-2689 / 12288)),
    ([0, 1, 1, 1, 2], (-2689 / 8192)), ([0, 1, 1, 3], (-13445 / 6144)), ([0, 1, 1, 4], (-2689 / 2048)), ([0, 1, 2], (-2689 / 1024)),
    ([0, 1, 2, 2], (-2689 / 3072)), ([0, 1, 2, 3], (-8067 / 4096)), ([0, 1, 5], (-2689 / 384)), ([0, 1, 6], (-2689 / 512)),
    ([0, 2, 4], (-2689 / 384)), ([0, 2, 5], (-2689 / 1024)), ([0, 3, 3], (-2689 / 512)), ([0, 3, 4], (-8067 / 1024)),
    ([0, 4], (-2689 / 384)), ([0, 7], (-2689 / 96)), ([0, 8], (-2689 / 128)), ([1, 1, 1], (-2689 / 6144)),
    ([1, 1, 1, 2], (-2689 / 6144)), ([1, 1, 2, 2], (-2689 / 4096)), ([1, 1, 4], (-2689 / 768)), ([1, 1, 5], (-2689 / 2048)),
    ([1, 2, 3], (-2689 / 1024)), ([1, 2, 4], (-2689 / 512)), ([1, 3], (-13445 / 3072)), ([1, 6], (-2689 / 256)),
    ([1, 7], (-8067 / 1024)), ([2, 2], (-2689 / 1536)), ([2, 5], (-2689 / 384)), ([2, 6], (-2689 / 512)),
    ([3, 4], (-13445 / 768)), ([3, 5], (-2689 / 512)), ([4, 4], (-2689 / 256)), ([5], (-13445 / 768)),
    ([8], (-13445 / 192)), ([9], (-13445 / 256))]

macro "close_l4_entry" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
    [l4Entry0ExpectedQ, l4Entry1ExpectedQ, l4Entry2ExpectedQ, l4Entry3ExpectedQ, l4Entry4ExpectedQ, l4Entry5ExpectedQ, l4Entry6ExpectedQ, virVacCircleSparseQ, virVacModeSparseQ,
    virVacModeCoefficientQ, virModeSparseQ, omegaSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, vacuumSparseQ,
    zhuVir2ExpectedQ, vir3ExpectedQ, zhuVir4ExpectedQ, vir22ExpectedQ,
    zhuVir5ExpectedQ, vir32ExpectedQ, aWordActSparseQ, aWordWeightQ,
    sumSparseIcc, intIccListQ, natRangeQ, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ, normalizeQ,
    insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry0_eq : l4Entry0SparseQ = l4Entry0ExpectedQ := by
  unfold l4Entry0SparseQ
  change scaleQ (2431 / 384) (virVacCircleSparseQ 4 0 vacuumSparseQ) = _
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry1_eq : l4Entry1SparseQ = l4Entry1ExpectedQ := by
  unfold l4Entry1SparseQ
  rw [reifyZhuVir2SparseQ_eq_expected]
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry2_eq : l4Entry2SparseQ = l4Entry2ExpectedQ := by
  unfold l4Entry2SparseQ
  rw [reifyVir3SparseQ_eq_expected]
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry3_eq : l4Entry3SparseQ = l4Entry3ExpectedQ := by
  unfold l4Entry3SparseQ
  rw [reifyZhuVir4SparseQ_eq_expected]
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry4_eq : l4Entry4SparseQ = l4Entry4ExpectedQ := by
  unfold l4Entry4SparseQ
  rw [reifyVir22SparseQ_eq_expected]
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry5_eq : l4Entry5SparseQ = l4Entry5ExpectedQ := by
  unfold l4Entry5SparseQ
  rw [reifyZhuVir5SparseQ_eq_expected]
  close_l4_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l4Entry6_eq : l4Entry6SparseQ = l4Entry6ExpectedQ := by
  unfold l4Entry6SparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l4_entry

/-- The seven L(-4)-left ledger entries reconstruct their canonical family coordinate. -/
theorem certificateL4SparseQ_eq_expected :
    evalVirVacLedger certificateL4Ledger = rhsL4ExpectedQ := by
  simp only [evalVirVacLedger, certificateL4Ledger, List.map_cons, List.map_nil,
    ZhuStateDesc.weight, ZhuStateDesc.eval]
  change sumQ [l4Entry0SparseQ, l4Entry1SparseQ, l4Entry2SparseQ,
    l4Entry3SparseQ, l4Entry4SparseQ, l4Entry5SparseQ,
    l4Entry6SparseQ] = rhsL4ExpectedQ
  rw [l4Entry0_eq, l4Entry1_eq, l4Entry2_eq, l4Entry3_eq,
    l4Entry4_eq, l4Entry5_eq, l4Entry6_eq]
  norm_num (config := { maxSteps := 1000000 })
    [l4Entry0ExpectedQ, l4Entry1ExpectedQ, l4Entry2ExpectedQ, l4Entry3ExpectedQ, l4Entry4ExpectedQ, l4Entry5ExpectedQ, l4Entry6ExpectedQ, rhsL4ExpectedQ, sumQ, addQ, compareWord]

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.certificateL4SparseQ_eq_expected
end AxiomAudit
