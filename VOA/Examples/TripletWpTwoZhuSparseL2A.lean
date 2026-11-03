/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL2Expected

/-! # First eight finite certificates for the L(-2) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l2Entry0SparseQ : SparseRational.Poly ℕ :=
  scaleQ (221 / 64) (virVacCircleSparseQ 2 0 vacuumSparseQ)
def l2Entry1SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-1313 / 128) (virVacCircleSparseQ 2 2 (reifyVirWordSparseQ [2]))
def l2Entry2SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-845 / 256) (virVacCircleSparseQ 2 3 (reifyVirWordSparseQ [3]))
def l2Entry3SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-131 / 64) (virVacCircleSparseQ 2 4 (reifyVirWordSparseQ [4]))
def l2Entry4SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-1223 / 128) (virVacCircleSparseQ 2 4 (reifyVirWordSparseQ [2, 2]))
def l2Entry5SparseQ : SparseRational.Poly ℕ :=
  scaleQ (27119 / 128) (virVacCircleSparseQ 2 5 (reifyVirWordSparseQ [5]))
def l2Entry6SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-71833 / 128) (virVacCircleSparseQ 2 5 (reifyVirWordSparseQ [3, 2]))
def l2Entry7SparseQ : SparseRational.Poly ℕ :=
  scaleQ (15899 / 64) (virVacCircleSparseQ 2 6 (reifyVirWordSparseQ [6]))

macro "close_l2a_entry" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
    [l2Entry0ExpectedQ, l2Entry1ExpectedQ, l2Entry2ExpectedQ,
    l2Entry3ExpectedQ, l2Entry4ExpectedQ, l2Entry5ExpectedQ,
    l2Entry6ExpectedQ, l2Entry7ExpectedQ,
    virVacCircleSparseQ, virVacModeSparseQ, virVacModeCoefficientQ,
    virModeSparseQ, omegaSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, vacuumSparseQ, zhuVir2ExpectedQ,
    vir3ExpectedQ, zhuVir4ExpectedQ, vir22ExpectedQ, zhuVir5ExpectedQ,
    vir32ExpectedQ, zhuVir6ExpectedQ, aWordActSparseQ, aWordWeightQ,
    sumSparseIcc, intIccListQ, natRangeQ, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ, normalizeQ,
    insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
theorem l2Entry0_eq : l2Entry0SparseQ = l2Entry0ExpectedQ := by
  unfold l2Entry0SparseQ
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry1_eq : l2Entry1SparseQ = l2Entry1ExpectedQ := by
  unfold l2Entry1SparseQ
  rw [reifyZhuVir2SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry2_eq : l2Entry2SparseQ = l2Entry2ExpectedQ := by
  unfold l2Entry2SparseQ
  rw [reifyVir3SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry3_eq : l2Entry3SparseQ = l2Entry3ExpectedQ := by
  unfold l2Entry3SparseQ
  rw [reifyZhuVir4SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry4_eq : l2Entry4SparseQ = l2Entry4ExpectedQ := by
  unfold l2Entry4SparseQ
  rw [reifyVir22SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry5_eq : l2Entry5SparseQ = l2Entry5ExpectedQ := by
  unfold l2Entry5SparseQ
  rw [reifyZhuVir5SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry6_eq : l2Entry6SparseQ = l2Entry6ExpectedQ := by
  unfold l2Entry6SparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l2a_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry7_eq : l2Entry7SparseQ = l2Entry7ExpectedQ := by
  unfold l2Entry7SparseQ
  rw [reifyZhuVir6SparseQ_eq_expected]
  close_l2a_entry

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l2Entry7_eq
end AxiomAudit
