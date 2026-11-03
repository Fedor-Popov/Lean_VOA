/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL2A

/-! # Next six finite certificates for the L(-2) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l2Entry8SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-49111 / 128) (virVacCircleSparseQ 2 6 (reifyVirWordSparseQ [4, 2]))
def l2Entry9SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-62005 / 256) (virVacCircleSparseQ 2 6 (reifyVirWordSparseQ [3, 3]))
def l2Entry10SparseQ : SparseRational.Poly ℕ :=
  scaleQ (75 / 8) (virVacCircleSparseQ 2 6 (reifyVirWordSparseQ [2, 2, 2]))
def l2Entry11SparseQ : SparseRational.Poly ℕ :=
  scaleQ (2057 / 64) (virVacCircleSparseQ 2 7 (reifyVirWordSparseQ [7]))
def l2Entry12SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-3709 / 128) (virVacCircleSparseQ 2 7 (reifyVirWordSparseQ [5, 2]))
def l2Entry13SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-9969 / 64) (virVacCircleSparseQ 2 7 (reifyVirWordSparseQ [4, 3]))

macro "close_l2b_entry" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
    [l2Entry8ExpectedQ, l2Entry9ExpectedQ, l2Entry10ExpectedQ,
    l2Entry11ExpectedQ, l2Entry12ExpectedQ, l2Entry13ExpectedQ,
    virVacCircleSparseQ, virVacModeSparseQ, virVacModeCoefficientQ,
    virModeSparseQ, omegaSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, zhuVir42ExpectedQ, zhuVir33ExpectedQ,
    zhuVir222ExpectedQ, zhuVir7ExpectedQ, zhuVir52ExpectedQ,
    zhuVir43ExpectedQ, aWordActSparseQ, aWordWeightQ,
    sumSparseIcc, intIccListQ, natRangeQ, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ, normalizeQ,
    insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
theorem l2Entry8_eq : l2Entry8SparseQ = l2Entry8ExpectedQ := by
  unfold l2Entry8SparseQ
  rw [reifyZhuVir42SparseQ_eq_expected]
  close_l2b_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry9_eq : l2Entry9SparseQ = l2Entry9ExpectedQ := by
  unfold l2Entry9SparseQ
  rw [reifyZhuVir33SparseQ_eq_expected]
  close_l2b_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry10_eq : l2Entry10SparseQ = l2Entry10ExpectedQ := by
  unfold l2Entry10SparseQ
  rw [reifyZhuVir222SparseQ_eq_expected]
  close_l2b_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry11_eq : l2Entry11SparseQ = l2Entry11ExpectedQ := by
  unfold l2Entry11SparseQ
  rw [reifyZhuVir7SparseQ_eq_expected]
  close_l2b_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry12_eq : l2Entry12SparseQ = l2Entry12ExpectedQ := by
  unfold l2Entry12SparseQ
  rw [reifyZhuVir52SparseQ_eq_expected]
  close_l2b_entry
set_option maxHeartbeats 1000000 in
theorem l2Entry13_eq : l2Entry13SparseQ = l2Entry13ExpectedQ := by
  unfold l2Entry13SparseQ
  rw [reifyZhuVir43SparseQ_eq_expected]
  close_l2b_entry

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l2Entry13_eq
end AxiomAudit
