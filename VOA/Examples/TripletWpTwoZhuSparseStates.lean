/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL22

/-! # Reified Virasoro right states for the sparse Zhu ledger -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational

set_option maxRecDepth 100000

def zhuVir2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0], 1 / 8), ([1], 1 / 4)]

-- 3 canonical terms; sorted and zero-free
def zhuVir4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 2], (1 / 4)), ([1, 1], (1 / 8)), ([3], (3 / 4))]
-- 3 canonical terms; sorted and zero-free
def zhuVir5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 3], (1 / 4)), ([1, 2], (1 / 4)), ([4], 1)]
-- 4 canonical terms; sorted and zero-free
def zhuVir6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 4], (1 / 4)), ([1, 3], (1 / 4)), ([2, 2], (1 / 8)), ([5], (5 / 4))]
-- 8 canonical terms; sorted and zero-free
def zhuVir42ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 2], (1 / 32)), ([0, 0, 1, 1], (1 / 64)), ([0, 0, 3], (3 / 32)), ([0, 1, 2], (1 / 16)),
    ([0, 4], (1 / 4)), ([1, 1, 1], (1 / 32)), ([1, 3], (3 / 16)), ([5], (1 / 2))]
-- 6 canonical terms; sorted and zero-free
def zhuVir33ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 1], (1 / 16)), ([0, 1, 2], (1 / 4)), ([0, 4], (1 / 2)), ([1, 3], (1 / 4)),
    ([2, 2], (1 / 4)), ([5], (3 / 2))]
-- 11 canonical terms; sorted and zero-free
def zhuVir222ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0], (1 / 512)), ([0, 0, 0, 0, 1], (3 / 256)), ([0, 0, 0, 2], (3 / 32)), ([0, 0, 1, 1], (3 / 128)),
    ([0, 0, 3], (3 / 16)), ([0, 1, 2], (3 / 16)), ([0, 4], (3 / 4)), ([1, 1, 1], (1 / 64)),
    ([1, 3], (3 / 8)), ([2, 2], (1 / 4)), ([5], 2)]
-- 4 canonical terms; sorted and zero-free
def zhuVir7ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 5], (1 / 4)), ([1, 4], (1 / 4)), ([2, 3], (1 / 4)), ([6], (3 / 2))]
-- 8 canonical terms; sorted and zero-free
def zhuVir52ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 3], (1 / 32)), ([0, 0, 1, 2], (1 / 32)), ([0, 0, 4], (1 / 8)), ([0, 1, 3], (1 / 16)),
    ([0, 5], (1 / 4)), ([1, 1, 2], (1 / 16)), ([1, 4], (1 / 4)), ([6], (1 / 2))]
-- 9 canonical terms; sorted and zero-free
def zhuVir43ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 2], (1 / 16)), ([0, 1, 1, 1], (1 / 32)), ([0, 1, 3], (3 / 16)), ([0, 2, 2], (1 / 8)),
    ([0, 5], (1 / 2)), ([1, 1, 2], (1 / 16)), ([1, 4], (1 / 4)), ([2, 3], (3 / 8)),
    ([6], (3 / 2))]
-- 14 canonical terms; sorted and zero-free
def zhuVir322ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 1], (1 / 256)), ([0, 0, 0, 0, 2], (1 / 128)), ([0, 0, 0, 1, 1], (1 / 64)), ([0, 0, 0, 3], (1 / 16)),
    ([0, 0, 1, 2], (3 / 32)), ([0, 0, 4], (1 / 8)), ([0, 1, 1, 1], (1 / 64)), ([0, 1, 3], (1 / 4)),
    ([0, 2, 2], (1 / 8)), ([0, 5], (3 / 4)), ([1, 1, 2], (1 / 32)), ([1, 4], (1 / 4)),
    ([2, 3], (1 / 2)), ([6], 2)]

macro "close_zhu_vir_state" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
    [reifyVirWordSparseQ, virActSparseQ, virVacuumSparseQ, virShiftRawQ,
    mulSparseQ, vacuumSparseQ, zhuVir2ExpectedQ, zhuVir4ExpectedQ, zhuVir5ExpectedQ,
    zhuVir6ExpectedQ, zhuVir42ExpectedQ, zhuVir33ExpectedQ,
    zhuVir222ExpectedQ, zhuVir7ExpectedQ, zhuVir52ExpectedQ,
    zhuVir43ExpectedQ, zhuVir322ExpectedQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    Function.comp_apply]))

theorem reifyZhuVir2SparseQ_eq_expected :
    reifyVirWordSparseQ [2] = zhuVir2ExpectedQ := by
  close_zhu_vir_state

set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir4SparseQ_eq_expected :
    reifyVirWordSparseQ [4] = zhuVir4ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir5SparseQ_eq_expected :
    reifyVirWordSparseQ [5] = zhuVir5ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir6SparseQ_eq_expected :
    reifyVirWordSparseQ [6] = zhuVir6ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir42SparseQ_eq_expected :
    reifyVirWordSparseQ [4, 2] = zhuVir42ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir33SparseQ_eq_expected :
    reifyVirWordSparseQ [3, 3] = zhuVir33ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir222SparseQ_eq_expected :
    reifyVirWordSparseQ [2, 2, 2] = zhuVir222ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir7SparseQ_eq_expected :
    reifyVirWordSparseQ [7] = zhuVir7ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir52SparseQ_eq_expected :
    reifyVirWordSparseQ [5, 2] = zhuVir52ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir43SparseQ_eq_expected :
    reifyVirWordSparseQ [4, 3] = zhuVir43ExpectedQ := by
  close_zhu_vir_state
set_option maxHeartbeats 1000000 in
-- A reusable exact right-state coordinate for the Zhu ledger.
theorem reifyZhuVir322SparseQ_eq_expected :
    reifyVirWordSparseQ [3, 2, 2] = zhuVir322ExpectedQ := by
  close_zhu_vir_state

end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.reifyZhuVir322SparseQ_eq_expected
end AxiomAudit
