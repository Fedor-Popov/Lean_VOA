/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSound
import VOA.DeligneAudit.D4FusionRealizationTwoMatrixBridge

/-! Exact flattening of tensor columns. The right-column support bound is
essential: it prevents a row coordinate from carrying into the other site. -/
namespace VOA.DeligneAudit.D4Two.Certificate

theorem coeff_map_left (v : SV) (j i' j' : ℕ) (hj : j < 29) (hj' : j' < 29) :
    coeff (v.map fun p => (p.1 * 29 + j, p.2)) (i' * 29 + j') =
      if j = j' then coeff v i' else 0 := by
  induction v with
  | nil => simp
  | cons p v ih =>
      simp only [List.map_cons, coeff_cons, ih]
      have he : p.1 * 29 + j = i' * 29 + j' ↔ p.1 = i' ∧ j = j' := by omega
      by_cases h : j = j'
      · simp [h]
      · simp [he, h]

theorem coeff_map_right (v : SV) (i i' j' : ℕ) (hj' : j' < 29)
    (hv : ∀ p ∈ v, p.1 < 29) :
    coeff (v.map fun p => (i * 29 + p.1, p.2)) (i' * 29 + j') =
      if i = i' then coeff v j' else 0 := by
  induction v with
  | nil => simp
  | cons p v ih =>
      have hp := hv p List.mem_cons_self
      have hr : ∀ q ∈ v, q.1 < 29 := fun q hq => hv q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, coeff_cons, ih hr]
      have he : i * 29 + p.1 = i' * 29 + j' ↔ i = i' ∧ p.1 = j' := by omega
      by_cases h : i = i'
      · simp [h]
      · simp [he, h]

/-- The full two-site current column, at every mode, decomposes into its
two actual adjoint columns and the two evaluation-to-line columns. -/
theorem coeff_pairColumn (c k i j i' j' : ℕ) (hc : c < 28)
    (_hi : i < 29) (hj : j < 29) (hi' : i' < 29) (hj' : j' < 29) :
    coeff (pairColumn 28 (rawColumn c) c k (i * 29 + j)) (i' * 29 + j') =
      (if k = 0 then if j = j' then coeff (rawColumn c i) i' else 0
       else if k = 1 ∧ i = c then if i' = 28 ∧ j' = j then 1 else 0 else 0) +
      (if i = i' then coeff (rawColumn c j) j' else 0) +
      (if j = c then if i' = i ∧ j' = 28 then (k : ℤ) else 0 else 0) := by
  have hidiv : (i * 29 + j) / 29 = i := by omega
  have hjmod : (i * 29 + j) % 29 = j := by omega
  have hr : ∀ p ∈ rawColumn c j, p.1 < 29 := by
    simpa only [rangeCheck, List.all_eq_true, decide_eq_true_eq] using
      rawColumn_range c j hc hj
  have hleft : 28 * 29 + j = i' * 29 + j' ↔ i' = 28 ∧ j' = j := by omega
  have hright : i * 29 + 28 = i' * 29 + j' ↔ i' = i ∧ j' = 28 := by omega
  have hL :
      coeff (if k = 0 then (rawColumn c i).map fun p => (p.1 * 29 + j, p.2)
        else if k = 1 ∧ i = c then [(28 * 29 + j, 1)] else []) (i' * 29 + j') =
        if k = 0 then if j = j' then coeff (rawColumn c i) i' else 0
        else if k = 1 ∧ i = c then if i' = 28 ∧ j' = j then 1 else 0 else 0 := by
    by_cases hk0 : k = 0
    · simpa only [if_pos hk0] using coeff_map_left (rawColumn c i) j i' j' hj hj'
    · simp only [if_neg hk0]
      by_cases hk1 : k = 1 ∧ i = c
      · simp only [if_pos hk1, coeff_cons, coeff_nil, add_zero, hleft]
      · simp only [if_neg hk1, coeff_nil]
  have hT :
      coeff (if j = c then [(i * 29 + 28, (k : ℤ))] else []) (i' * 29 + j') =
        if j = c then if i' = i ∧ j' = 28 then (k : ℤ) else 0 else 0 := by
    by_cases hjc : j = c
    · simp only [if_pos hjc, coeff_cons, coeff_nil, add_zero, hright]
    · simp only [if_neg hjc, coeff_nil]
  simp only [pairColumn, hidiv, hjmod, coeff_append]
  rw [hL, coeff_map_right _ i i' j' hj' hr, hT]

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.coeff_pairColumn
