/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GrowthClosure
import VOA.Modularity.OnePointGrowth

/-!
# Closure properties of `Subexponential`

`Modularity.ConvergenceBridge` supplies `Subexponential.of_le`, `subexponential_const`,
`Subexponential.const_mul`; `Modularity.GrowthClosure` adds `mul_pow`.  The peeling argument of
residual **(d)** needs three more, all elementary and all missing: closure under **addition**, under
**finite sums**, and under an **index shift** in both directions.

The shift matters because members of one `T`-eigenvalue fibre have conformal weights differing by
integers, so their coefficient sequences are compared only after rebasing (`qEvalAt_shift`).

## Main results

* `Subexponential.finsetSum` (⚠ `Subexponential.add` already exists: `Modularity/OnePointGrowth.lean:37`);
* `Subexponential.shift`, `Subexponential.of_shift`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

/-- Subexponential sequences are closed under finite sums. -/
theorem Subexponential.finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Subexponential (f i)) :
    Subexponential (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using subexponential_const 0
  | insert i s hi ih =>
      have hfi : Subexponential (f i) := hf i (Finset.mem_insert_self i s)
      have hrest : Subexponential (fun n => ∑ j ∈ s, f j n) :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have := Subexponential.add hfi hrest
      refine Subexponential.of_le (fun n => le_of_eq ?_) this
      rw [Finset.sum_insert hi]

/-- Shifting the index forward preserves subexponential growth. -/
theorem Subexponential.shift {a : ℕ → ℝ} (ha : Subexponential a) (k : ℕ) :
    Subexponential (fun n => a (n + k)) := by
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  obtain ⟨C, hC⟩ := ha r hr
  refine ⟨C * r ^ k, fun n => ?_⟩
  calc a (n + k) ≤ C * r ^ (n + k) := hC (n + k)
    _ = C * r ^ k * r ^ n := by rw [pow_add]; ring

/-- Shifting the index backward preserves subexponential growth: the finitely many initial values
are absorbed into the constant. -/
theorem Subexponential.of_shift {a : ℕ → ℝ} (k : ℕ)
    (ha : Subexponential (fun n => a (n + k))) : Subexponential a := by
  classical
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  obtain ⟨C₀, hC₀⟩ := ha r hr
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ n : ℕ, a (n + k) ≤ C * r ^ n := fun n =>
    le_trans (hC₀ n) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨B, hB⟩ := Finset.exists_le ((Finset.range k).image (fun n => a n / r ^ n))
  refine ⟨max C B, fun n => ?_⟩
  by_cases hn : n < k
  · have hmem : a n / r ^ n ∈ (Finset.range k).image (fun n => a n / r ^ n) :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)
    have hle : a n / r ^ n ≤ max C B := le_trans (hB _ hmem) (le_max_right _ _)
    rwa [div_le_iff₀ (by positivity : (0:ℝ) < r ^ n)] at hle
  · push_neg at hn
    have hk : n - k + k = n := Nat.sub_add_cancel hn
    have h1 : a n ≤ C * r ^ (n - k) := by
      have h := hC (n - k)
      rwa [hk] at h
    have hmono : r ^ (n - k) ≤ r ^ n :=
      pow_le_pow_right₀ (le_of_lt hr) (Nat.sub_le n k)
    calc a n ≤ C * r ^ (n - k) := h1
      _ ≤ C * r ^ n := mul_le_mul_of_nonneg_left hmono hC0
      _ ≤ max C B * r ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end VOA
