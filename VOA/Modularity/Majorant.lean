/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GrowthClosure
import VOA.Modularity.ConvergenceBridge

/-!
# (★) The majorant theorem — subexponential growth from an indicial recursion

This is the single analytic input that residual **(c)** needs and that **Mathlib does not have** in
any form (`grep` for `regular singular`, `Frobenius`, `Fuchsian`, `indicial`, `majorant` over all of
Mathlib returns zero files; `Analysis/ODE/` is entirely real-variable).

Zhu §4.4 and DLM §6–7 obtain the convergence of `Z_M(v,q)` from the modular linear differential
equation via the Frobenius–Fuchs theory.  ⚠ But the repo does **not** need Frobenius–Fuchs: its
downstream consumer is `Subexponential`, so only the *coefficient-estimate half* is required, and
that half is elementary.  Writing the ODE's `q^n`-coefficient as

  `P(n)·χ n = −∑_{m<n} (…)·χ m + (inhomogeneity)`,

and using that the indicial polynomial `P` has finitely many roots — so `|P(n)| → ∞` — a geometric
majorant closes the induction.

⚠ **The growth of `P` is essential, not cosmetic.**  With only `|P n| ≥ c > 0` the induction does
*not* close: the contraction factor would be `D(σ)·θ/c`, and `D(σ)` blows up as `σ → 1⁺`, so no
single constant serves every `r > 1`.  It is precisely `|P n| → ∞` that lets one constant `K` work
for all `r`.  The hypothesis below is therefore `Tendsto p atTop atTop`.

⚠ The recursion is stated **inhomogeneously** (`b`), as DLM (6.19)/(6.20) require for non-primary
vectors.

## Main result

* `subexponential_of_majorant_recursion`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  This is (★).  It is connected to VOAs through
`subexponential_of_indicial_recursion` (`Modularity.IndicialRecursion`) and the formal-ODE theorem
`onePointSubexp_of_formalODE` (`Modularity.FormalODE`), and is also used in
`Modularity.SystemGrowth`.
-/

namespace VOA

open scoped BigOperators
open Filter

/-- The geometric tail bound `∑_{m<n} t^{n−m} ≤ t/(1−t)` for `0 ≤ t < 1`. -/
theorem sum_geom_shift_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    ∑ m ∈ Finset.range n, t ^ (n - m) ≤ t / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have hreflect : ∑ m ∈ Finset.range n, t ^ (n - m) = ∑ j ∈ Finset.range n, t ^ (j + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    have := Finset.mem_range.mp hj
    omega
  rw [hreflect]
  have hstep : ∑ j ∈ Finset.range n, t ^ (j + 1) = t * ∑ j ∈ Finset.range n, t ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
  rw [hstep, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ ht0.le
  have hne : t ≠ 1 := ne_of_lt ht1
  rw [geom_sum_eq hne]
  have hval : (t ^ n - 1) / (t - 1) = (1 - t ^ n) / (1 - t) := by
    rw [← neg_div_neg_eq]
    congr 1 <;> ring
  rw [hval, div_le_iff₀ h1t, inv_mul_cancel₀ (ne_of_gt h1t)]
  nlinarith [pow_nonneg ht0.le n]

/-- **(★) The majorant theorem.**  A nonnegative sequence obeying an indicial recursion with
subexponential kernel and inhomogeneity, divided by a divisor tending to infinity, is
subexponential. -/
theorem subexponential_of_majorant_recursion {χ a b p : ℕ → ℝ}
    (hχ0 : ∀ n, 0 ≤ χ n) (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : Subexponential a) (hb : Subexponential b)
    (hp : Tendsto p atTop atTop) (N₀ : ℕ)
    (hrec : ∀ n, N₀ ≤ n → p n * χ n ≤ (∑ m ∈ Finset.range n, a (n - m) * χ m) + b n) :
    Subexponential χ := by
  classical
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  obtain ⟨σ, hσ1, hσr⟩ : ∃ σ : ℝ, 1 < σ ∧ σ < r := ⟨(1 + r) / 2, by linarith, by linarith⟩
  have hσ0 : (0 : ℝ) < σ := lt_trans zero_lt_one hσ1
  obtain ⟨D, hD⟩ := ha σ hσ1
  obtain ⟨E, hE⟩ := hb r hr
  have hD0 : 0 ≤ D := le_trans (ha0 0) (by simpa using hD 0)
  have hE0 : 0 ≤ E := le_trans (hb0 0) (by simpa using hE 0)
  set t : ℝ := σ / r with htdef
  have ht0 : 0 < t := div_pos hσ0 hr0
  have ht1 : t < 1 := (div_lt_one hr0).mpr hσr
  set θ : ℝ := t / (1 - t) with hθdef
  have hθ0 : 0 ≤ θ := le_of_lt (div_pos ht0 (by linarith))
  -- a threshold past which the divisor dominates
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hp.eventually_ge_atTop (D * θ + 1))
  set N : ℕ := max N₀ N₁ with hNdef
  -- the constant
  obtain ⟨K, hKE, hKlow⟩ : ∃ K : ℝ, E ≤ K ∧ ∀ n < N, χ n ≤ K * r ^ n := by
    obtain ⟨B, hB⟩ := Finset.exists_le ((Finset.range N).image (fun n => χ n / r ^ n))
    refine ⟨max E B, le_max_left _ _, fun n hn => ?_⟩
    have hmem : χ n / r ^ n ∈ (Finset.range N).image (fun n => χ n / r ^ n) :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)
    have hle : χ n / r ^ n ≤ max E B := le_trans (hB _ hmem) (le_max_right _ _)
    rwa [div_le_iff₀ (by positivity : (0:ℝ) < r ^ n)] at hle
  refine ⟨K, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · exact hKlow n hn
    · push_neg at hn
      have hN₀n : N₀ ≤ n := le_trans (le_max_left _ _) hn
      have hN₁n : N₁ ≤ n := le_trans (le_max_right _ _) hn
      have hpn : D * θ + 1 ≤ p n := hN₁ n hN₁n
      have hpn0 : (0 : ℝ) < p n := by nlinarith
      have hK0 : 0 ≤ K := le_trans hE0 hKE
      have hsum : ∑ m ∈ Finset.range n, a (n - m) * χ m ≤ D * K * θ * r ^ n := by
        calc ∑ m ∈ Finset.range n, a (n - m) * χ m
            ≤ ∑ m ∈ Finset.range n, (D * σ ^ (n - m)) * (K * r ^ m) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmn : m < n := Finset.mem_range.mp hm
              exact mul_le_mul (hD (n - m)) (ih m hmn) (hχ0 m)
                (le_trans (ha0 (n - m)) (hD (n - m)))
          _ = D * K * r ^ n * ∑ m ∈ Finset.range n, t ^ (n - m) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun m hm => ?_
              have hmn : m ≤ n := le_of_lt (Finset.mem_range.mp hm)
              have hrpow : r ^ (n - m) * r ^ m = r ^ n := by
                rw [← pow_add, Nat.sub_add_cancel hmn]
              have hrne : (r : ℝ) ^ (n - m) ≠ 0 := by positivity
              rw [htdef, div_pow, ← hrpow]
              field_simp
          _ ≤ D * K * r ^ n * θ := by
              refine mul_le_mul_of_nonneg_left (sum_geom_shift_le ht0 ht1 n) ?_
              positivity
          _ = D * K * θ * r ^ n := by ring
      have hbn : b n ≤ K * r ^ n := le_trans (hE n) (by
        exact mul_le_mul_of_nonneg_right hKE (pow_nonneg hr0.le n))
      have hkey : p n * χ n ≤ (D * θ + 1) * K * r ^ n := by
        calc p n * χ n ≤ (∑ m ∈ Finset.range n, a (n - m) * χ m) + b n := hrec n hN₀n
          _ ≤ D * K * θ * r ^ n + K * r ^ n := add_le_add hsum hbn
          _ = (D * θ + 1) * K * r ^ n := by ring
      have hfin : p n * χ n ≤ p n * (K * r ^ n) := by
        refine le_trans hkey ?_
        have : (D * θ + 1) * (K * r ^ n) ≤ p n * (K * r ^ n) :=
          mul_le_mul_of_nonneg_right hpn (by positivity)
        linarith [this]
      exact le_of_mul_le_mul_left hfin hpn0

end VOA
