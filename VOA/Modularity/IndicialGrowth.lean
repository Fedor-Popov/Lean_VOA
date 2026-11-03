/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.IndicialRecursion

/-!
# The indicial divisor grows — step (2), and it is free

`Modularity.Majorant` records that mere nonvanishing of the indicial polynomial does **not** make
the majorant induction close: the contraction factor would be `D(σ)·θ/c` with `D(σ)` blowing up as
`σ → 1⁺`.  What makes one constant serve every `r > 1` is that `|P(λ+n)| → ∞`, and *that* is free,
because `P` is **monic**: the indicial polynomial of a monic linear equation of order `s` is
`P(x) = x^s + ∑_{i<s} g_{i,0} x^i`.

This file proves it, in exactly the normalisation `Modularity.IndicialRecursion` needs:

  `indicialDivisor λ s g n = ‖P(λ+n)‖ / (max ‖λ‖ 1 + n)^{s−1} → ∞`.

The estimate is elementary.  With `u = ‖λ+n‖` and `C = ∑_{i<s} ‖g_{i,0}‖`, monicity gives
`‖P(λ+n)‖ ≥ u^{s−1}(u − C)` once `u ≥ 1`; and for `n ≥ 2B + 2C + 2` one has `u/(B+n) ≥ 1/4` and
`u ≥ n/2`, whence `indicialDivisor ≥ (1/4)^{s−1}(n/2 − C) → ∞`.

## Main result

* `tendsto_indicialDivisor_atTop`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open Filter

/-- **The indicial divisor tends to infinity**, because the indicial polynomial is monic. -/
theorem tendsto_indicialDivisor_atTop (lam : ℂ) {s : ℕ} (hs : 1 ≤ s) (g : ℕ → ℕ → ℂ) :
    Tendsto (indicialDivisor lam s g) atTop atTop := by
  classical
  set B : ℝ := max ‖lam‖ 1 with hB
  set C : ℝ := ∑ i ∈ Finset.range s, ‖g i 0‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hBlam : ‖lam‖ ≤ B := le_max_left _ _
  have hs1 : s - 1 + 1 = s := by omega
  -- the eventual lower bound
  have hkey : ∀ n : ℕ, 2 * B + 4 * C + 4 ≤ (n : ℝ) →
      ((1 : ℝ) / 4) ^ (s - 1) * ((n : ℝ) / 4) ≤ indicialDivisor lam s g n := by
    intro n hn
    have hBn2 : B ≤ (n : ℝ) / 2 := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    set u : ℝ := ‖lam + (n : ℂ)‖ with hu
    have hu_lb : (n : ℝ) - B ≤ u := by
      have hcast : ‖((n : ℕ) : ℂ)‖ = (n : ℝ) := by simp
      have htri : ‖((n : ℕ) : ℂ)‖ ≤ ‖lam + (n : ℂ)‖ + ‖lam‖ := by
        calc ‖((n : ℕ) : ℂ)‖ = ‖(lam + (n : ℂ)) - lam‖ := by ring_nf
          _ ≤ ‖lam + (n : ℂ)‖ + ‖lam‖ := norm_sub_le _ _
      rw [hcast] at htri
      linarith
    have hu_half : (n : ℝ) / 2 ≤ u := by linarith
    have hu1 : (1 : ℝ) ≤ u := by linarith
    have hu_ub : u ≤ B + (n : ℝ) := by
      refine le_trans (norm_add_le _ _) ?_
      have hcast : ‖((n : ℕ) : ℂ)‖ = (n : ℝ) := by simp
      rw [hcast]; linarith
    have hBnpos : (0 : ℝ) < B + (n : ℝ) := by linarith
    -- monicity gives the lower bound on `‖P‖`
    have hPlb : u ^ (s - 1) * (u - C) ≤ ‖indicialP lam s g n‖ := by
      have htail : ‖∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i‖ ≤ C * u ^ (s - 1) := by
        refine le_trans (norm_sum_le _ _) ?_
        rw [hC, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        have his : i ≤ s - 1 := by have := Finset.mem_range.mp hi; omega
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu1 his) (norm_nonneg _)
      have hmain : ‖(lam + (n : ℂ)) ^ s‖ - ‖∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i‖
          ≤ ‖indicialP lam s g n‖ := by
        have hsub := norm_sub_le (indicialP lam s g n)
          (∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i)
        have heq : indicialP lam s g n - ∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i
            = (lam + (n : ℂ)) ^ s := by rw [indicialP, add_sub_cancel_right]
        rw [heq] at hsub
        linarith
      have hlead : ‖(lam + (n : ℂ)) ^ s‖ = u ^ (s - 1) * u := by
        rw [← pow_succ, hs1, hu, norm_pow]
      rw [hlead] at hmain
      calc u ^ (s - 1) * (u - C) = u ^ (s - 1) * u - C * u ^ (s - 1) := by ring
        _ ≤ u ^ (s - 1) * u - ‖∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i‖ := by linarith
        _ ≤ ‖indicialP lam s g n‖ := hmain
    -- the ratio bound
    have hratio : (1 : ℝ) / 4 ≤ u / (B + (n : ℝ)) := by
      rw [le_div_iff₀ hBnpos]
      linarith
    have hpowratio : ((1 : ℝ) / 4) ^ (s - 1) ≤ (u / (B + (n : ℝ))) ^ (s - 1) :=
      pow_le_pow_left₀ (by norm_num) hratio _
    -- assemble
    have hdiv : u ^ (s - 1) * (u - C) / (B + (n : ℝ)) ^ (s - 1)
        = (u / (B + (n : ℝ))) ^ (s - 1) * (u - C) := by
      rw [div_pow]; ring
    have hstep : ((1 : ℝ) / 4) ^ (s - 1) * ((n : ℝ) / 4)
        ≤ (u / (B + (n : ℝ))) ^ (s - 1) * (u - C) := by
      refine mul_le_mul hpowratio (by linarith) (by linarith) ?_
      positivity
    rw [indicialDivisor, ← hB]
    refine le_trans hstep (le_trans (le_of_eq hdiv.symm) ?_)
    gcongr
  -- conclude
  have hlim : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ (s - 1) * ((n : ℝ) / 4)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (Filter.Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 * B + 4 * C + 4))] with n hn
  refine hkey n ?_
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)

end VOA
