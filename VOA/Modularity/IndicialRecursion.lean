/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.Majorant
import VOA.Modularity.SubexpClosure

/-!
# From the indicial coefficient recursion to subexponential growth

Steps (2)–(3) of the route to residual **(c)**: the `q^{λ+n}`-coefficient of a monic linear
equation `(q d/dq)^s F + ∑_{i<s} g_i(q)·(q d/dq)^i F = 0` reads

  `P(λ+n)·χ n = −∑_{m<n} ∑_{i<s} g_{i,n−m}·(λ+m)^i·χ m`,   `P(x) = x^s + ∑_{i<s} g_{i,0} x^i`,

and this file turns that identity into the majorant hypothesis of
`Modularity.Majorant.subexponential_of_majorant_recursion` (★).

The one subtlety: the weight `(λ+m)^i` depends on `m`, so it is **not** part of a convolution
kernel.  It is absorbed by dividing through by `(B+n)^{s−1}` with `B = max ‖λ‖ 1`: for `m < n` and
`i < s` one has `‖λ+m‖^i ≤ (B+n)^{s−1}`, so the *whole* weight is dominated by the single
`n`-dependent factor, leaving the genuine convolution kernel `a k = ∑_{i<s} ‖g_{i,k}‖`.  The
divisor is then `p n = ‖P(λ+n)‖/(B+n)^{s−1}`, which grows like `n` because `P` is **monic** — that
growth is the separate lemma `tendsto_indicialDivisor_atTop` (`Modularity.IndicialGrowth`), and it is what
(★) requires (mere nonvanishing of `P` does **not** suffice; see `Majorant`'s warning).

## Main result

* `subexponential_of_indicial_recursion`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  The growth of `p` is a hypothesis here and is
discharged in `Modularity.IndicialGrowth`.
-/

namespace VOA

open scoped BigOperators
open Filter

/-- The indicial polynomial evaluated along `λ + n`. -/
noncomputable def indicialP (lam : ℂ) (s : ℕ) (g : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  (lam + (n : ℂ)) ^ s + ∑ i ∈ Finset.range s, g i 0 * (lam + (n : ℂ)) ^ i

/-- The convolution kernel of the recursion. -/
noncomputable def indicialKernel (s : ℕ) (g : ℕ → ℕ → ℂ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range s, ‖g i k‖

/-- The divisor of the recursion. -/
noncomputable def indicialDivisor (lam : ℂ) (s : ℕ) (g : ℕ → ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖indicialP lam s g n‖ / (max ‖lam‖ 1 + (n : ℝ)) ^ (s - 1)

theorem indicialKernel_nonneg (s : ℕ) (g : ℕ → ℕ → ℂ) (k : ℕ) :
    0 ≤ indicialKernel s g k :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem subexponential_indicialKernel (s : ℕ) (g : ℕ → ℕ → ℂ)
    (hg : ∀ i, Subexponential (fun k => ‖g i k‖)) :
    Subexponential (indicialKernel s g) :=
  Subexponential.finsetSum (Finset.range s) (fun i k => ‖g i k‖) (fun i _ => hg i)

/-- **The indicial recursion gives subexponential coefficients.** -/
theorem subexponential_of_indicial_recursion {χ : ℕ → ℂ} (lam : ℂ) {s : ℕ} (hs : 1 ≤ s)
    (g : ℕ → ℕ → ℂ) (hg : ∀ i, Subexponential (fun k => ‖g i k‖))
    (hp : Tendsto (indicialDivisor lam s g) atTop atTop)
    (hrec : ∀ n : ℕ, indicialP lam s g n * χ n
      = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          g i (n - m) * (lam + (m : ℂ)) ^ i * χ m) :
    Subexponential (fun n => ‖χ n‖) := by
  classical
  set B : ℝ := max ‖lam‖ 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hBlam : ‖lam‖ ≤ B := le_max_left _ _
  have hBn : ∀ n : ℕ, (1 : ℝ) ≤ B + (n : ℝ) := fun n => by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hBnpos : ∀ n : ℕ, (0 : ℝ) < (B + (n : ℝ)) ^ (s - 1) := fun n =>
    pow_pos (by linarith [hBn n]) _
  refine subexponential_of_majorant_recursion
    (χ := fun n => ‖χ n‖) (a := indicialKernel s g) (b := fun _ => (0 : ℝ))
    (p := indicialDivisor lam s g)
    (fun n => norm_nonneg _) (indicialKernel_nonneg s g) (fun _ => le_rfl)
    (subexponential_indicialKernel s g hg) (subexponential_const 0) hp 0 ?_
  intro n _
  rw [add_zero]
  -- bound the right-hand side of the recursion
  have hnorm : ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖ := by
    have h1 : ‖indicialP lam s g n‖ * ‖χ n‖
        = ‖∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            g i (n - m) * (lam + (m : ℂ)) ^ i * χ m‖ := by
      rw [← norm_mul, hrec n, norm_neg]
    rw [h1]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmn : m < n := Finset.mem_range.mp hm
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range s,
        ‖g i (n - m) * (lam + (m : ℂ)) ^ i * χ m‖
          ≤ (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by
      intro i hi
      have his : i ≤ s - 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hlm : ‖lam + (m : ℂ)‖ ≤ B + (n : ℝ) := by
        refine le_trans (norm_add_le _ _) ?_
        have : ‖(m : ℂ)‖ = (m : ℝ) := by simp
        rw [this]
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hmn
        linarith
      have hpow : ‖lam + (m : ℂ)‖ ^ i ≤ (B + (n : ℝ)) ^ (s - 1) := by
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hlm i) ?_
        exact pow_le_pow_right₀ (hBn n) his
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖g i (n - m)‖ * ‖lam + (m : ℂ)‖ ^ i * ‖χ m‖
          ≤ ‖g i (n - m)‖ * (B + (n : ℝ)) ^ (s - 1) * ‖χ m‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by ring
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [← Finset.mul_sum, indicialKernel, Finset.sum_mul]
  -- divide by the positive factor
  rw [indicialDivisor, div_mul_eq_mul_div, div_le_iff₀ (hBnpos n)]
  calc ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖ :=
        hnorm
    _ = (∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖) * (B + (n : ℝ)) ^ (s - 1) := by
        ring

end VOA
