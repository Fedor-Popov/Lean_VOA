/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointDescent

/-!
# Closure of subexponential growth under polynomial factors

`Modularity.OnePointDescent` reduces the growth datum `OnePointSubexp` to the `g` `C₂`-generator
sequences.  The intended route to those is the trace bound

  `|tr_{M_{h+n}} o(v)| ≤ C·n^p·dim M_{h+n}`   (Zhu §4 / DLM, via Buhl's ordered spanning set),

consumed against `SubexponentialCoeffs`.  This file supplies the *consumption* step — a polynomial
factor does not spoil subexponential growth — leaving the trace bound itself as the single
remaining mathematical input on the `𝒱` side.

## Main results

* `Subexponential.mul_pow` — `n ↦ nᵖ·aₙ` is subexponential when `a` is;
* `subexponential_of_le_pow_mul` — the packaged consumption step.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

/-- **A polynomial factor preserves subexponential growth.**  Split `r = √r·√r` and apply
`subexponential_pow` and the hypothesis at `√r`. -/
theorem Subexponential.mul_pow {a : ℕ → ℝ} (ha : Subexponential a) (hnn : ∀ n, 0 ≤ a n) (p : ℕ) :
    Subexponential (fun n : ℕ => (n : ℝ) ^ p * a n) := by
  intro r hr
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hs1 : 1 < Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hr
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
  obtain ⟨C₁, hC₁⟩ := subexponential_pow p (Real.sqrt r) hs1
  obtain ⟨C₂, hC₂⟩ := ha (Real.sqrt r) hs1
  refine ⟨C₁ * C₂, fun n => ?_⟩
  have h1 : (n : ℝ) ^ p ≤ C₁ * Real.sqrt r ^ n := hC₁ n
  have h3 : (0 : ℝ) ≤ C₁ * Real.sqrt r ^ n := le_trans (by positivity) h1
  have hpow : Real.sqrt r ^ n * Real.sqrt r ^ n = r ^ n := by
    rw [← _root_.mul_pow, hss]
  calc (n : ℝ) ^ p * a n
      ≤ (C₁ * Real.sqrt r ^ n) * (C₂ * Real.sqrt r ^ n) := mul_le_mul h1 (hC₂ n) (hnn n) h3
    _ = C₁ * C₂ * (Real.sqrt r ^ n * Real.sqrt r ^ n) := by ring
    _ = C₁ * C₂ * r ^ n := by rw [hpow]

/-- The packaged consumption step: a sequence dominated by `C·nᵖ·(subexponential)` is itself
subexponential.  This is the shape the missing trace bound
`|tr_{M_{h+n}} o(v)| ≤ C·nᵖ·dim M_{h+n}` would be consumed in. -/
theorem subexponential_of_le_pow_mul {b a : ℕ → ℝ} (ha : Subexponential a) (hnn : ∀ n, 0 ≤ a n)
    {C : ℝ} (hC : 0 ≤ C) (p : ℕ) (hb : ∀ n, b n ≤ C * ((n : ℝ) ^ p * a n)) :
    Subexponential b :=
  Subexponential.of_le hb ((ha.mul_pow hnn p).const_mul hC)

end VOA
