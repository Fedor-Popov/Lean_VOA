/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuRecursion
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The formal Eisenstein series for Zhu's recursion  (TASK B1)

The Eisenstein family `G_{2k}` entering Zhu's recursion, as **formal `q`-expansion coefficients** —
no analysis, no convergence, no `ℍ`.

## What Mathlib gives vs what is defined here

Mathlib **proves** the `q`-expansion coefficients of the *normalised* Eisenstein series `E k`
(`EisensteinSeries.E_qExpansion_coeff`, `NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean`,
for `3 ≤ k` and `Even k`):

  `(qExpansion 1 (E hk)).coeff m = if m = 0 then 1 else -(2k / B_k) · σ_{k−1}(m)`

That statement is *analytic* — `E hk` is a modular form on `ℍ` and `qExpansion` its `q`-expansion.  A
formal `q`-series, by contrast, **is** its coefficient function, so here `eisensteinCoeff` is defined
by exactly that formula, built only from `bernoulli` and `ArithmeticFunction.sigma` (light
number-theory imports; the heavy `EisensteinSeries`/modular-forms stack is deliberately **not**
imported).  Consequently:

* **Defined here:** `eisensteinCoeff k` (`ℕ → ℂ`), `zhuEisenstein j = eisensteinCoeff (2j)`, and their
  basic values.
* **Available from Mathlib, not imported here:** the theorem that these coefficients *are* the
  `q`-expansion of the analytic `E k`.  The analytic link is made elsewhere for the pinned family
  `zhuG` (`Modularity/QExpansionBridge.lean`: `coeff_qExpansion_E`, `qExpansion_zhuGC`).

⚠ **Normalisation.**  This is `E_k` (constant term `1`), matching Mathlib.  It is the
**wrong** normalisation for Zhu's recursion.  The recursion proved in the library is
`zhuRecursionPinned_holds` (`Modularity/ZhuRecursionClose.lean`), at the pinned family `zhuG`
(`Modularity/ZhuNormalization.lean`), whose constant terms are not `1`.  So
`ZhuRecursionEisenstein` below (the recursion at `zhuEisenstein = E_{2j}`) is expected to be
**false**; it has no consumers and is kept only as a record.

## Status
The formal Eisenstein layer is built, axiom-clean and `pbw`-free.  This is the repo's first
`Mathlib.NumberTheory.*` import, isolated in this leaf file.

## References
* Zhu, J. AMS 9 (1996), §4; Gannon §5.3.5; Mathlib
  `NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean`.
-/

namespace VOA

open scoped BigOperators

/-- **The formal `q`-expansion coefficients of the normalised Eisenstein series `E_k`**:
`E_k = 1 − (2k/B_k)·Σ_{m≥1} σ_{k−1}(m)·qᵐ`.  Identical to the formula Mathlib proves for the analytic
`E k` (`EisensteinSeries.E_qExpansion_coeff`, `3 ≤ k`, `Even k`) — see the module docstring. -/
noncomputable def eisensteinCoeff (k : ℕ) (m : ℕ) : ℂ :=
  if m = 0 then 1
  else -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ))
        * ((ArithmeticFunction.sigma (k - 1) m : ℕ) : ℂ)

@[simp] theorem eisensteinCoeff_zero (k : ℕ) : eisensteinCoeff k 0 = 1 := by
  rw [eisensteinCoeff, if_pos rfl]

theorem eisensteinCoeff_of_ne_zero (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    eisensteinCoeff k m
      = -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ))
          * ((ArithmeticFunction.sigma (k - 1) m : ℕ) : ℂ) := by
  rw [eisensteinCoeff, if_neg hm]

/-- **The Eisenstein family indexed as Zhu indexes it**: `zhuEisenstein j` is the weight-`2j` series
`E_{2j}`, i.e. the `G_{2k}` slot of `ZhuRecursionAt` with `k = j`. -/
noncomputable def zhuEisenstein (j : ℕ) : ℕ → ℂ := eisensteinCoeff (2 * j)

@[simp] theorem zhuEisenstein_zero (j : ℕ) : zhuEisenstein j 0 = 1 :=
  eisensteinCoeff_zero (2 * j)

/-- The convolution of a `q`-series against `E_{2j}` picks up the series itself in degree `0` — the
`n = 0` term of `qConv`, isolated (`E_{2j}` has constant term `1`). -/
theorem qConv_zhuEisenstein_zero_term (j : ℕ) (g : FormalQSeries) (e : ℂ) :
    zhuEisenstein j 0 * g (e - (0 : ℕ)) = g e := by
  rw [zhuEisenstein_zero, one_mul, Nat.cast_zero, sub_zero]

/-! ## Zhu's recursion with the concrete Eisenstein family -/

section
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `ZhuRecursionAt` instantiated at `zhuEisenstein` (the `E_{2j}` normalisation).  ⚠ This is the
**wrong normalisation**: the true recursion is `ZhuRecursionPinned` (at `zhuG`), proved as
`zhuRecursionPinned_holds`.  This `Prop` is not proved, is expected to be false, and has no
consumers. -/
def ZhuRecursionEisenstein (N : OrdVModule W M) (a v : 𝒱) (ka : ℕ) : Prop :=
  ZhuRecursionAt N zhuEisenstein a v ka

end

/-! ## Status of the former residuals

* **The recursion** — proved at the pinned normalisation `zhuG`: `zhuRecursionPinned_holds`
  (`Modularity/ZhuRecursionClose.lean`).  `ZhuRecursionEisenstein` is not the right statement.
* **The analytic link** — made for `zhuG` in `Modularity/QExpansionBridge.lean`
  (`coeff_qExpansion_E`, `qExpansion_zhuGC`).
-/

end VOA
