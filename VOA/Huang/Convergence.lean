/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.MatrixCoeff
import VOA.Huang.FuchsianODE
import VOA.Huang.FusionC2

/-!
# Convergence of products and iterates of intertwining operators (conditional)

Huang's convergence theorem (CCM 7 (2005), Thm 3.5, first part) uses exactly two inputs:
(i) the matrix coefficients satisfy linear ODEs whose relevant singular point is **regular**
(Thms 1.4, 2.3), and (ii) a formal power-series solution at a regular singular point converges.
This file proves (ii) ⟹ convergence, so that only (i) remains, as a named, TRUE input.

## The one-variable form of Huang's equations

By `Huang/MatrixCoeff.lean`, on one coset the product is
`z₁^{−σ+ν₀−1} z₂^{−ν₀−1} · G(z₂/z₁)`, `G = prodSeries … σ ν₀ ∈ ℂ⟦x⟧`, and the iterate is
`z₀^{−ν₀−1} z₂^{−σ+ν₀−1} · G'(z₀/z₂)`, `G' = iterSeries … σ ν₀`.  Huang's Theorem 2.3 (for the
prescribed singular point `z₂ = 0`, resp. `z₂⁻¹(z₁ − z₂) = 0`) gives an equation in `z₂`, resp.
`z₁`, with coefficients in `ℂ[z₁^{±1}, z₂^{±1}, (z₁−z₂)^{−1}]`, regular at that point; his
degree-0 argument (proof of Thm 2.3: assign `z₁, z₂` degree `−1`; the classes
`[w₀ ⊗ L(−1)^l w₁ ⊗ w₂ ⊗ w₃]` are homogeneous, so the coefficients may be taken of degree 0)
turns it into a one-variable equation in `x = z₂/z₁`, resp. `x = (z₁−z₂)/z₂`.  The remaining
singular points are `x = 1` (`z₁ = z₂`), resp. `x = −1` (`z₁ = 0`), and `∞`.  Multiplying the
`m`-th order equation by `x^m` and using `x^k ∂^k = θ(θ−1)⋯(θ−k+1)` and
`θ(x^λ G) = x^λ θ_λ G` gives:

* `RatFuchsian a lam G`: `G` satisfies a monic `θ_λ`-equation (`FuchsianEq`) whose coefficients
  `cᵢ` satisfy `(1 − a x)^b cᵢ ∈ ℂ[x]` — poles only at `x = 1/a`.

* `HuangProductODE W`: for irreducible `P₁, P₂, P₃, P₄`, an arbitrary intermediate module `M₅`,
  FHL intertwiners `𝒴₁ : (P₄ / P₁ M₅)`, `𝒴₂ : (M₅ / P₂ P₃)`, homogeneous `wᵢ`, `f` supported at
  `h₄` and a base `ν₀`, the product series satisfies `RatFuchsian 1 (−ν₀−1)`.
* `HuangIterateODE W`: the same for iterates, `RatFuchsian (−1) (−ν₀−1)`.
* `HuangODEInput`: both hold for every strongly rational `V`.

**These are TRUE** for strongly rational `V`: Huang 2005, Thms 1.4 and 2.3 (with the degree-0
selection of his proof of 2.3), whose hypotheses hold because irreducible modules of a strongly
rational `V` (and their contragredients) are `C₂`-, hence `C₁`-cofinite (Abe–Buhl–Dong 2004; `C₂(W)
⊆ C₁(W)` as `u₋₂w = (L₋₁u)₋₁w`), and have rational conformal weights (Dong–Li–Mason 2000), so they
are discretely `ℝ`-graded; the intermediate module enters Huang's argument only through the Jacobi
identity of the intertwiners.  The `z₂ = 0` case of Thm 2.3 is among "the other cases are similar".

## Main results (proved)

* `subexponential_of_ratFuchsian`, `summable_of_ratFuchsian` — formal solutions of such
  equations converge on the unit disc (from `Huang/FuchsianODE.lean`).
* `summable_prodTerm_of_huangProductODE` — **absolute convergence of the product on each
  coset for `|z₁| > |z₂| > 0`**, conditional on `HuangProductODE`.
* `summable_iterTerm_of_huangIterateODE` — **absolute convergence of the iterate on each
  coset for `|z₂| > |z₀| > 0`** (`z₀ = z₁ − z₂`), conditional on `HuangIterateODE`.
* `summable_twoVar` — the general estimate behind both.

Powers `z^s` are Mathlib's principal-branch `Complex.cpow`; on a coset, all exponents differ by
integers, so the branch choice only multiplies the whole coset by a common nonzero constant.

## Status
No `sorry`, no new axioms.  Conditional on the named inputs above (V3b, open).
-/

namespace VOA.Huang.Convergence

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FuchsianODE PowerSeries
open scoped BigOperators

universe u

/-! ## Rational Fuchsian equations and their solutions -/

/-- `G` satisfies a monic `θ_λ`-equation whose coefficients have poles only at `x = 1/a`:
`(1 − a x)^b cᵢ` is a polynomial for each `i < s`. -/
def RatFuchsian (a lam : ℂ) (G : PowerSeries ℂ) : Prop :=
  ∃ (s b : ℕ) (c : ℕ → PowerSeries ℂ) (p : ℕ → Polynomial ℂ),
    (∀ i < s, (1 - PowerSeries.C a * X) ^ b * c i = (p i : PowerSeries ℂ)) ∧
      FuchsianEq lam s c G

/-- Solutions of a rational Fuchsian equation with `‖a‖ ≤ 1` have subexponential
coefficients. -/
theorem subexponential_of_ratFuchsian {a lam : ℂ} (ha : ‖a‖ ≤ 1) {G : PowerSeries ℂ}
    (h : RatFuchsian a lam G) : Subexponential fun n => ‖coeff n G‖ := by
  obtain ⟨s, b, c, p, hc, hG⟩ := h
  exact subexponential_of_fuchsianEq (fun i hi => mem_subexpPS_of_mul_eq' ha (hc i hi)) hG

/-- ... hence converge absolutely on the open unit disc. -/
theorem summable_of_ratFuchsian {a lam : ℂ} (ha : ‖a‖ ≤ 1) {G : PowerSeries ℂ}
    (h : RatFuchsian a lam G) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => ‖coeff n G * x ^ n‖ := by
  obtain ⟨s, b, c, p, hc, hG⟩ := h
  exact summable_of_fuchsianEq (fun i hi => mem_subexpPS_of_mul_eq' ha (hc i hi)) hG hx

/-- The general two-variable estimate: if `‖coeff k G‖` is subexponential and `0 < ‖v‖ < ‖u‖`,
then `Σ_k coeff_k(G) · u^{A−k} v^{B+k}` converges absolutely (principal-branch powers). -/
theorem summable_twoVar {G : PowerSeries ℂ} (hG : Subexponential fun n => ‖coeff n G‖)
    {u v : ℂ} (hv : v ≠ 0) (hvu : ‖v‖ < ‖u‖) (A B : ℂ) :
    Summable fun k : ℕ => ‖coeff k G * u ^ (A - k) * v ^ (B + k)‖ := by
  have hu : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hvu; exact absurd hvu (not_lt.mpr (norm_nonneg v))
  have hx : ‖v / u‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hu)]; exact hvu
  have hs := summable_of_subexponential (fun n => norm_nonneg _) hG (norm_nonneg _) hx
  refine (hs.mul_left (‖u ^ A‖ * ‖v ^ B‖)).congr fun k => ?_
  have e1 : u ^ (A - (k : ℂ)) = u ^ A / u ^ k := by
    rw [Complex.cpow_sub _ _ hu, Complex.cpow_natCast]
  have e2 : v ^ (B + (k : ℂ)) = v ^ B * v ^ k := by
    rw [Complex.cpow_add _ _ hv, Complex.cpow_natCast]
  rw [e1, e2]
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  simp only [norm_mul, norm_div, norm_pow]
  rw [div_pow]
  field_simp

/-! ## The named inputs (Huang's equations, one-variable form) -/

section Inputs

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Huang's equation for products, one-variable form** (V3b, TRUE for strongly rational `V`:
Huang 2005, Thms 1.4, 2.3 at `z₂ = 0`; see the module docstring). -/
def HuangProductODE (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → P₃.IsIrreducibleLW →
    P₄.IsIrreducibleLW →
  ∀ {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₁ : IntertwiningModes P₁.carrier M₅ P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier M₅},
    IsIntertwiningOperator P₁.isMod A₅ P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod A₅ Y₂ →
  ∀ {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ},
    w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
    SupportedAt P₄.isMod f h₄ →
  ∀ {ν₀ : ℂ}, IsBase Y₂ w₂ w₃ ν₀ →
    RatFuchsian 1 (-ν₀ - 1) (prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) ν₀)

/-- **Huang's equation for iterates, one-variable form** (V3b, TRUE for strongly rational `V`:
Huang 2005, Thms 1.4, 2.3 at `z₂⁻¹(z₁ − z₂) = 0`, the case proved in detail there). -/
def HuangIterateODE (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → P₃.IsIrreducibleLW →
    P₄.IsIrreducibleLW →
  ∀ {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₃ : IntertwiningModes M₅ P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier M₅},
    IsIntertwiningOperator A₅ P₃.isMod P₄.isMod Y₃ →
    IsIntertwiningOperator P₁.isMod P₂.isMod A₅ Y₄ →
  ∀ {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ},
    w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
    SupportedAt P₄.isMod f h₄ →
  ∀ {ν₀ : ℂ}, IsBase Y₄ w₁ w₂ ν₀ →
    RatFuchsian (-1) (-ν₀ - 1) (iterSeries Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) ν₀)

end Inputs

/-- **The V3b input**: Huang's one-variable equations for products and iterates, for every
strongly rational `V`.  TRUE (Huang 2005 + Abe–Buhl–Dong + Dong–Li–Mason; module docstring). -/
def HuangODEInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → HuangProductODE W ∧ HuangIterateODE W

/-! ## Convergence (V3d), conditional on the named inputs -/

section Convergence

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Products of intertwining operators converge** (on each coset, absolutely, in
`|z₁| > |z₂| > 0`), conditional on `HuangProductODE`.  The summand is the
`z₁^{−n₁−1} z₂^{−n₂−1}`-term of `⟨f, 𝒴₁(w₁, z₁)𝒴₂(w₂, z₂)w₃⟩` at
`(n₁, n₂) = (σ − ν₀ + k, ν₀ − k)`; by `prodCoeff_eq_coeff` these are all the nonzero terms of the
coset `n₂ ∈ ν₀ + ℤ`. -/
theorem summable_prodTerm_of_huangProductODE (hH : HuangProductODE W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₁ : IntertwiningModes P₁.carrier M₅ P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier M₅}
    (hY₁ : IsIntertwiningOperator P₁.isMod A₅ P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod A₅ Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : IsBase Y₂ w₂ w₃ ν₀) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable fun k : ℕ =>
      ‖prodCoeff Y₁ Y₂ f w₁ w₂ w₃ ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) (ν₀ - k)
        * z₁ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₂ ^ (-(ν₀ - k) - 1)‖ := by
  set σ := α₁ + α₂ + α₃ - h₄ - 2
  have hR := hH P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ A₅ hY₁ hY₂ h₁ h₂ h₃ hf hb
  have hS := summable_twoVar (subexponential_of_ratFuchsian (by simp) hR) hz₂ hz
    (-(σ - ν₀) - 1) (-ν₀ - 1)
  refine hS.congr fun k => ?_
  rw [coeff_prodSeries]
  have e1 : -(σ - ν₀) - 1 - (k : ℂ) = -(σ - ν₀ + k) - 1 := by ring
  have e2 : -ν₀ - 1 + (k : ℂ) = -(ν₀ - k) - 1 := by ring
  rw [e1, e2]

/-- **Iterates of intertwining operators converge** (on each coset, absolutely, in
`|z₂| > |z₀| > 0`, `z₀ = z₁ − z₂`), conditional on `HuangIterateODE`.  The summand is the
`z₀^{−n₀−1} z₂^{−n₂−1}`-term of `⟨f, 𝒴₃(𝒴₄(w₁, z₀)w₂, z₂)w₃⟩` at
`(n₀, n₂) = (ν₀ − k, σ − ν₀ + k)` (all nonzero terms of the coset, `iterCoeff_eq_coeff`). -/
theorem summable_iterTerm_of_huangIterateODE (hH : HuangIterateODE W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₃ : IntertwiningModes M₅ P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier M₅}
    (hY₃ : IsIntertwiningOperator A₅ P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod A₅ Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : IsBase Y₄ w₁ w₂ ν₀) {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖) :
    Summable fun k : ℕ =>
      ‖iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k) ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k)
        * z₂ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₀ ^ (-(ν₀ - k) - 1)‖ := by
  set σ := α₁ + α₂ + α₃ - h₄ - 2
  have hR := hH P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ A₅ hY₃ hY₄ h₁ h₂ h₃ hf hb
  have hS := summable_twoVar (subexponential_of_ratFuchsian (by simp) hR) hz₀ hz
    (-(σ - ν₀) - 1) (-ν₀ - 1)
  refine hS.congr fun k => ?_
  rw [coeff_iterSeries]
  have e1 : -(σ - ν₀) - 1 - (k : ℂ) = -(σ - ν₀ + k) - 1 := by ring
  have e2 : -ν₀ - 1 + (k : ℂ) = -(ν₀ - k) - 1 := by ring
  rw [e1, e2]

/-- **V3d for strongly rational `V`**, conditional on `HuangODEInput` alone: products
converge absolutely on every coset in `|z₁| > |z₂| > 0`. -/
theorem summable_prodTerm (hIn : HuangODEInput.{u}) (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₁ : IntertwiningModes P₁.carrier M₅ P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier M₅}
    (hY₁ : IsIntertwiningOperator P₁.isMod A₅ P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod A₅ Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : IsBase Y₂ w₂ w₃ ν₀) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable fun k : ℕ =>
      ‖prodCoeff Y₁ Y₂ f w₁ w₂ w₃ ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) (ν₀ - k)
        * z₁ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₂ ^ (-(ν₀ - k) - 1)‖ :=
  summable_prodTerm_of_huangProductODE (hIn 𝒱 W hV).1 i₁ i₂ i₃ i₄ A₅ hY₁ hY₂ h₁ h₂ h₃ hf hb
    hz₂ hz

/-- **V3d for strongly rational `V`**, iterates, conditional on `HuangODEInput` alone. -/
theorem summable_iterTerm (hIn : HuangODEInput.{u}) (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₃ : IntertwiningModes M₅ P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier M₅}
    (hY₃ : IsIntertwiningOperator A₅ P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod A₅ Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : IsBase Y₄ w₁ w₂ ν₀) {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖) :
    Summable fun k : ℕ =>
      ‖iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k) ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k)
        * z₂ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₀ ^ (-(ν₀ - k) - 1)‖ :=
  summable_iterTerm_of_huangIterateODE (hIn 𝒱 W hV).2 i₁ i₂ i₃ i₄ A₅ hY₃ hY₄ h₁ h₂ h₃ hf hb
    hz₀ hz

end Convergence

end VOA.Huang.Convergence
