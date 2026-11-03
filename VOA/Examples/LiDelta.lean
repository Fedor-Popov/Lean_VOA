/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.Heisenberg

/-!
# Li's `Δ`-operator on the rank-one Fock space (substitution form)

Toward the **charged Fock modules** `F_λ` over the free boson (step B1), and thence the
first genuinely logarithmic module (step B2).

## Why a substitution

Li's operator (Li, *Local systems of twisted vertex operators*, 1997) is
`Δ(λ,z) = z^{λa₀} exp(-Σ_{n≥1} (λ/n)·aₙ·(-z)^{-n})`, and the twisted action
`Y_λ(u,z) := Y(Δ(λ,z)u, z)` makes the same space a new module.  On this Fock space the two
factors simplify decisively:

* `osc k 0 = 0` — the zero mode acts as **zero**, so `z^{λa₀} = id`.  (This is exactly why the
  repo's `Fock` is the charge-zero module and why `F_λ` needs the twist at all.)
* `osc k n = n·k·∂/∂X_{n-1}` for `n ≥ 1` — so the exponent is a **constant-coefficient
  derivation**, and `exp` of it is a *translation of the variables*:
  `X_i ↦ X_i + λk(-1)^i z^{-i-1}`.

So `Δ` needs no operator-exponential machinery and no local-nilpotency bookkeeping: it is an
algebra map defined by `MvPolynomial.aeval`.  Writing `w := z⁻¹` (only negative powers of `z`
occur), the target is `MvPolynomial ℕ (Polynomial ℂ)` — Fock coefficients that are polynomials
in `w`.

## What is here

* `deltaCoeff` — the substitution constants `λk(-1)^i w^{i+1}`;
* `deltaSub` — the `Δ`-operator as an `ℂ`-algebra map, and `deltaSub_X`;
* `deltaSub_zero` — at `λ = 0` it is the inclusion (the untwisted module is recovered);
* `deltaSub_vacuum` — the vacuum is fixed;
* `deltaSub_add` — the group law `Δ_λ ∘ Δ_μ = Δ_{λ+μ}`, the algebraic heart of
  "`F_λ` is a family with `F_0` the adjoint module", and the source of the first-order
  deformation that B2 differentiates to get a Jordan block.

## Status

Definitional layer only.  Not proved here: the remaining obligations for B1; the load-bearing
one is Li's conjugation identity
`Δ(λ,z) Y(u,z₀) Δ(λ,z)⁻¹ = Y(Δ(λ,z+z₀)u, z₀)`, from which the module Jacobi identity follows.
-/

namespace VOA.Heisenberg

open MvPolynomial

/-- Fock coefficients valued in polynomials in `w = z⁻¹`. -/
abbrev FockW : Type := MvPolynomial ℕ (Polynomial ℂ)

/-- The substitution constant for the `i`-th variable: `λk(-1)^i w^{i+1}`. -/
noncomputable def deltaCoeff (k lam : ℂ) (i : ℕ) : Polynomial ℂ :=
  Polynomial.C (lam * k * (-1) ^ i) * Polynomial.X ^ (i + 1)

/-- **Li's `Δ`-operator**, in substitution form: the `ℂ`-algebra map
`X_i ↦ X_i + λk(-1)^i w^{i+1}`. -/
noncomputable def deltaSub (k lam : ℂ) : Fock →ₐ[ℂ] FockW :=
  aeval (fun i : ℕ => (X i : FockW) + MvPolynomial.C (deltaCoeff k lam i))

@[simp] theorem deltaSub_X (k lam : ℂ) (i : ℕ) :
    deltaSub k lam (X i) = (X i : FockW) + MvPolynomial.C (deltaCoeff k lam i) := by
  simp [deltaSub]

/-- At `λ = 0` the operator is the plain coefficient inclusion: the untwisted module. -/
@[simp] theorem deltaCoeff_zero (k : ℂ) (i : ℕ) : deltaCoeff k 0 i = 0 := by
  simp [deltaCoeff]

/-- At `λ = 0`, `Δ` sends each variable to itself: the untwisted (adjoint) module. -/
@[simp] theorem deltaSub_zero_X (k : ℂ) (i : ℕ) :
    deltaSub k 0 (X i) = (X i : FockW) := by
  simp [deltaSub]

/-- The vacuum `1` is fixed by every `Δ`. -/
@[simp] theorem deltaSub_vacuum (k lam : ℂ) : deltaSub k lam vacuum = 1 := by
  simp [deltaSub, vacuum]

/-! ## The group law

`Δ` is additive in the charge: the charged modules form a one-parameter *family* through the
adjoint module at `λ = 0`.  This is what B2 differentiates — the first-order deformation in `λ`
is the cocycle producing a Jordan block for `L₀`. -/

@[simp] theorem deltaCoeff_add (k lam mu : ℂ) (i : ℕ) :
    deltaCoeff k (lam + mu) i = deltaCoeff k lam i + deltaCoeff k mu i := by
  simp only [deltaCoeff, add_mul, map_add]

/-- Lift a `Δ`-substitution to an endomorphism of `FockW`, fixing the coefficient ring. -/
noncomputable def deltaSubW (k lam : ℂ) : FockW →ₐ[Polynomial ℂ] FockW :=
  aeval (fun i : ℕ => (X i : FockW) + MvPolynomial.C (deltaCoeff k lam i))

@[simp] theorem deltaSubW_X (k lam : ℂ) (i : ℕ) :
    deltaSubW k lam (X i) = (X i : FockW) + MvPolynomial.C (deltaCoeff k lam i) := by
  simp [deltaSubW]

/-- `Δ` on `FockW` fixes the coefficient ring (it is a `Polynomial ℂ`-algebra map). -/
@[simp] theorem deltaSubW_C (k lam : ℂ) (c : Polynomial ℂ) :
    deltaSubW k lam (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [deltaSubW, MvPolynomial.algebraMap_eq]

/-- **The group law** `Δ_μ ∘ Δ_λ = Δ_{λ+μ}`: the charged modules form a one-parameter family. -/
theorem deltaSubW_comp_deltaSub (k lam mu : ℂ) :
    ((deltaSubW k mu).restrictScalars ℂ).comp (deltaSub k lam) = deltaSub k (lam + mu) := by
  apply MvPolynomial.algHom_ext
  intro i
  show (deltaSubW k mu) (deltaSub k lam (X i)) = deltaSub k (lam + mu) (X i)
  rw [deltaSub_X, deltaSub_X, map_add, deltaSubW_X, deltaSubW_C, deltaCoeff_add, map_add]
  ring

/-! ## The conjugation identity, at the oscillator level

Li's conjugation identity `Δ(λ,z) Y(u,z₀) Δ(λ,z)⁻¹ = Y(Δ(λ,z+z₀)u, z₀)` has concrete content
here, because the Heisenberg modes are exactly multiplication and differentiation
(`osc k n = mulX (-n-1)` for `n < 0`, `= n·k·∂/∂X_{n-1}` for `n > 0`).  Since `Δ` is a
*translation* of the variables:

* it **shifts the creation modes** by the substitution constant — `Δ ∘ mulX i = (mulX i + cᵢ) ∘ Δ`;
* it **commutes with the annihilation modes** — translation commutes with `∂/∂X_j`.

Together these are the oscillator-level conjugation, and they are what the general identity
reduces to on generators. -/

/-- **Creation modes are shifted**: `Δ(X_i · p) = (X_i + cᵢ)·Δ(p)`. -/
theorem deltaSub_mul_X (k lam : ℂ) (i : ℕ) (p : Fock) :
    deltaSub k lam (X i * p)
      = ((X i : FockW) + MvPolynomial.C (deltaCoeff k lam i)) * deltaSub k lam p := by
  rw [map_mul, deltaSub_X]

/-- **Annihilation modes are untouched**: `Δ` commutes with `∂/∂X_j`, because a translation of
the variables does. -/
theorem deltaSub_pderiv (k lam : ℂ) (j : ℕ) (p : Fock) :
    deltaSub k lam (MvPolynomial.pderiv j p)
      = MvPolynomial.pderiv j (deltaSub k lam p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [mul_comm p (X i), MvPolynomial.pderiv_mul, deltaSub_mul_X,
        MvPolynomial.pderiv_mul]
      simp only [map_add, map_mul, deltaSub_X, hp, MvPolynomial.pderiv_X,
        MvPolynomial.pderiv_C, add_zero, Pi.single_apply]
      by_cases h : j = i <;> simp [h]

/-! ## Invertibility

`Δ(λ,z)⁻¹` in Li's conjugation identity is `Δ(-λ,z)`: an immediate corollary of the group law,
and the form in which the identity will consume it. -/

/-- The coefficient inclusion `Fock → FockW`. -/
noncomputable def includeW : Fock →ₐ[ℂ] FockW :=
  aeval (fun i : ℕ => (X i : FockW))

@[simp] theorem includeW_X (i : ℕ) : includeW (X i) = (X i : FockW) := by
  simp [includeW]

/-- At `λ = 0` the twist is the plain inclusion — the untwisted (adjoint) module. -/
theorem deltaSub_zero_eq (k : ℂ) : deltaSub k 0 = includeW := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- **`Δ(-λ)` inverts `Δ(λ)`.** -/
theorem deltaSubW_neg_comp_deltaSub (k lam : ℂ) :
    ((deltaSubW k (-lam)).restrictScalars ℂ).comp (deltaSub k lam) = includeW := by
  rw [deltaSubW_comp_deltaSub, add_neg_cancel, deltaSub_zero_eq]

end VOA.Heisenberg
