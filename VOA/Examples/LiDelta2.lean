/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.FockBaseChange
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The two-variable `Δ`  (Route 1, step 4)

Li's conjugation identity needs `Δ(λ, z+z₀)`, and the one-variable `Δ` of `Examples/LiDelta`
cannot express it: its substitution constant is the *monomial*
`deltaCoeff k lam i = C(λk(-1)^i)·w^{i+1}`, a polynomial in the single variable `w`, whereas
`(z+z₀)^{-(i+1)}` is not polynomial at all.

## Choosing the coefficient ring

Writing `w = z⁻¹`, the shifted constant is

`(z+z₀)^{-(i+1)} = w^{i+1}(1 + z₀w)^{-(i+1)} = Σ_{j ≥ 0} C(-(i+1), j) · w^{i+1+j} · z₀^j`,

expanded in **nonnegative** powers of `z₀` — Gannon's `ι_{z,z₀}` convention, the same one
`Foundations.Expansion` uses.  So the coefficients are a *power series in `z₀`* whose
coefficients are *polynomials in `w`*:

`PowerSeries (Polynomial ℂ)`.

That is a commutative ring, so `MvPolynomial ℕ (PowerSeries (Polynomial ℂ))` is a legitimate
target and `aeval` applies exactly as before.  (A `FormalDist`-valued target would *not* work:
formal distributions are deliberately not a ring — Gannon's Paradox 5.1 — which is why the
expansion has to be one-sided.)

## What is proved here

* `expandNegPow i` — the expansion above, as an element of `PowerSeries (Polynomial ℂ)`;
* `deltaCoeff₂`, `deltaSub₂` — the two-variable operator, defined by `aeval` just like the
  one-variable one;
* `deltaCoeff₂_constantCoeff` / `deltaSub₂_specialize` — **the correctness check**: setting
  `z₀ = 0` recovers the one-variable `Δ` on the nose.  This is what pins the normalization; a
  two-variable object that did not specialize correctly would be the wrong object.
-/

namespace VOA.Heisenberg

open MvPolynomial

/-- Coefficients for the two-variable twist: power series in `z₀`, polynomial in `w`. -/
abbrev CoeffW₂ : Type := PowerSeries (Polynomial ℂ)

/-- Fock space with two-variable twist coefficients. -/
abbrev FockW₂ : Type := MvPolynomial ℕ CoeffW₂

/-- **The `ι`-expansion of `(z+z₀)^{-(i+1)}`** in nonnegative powers of `z₀`, written in
`w = z⁻¹`: the `z₀^j` coefficient is `C(-(i+1), j)·w^{i+1+j}`. -/
noncomputable def expandNegPow (i : ℕ) : CoeffW₂ :=
  PowerSeries.mk fun j =>
    Polynomial.C (gBinom (-(i : ℤ) - 1) j) * Polynomial.X ^ (i + 1 + j)

@[simp] theorem expandNegPow_coeff (i j : ℕ) :
    PowerSeries.coeff j (expandNegPow i)
      = Polynomial.C (gBinom (-(i : ℤ) - 1) j) * Polynomial.X ^ (i + 1 + j) := by
  simp [expandNegPow]

/-- At `z₀ = 0` the expansion is the one-variable monomial `w^{i+1}`. -/
@[simp] theorem expandNegPow_constantCoeff (i : ℕ) :
    PowerSeries.constantCoeff (expandNegPow i) = Polynomial.X ^ (i + 1) := by
  rw [expandNegPow, PowerSeries.constantCoeff_mk]
  simp

/-- The two-variable substitution constant. -/
noncomputable def deltaCoeff₂ (k lam : ℂ) (i : ℕ) : CoeffW₂ :=
  PowerSeries.C (Polynomial.C (lam * k * (-1) ^ i)) * expandNegPow i

/-- **Correctness**: at `z₀ = 0`, `deltaCoeff₂` is `deltaCoeff`. -/
@[simp] theorem deltaCoeff₂_constantCoeff (k lam : ℂ) (i : ℕ) :
    PowerSeries.constantCoeff (deltaCoeff₂ k lam i) = deltaCoeff k lam i := by
  rw [deltaCoeff₂, map_mul, PowerSeries.constantCoeff_C, expandNegPow_constantCoeff, deltaCoeff]

/-- **The two-variable `Δ`**: `X_i ↦ X_i + (the ι-expansion of λk(-1)^i (z+z₀)^{-(i+1)})`. -/
noncomputable def deltaSub₂ (k lam : ℂ) : Fock →ₐ[ℂ] FockW₂ :=
  aeval fun i : ℕ => (X i : FockW₂) + MvPolynomial.C (deltaCoeff₂ k lam i)

@[simp] theorem deltaSub₂_X (k lam : ℂ) (i : ℕ) :
    deltaSub₂ k lam (X i) = (X i : FockW₂) + MvPolynomial.C (deltaCoeff₂ k lam i) := by
  simp [deltaSub₂]

/-! ## Specialization `z₀ = 0` recovers the one-variable `Δ` -/

/-- Setting `z₀ = 0` on coefficients, as a ring hom `CoeffW₂ → Polynomial ℂ`. -/
noncomputable def setZ₀Zero : CoeffW₂ →+* Polynomial ℂ := PowerSeries.constantCoeff

/-- Setting `z₀ = 0` on states. -/
noncomputable def specializeZ₀ : FockW₂ →+* FockW := MvPolynomial.map setZ₀Zero

@[simp] theorem specializeZ₀_X (i : ℕ) : specializeZ₀ (X i : FockW₂) = (X i : FockW) := by
  simp [specializeZ₀]

@[simp] theorem specializeZ₀_C (c : CoeffW₂) :
    specializeZ₀ (MvPolynomial.C c) = MvPolynomial.C (setZ₀Zero c) := by
  simp [specializeZ₀]

/-- **The two-variable `Δ` specializes to the one-variable `Δ` at `z₀ = 0`.**  This pins the
normalization: a two-variable object failing this would be the wrong one. -/
theorem deltaSub₂_specialize (k lam : ℂ) (p : Fock) :
    specializeZ₀ (deltaSub₂ k lam p) = deltaSub k lam p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hL : deltaSub₂ k lam (MvPolynomial.C a)
          = MvPolynomial.C (algebraMap ℂ CoeffW₂ a) := by
        simp [deltaSub₂]
      have hR : deltaSub k lam (MvPolynomial.C a)
          = MvPolynomial.C (algebraMap ℂ (Polynomial ℂ) a) := by
        simp [deltaSub]
      rw [hL, hR, specializeZ₀_C]
      congr 1
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
      have hR : deltaSub k lam (p * X i) = deltaSub k lam p * deltaSub k lam (X i) :=
        map_mul _ _ _
      rw [map_mul, map_mul, hp, hR, deltaSub₂_X, deltaSub_X, map_add, specializeZ₀_X,
        specializeZ₀_C]
      congr 2
      exact congrArg MvPolynomial.C (deltaCoeff₂_constantCoeff k lam i)

/-! ## The group law, in two variables

`Δ₂` obeys the same additivity in `λ` as the one-variable operator, for the same reason: the
substitution constant is linear in `λ`.  As before the composite is taken on the `FockW₂` side,
where the twist is an endomorphism. -/

/-- The two-variable twist as an endomorphism of `FockW₂`. -/
noncomputable def deltaSubW₂ (k lam : ℂ) : FockW₂ →ₐ[CoeffW₂] FockW₂ :=
  aeval fun i : ℕ => (X i : FockW₂) + MvPolynomial.C (deltaCoeff₂ k lam i)

@[simp] theorem deltaSubW₂_X (k lam : ℂ) (i : ℕ) :
    deltaSubW₂ k lam (X i) = (X i : FockW₂) + MvPolynomial.C (deltaCoeff₂ k lam i) := by
  simp [deltaSubW₂]

@[simp] theorem deltaSubW₂_C (k lam : ℂ) (c : CoeffW₂) :
    deltaSubW₂ k lam (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [deltaSubW₂]

/-- The substitution constant is additive in `λ`. -/
theorem deltaCoeff₂_add (k lam mu : ℂ) (i : ℕ) :
    deltaCoeff₂ k (lam + mu) i = deltaCoeff₂ k lam i + deltaCoeff₂ k mu i := by
  rw [deltaCoeff₂, deltaCoeff₂, deltaCoeff₂, ← add_mul]
  congr 1
  rw [← map_add, ← map_add]
  congr 2
  ring

/-- **The group law**: `Δ₂(μ) ∘ Δ₂(λ) = Δ₂(λ+μ)`. -/
theorem deltaSubW₂_comp_deltaSub₂ (k lam mu : ℂ) :
    ((deltaSubW₂ k mu).restrictScalars ℂ).comp (deltaSub₂ k lam) = deltaSub₂ k (lam + mu) := by
  apply MvPolynomial.algHom_ext
  intro i
  show (deltaSubW₂ k mu) (deltaSub₂ k lam (X i)) = deltaSub₂ k (lam + mu) (X i)
  rw [deltaSub₂_X, deltaSub₂_X, map_add, deltaSubW₂_X, deltaSubW₂_C, deltaCoeff₂_add, map_add]
  ring

/-- The coefficient inclusion `Fock → FockW₂`. -/
noncomputable def includeW₂ : Fock →ₐ[ℂ] FockW₂ :=
  aeval fun i : ℕ => (X i : FockW₂)

/-- At `λ = 0` the two-variable twist is the plain inclusion. -/
theorem deltaSub₂_zero_eq (k : ℂ) : deltaSub₂ k 0 = includeW₂ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [deltaSub₂_X, deltaCoeff₂, zero_mul, zero_mul]
  simp [includeW₂]

/-- **`Δ₂(-λ)` inverts `Δ₂(λ)`** — the form the conjugation identity consumes. -/
theorem deltaSubW₂_neg_comp_deltaSub₂ (k lam : ℂ) :
    ((deltaSubW₂ k (-lam)).restrictScalars ℂ).comp (deltaSub₂ k lam) = includeW₂ := by
  rw [deltaSubW₂_comp_deltaSub₂, add_neg_cancel, deltaSub₂_zero_eq]

end VOA.Heisenberg
