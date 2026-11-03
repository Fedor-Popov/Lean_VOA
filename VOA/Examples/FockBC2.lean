/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LiDelta2
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change to `FockW₂`  (Route 1, step 6)

Li's conjugation identity has `Y` applied to `Δ₂(λ,z+z₀)u`, which lives in `FockW₂`.  So `Y` has
to be transported one level further than `Examples/FockBaseChange` took it.

Rather than duplicate that file, this one **generalizes the construction over the coefficient
ring**: `MvPolynomial.scalarRTensorAlgEquiv` identifies `Fock ⊗[ℂ] R ≅ MvPolynomial ℕ R` for any
commutative `ℂ`-algebra `R`, so an operator on `Fock` transports to one on `MvPolynomial ℕ R` by
acting on the `Fock` factor.  Taking `R = Polynomial ℂ` recovers `bcEnd`; taking
`R = CoeffW₂` gives what the identity needs.

## What is here

* `bcR` — base change of an operator over an arbitrary coefficient algebra `R`, with the same
  ring-map laws (`bcR_one`, `bcR_comp`, `bcR_add`, `bcR_smul`) and the field-property transport
  (`bcR_isField`);
* `bcEnd₂`, `YW₂`, `YW₂_isField` — the specialization to `R = CoeffW₂`, i.e. `Y` on `FockW₂`.
-/

namespace VOA.Heisenberg

open MvPolynomial
open scoped TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- `MvPolynomial ℕ R ≅ Fock ⊗[ℂ] R` for any coefficient algebra `R`. -/
noncomputable def fockREquiv : Fock ⊗[ℂ] R ≃ₐ[ℂ] MvPolynomial ℕ R :=
  MvPolynomial.scalarRTensorAlgEquiv

/-- **Base change of an operator** over an arbitrary coefficient algebra. -/
noncomputable def bcR (T : Module.End ℂ Fock) : Module.End ℂ (MvPolynomial ℕ R) :=
  (fockREquiv R).toLinearEquiv.conj (LinearMap.rTensor R T)

variable {R}

theorem bcR_comp (T S : Module.End ℂ Fock) : bcR R (T * S) = bcR R T * bcR R S := by
  unfold bcR
  rw [show (T * S) = T ∘ₗ S from rfl, LinearMap.rTensor_comp]
  ext x
  simp [LinearEquiv.conj_apply]

theorem bcR_one : bcR R 1 = 1 := by
  unfold bcR
  rw [show (1 : Module.End ℂ Fock) = LinearMap.id from rfl, LinearMap.rTensor_id]
  ext x
  simp [LinearEquiv.conj_apply]

theorem bcR_add (T S : Module.End ℂ Fock) : bcR R (T + S) = bcR R T + bcR R S := by
  unfold bcR
  rw [LinearMap.rTensor_add]
  ext x
  simp [LinearEquiv.conj_apply]

theorem bcR_smul (c : ℂ) (T : Module.End ℂ Fock) : bcR R (c • T) = c • bcR R T := by
  unfold bcR
  rw [LinearMap.rTensor_smul]
  ext x
  simp [LinearEquiv.conj_apply]

/-- **The field property transports** over any coefficient algebra. -/
theorem bcR_isField {a : FormalDist (Module.End ℂ Fock)} (ha : IsField a) :
    IsField (fun n => bcR R (a n)) := by
  intro x
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ n : ℤ, n < B →
      LinearMap.rTensor R (a n) ((fockREquiv R).toLinearEquiv.symm x) = 0 := by
    induction ((fockREquiv R).toLinearEquiv.symm x) using TensorProduct.induction_on with
    | zero => exact ⟨0, fun n _ => by simp⟩
    | tmul p q =>
        obtain ⟨B, hB⟩ := ha p
        exact ⟨B, fun n hn => by
          rw [LinearMap.rTensor_tmul, hB n hn, TensorProduct.zero_tmul]⟩
    | add y z hy hz =>
        obtain ⟨B1, h1⟩ := hy
        obtain ⟨B2, h2⟩ := hz
        exact ⟨min B1 B2, fun n hn => by
          rw [map_add, h1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            h2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩
  refine ⟨B, fun n hn => ?_⟩
  show bcR R (a n) x = 0
  unfold bcR
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hB n hn]
  exact map_zero _

/-! ## Specialization to `FockW₂` -/

/-- Base change of an operator to `FockW₂`. -/
noncomputable abbrev bcEnd₂ (T : Module.End ℂ Fock) : Module.End ℂ FockW₂ := bcR CoeffW₂ T

/-- **`Y` transported to `FockW₂`** — the operator Li's identity applies to `Δ₂(λ,z+z₀)u`. -/
noncomputable def YW₂ (k : ℂ) : Fock →ₗ[ℂ] FormalDist (Module.End ℂ FockW₂) where
  toFun u := fun n => bcEnd₂ (Y k u n)
  map_add' u v := by
    funext n
    show bcEnd₂ (Y k (u + v) n) = bcEnd₂ (Y k u n) + bcEnd₂ (Y k v n)
    rw [map_add]
    exact bcR_add _ _
  map_smul' c u := by
    funext n
    show bcEnd₂ (Y k (c • u) n) = c • bcEnd₂ (Y k u n)
    rw [map_smul]
    exact bcR_smul _ _

@[simp] theorem YW₂_apply (k : ℂ) (u : Fock) (n : ℤ) :
    YW₂ k u n = bcEnd₂ (Y k u n) := rfl

theorem YW₂_isField (k : ℂ) (u : Fock) : IsField (YW₂ k u) :=
  bcR_isField (Y_isField k u)
/-! ## ⚠ The `z₀`-coefficient extraction, and the CORRECT form of Li's identity

**A trap.**  It is tempting to
extend `Y` to `FockW₂`-states the same way `YWfull` extends it to `FockW`-states — by treating
the coefficient ring as inert scalars (`u ⊗ c ↦ c · Y_W u`).  For `FockW` that is correct: its
coefficients are polynomials in `w = 1/z` alone, and `z` genuinely is inert with respect to the
vertex variable `z₀`.  For `FockW₂` it is **wrong**, and the resulting statement is false.

The reason: `CoeffW₂ = PowerSeries (Polynomial ℂ)` carries `z₀`-dependence, and `z₀` is the
*vertex variable*.  Li's `Y(f(z₀)·v, z₀)` means the **product of formal series** `f(z₀)·Y(v,z₀)`,
whose index-`j` coefficient is the convolution `Σ_l f_l · Y(v)_{j-l}` — not `f · Y(v)_j`.

Concretely, at the generator `u = X i` the two sides have different support:

* conjugating `Y(X i, z₀)` by `Δ(λ,z)` shifts every **creation** oscillator by a scalar
  (`deltaSub_mul_X`), and `genField k i` has creation modes at infinitely many indices `j`, so
  the correction is spread over **infinitely many** `j`;
* an inert-scalar right-hand side puts the whole correction on `Y k vacuum`, which by
  `Y_vacuum_apply` is supported at the **single** index `j = 0`.

So the identity must be stated with the convolution.  Doing so also relocates it: once the
`z₀`-dependence is expanded out, both sides are operators on `FockW`, and `FockW₂` is needed only
as the home of the *twisted state*.  The base change of §1 stays useful in general, but Li's
identity does not need it. -/

/-- Extract the `z₀^l` Taylor coefficient of a `FockW₂`-state, giving a `FockW`-state.
`FockW₂ = (ℕ →₀ ℕ) →₀ CoeffW₂` and `FockW = (ℕ →₀ ℕ) →₀ Polynomial ℂ`, so this is
`PowerSeries.coeff l` applied to each `MvPolynomial` coefficient. -/
noncomputable def coeffZ₀ (l : ℕ) : FockW₂ →ₗ[ℂ] FockW :=
  Finsupp.mapRange.linearMap
    ((PowerSeries.coeff l : CoeffW₂ →ₗ[Polynomial ℂ] Polynomial ℂ).restrictScalars ℂ)

@[simp] theorem coeffZ₀_apply (l : ℕ) (v : FockW₂) (a : ℕ →₀ ℕ) :
    (coeffZ₀ l v) a = PowerSeries.coeff l (v a) := rfl

/-- **Li's conjugation identity**, correctly stated.

`Δ(λ,z) · Y(u,z₀) · Δ(λ,z)⁻¹ = Y(Δ(λ,z+z₀)u, z₀)`

Both sides are operators on `FockW`.  The right-hand side expands the twisted state
`Δ₂(λ,z+z₀)u ∈ FockW₂` into its `z₀`-Taylor coefficients and **convolves** against the vertex
index, which is what `Y(f(z₀)v, z₀) = f(z₀)Y(v,z₀)` means.

Well-formedness does not depend on the sum being finite (`finsum` is total), but it is: at a
generator the `l`-th coefficient for `l ≥ 1` is a multiple of the vacuum, whose field is
supported at index `0`, so exactly one `l` contributes to each `j`.

This is the single remaining mathematical obligation of Route 1.  Proving it is **not** mere
bookkeeping: beyond the generator case it requires compatibility of the conjugation with the
normal-ordered-product recursion that defines `Y` off the generators, which is the actual content
of Li's theorem. -/
def LiConjugation (k lam : ℂ) : Prop :=
  ∀ (u : Fock) (j : ℤ),
    ((deltaSubW k lam).restrictScalars ℂ).toLinearMap ∘ₗ (YW k u j) ∘ₗ
        ((deltaSubW k (-lam)).restrictScalars ℂ).toLinearMap
      = ∑ᶠ l : ℕ, YWfull k (coeffZ₀ l (deltaSub₂ k lam u)) (j - l)

end VOA.Heisenberg
