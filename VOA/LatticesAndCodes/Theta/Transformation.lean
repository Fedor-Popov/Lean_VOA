/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Theta.Defs
import VOA.LatticesAndCodes.ForMathlib.EuclideanTheta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The transformation `τ ↦ -1/τ` of a theta function

**Ebeling, Proposition 2.1:** `ϑ_Γ(-1/τ) = (τ/i)^{n/2} (1/covol Γ) ϑ_{Γ*}(τ)`.

## Why a second theta function

`IntegralLattice.theta` is defined for an `IntegralLattice`, whose form is `ℤ`-valued.  The dual
lattice `Γ*` is **not** integral — its form takes values in `ℚ` — so the right-hand side cannot be
expressed with `IntegralLattice.theta`.  `EuclideanTheta.theta` is therefore introduced here for an
arbitrary `ℤ`-lattice in a finite-dimensional real inner product space, and
`IntegralLattice.theta_eq_euclidean` identifies `IntegralLattice.theta Γ` with it through the
Euclidean realisation of `Γ` (M4).

## The route

Poisson summation (`ZLattice.poissonSummation`, `ForMathlib/PoissonSummation.lean`) applied to the
Gaussian at `-1/τ`.  Ebeling proves the identity first for `τ = it` and then continues
holomorphically; here it is proved directly for every `τ` in the upper half plane, because
Mathlib's `fourier_gaussian_innerProductSpace` already allows a complex Gaussian parameter with
positive real part.  So no continuation argument is needed.

The two hypotheses of Poisson summation are discharged by:

* `EuclideanTheta.exp_neg_mul_sq_le_rpow` — `exp (-a s²) ≤ C (1+s)^{-2k}`, from a single term of
  the exponential series, which feeds `ZLattice.locallySummableOn_of_norm_le`;
* `EuclideanTheta.summable_gaussian` — the Gaussian sum over any `ℤ`-lattice converges, by the
  same estimate together with `ZLattice.summable_norm_rpow`.

## Main results

* `EuclideanTheta.theta` — the theta function of a lattice in a Euclidean space.
* `EuclideanTheta.fourier_gaussian_neg_one_div` — Ebeling's Lemma 2.1 in the shape needed.
* `EuclideanTheta.theta_neg_inv` — Proposition 2.1, dual side spanned by the dual basis.
* `IntegralLattice.theta_neg_inv` — Proposition 2.1 for an integral lattice, with covolume `√det`.

## References

Ebeling, *Lattices and Codes*, §2.1 (Lemma 2.1, Proposition 2.1).
-/

noncomputable section

open MeasureTheory Complex Module
open scoped Real FourierTransform RealInnerProductSpace


/-! ## Proposition 2.1 for an integral lattice -/

namespace IntegralLattice

variable {Γ : IntegralLattice}

theorem gaussian_toEuclidean (h : Γ.IsPosDef) (τ : ℂ) (x : Γ) :
    EuclideanTheta.gaussian τ (Γ.toEuclidean h x) = Γ.thetaTerm x τ := by
  rw [EuclideanTheta.gaussian_apply, thetaTerm, EuclideanTheta.gaussCoeff]
  congr 1
  have hn : ((‖Γ.toEuclidean h x‖ : ℝ) : ℂ) ^ 2 = (((normSq x : ℤ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Γ.norm_sq_toEuclidean h x]
  rw [hn]
  push_cast
  ring

/-- The theta function of `Γ` is the theta function of its Euclidean realisation. -/
theorem theta_eq_euclidean (h : Γ.IsPosDef) (τ : ℂ) :
    Γ.theta τ = EuclideanTheta.theta (LinearMap.range (Γ.toEuclidean h)) τ := by
  rw [theta, EuclideanTheta.theta,
    ← (LinearEquiv.ofInjective (Γ.toEuclidean h) (Γ.toEuclidean_injective h)).toEquiv.tsum_eq
      (fun z : LinearMap.range (Γ.toEuclidean h) =>
        EuclideanTheta.gaussian τ (z : EuclideanSpace ℝ (Fin Γ.rank)))]
  exact tsum_congr fun x => (gaussian_toEuclidean h τ x).symm

/-- **Ebeling, Proposition 2.1.**  `ϑ_Γ(-1/τ) = (τ/i)^{n/2} (1/√det Γ) ϑ_{Γ*}(τ)`, where `Γ*`
is the dual of the Euclidean realisation of `Γ` and `√det Γ` is its covolume. -/
theorem theta_neg_inv (h : Γ.IsPosDef) {τ : ℂ} (hτ : 0 < τ.im) :
    Γ.theta (-1 / τ)
      = (τ / Complex.I) ^ ((Γ.rank : ℂ) / 2)
        * ((Real.sqrt ((Γ.det : ℤ) : ℝ) : ℝ) : ℂ)⁻¹
        * EuclideanTheta.theta
            (ZLattice.dual (EuclideanSpace ℝ (Fin Γ.rank))
              (LinearMap.range (Γ.toEuclidean h))) τ := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin Γ.rank)) = Γ.rank := by simp
  have hcov := Γ.covolume_toEuclidean h
  rw [theta_eq_euclidean h, Γ.range_toEuclidean_eq_span h] at *
  rw [EuclideanTheta.theta_neg_inv (Γ.euclideanBasis h) hτ, hrank, hcov,
    ZLattice.dual_span (Γ.euclideanBasis h)]

end IntegralLattice
