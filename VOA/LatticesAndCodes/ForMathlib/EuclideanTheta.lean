/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.ForMathlib.ExpBound
import VOA.LatticesAndCodes.ForMathlib.PoissonShift
import VOA.LatticesAndCodes.ForMathlib.QuotientCoset
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian theta function of a lattice in a Euclidean space

For a `ℤ`-lattice `L` in a finite-dimensional real inner product space `V` and `τ` in the upper
half plane, `θ_L(τ) = ∑_{x ∈ L} e^{π i τ ‖x‖²}`, and Poisson summation gives

`θ_L(-1/τ) = (τ/i)^{n/2} (covol L)⁻¹ θ_{L*}(τ)`.

The same computation over a **coset** `μ + L` gives the theta series with a characteristic,
`θ_{L,μ}`, whose `S`-transformation carries the character `e^{2π i ⟪μ, y⟫}` on the dual lattice.
Together with its `T`-transformation these are the two generators of the Weil representation
attached to `L`, and they are what the theta series of a lattice of level `N > 1` transforms by.

Nothing here mentions an `IntegralLattice`: the statements are about an arbitrary `ℤ`-lattice in
a Euclidean space, and are upstreamable as they stand.

## Main definitions and results

* `EuclideanTheta.gaussian` — `v ↦ e^{π i τ ‖v‖²}` as a bundled continuous map.
* `EuclideanTheta.theta`, `EuclideanTheta.thetaShift` — the theta series of a lattice and of a
  coset of it.
* `EuclideanTheta.fourier_gaussian_neg_one_div` — Ebeling's Lemma 2.1.
* `EuclideanTheta.theta_neg_inv` — Ebeling's Proposition 2.1.
* `EuclideanTheta.thetaShift_neg_inv` — the `S`-law of the theta with a characteristic.
* `EuclideanTheta.thetaShift_add_one` — its `T`-law.

## References

Ebeling, *Lattices and Codes*, §2.1 (Lemma 2.1, Proposition 2.1), §3.2.
-/

noncomputable section

open MeasureTheory Complex Module
open scoped Real FourierTransform RealInnerProductSpace


namespace EuclideanTheta

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian parameter attached to `τ`: `exp (-gaussCoeff τ * ‖v‖²) = exp (π i τ ‖v‖²)`. -/
def gaussCoeff (τ : ℂ) : ℂ := -((Real.pi : ℂ) * Complex.I * τ)

@[simp] theorem gaussCoeff_re (τ : ℂ) : (gaussCoeff τ).re = Real.pi * τ.im := by
  simp [gaussCoeff]

/-- The Gaussian `v ↦ exp (π i τ ‖v‖²)`, whose sum over a lattice is its theta function. -/
def gaussian (τ : ℂ) : C(V, ℂ) :=
  ⟨fun v => Complex.exp (-gaussCoeff τ * (‖v‖ : ℂ) ^ 2), by fun_prop⟩

@[simp] theorem gaussian_apply (τ : ℂ) (v : V) :
    gaussian τ v = Complex.exp (-gaussCoeff τ * (‖v‖ : ℂ) ^ 2) := rfl

theorem norm_gaussian (τ : ℂ) (v : V) :
    ‖gaussian τ v‖ = Real.exp (-(Real.pi * τ.im * ‖v‖ ^ 2)) := by
  rw [gaussian_apply, Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, gaussCoeff, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### Gaussian decay estimates -/

/-- `exp (-a s²) ≤ C (1 + s)^{-2k}`: the Gaussian beats every polynomial, in the explicit
form `ZLattice.locallySummableOn_of_norm_le` asks for.  Proved from one term of the exponential
series (`Real.exp_neg_le_factorial_div_pow`), with no asymptotics. -/
theorem exp_neg_mul_sq_le_rpow {a : ℝ} (ha : 0 < a) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-(a * s ^ 2))
      ≤ (2 ^ (2 * k) * (1 + (k.factorial : ℝ) / a ^ k)) * (1 + s) ^ (-(2 * k : ℕ) : ℝ) := by
  have hM : (1 : ℝ) ≤ 1 + (k.factorial : ℝ) / a ^ k := by
    have : (0 : ℝ) ≤ (k.factorial : ℝ) / a ^ k := by positivity
    linarith
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hrw : ((1 + s) ^ (-(2 * k : ℕ) : ℝ)) = ((1 + s) ^ (2 * k))⁻¹ := by
    rw [Real.rpow_neg h1s.le, Real.rpow_natCast]
  rw [hrw, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rcases le_total s 1 with hle | hle
  · have hp : (1 + s) ^ (2 * k) ≤ 2 ^ (2 * k) := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(a * s ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    calc Real.exp (-(a * s ^ 2)) * (1 + s) ^ (2 * k) ≤ 1 * 2 ^ (2 * k) := by
          exact mul_le_mul he hp (by positivity) zero_le_one
      _ ≤ 2 ^ (2 * k) * (1 + (k.factorial : ℝ) / a ^ k) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (2 * k)]
  · have hs1 : (0 : ℝ) < s := by linarith
    have hx : (0 : ℝ) < a * s ^ 2 := by positivity
    have he := Real.exp_neg_le_factorial_div_pow k hx
    have hp : (1 + s) ^ (2 * k) ≤ 2 ^ (2 * k) * s ^ (2 * k) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpow : (a * s ^ 2) ^ k = a ^ k * s ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    calc Real.exp (-(a * s ^ 2)) * (1 + s) ^ (2 * k)
        ≤ ((k.factorial : ℝ) / (a * s ^ 2) ^ k) * (2 ^ (2 * k) * s ^ (2 * k)) := by
          refine mul_le_mul he hp (by positivity) (by positivity)
      _ = 2 ^ (2 * k) * ((k.factorial : ℝ) / a ^ k) := by
          rw [hpow]
          field_simp
      _ ≤ 2 ^ (2 * k) * (1 + (k.factorial : ℝ) / a ^ k) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (2 * k)]

theorem norm_gaussian_le {τ : ℂ} (hτ : 0 < τ.im) (k : ℕ) (v : V) :
    ‖gaussian τ v‖
      ≤ (2 ^ (2 * k) * (1 + (k.factorial : ℝ) / (Real.pi * τ.im) ^ k))
        * (1 + ‖v‖) ^ (-(2 * k : ℕ) : ℝ) := by
  rw [norm_gaussian]
  exact exp_neg_mul_sq_le_rpow (by positivity) k (norm_nonneg v)

/-! ### The theta function of a lattice in a Euclidean space -/

/-- `∑_{x ∈ L} e^{π i τ x²}`, the theta function of an arbitrary lattice in a Euclidean space.
Unlike `IntegralLattice.theta` this makes sense for the dual lattice, whose form is only
rational-valued. -/
def theta (L : Submodule ℤ V) (τ : ℂ) : ℂ := ∑' x : L, gaussian τ (x : V)

theorem summable_norm_gaussian (L : Submodule ℤ V) [DiscreteTopology L] {τ : ℂ}
    (hτ : 0 < τ.im) : Summable fun x : L => ‖gaussian τ (x : V)‖ := by
  set a : ℝ := Real.pi * τ.im with ha'
  have ha : 0 < a := by positivity
  set k : ℕ := Module.finrank ℤ L + 1 with hk
  set r : ℝ := -((2 * k : ℕ) : ℝ) with hr
  have hrlt : r < -(Module.finrank ℤ L : ℝ) := by
    rw [hr, hk]
    push_cast
    have : (0 : ℝ) ≤ (Module.finrank ℤ L : ℝ) := Nat.cast_nonneg _
    linarith
  have hmaj : Summable (fun z : L => ((k.factorial : ℝ) / a ^ k) * ‖(z : V)‖ ^ r) :=
    Summable.mul_left _ (ZLattice.summable_norm_rpow L r hrlt)
  refine Summable.of_norm_bounded_eventually hmaj ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with z hz
  have hpos : (0 : ℝ) < ‖(z : V)‖ := by
    rw [norm_pos_iff]
    exact fun h => hz (Subtype.ext h)
  have hxpos : (0 : ℝ) < a * ‖(z : V)‖ ^ 2 := by positivity
  have hbound := Real.exp_neg_le_factorial_div_pow k hxpos
  rw [norm_norm, norm_gaussian, ← ha']
  refine hbound.trans (le_of_eq ?_)
  have hrp : ‖(z : V)‖ ^ r = ((‖(z : V)‖ ^ 2) ^ k)⁻¹ := by
    rw [hr, Real.rpow_neg hpos.le, Real.rpow_natCast, pow_mul]
  rw [hrp, mul_pow]
  field_simp

theorem summable_gaussian (L : Submodule ℤ V) [DiscreteTopology L] {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : L => gaussian τ (x : V) :=
  Summable.of_norm (summable_norm_gaussian L hτ)

/-! ### The Fourier transform of the Gaussian -/

theorem im_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ : ℂ).im := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hns : 0 < Complex.normSq τ := Complex.normSq_pos.2 hτ0
  have h : (-1 / τ : ℂ).im = τ.im / Complex.normSq τ := by
    rw [Complex.div_im]
    simp
    ring
  rw [h]
  positivity

theorem gaussCoeff_neg_one_div {τ : ℂ} (hτ0 : τ ≠ 0) :
    gaussCoeff (-1 / τ) = (Real.pi : ℂ) * Complex.I / τ := by
  rw [gaussCoeff]
  field_simp

/-- The Fourier transform of the Gaussian `v ↦ e^{π i (-1/τ) v²}` is
`(τ/i)^{n/2} e^{π i τ v²}`.  This is Ebeling's Lemma 2.1 in the form Proposition 2.1 needs;
the input is Mathlib's `fourier_gaussian_innerProductSpace`. -/
theorem fourier_gaussian_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) (w : V) :
    𝓕 (gaussian (-1 / τ) : V → ℂ) w
      = (τ / Complex.I) ^ ((Module.finrank ℝ V : ℂ) / 2) * gaussian τ w := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hre : 0 < (gaussCoeff (-1 / τ)).re := by
    rw [gaussCoeff_re]
    have := im_neg_one_div hτ
    positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have key := fourier_gaussian_innerProductSpace (b := gaussCoeff (-1 / τ)) (V := V) hre w
  rw [show (gaussian (-1 / τ) : V → ℂ)
      = fun v : V => Complex.exp (-gaussCoeff (-1 / τ) * (‖v‖ : ℂ) ^ 2) from rfl, key,
    gaussCoeff_neg_one_div hτ0]
  congr 1
  · congr 1
    field_simp
  · rw [gaussian_apply, gaussCoeff]
    congr 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-! ### Proposition 2.1 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem locallySummableOn_gaussian (b : Basis ι ℝ V) {τ : ℂ} (hτ : 0 < τ.im) :
    ZSpan.LocallySummableOn b (gaussian τ) := by
  refine ZLattice.locallySummableOn_of_norm_le b (gaussian τ)
    (C := 2 ^ (2 * (Fintype.card ι + 1))
      * (1 + (((Fintype.card ι + 1).factorial : ℝ)) / (Real.pi * τ.im) ^ (Fintype.card ι + 1)))
    (p := ((2 * (Fintype.card ι + 1) : ℕ) : ℝ)) ?_ ?_
  · push_cast
    have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    linarith
  · intro v
    exact norm_gaussian_le hτ (Fintype.card ι + 1) v

/-- **Ebeling, Proposition 2.1.**  `ϑ_Γ(-1/τ) = (τ/i)^{n/2} (1/covol Γ) ϑ_{Γ*}(τ)`,
with `Γ* ` spanned by the dual basis. -/
theorem theta_neg_inv (b : Basis ι ℝ V) {τ : ℂ} (hτ : 0 < τ.im) :
    theta (Submodule.span ℤ (Set.range b)) (-1 / τ)
      = (τ / Complex.I) ^ ((Module.finrank ℝ V : ℂ) / 2)
        * ((ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume : ℝ) : ℂ)⁻¹
        * theta (Submodule.span ℤ (Set.range (ZSpan.dualBasis b))) τ := by
  have hτ' : 0 < (-1 / τ : ℂ).im := im_neg_one_div hτ
  set c : ℂ := (τ / Complex.I) ^ ((Module.finrank ℝ V : ℂ) / 2) with hc
  -- the Fourier transforms are summable over the dual lattice
  have hFsum : Summable fun y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)) =>
      𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V) := by
    refine ((summable_gaussian (Submodule.span ℤ (Set.range (ZSpan.dualBasis b)))
      hτ).mul_left c).congr fun y => ?_
    rw [fourier_gaussian_neg_one_div hτ]
  have hFsum' : Summable fun y : ZLattice.dual V (Submodule.span ℤ (Set.range b)) =>
      𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V) := by
    rw [ZLattice.dual_span b]
    exact hFsum
  have hP := ZLattice.poissonSummation b (locallySummableOn_gaussian b hτ') hFsum'
  rw [ZLattice.dual_span b] at hP
  rw [theta, hP]
  have hR : ∑' y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)),
      𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V)
      = c * theta (Submodule.span ℤ (Set.range (ZSpan.dualBasis b))) τ := by
    rw [theta, ← tsum_mul_left]
    exact tsum_congr fun y => fourier_gaussian_neg_one_div hτ _
  rw [hR, Complex.real_smul]
  push_cast
  ring

/-! ### The theta series of a coset -/

section Shift

/-- A Gaussian summed over a coset converges: `‖x‖² ≤ 2‖x+μ‖² + 2‖μ‖²`, so the shifted Gaussian
is majorised by the unshifted one with half the parameter. -/
theorem summable_norm_gaussian_shift (L : Submodule ℤ V) [DiscreteTopology L] {τ : ℂ}
    (hτ : 0 < τ.im) (μ : V) : Summable fun x : L => ‖gaussian τ ((x : V) + μ)‖ := by
  set σ : ℂ := Complex.I * ((τ.im / 2 : ℝ) : ℂ) with hσ
  have him : σ.im = τ.im / 2 := by simp [hσ]
  have hhalf : (0 : ℝ) < σ.im := by rw [him]; linarith
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
    ((summable_norm_gaussian L hhalf).mul_left (Real.exp (Real.pi * τ.im * ‖μ‖ ^ 2)))
  have hsq : ‖(x : V)‖ ^ 2 ≤ 2 * ‖(x : V) + μ‖ ^ 2 + 2 * ‖μ‖ ^ 2 := by
    have h1 : ‖(x : V)‖ ≤ ‖(x : V) + μ‖ + ‖μ‖ := by
      have := norm_sub_le ((x : V) + μ) μ
      simpa using this
    have hc2 : ‖(x : V)‖ ^ 2 ≤ (‖(x : V) + μ‖ + ‖μ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖(x : V) + μ‖ - ‖μ‖)]
  rw [norm_gaussian, norm_gaussian, ← Real.exp_add, him]
  refine Real.exp_le_exp.2 ?_
  have h3 : 0 ≤ Real.pi * τ.im * (2 * ‖(x : V) + μ‖ ^ 2 + 2 * ‖μ‖ ^ 2 - ‖(x : V)‖ ^ 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [h3]

theorem summable_gaussian_shift (L : Submodule ℤ V) [DiscreteTopology L] {τ : ℂ}
    (hτ : 0 < τ.im) (μ : V) : Summable fun x : L => gaussian τ ((x : V) + μ) :=
  Summable.of_norm (summable_norm_gaussian_shift L hτ μ)

/-- The real Gaussian sum over a coset converges. -/
theorem summable_exp_neg_mul_sq_norm_shift (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ}
    (hc : 0 < c) (μ : V) : Summable fun x : L => Real.exp (-(c * ‖(x : V) + μ‖ ^ 2)) := by
  set σ : ℂ := Complex.I * ((c / Real.pi : ℝ) : ℂ) with hσ
  have him : σ.im = c / Real.pi := by simp [hσ]
  have hpos : (0 : ℝ) < σ.im := by rw [him]; positivity
  refine (summable_norm_gaussian_shift L hpos μ).congr fun x => ?_
  rw [norm_gaussian, him]
  congr 1
  field_simp

/-- `Θ_{L,μ}(τ) = ∑_{x ∈ L} e^{π i τ ‖x + μ‖²}`, the theta series of the coset `μ + L`. -/
def thetaShift (L : Submodule ℤ V) (μ : V) (τ : ℂ) : ℂ :=
  ∑' x : L, gaussian τ ((x : V) + μ)

@[simp] theorem thetaShift_zero (L : Submodule ℤ V) (τ : ℂ) : thetaShift L 0 τ = theta L τ :=
  tsum_congr fun x => by rw [add_zero]

/-- **The `T`-transformation of the theta with a characteristic.**  If `‖x‖² + 2⟪x,μ⟫` is an even
integer for every lattice vector `x` — which holds when `L` is even and `μ` lies in its dual —
then `τ ↦ τ + 1` multiplies `Θ_{L,μ}` by `e^{π i ‖μ‖²}`. -/
theorem thetaShift_add_one (L : Submodule ℤ V) (μ : V)
    (heven : ∀ x : L, ∃ m : ℤ, ‖(x : V)‖ ^ 2 + 2 * ⟪(x : V), μ⟫ = 2 * m) (τ : ℂ) :
    thetaShift L μ (τ + 1)
      = Complex.exp (Real.pi * Complex.I * ((‖μ‖ ^ 2 : ℝ) : ℂ)) * thetaShift L μ τ := by
  rw [thetaShift, thetaShift, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  obtain ⟨m, hm⟩ := heven x
  have hsq : ‖(x : V) + μ‖ ^ 2 = 2 * (m : ℝ) + ‖μ‖ ^ 2 := by
    have hcomm : ⟪μ, (x : V)⟫ = ⟪(x : V), μ⟫ := real_inner_comm _ _
    rw [← real_inner_self_eq_norm_sq, inner_add_add_self, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    linarith [hm, hcomm]
  have hcast : ((‖(x : V) + μ‖ : ℝ) : ℂ) ^ 2 = ((2 * (m : ℝ) + ‖μ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hsq]
  rw [gaussian_apply, gaussian_apply, hcast]
  simp only [gaussCoeff]
  rw [show (-(-((Real.pi : ℂ) * Complex.I * (τ + 1))) * ((2 * (m : ℝ) + ‖μ‖ ^ 2 : ℝ) : ℂ))
      = (Real.pi * Complex.I * ((‖μ‖ ^ 2 : ℝ) : ℂ))
        + (-(-((Real.pi : ℂ) * Complex.I * τ)) * ((2 * (m : ℝ) + ‖μ‖ ^ 2 : ℝ) : ℂ))
        + (m : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The `S`-transformation of the theta with a characteristic.**  Poisson summation over the
coset `μ + L` (`ZLattice.poissonSummation_shift`) produces the character `e^{2π i ⟪μ, y⟫}` on the
dual lattice. -/
theorem thetaShift_neg_inv (b : Basis ι ℝ V) (μ : V) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaShift (Submodule.span ℤ (Set.range b)) μ (-1 / τ)
      = (τ / Complex.I) ^ ((Module.finrank ℝ V : ℂ) / 2)
        * ((ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume : ℝ) : ℂ)⁻¹
        * ∑' y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)),
            Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ)) * gaussian τ (y : V) := by
  have hτ' : 0 < (-1 / τ : ℂ).im := im_neg_one_div hτ
  set C : ℂ := (τ / Complex.I) ^ ((Module.finrank ℝ V : ℂ) / 2) with hC
  have hFsum : Summable fun y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)) =>
      Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ))
        * 𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V) := by
    refine Summable.of_norm ?_
    refine (((summable_gaussian (Submodule.span ℤ (Set.range (ZSpan.dualBasis b)))
      hτ).norm).mul_left ‖C‖).congr fun y => ?_
    rw [fourier_gaussian_neg_one_div hτ, norm_mul, norm_mul, ← hC]
    have hunit : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]; norm_num
    rw [hunit, one_mul]
  have hFsum' : Summable fun y : ZLattice.dual V (Submodule.span ℤ (Set.range b)) =>
      Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ))
        * 𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V) := by
    rw [ZLattice.dual_span b]; exact hFsum
  have hP := ZLattice.poissonSummation_shift b μ
    ((locallySummableOn_gaussian b hτ').comp_addRight μ) hFsum'
  rw [ZLattice.dual_span b] at hP
  rw [thetaShift, hP, Complex.real_smul]
  have hR : ∑' y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)),
      Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ))
        * 𝓕 (gaussian (-1 / τ) : V → ℂ) (y : V)
      = C * ∑' y : Submodule.span ℤ (Set.range (ZSpan.dualBasis b)),
          Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ)) * gaussian τ (y : V) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun y => ?_
    rw [fourier_gaussian_neg_one_div hτ, ← hC]
    ring
  rw [hR]
  push_cast
  ring

end Shift

end EuclideanTheta
