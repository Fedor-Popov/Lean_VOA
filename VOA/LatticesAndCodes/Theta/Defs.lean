/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Theta.Counting
import VOA.LatticesAndCodes.ForMathlib.ExpBound
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The theta function of a positive definite lattice

`IntegralLattice.theta Γ τ = ∑_{x ∈ Γ} e^{πiτ x²}` — Ebeling's `ϑ_Γ`, §2.1 — together with the
convergence that makes it well defined and holomorphic on the upper half plane.

## The convergence argument

Ebeling's Lemma 2.2 writes `Γ = M·ℤⁿ`, takes `ε = min_{|x|=1} (Mx)²` and compares with
`(∑_{r ∈ ℤ} e^{-πv₀εr²})ⁿ`. The route here is different and asymptotics-free:

* `IntegralLattice.exp_neg_le_factorial_div_pow` — one term of the exponential series gives
  `exp (-x) ≤ k!/xᵏ` for `x > 0`. This is the explicit form of "the exponential beats every
  polynomial"; no limit is taken.
* the image of `Γ` under `IntegralLattice.toEuclidean` (M4) is a `ZLattice` of rank `Γ.rank`, so
  `ZLattice.summable_norm_rpow` sums `‖z‖^{-2k}` as soon as `2k > rank`.
* the two combine into `IntegralLattice.summable_exp_neg_mul_normSq`, and the finitely many
  exceptional terms (only `z = 0`) are absorbed by taking the bound on the cofinite filter.

Holomorphy then comes from `Complex.differentiableOn_tsum_of_summable_norm` applied on each
half plane `Im τ > v > 0`, where the majorant is uniform; every point of the upper half plane is
interior to such a half plane.

## Main definitions

* `IntegralLattice.thetaTerm`, `IntegralLattice.theta`.

## Main results

* `IntegralLattice.summable_exp_neg_mul_normSq` — the Gaussian sum over a positive definite
  lattice converges.
* `IntegralLattice.summable_thetaTerm` — hence so does the theta series, for `Im τ > 0`.
* `IntegralLattice.theta_differentiableOn`, `IntegralLattice.theta_holomorphic`.

## References

Ebeling, *Lattices and Codes*, §2.1 and §2.4 (Lemma 2.2).
-/

namespace IntegralLattice

variable {Γ : IntegralLattice}

/-- `exp (-x) ≤ k! / xᵏ` for `x > 0`: the `k`-th term of the exponential series bounds `exp`
from below.  This is the explicit, asymptotics-free form of "the exponential beats every
polynomial". -/
theorem exp_neg_le_factorial_div_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (k.factorial : ℝ) / x ^ k :=
  Real.exp_neg_le_factorial_div_pow k hx

/-! ### Convergence of the theta series -/

theorem norm_sq_toEuclidean (h : Γ.IsPosDef) (x : Γ) :
    ‖Γ.toEuclidean h x‖ ^ 2 = ((normSq x : ℤ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  exact Γ.inner_toEuclidean h x x

theorem finrank_range_toEuclidean (h : Γ.IsPosDef) :
    Module.finrank ℤ (LinearMap.range (Γ.toEuclidean h)) = Γ.rank := by
  rw [Module.finrank_eq_card_basis (Γ.rangeBasis h), Fintype.card_fin]

/-- **Ebeling, Lemma 2.2** (the convergence behind the theta function). For a positive definite
lattice the Gaussian sum `∑_{x ∈ Γ} exp (-a·x²)` converges for every `a > 0`.

The proof is asymptotics-free: `exp (-x) ≤ k!/xᵏ` (`exp_neg_le_factorial_div_pow`) turns the
Gaussian into a majorant `C·‖z‖^{-2k}`, and `ZLattice.summable_norm_rpow` sums that once
`2k > n`. The only lattice input is that `toEuclidean` is an injective isometry onto a
`ZLattice` of the right rank. -/
theorem summable_exp_neg_mul_normSq (h : Γ.IsPosDef) {a : ℝ} (ha : 0 < a) :
    Summable (fun x : Γ => Real.exp (-(a * ((normSq x : ℤ) : ℝ)))) := by
  classical
  have : DiscreteTopology (LinearMap.range (Γ.toEuclidean h)) :=
    Γ.discreteTopology_range_toEuclidean h
  set L := LinearMap.range (Γ.toEuclidean h) with hL
  set e : Γ ≃ₗ[ℤ] L := LinearEquiv.ofInjective (Γ.toEuclidean h) (Γ.toEuclidean_injective h)
    with he
  have hnorm : ∀ x : Γ, ‖e x‖ ^ 2 = ((normSq x : ℤ) : ℝ) := fun x => Γ.norm_sq_toEuclidean h x
  have hFG : (fun x : Γ => Real.exp (-(a * ((normSq x : ℤ) : ℝ))))
      = (fun z : L => Real.exp (-(a * ‖z‖ ^ 2))) ∘ e.toEquiv := by
    funext x
    show Real.exp (-(a * ((normSq x : ℤ) : ℝ))) = Real.exp (-(a * ‖e x‖ ^ 2))
    rw [hnorm x]
  rw [hFG, Equiv.summable_iff e.toEquiv]
  set k : ℕ := Γ.rank + 1 with hk
  set r : ℝ := -((2 * k : ℕ) : ℝ) with hr
  have hrlt : r < -(Module.finrank ℤ L : ℝ) := by
    rw [hr, Γ.finrank_range_toEuclidean h, hk]
    push_cast
    have : (0 : ℝ) ≤ (Γ.rank : ℝ) := Nat.cast_nonneg _
    linarith
  set C : ℝ := (k.factorial : ℝ) / a ^ k with hC
  have hmaj : Summable (fun z : L => C * ‖z‖ ^ r) :=
    Summable.mul_left C (ZLattice.summable_norm_rpow L r hrlt)
  refine Summable.of_norm_bounded_eventually hmaj ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with z hz
  have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hxpos : (0 : ℝ) < a * ‖z‖ ^ 2 := by positivity
  have hbound := exp_neg_le_factorial_div_pow k hxpos
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine hbound.trans (le_of_eq ?_)
  have hrp : ‖z‖ ^ r = ((‖z‖ ^ 2) ^ k)⁻¹ := by
    rw [hr, Real.rpow_neg hpos.le, Real.rpow_natCast, pow_mul]
  rw [hC, hrp, mul_pow]
  field_simp

/-! ### The theta function -/

/-- The exponent of the theta series, `π i τ x²`. -/
noncomputable def thetaTerm (Γ : IntegralLattice) (x : Γ) (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((normSq x : ℤ) : ℂ))

theorem norm_thetaTerm (x : Γ) (τ : ℂ) :
    ‖Γ.thetaTerm x τ‖ = Real.exp (-(Real.pi * τ.im * ((normSq x : ℤ) : ℝ))) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
  ring

theorem differentiable_thetaTerm (x : Γ) : Differentiable ℂ (Γ.thetaTerm x) := by
  unfold thetaTerm
  fun_prop

/-- The theta series is summable on the open upper half plane. -/
theorem summable_thetaTerm (h : Γ.IsPosDef) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun x : Γ => Γ.thetaTerm x τ) := by
  refine Summable.of_norm ?_
  have hpi : 0 < Real.pi * τ.im := by positivity
  refine (Γ.summable_exp_neg_mul_normSq h hpi).congr fun x => ?_
  rw [norm_thetaTerm]

/-- The **theta function** of a positive definite lattice, `ϑ_Γ(τ) = ∑_{x ∈ Γ} q^{x²/2}` with
`q = e^{2πiτ}`. Ebeling §2.1. -/
noncomputable def theta (Γ : IntegralLattice) (τ : ℂ) : ℂ := ∑' x : Γ, Γ.thetaTerm x τ

/-- **Ebeling, Lemma 2.2.** On each half plane `Im τ > v > 0` the theta series is bounded by a
summable series, so its sum is holomorphic there. -/
theorem theta_differentiableOn (h : Γ.IsPosDef) {v : ℝ} (hv : 0 < v) :
    DifferentiableOn ℂ Γ.theta {τ : ℂ | v < τ.im} := by
  have hpi : 0 < Real.pi * v := by positivity
  refine Complex.differentiableOn_tsum_of_summable_norm (u := fun x : Γ =>
      Real.exp (-(Real.pi * v * ((normSq x : ℤ) : ℝ))))
    ((Γ.summable_exp_neg_mul_normSq h hpi).congr fun x => rfl)
    (fun x => (Γ.differentiable_thetaTerm x).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_im) ?_
  intro x τ hτ
  have hvτ : v < τ.im := hτ
  have hnn : (0 : ℝ) ≤ ((normSq x : ℤ) : ℝ) := by
    exact_mod_cast h.normSq_nonneg x
  rw [norm_thetaTerm]
  refine Real.exp_le_exp.mpr ?_
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : Real.pi * v * ((normSq x : ℤ) : ℝ)
      ≤ Real.pi * τ.im * ((normSq x : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvτ.le hp.le) hnn
  linarith

/-- **The theta function is holomorphic on the upper half plane.** -/
theorem theta_holomorphic (h : Γ.IsPosDef) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ Γ.theta τ := by
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmem : τ ∈ {z : ℂ | τ.im / 2 < z.im} := by
    show τ.im / 2 < τ.im
    linarith
  exact ((Γ.theta_differentiableOn h (by linarith : (0:ℝ) < τ.im / 2)).differentiableAt
    (hopen.mem_nhds hmem))

end IntegralLattice
