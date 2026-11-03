/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FrobeniusLogConv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Frobenius theory with logarithms: the analytic functions

A formal log-solution `F = y^λ Σ_n yⁿ pₙ(log y)` (`FrobeniusLog.LogFuchsianEq`) becomes an honest
holomorphic function once one passes to the **universal cover of the punctured disc**: with
`y = e^t`, `Re t < 0`,

  `logFun λ p t = Σ_n e^{(λ+n)t} pₙ(t)`,

and `θ = y d/dy` becomes `d/dt`.  No branch of `log` and no analytic continuation in the punctured
disc is ever chosen: the half-plane `Re t < 0` is simply connected, and the monodromy around
`y = 0` is the translation `t ↦ t + 2πi` (used in `Huang/FrobeniusIndep.lean`).

## Main results

* `LogGood p`: bounded `ℓ`-degree and subexponential `ℓᵏ`-coefficients; closed under `thetaL`,
  `psMul` (by a subexponential series), sums, scalars, and degree-non-increasing linear maps
  (`LogGood.map`).  `logGood_of_logFuchsianEq`: every formal log-solution is `LogGood`
  (from `FrobeniusLogConv`).
* `logFun`, `summable_logFun_norm` (absolute convergence on `Re t < 0`), linearity
  (`logFun_add`, `logFun_smul`, `logFun_sum`, `logFun_zero`).
* `hasDerivAt_logFun`: `d/dt logFun λ p = logFun λ (θ_λ p)` on `Re t < 0`;
  `differentiableOn_logFun`, `iteratedDeriv_logFun`.
* `logFun_psMul`: multiplication by a convergent power series `c(e^t)` (`psEval`).
* `logFun_ode`: a formal log-solution of `θ^s F + Σ_{i<s} cᵢ θ^i F = 0` is an honest
  holomorphic solution of `F⁽ˢ⁾(t) + Σ_{i<s} cᵢ(e^t) F⁽ⁱ⁾(t) = 0` on `Re t < 0`.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.FrobeniusLog

open Polynomial Filter Topology
open scoped BigOperators

/-! ## Good log-series -/

/-- The left half-plane `Re t < 0`, the universal cover of the punctured unit disc via `y = e^t`. -/
def halfPlane : Set ℂ := {t | t.re < 0}

theorem isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt Complex.continuous_re continuous_const

theorem convex_halfPlane : Convex ℝ halfPlane := by
  intro x hx y hy a b ha hb hab
  simp only [halfPlane, Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simpa using hy
  · nlinarith [mul_lt_mul_of_pos_left hx ha']

theorem isPreconnected_halfPlane : IsPreconnected halfPlane :=
  convex_halfPlane.isPreconnected

/-- A log-series with bounded `ℓ`-degree and subexponential `ℓᵏ`-coefficients. -/
structure LogGood (p : ℕ → ℂ[X]) : Prop where
  deg : ∃ K : ℕ, ∀ n, (p n).natDegree ≤ K
  coeff : ∀ k, Subexponential fun n => ‖(p n).coeff k‖

/-- Every formal log-solution of a Fuchsian equation with convergent coefficients is good. -/
theorem logGood_of_logFuchsianEq {lam : ℂ} {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {p : ℕ → ℂ[X]} (h : LogFuchsianEq lam s c p) : LogGood p where
  deg := by
    classical
    set c' : ℕ → PowerSeries ℂ := fun i => if i < s then c i else 0
    exact exists_natDegree_bound hs ((logFuchsianEq_congr (c' := c')
      (fun i hi => by simp [c', hi])).mp h)
  coeff := subexponential_coeff_of_logFuchsianEq hs hc h

theorem LogGood.zero : LogGood (fun _ => (0 : ℂ[X])) where
  deg := ⟨0, fun _ => by simp⟩
  coeff := fun _ => Subexponential.of_le (fun _ => by simp) subexponential_zero

theorem LogGood.add {p q : ℕ → ℂ[X]} (hp : LogGood p) (hq : LogGood q) :
    LogGood (p + q) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    obtain ⟨L, hL⟩ := hq.deg
    exact ⟨max K L, fun n => le_trans (natDegree_add_le _ _)
      (max_le_max (hK n) (hL n))⟩
  coeff := fun k => Subexponential.of_le (fun n => by
    simp only [Pi.add_apply, coeff_add]; exact norm_add_le _ _) ((hp.coeff k).add (hq.coeff k))

theorem LogGood.smul {p : ℕ → ℂ[X]} (hp : LogGood p) (a : ℂ) : LogGood (a • p) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    exact ⟨K, fun n => le_trans (natDegree_smul_le _ _) (hK n)⟩
  coeff := fun k => Subexponential.of_le (fun n => by
    simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul]; exact le_rfl)
    ((hp.coeff k).const_mul (norm_nonneg a))

theorem LogGood.neg {p : ℕ → ℂ[X]} (hp : LogGood p) : LogGood (-p) := by
  have := hp.smul (-1)
  simpa using this

theorem LogGood.sub {p q : ℕ → ℂ[X]} (hp : LogGood p) (hq : LogGood q) : LogGood (p - q) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem LogGood.sum {ι : Type*} (S : Finset ι) {p : ι → ℕ → ℂ[X]} (hp : ∀ i ∈ S, LogGood (p i)) :
    LogGood (∑ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LogGood.zero
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

/-- The `ℓᵏ`-coefficient of `L q` for a linear map `L` and `deg q ≤ K`. -/
theorem coeff_map_eq_sum (L : ℂ[X] →ₗ[ℂ] ℂ[X]) {K : ℕ} {q : ℂ[X]} (hq : q.natDegree ≤ K) (k : ℕ) :
    (L q).coeff k = ∑ j ∈ Finset.range (K + 1), q.coeff j * (L (X ^ j)).coeff k := by
  conv_lhs => rw [q.as_sum_range' (K + 1) (by omega)]
  simp only [map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_X_eq_monomial, map_smul, coeff_smul, smul_eq_mul]

/-- **A degree-non-increasing linear map preserves goodness** (its matrix on `ℂ[ℓ]_{≤K}` is
bounded). -/
theorem LogGood.map {p : ℕ → ℂ[X]} (hp : LogGood p) (L : ℂ[X] →ₗ[ℂ] ℂ[X])
    (hL : ∀ q : ℂ[X], (L q).natDegree ≤ q.natDegree) : LogGood (fun n => L (p n)) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    exact ⟨K, fun n => le_trans (hL _) (hK n)⟩
  coeff := fun k => by
    obtain ⟨K, hK⟩ := hp.deg
    refine Subexponential.of_le (fun n => ?_) (Subexponential.finsetSum (Finset.range (K + 1))
      (fun j n => ‖(L (X ^ j)).coeff k‖ * ‖(p n).coeff j‖)
      fun j _ => (hp.coeff j).const_mul (norm_nonneg _))
    rw [coeff_map_eq_sum L (hK n) k]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, mul_comm]

/-- `dOp (X + C a) q = q' + a q`. -/
theorem dOp_X_add_C_apply (a : ℂ) (q : ℂ[X]) :
    dOp (X + Polynomial.C a) q = derivative q + a • q := by
  rw [dOp_add, LinearMap.add_apply]
  congr 1
  · simpa using dOp_X_pow_apply 1 q
  · simp [dOp, Module.algebraMap_end_eq_smul_id]

theorem LogGood.thetaL {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) :
    LogGood (FrobeniusLog.thetaL lam p) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    exact ⟨K, fun n => le_trans (natDegree_dOp_le _ _) (hK n)⟩
  coeff := fun k => by
    have h1 : Subexponential fun n => ‖(derivative (p n)).coeff k‖ := by
      have := (hp.map derivative
        (fun q => natDegree_derivative_le q |>.trans (Nat.sub_le _ _))).coeff k
      simpa using this
    have h2 : Subexponential fun n => (n : ℝ) ^ 1 * ‖(p n).coeff k‖ :=
      (hp.coeff k).mul_pow (fun _ => norm_nonneg _) 1
    refine Subexponential.of_le (fun n => ?_)
      ((h1.add ((hp.coeff k).const_mul (norm_nonneg lam))).add h2)
    simp only [FrobeniusLog.thetaL, dOp_X_add_C_apply, coeff_add, coeff_smul, smul_eq_mul]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, pow_one]
    have : ‖lam + (n : ℂ)‖ ≤ ‖lam‖ + n := by
      refine le_trans (norm_add_le _ _) ?_; simp
    nlinarith [norm_nonneg ((p n).coeff k)]

theorem LogGood.thetaL_iterate {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) (i : ℕ) :
    LogGood ((FrobeniusLog.thetaL lam)^[i] p) := by
  induction i with
  | zero => simpa using hp
  | succ i ih => rw [Function.iterate_succ_apply']; exact ih.thetaL lam

theorem LogGood.psMul {p : ℕ → ℂ[X]} (hp : LogGood p) {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) :
    LogGood (FrobeniusLog.psMul c p) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    refine ⟨K, fun n => ?_⟩
    refine natDegree_sum_le_of_forall_le _ _ fun m _ => ?_
    exact le_trans (natDegree_smul_le _ _) (hK m)
  coeff := fun k => by
    have := subexponential_cauchy (a := fun m => (p m).coeff k)
      (b := fun m => PowerSeries.coeff m c) (hp.coeff k) (mem_subexpPS.mp hc)
    refine Subexponential.of_le (fun n => le_of_eq ?_) this
    simp only [FrobeniusLog.psMul, finsetSum_coeff, coeff_smul, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-! ## Elementary bounds -/

/-- `|q(t)| ≤ Σ_{k ≤ K} |q_k| R^k` for `deg q ≤ K`, `‖t‖ ≤ R`. -/
theorem norm_eval_le {q : ℂ[X]} {K : ℕ} (hq : q.natDegree ≤ K) {t : ℂ} {R : ℝ} (ht : ‖t‖ ≤ R) :
    ‖q.eval t‖ ≤ ∑ k ∈ Finset.range (K + 1), ‖q.coeff k‖ * R ^ k := by
  rw [eval_eq_sum_range' (n := K + 1) (by omega)]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht k) (norm_nonneg _)

/-- `‖e^{(λ+n)t}‖ ≤ e^{‖λ‖R} (e^{Re t})ⁿ` for `‖t‖ ≤ R`. -/
theorem norm_exp_le (lam t : ℂ) (n : ℕ) {R : ℝ} (ht : ‖t‖ ≤ R) :
    ‖Complex.exp ((lam + n) * t)‖ ≤ Real.exp (‖lam‖ * R) * Real.exp t.re ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : ((lam + n) * t).re = (lam * t).re + n * t.re := by
    simp [add_mul, Complex.mul_re]
  rw [h1]
  have h2 : (lam * t).re ≤ ‖lam‖ * R := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  linarith

/-- The summable majorant: `ρⁿ Σ_{k ≤ K} |pₙ,ₖ| R^k`, `0 ≤ ρ < 1`. -/
theorem LogGood.summable_majorant {p : ℕ → ℂ[X]} (hp : LogGood p) (K : ℕ) (R : ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable fun n => ρ ^ n * ∑ k ∈ Finset.range (K + 1), ‖(p n).coeff k‖ * R ^ k := by
  simp_rw [Finset.mul_sum]
  refine summable_sum fun k _ => ?_
  have := (summable_of_subexponential (fun n => norm_nonneg _) (hp.coeff k) hρ0 hρ1).mul_right
    (R ^ k)
  refine this.congr fun n => ?_
  ring

/-! ## The functions -/

/-- `logFun λ p t = Σ_n e^{(λ+n)t} pₙ(t)`: the log-series `y^λ Σ yⁿ pₙ(log y)` on the universal
cover `y = e^t`. -/
noncomputable def logFun (lam : ℂ) (p : ℕ → ℂ[X]) (t : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp ((lam + n) * t) * (p n).eval t

/-- A local majorant for the terms of `logFun` on `‖t‖ ≤ R`, `Re t ≤ -δ`. -/
theorem norm_logTerm_le {p : ℕ → ℂ[X]} {K : ℕ} (hK : ∀ n, (p n).natDegree ≤ K) (lam : ℂ)
    {t : ℂ} {R δ : ℝ} (ht : ‖t‖ ≤ R) (htδ : t.re ≤ -δ) (n : ℕ) :
    ‖Complex.exp ((lam + n) * t) * (p n).eval t‖
      ≤ Real.exp (‖lam‖ * R) * (Real.exp (-δ) ^ n
          * ∑ k ∈ Finset.range (K + 1), ‖(p n).coeff k‖ * R ^ k) := by
  rw [norm_mul, ← mul_assoc]
  have hS : 0 ≤ ∑ k ∈ Finset.range (K + 1), ‖(p n).coeff k‖ * R ^ k :=
    le_trans (norm_nonneg _) (norm_eval_le (hK n) ht)
  refine mul_le_mul ?_ (norm_eval_le (hK n) ht) (norm_nonneg _) (by positivity)
  refine le_trans (norm_exp_le lam t n ht) ?_
  gcongr

/-- **Absolute convergence on `Re t < 0`.** -/
theorem summable_logFun_norm {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) {t : ℂ}
    (ht : t ∈ halfPlane) :
    Summable fun n : ℕ => ‖Complex.exp ((lam + n) * t) * (p n).eval t‖ := by
  obtain ⟨K, hK⟩ := hp.deg
  have hρ1 : Real.exp t.re < 1 := (Real.exp_lt_one_iff.mpr ht)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_logTerm_le hK lam le_rfl (le_of_eq (neg_neg t.re).symm) n) ?_
  exact ((hp.summable_majorant K ‖t‖ (Real.exp_pos _).le (by simpa using hρ1)).mul_left _)

theorem summable_logFun {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) {t : ℂ} (ht : t ∈ halfPlane) :
    Summable fun n : ℕ => Complex.exp ((lam + n) * t) * (p n).eval t :=
  (summable_logFun_norm hp lam ht).of_norm

theorem logFun_add {p q : ℕ → ℂ[X]} (hp : LogGood p) (hq : LogGood q) (lam : ℂ) {t : ℂ}
    (ht : t ∈ halfPlane) : logFun lam (p + q) t = logFun lam p t + logFun lam q t := by
  rw [logFun, logFun, logFun, ← (summable_logFun hp lam ht).tsum_add (summable_logFun hq lam ht)]
  refine tsum_congr fun n => ?_
  simp [mul_add]

theorem logFun_smul (a : ℂ) (p : ℕ → ℂ[X]) (lam t : ℂ) :
    logFun lam (a • p) t = a * logFun lam p t := by
  rw [logFun, logFun, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [Pi.smul_apply, eval_smul, smul_eq_mul]
  ring

theorem logFun_zero (lam t : ℂ) : logFun lam (fun _ => 0) t = 0 := by
  simp [logFun]

theorem logFun_zero' (lam t : ℂ) : logFun lam 0 t = 0 := logFun_zero lam t

theorem logFun_neg (p : ℕ → ℂ[X]) (lam t : ℂ) : logFun lam (-p) t = -logFun lam p t := by
  have := logFun_smul (-1) p lam t
  simpa using this

theorem logFun_sub {p q : ℕ → ℂ[X]} (hp : LogGood p) (hq : LogGood q) (lam : ℂ) {t : ℂ}
    (ht : t ∈ halfPlane) : logFun lam (p - q) t = logFun lam p t - logFun lam q t := by
  rw [sub_eq_add_neg, logFun_add hp hq.neg lam ht, logFun_neg, ← sub_eq_add_neg]

theorem logFun_sum {ι : Type*} (S : Finset ι) {p : ι → ℕ → ℂ[X]} (hp : ∀ i ∈ S, LogGood (p i))
    (lam : ℂ) {t : ℂ} (ht : t ∈ halfPlane) :
    logFun lam (∑ i ∈ S, p i) t = ∑ i ∈ S, logFun lam (p i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using logFun_zero lam t
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      logFun_add (hp i (Finset.mem_insert_self _ _))
        (LogGood.sum S fun j hj => hp j (Finset.mem_insert_of_mem hj)) lam ht,
      ih fun j hj => hp j (Finset.mem_insert_of_mem hj)]

theorem logFun_congr {p q : ℕ → ℂ[X]} (h : ∀ n, p n = q n) (lam t : ℂ) :
    logFun lam p t = logFun lam q t := by
  rw [funext h]

/-! ## Differentiation -/

/-- The derivative of one term: `d/dt (e^{(λ+n)t} q(t)) = e^{(λ+n)t} ((λ+n) q + q')(t)`. -/
theorem hasDerivAt_logTerm (lam : ℂ) (n : ℕ) (q : ℂ[X]) (t : ℂ) :
    HasDerivAt (fun t => Complex.exp ((lam + n) * t) * q.eval t)
      (Complex.exp ((lam + n) * t) * (dOp (X + Polynomial.C (lam + n)) q).eval t) t := by
  have h1 : HasDerivAt (fun t => Complex.exp ((lam + n) * t))
      (Complex.exp ((lam + n) * t) * (lam + n)) t := by
    have := ((hasDerivAt_id t).const_mul (lam + n)).cexp
    simpa using this
  have h2 := h1.mul (q.hasDerivAt t)
  convert h2 using 1
  rw [dOp_X_add_C_apply, eval_add, eval_smul, smul_eq_mul]
  ring

/-- **Termwise differentiation**: `d/dt logFun λ p = logFun λ (θ_λ p)` on `Re t < 0`. -/
theorem hasDerivAt_logFun {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) {t : ℂ}
    (ht : t ∈ halfPlane) :
    HasDerivAt (logFun lam p) (logFun lam (FrobeniusLog.thetaL lam p) t) t := by
  have ht' : t.re < 0 := ht
  set δ : ℝ := -t.re / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set R : ℝ := ‖t‖ + δ with hR
  obtain ⟨K, hK⟩ := (hp.thetaL lam).deg
  set u : ℕ → ℝ := fun n => Real.exp (‖lam‖ * R) * (Real.exp (-δ) ^ n
    * ∑ k ∈ Finset.range (K + 1), ‖(FrobeniusLog.thetaL lam p n).coeff k‖ * R ^ k) with hu
  have hus : Summable u := ((hp.thetaL lam).summable_majorant K R (Real.exp_pos _).le
    ((Real.exp_lt_one_iff.mpr (by linarith)))).mul_left _
  have hball : ∀ y ∈ Metric.ball t δ, ‖y‖ ≤ R ∧ y.re ≤ -δ := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine ⟨?_, ?_⟩
    · have := norm_le_norm_add_norm_sub' y t
      rw [hR]; linarith [norm_sub_rev y t]
    · have h1 : |(y - t).re| ≤ ‖y - t‖ := Complex.abs_re_le_norm _
      have h2 : (y - t).re = y.re - t.re := by simp
      rw [h2] at h1
      have := (abs_le.mp h1).2
      rw [hδ] at hy ⊢; linarith
  have key := hasDerivAt_tsum_of_isPreconnected (u := u) (g := fun n t =>
      Complex.exp ((lam + n) * t) * (p n).eval t)
    (g' := fun n t => Complex.exp ((lam + n) * t) * (FrobeniusLog.thetaL lam p n).eval t)
    (t := Metric.ball t δ) (y₀ := t) hus Metric.isOpen_ball (convex_ball t δ).isPreconnected
    (fun n y _ => hasDerivAt_logTerm lam n (p n) y)
    (fun n y hy => norm_logTerm_le hK lam (hball y hy).1 (hball y hy).2 n)
    (Metric.mem_ball_self hδ0) (summable_logFun hp lam ht) (Metric.mem_ball_self hδ0)
  exact key

theorem differentiableOn_logFun {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) :
    DifferentiableOn ℂ (logFun lam p) halfPlane :=
  fun _ ht => (hasDerivAt_logFun hp lam ht).differentiableAt.differentiableWithinAt

theorem deriv_logFun {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) {t : ℂ} (ht : t ∈ halfPlane) :
    _root_.deriv (logFun lam p) t = logFun lam (FrobeniusLog.thetaL lam p) t :=
  (hasDerivAt_logFun hp lam ht).deriv

/-- `F⁽ⁱ⁾ = logFun λ (θ_λ^i p)` on `Re t < 0`. -/
theorem iteratedDeriv_logFun {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) (i : ℕ) {t : ℂ}
    (ht : t ∈ halfPlane) :
    iteratedDeriv i (logFun lam p) t = logFun lam ((FrobeniusLog.thetaL lam)^[i] p) t := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv i (logFun lam p) =ᶠ[𝓝 t]
        logFun lam ((FrobeniusLog.thetaL lam)^[i] p) :=
      Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds ht) fun y hy => ih hy
    rw [hev.deriv_eq, deriv_logFun (hp.thetaL_iterate lam i) lam ht]

/-! ## Multiplication by a convergent power series -/

/-- The value `c(y) = Σ cₙ yⁿ` of a power series. -/
noncomputable def psEval (c : PowerSeries ℂ) (y : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n c * y ^ n

theorem norm_exp_pow (t : ℂ) (n : ℕ) : ‖Complex.exp t ^ n‖ = Real.exp t.re ^ n := by
  rw [norm_pow, Complex.norm_exp]

theorem summable_psEval_norm {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) {t : ℂ}
    (ht : t ∈ halfPlane) :
    Summable fun n => ‖PowerSeries.coeff n c * Complex.exp t ^ n‖ := by
  have := summable_of_subexponential (fun n => norm_nonneg _) (mem_subexpPS.mp hc)
    (Real.exp_pos t.re).le ((Real.exp_lt_one_iff.mpr ht))
  refine this.congr fun n => ?_
  rw [norm_mul, norm_exp_pow]

/-- **Multiplication by `c(e^t)`** is `psMul c` on log-series. -/
theorem logFun_psMul {p : ℕ → ℂ[X]} (hp : LogGood p) {c : PowerSeries ℂ} (hc : c ∈ SubexpPS)
    (lam : ℂ) {t : ℂ} (ht : t ∈ halfPlane) :
    psEval c (Complex.exp t) * logFun lam p t = logFun lam (FrobeniusLog.psMul c p) t := by
  rw [psEval, logFun, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_psEval_norm hc ht) (summable_logFun_norm hp lam ht), logFun]
  refine tsum_congr fun n => ?_
  simp only [FrobeniusLog.psMul, eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m < n + 1 := Finset.mem_range.mp hm
  have e1 : n + 1 - 1 - m = n - m := by omega
  have e2 : n - (n - m) = m := by omega
  rw [e1, e2]
  have hexp : Complex.exp t ^ (n - m) * Complex.exp ((lam + (m : ℕ)) * t)
      = Complex.exp ((lam + (n : ℕ)) * t) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have : ((n - m : ℕ) : ℂ) = (n : ℂ) - m := by rw [Nat.cast_sub (by omega)]
    rw [this]; ring
  calc PowerSeries.coeff (n - m) c * Complex.exp t ^ (n - m)
        * (Complex.exp ((lam + (m : ℕ)) * t) * (p m).eval t)
      = (Complex.exp t ^ (n - m) * Complex.exp ((lam + (m : ℕ)) * t))
        * (PowerSeries.coeff (n - m) c * (p m).eval t) := by ring
    _ = _ := by rw [hexp]

/-- `c(e^t)` is itself a `logFun` (exponent `0`, constant polynomials), hence holomorphic. -/
theorem psEval_exp_eq_logFun (c : PowerSeries ℂ) (t : ℂ) :
    psEval c (Complex.exp t) = logFun 0 (fun n => Polynomial.C (PowerSeries.coeff n c)) t := by
  rw [psEval, logFun]
  refine tsum_congr fun n => ?_
  rw [eval_C, zero_add, ← Complex.exp_nat_mul, mul_comm]

theorem logGood_const {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) :
    LogGood (fun n => Polynomial.C (PowerSeries.coeff n c)) where
  deg := ⟨0, fun n => by simp⟩
  coeff := fun k => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using mem_subexpPS.mp hc
    · refine Subexponential.of_le (fun n => ?_) subexponential_zero
      rw [coeff_C, if_neg (by omega)]; simp

theorem differentiableOn_psEval_exp {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) :
    DifferentiableOn ℂ (fun t => psEval c (Complex.exp t)) halfPlane := by
  have := differentiableOn_logFun (logGood_const hc) 0
  refine this.congr fun t _ => ?_
  exact psEval_exp_eq_logFun c t

/-! ## Formal solutions are honest solutions -/

/-- **A formal log-solution is an honest holomorphic solution** of
`F⁽ˢ⁾(t) + Σ_{i<s} cᵢ(e^t) F⁽ⁱ⁾(t) = 0` on `Re t < 0` (`y = e^t`, `θ = d/dt`). -/
theorem logFun_ode {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ} (hc : ∀ i < s, c i ∈ SubexpPS)
    {p : ℕ → ℂ[X]} (hp : LogGood p) (h : LogFuchsianEq lam s c p) {t : ℂ} (ht : t ∈ halfPlane) :
    iteratedDeriv s (logFun lam p) t
      + ∑ i ∈ Finset.range s, psEval (c i) (Complex.exp t) * iteratedDeriv i (logFun lam p) t
      = 0 := by
  have hsum : ∀ i ∈ Finset.range s,
      psEval (c i) (Complex.exp t) * iteratedDeriv i (logFun lam p) t
        = logFun lam (FrobeniusLog.psMul (c i) ((FrobeniusLog.thetaL lam)^[i] p)) t := by
    intro i hi
    rw [iteratedDeriv_logFun hp lam i ht,
      logFun_psMul (hp.thetaL_iterate lam i) (hc i (Finset.mem_range.mp hi)) lam ht]
  have hgood : ∀ i ∈ Finset.range s,
      LogGood (FrobeniusLog.psMul (c i) ((FrobeniusLog.thetaL lam)^[i] p)) :=
    fun i hi => (hp.thetaL_iterate lam i).psMul (hc i (Finset.mem_range.mp hi))
  rw [Finset.sum_congr rfl hsum, iteratedDeriv_logFun hp lam s ht,
    ← logFun_sum _ hgood lam ht,
    ← logFun_add (hp.thetaL_iterate lam s) (LogGood.sum _ hgood) lam ht]
  have h0 : (FrobeniusLog.thetaL lam)^[s] p
      + ∑ i ∈ Finset.range s, FrobeniusLog.psMul (c i) ((FrobeniusLog.thetaL lam)^[i] p) = 0 := by
    funext n
    simpa [Finset.sum_apply] using h n
  rw [h0]
  exact logFun_zero' lam t

end VOA.Huang.FrobeniusLog
