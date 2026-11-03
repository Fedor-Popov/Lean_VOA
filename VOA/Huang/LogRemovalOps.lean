/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LogRemovalCoeff

/-!
# Operations on log-expansion coefficients

The coefficient argument (`AssocCoeffRules`) transfers identities among products
of intertwining operators — with coefficients `u^{ν}`, convergent power series `c(u)` and the
derivative `d/dt = u d/du` — to identities among their expansion coefficients.  This file provides
the three transfer rules, VOA-free, at the level of `LogExp` and of `logCoeff`.

## Main results
* Monomials: `LogExp.shift`, `eval_shift` (`e^{νt}·F`), `coeff_shift`
  (`coeff (μ + ν) = coeff μ`); `logCoeff_exp_mul`.
* Power series: `exCoeff_psMul` (Cauchy product, `finsum` form), `LogExp.psMul`, `eval_psMul`,
  `coeff_psMul`; `logCoeff_psEval_mul`.
* Derivative: `exCoeff_thetaL` (`μ·c(μ,k) + (k+1)·c(μ,k+1)`), `LogExp.theta`,
  `hasDerivAt_eval`, `coeff_theta`; `logCoeff_deriv`.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.LogRemovalCoeff

open VOA.Huang.FrobeniusLog Polynomial Filter Topology
open scoped BigOperators

/-! ## Monomials `e^{νt}` -/

theorem logFun_exp_mul (lam ν : ℂ) (p : ℕ → ℂ[X]) (t : ℂ) :
    Complex.exp (ν * t) * logFun lam p t = logFun (lam + ν) p t := by
  rw [logFun, logFun, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem exCoeff_add_left (lam ν : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff (lam + ν) p (μ + ν) k = exCoeff lam p μ k := by
  by_cases h : ∃ n : ℕ, lam + n = μ
  · obtain ⟨n, rfl⟩ := h
    rw [show lam + (n : ℂ) + ν = lam + ν + n by ring, exCoeff_of_eq, exCoeff_of_eq]
  · rw [exCoeff_of_forall_ne (fun n hn => h ⟨n, by linear_combination hn⟩),
      exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩)]

namespace LogExp

/-- `e^{νt} · E`. -/
def shift (ν : ℂ) (E : LogExp) : LogExp where
  ι := E.ι
  lam := fun j => E.lam j + ν
  p := E.p
  good := E.good

theorem eval_shift (ν : ℂ) (E : LogExp) (t : ℂ) :
    (E.shift ν).eval t = Complex.exp (ν * t) * E.eval t := by
  simp only [eval, shift, Finset.mul_sum, logFun_exp_mul]
  rfl

/-- Multiplication by `u^ν` shifts the coefficients by `ν`. -/
theorem coeff_shift (ν : ℂ) (E : LogExp) (μ : ℂ) (k : ℕ) :
    (E.shift ν).coeff (μ + ν) k = E.coeff μ k := by
  simp only [coeff, shift, exCoeff_add_left]
  rfl

end LogExp

/-! ## Power series `c(e^t)` -/

theorem hasFiniteSupport_exCoeff_sub (lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    (Function.support fun m : ℕ => exCoeff lam p (μ - m) k).Finite := by
  by_cases h : ∃ N : ℕ, lam + N = μ
  · obtain ⟨N, rfl⟩ := h
    refine (Finset.range (N + 1)).finite_toSet.subset fun m hm => ?_
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hm (exCoeff_of_forall_ne (fun n hn => by
      have : ((n + m : ℕ) : ℂ) = N := by push_cast; linear_combination hn
      have := Nat.cast_injective this
      omega) _ _)
  · have : (Function.support fun m : ℕ => exCoeff lam p (μ - m) k) = ∅ := by
      ext m
      simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
      exact exCoeff_of_forall_ne (fun n hn => h ⟨n + m, by push_cast; linear_combination hn⟩) _ _
    rw [this]; exact Set.finite_empty

/-- **Cauchy product**: the coefficients of `c(y) · y^λ Σ yⁿ pₙ(log y)`. -/
theorem exCoeff_psMul (c : PowerSeries ℂ) (lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (psMul c p) μ k = ∑ᶠ m : ℕ, PowerSeries.coeff m c * exCoeff lam p (μ - m) k := by
  by_cases h : ∃ N : ℕ, lam + N = μ
  · obtain ⟨N, rfl⟩ := h
    rw [exCoeff_of_eq]
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))]
    · simp only [psMul, finsetSum_coeff, coeff_smul, smul_eq_mul]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' : m < N + 1 := Finset.mem_range.mp hm
      have e0 : N + 1 - 1 - m = N - m := by omega
      have e : lam + (N : ℂ) - (m : ℂ) = lam + ((N - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [e0, e, exCoeff_of_eq, show N - (N - m) = m by omega]
    · intro m hm
      simp only [Function.mem_support] at hm
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      exact hm (by
        rw [exCoeff_of_forall_ne (fun n hn => by
          have : ((n + m : ℕ) : ℂ) = N := by push_cast; linear_combination hn
          have := Nat.cast_injective this
          omega) _ _, mul_zero])
  · rw [exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩)]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [exCoeff_of_forall_ne (fun n hn => h ⟨n + m, by push_cast; linear_combination hn⟩),
      mul_zero]

namespace LogExp

/-- `c(e^t) · E`. -/
noncomputable def psMul (c : PowerSeries ℂ) (hc : c ∈ SubexpPS) (E : LogExp) : LogExp where
  ι := E.ι
  lam := E.lam
  p := fun j => FrobeniusLog.psMul c (E.p j)
  good := fun j => (E.good j).psMul hc

theorem eval_psMul (c : PowerSeries ℂ) (hc : c ∈ SubexpPS) (E : LogExp) {t : ℂ}
    (ht : t ∈ halfPlane) : (E.psMul c hc).eval t = psEval c (Complex.exp t) * E.eval t := by
  simp only [eval, psMul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (logFun_psMul (E.good j) hc _ ht).symm

/-- Multiplication by `c(u)` is the Cauchy product on coefficients. -/
theorem coeff_psMul (c : PowerSeries ℂ) (hc : c ∈ SubexpPS) (E : LogExp) (μ : ℂ) (k : ℕ) :
    (E.psMul c hc).coeff μ k = ∑ᶠ m : ℕ, PowerSeries.coeff m c * E.coeff (μ - m) k := by
  simp only [coeff, psMul, exCoeff_psMul, Finset.mul_sum]
  exact (finsum_sum_comm _ _ fun j _ => (hasFiniteSupport_exCoeff_sub _ _ _ _).subset
    (Function.support_mul_subset_right _ _)).symm

end LogExp

/-! ## The derivative `d/dt` -/

/-- The coefficients of `θ_λ p` (`d/dt` of `logFun λ p`). -/
theorem exCoeff_thetaL (lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (thetaL lam p) μ k
      = μ * exCoeff lam p μ k + ((k : ℂ) + 1) * exCoeff lam p μ (k + 1) := by
  by_cases h : ∃ n : ℕ, lam + n = μ
  · obtain ⟨n, rfl⟩ := h
    rw [exCoeff_of_eq, exCoeff_of_eq, exCoeff_of_eq]
    simp only [thetaL, dOp_X_add_C_apply, coeff_add, coeff_smul, coeff_derivative, smul_eq_mul]
    ring
  · rw [exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩), exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩),
      exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩)]
    ring

namespace LogExp

/-- `d/dt E`. -/
noncomputable def theta (E : LogExp) : LogExp where
  ι := E.ι
  lam := E.lam
  p := fun j => thetaL (E.lam j) (E.p j)
  good := fun j => (E.good j).thetaL _

/-- Termwise differentiation of an expansion. -/
theorem hasDerivAt_eval (E : LogExp) {t : ℂ} (ht : t ∈ halfPlane) :
    HasDerivAt E.eval (E.theta.eval t) t := by
  have : HasDerivAt (fun t => ∑ j, logFun (E.lam j) (E.p j) t)
      (∑ j, logFun (E.lam j) (thetaL (E.lam j) (E.p j)) t) t :=
    HasDerivAt.fun_sum fun j _ => hasDerivAt_logFun (E.good j) (E.lam j) ht
  exact this

theorem coeff_theta (E : LogExp) (μ : ℂ) (k : ℕ) :
    E.theta.coeff μ k = μ * E.coeff μ k + ((k : ℂ) + 1) * E.coeff μ (k + 1) := by
  simp only [coeff, theta, exCoeff_thetaL, Finset.sum_add_distrib, Finset.mul_sum]
  rfl

end LogExp

/-! ## Function level -/

variable {U : Set ℂ}

/-- `logCoeff` of `e^{νt} F`. -/
theorem logCoeff_exp_mul (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} (hF : HasLogExp U F) (ν μ : ℂ) (k : ℕ) :
    logCoeff U (fun t => Complex.exp (ν * t) * F t) (μ + ν) k = logCoeff U F μ k := by
  obtain ⟨E, hE⟩ := hF
  have hS : IsExpOn U (fun t => Complex.exp (ν * t) * F t) (E.shift ν) :=
    fun t ht => by rw [LogExp.eval_shift, ← hE t ht]
  rw [logCoeff_eq hU hsub hne hS, logCoeff_eq hU hsub hne hE, LogExp.coeff_shift]

theorem hasLogExp_exp_mul {F : ℂ → ℂ} (hF : HasLogExp U F) (ν : ℂ) :
    HasLogExp U (fun t => Complex.exp (ν * t) * F t) := by
  obtain ⟨E, hE⟩ := hF
  exact ⟨E.shift ν, fun t ht => by rw [LogExp.eval_shift, ← hE t ht]⟩

/-- `logCoeff` of `c(e^t) F` (Cauchy product). -/
theorem logCoeff_psEval_mul (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} (hF : HasLogExp U F) {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) (μ : ℂ) (k : ℕ) :
    logCoeff U (fun t => psEval c (Complex.exp t) * F t) μ k
      = ∑ᶠ m : ℕ, PowerSeries.coeff m c * logCoeff U F (μ - m) k := by
  obtain ⟨E, hE⟩ := hF
  have hS : IsExpOn U (fun t => psEval c (Complex.exp t) * F t) (E.psMul c hc) :=
    fun t ht => by rw [LogExp.eval_psMul c hc E (hsub ht), ← hE t ht]
  rw [logCoeff_eq hU hsub hne hS, LogExp.coeff_psMul]
  simp only [logCoeff_eq hU hsub hne hE]

theorem hasLogExp_psEval_mul (hsub : U ⊆ halfPlane) {F : ℂ → ℂ} (hF : HasLogExp U F)
    {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) :
    HasLogExp U (fun t => psEval c (Complex.exp t) * F t) := by
  obtain ⟨E, hE⟩ := hF
  exact ⟨E.psMul c hc, fun t ht => by rw [LogExp.eval_psMul c hc E (hsub ht), ← hE t ht]⟩

/-- `logCoeff` of `d/dt F` on an open `U`. -/
theorem logCoeff_deriv (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} (hF : HasLogExp U F) (μ : ℂ) (k : ℕ) :
    HasLogExp U (_root_.deriv F) ∧
    logCoeff U (_root_.deriv F) μ k
      = μ * logCoeff U F μ k + ((k : ℂ) + 1) * logCoeff U F μ (k + 1) := by
  obtain ⟨E, hE⟩ := hF
  have hS : IsExpOn U (_root_.deriv F) E.theta := by
    intro t ht
    have hev : F =ᶠ[𝓝 t] E.eval :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun y hy => hE y hy
    rw [hev.deriv_eq]
    exact (E.hasDerivAt_eval (hsub ht)).deriv
  refine ⟨⟨E.theta, hS⟩, ?_⟩
  rw [logCoeff_eq hU hsub hne hS, logCoeff_eq hU hsub hne hE, logCoeff_eq hU hsub hne hE,
    LogExp.coeff_theta]

end VOA.Huang.LogRemovalCoeff
