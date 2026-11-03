/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Uniqueness for linear holomorphic ODEs

For a linear ODE `F⁽ˢ⁾ + Σ_{i<s} aᵢ F⁽ⁱ⁾ = 0` with coefficients holomorphic on a connected open set
`U ⊆ ℂ`, a holomorphic solution whose `(s−1)`-jet vanishes at one point of `U` vanishes on `U`
(`eqOn_zero_of_ode`).  Hence the jet map `F ↦ (F(t₀), …, F⁽ˢ⁻¹⁾(t₀))` is injective on solutions:
the solution space has dimension `≤ s`.

Method: differentiating the equation expresses every `F⁽ˢ⁺ᵐ⁾` as a holomorphic combination of
`F, …, F⁽ˢ⁻¹⁾` (`exists_higher_deriv_eq`), so the whole Taylor series at `t₀` vanishes; then the
identity theorem.  No Picard iteration, no Grönwall.

## Main results
* `differentiableOn_iteratedDeriv`, `iteratedDeriv_add_on`, `iteratedDeriv_const_mul_on`,
  `iteratedDeriv_sum_on` (linearity of `iteratedDeriv` on an open set).
* `exists_higher_deriv_eq`, `eqOn_zero_of_ode`, `eqOn_of_ode`.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.FrobeniusLog

open Filter Topology
open scoped BigOperators

variable {U : Set ℂ}

theorem differentiableOn_iteratedDeriv (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (i : ℕ) : DifferentiableOn ℂ (iteratedDeriv i F) U := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem hasDerivAt_iteratedDeriv (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (i : ℕ) {t : ℂ} (ht : t ∈ U) :
    HasDerivAt (iteratedDeriv i F) (iteratedDeriv (i + 1) F t) t := by
  rw [iteratedDeriv_succ]
  exact ((differentiableOn_iteratedDeriv hU hF i).differentiableAt
    (hU.mem_nhds ht)).hasDerivAt

/-- `iteratedDeriv` commutes with finite linear combinations on an open set. -/
theorem iteratedDeriv_sum_on (hU : IsOpen U) {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    {F : ι → ℂ → ℂ} (hF : ∀ j ∈ S, DifferentiableOn ℂ (F j) U) (i : ℕ) {t : ℂ} (ht : t ∈ U) :
    iteratedDeriv i (fun t => ∑ j ∈ S, a j * F j t) t
      = ∑ j ∈ S, a j * iteratedDeriv i (F j) t := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    have hev : iteratedDeriv i (fun t => ∑ j ∈ S, a j * F j t)
        =ᶠ[𝓝 t] fun t => ∑ j ∈ S, a j * iteratedDeriv i (F j) t :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun y hy => ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd : HasDerivAt (fun t => ∑ j ∈ S, a j * iteratedDeriv i (F j) t)
        (∑ j ∈ S, a j * iteratedDeriv (i + 1) (F j) t) t :=
      HasDerivAt.fun_sum fun j hj => (hasDerivAt_iteratedDeriv hU (hF j hj) i ht).const_mul (a j)
    exact hd.deriv

theorem iteratedDeriv_sub_on (hU : IsOpen U) {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U) (i : ℕ) {t : ℂ} (ht : t ∈ U) :
    iteratedDeriv i (fun t => F t - G t) t = iteratedDeriv i F t - iteratedDeriv i G t := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    have hev : iteratedDeriv i (fun t => F t - G t)
        =ᶠ[𝓝 t] fun t => iteratedDeriv i F t - iteratedDeriv i G t :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun y hy => ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact ((hasDerivAt_iteratedDeriv hU hF i ht).sub (hasDerivAt_iteratedDeriv hU hG i ht)).deriv

variable {s : ℕ} {a : ℕ → ℂ → ℂ} {F : ℂ → ℂ}

/-- Differentiating the equation: every `F⁽ˢ⁺ᵐ⁾` is a holomorphic combination of `F⁽ⁱ⁾`, `i < s`. -/
theorem exists_higher_deriv_eq (hU : IsOpen U) (hs : 1 ≤ s)
    (ha : ∀ i < s, DifferentiableOn ℂ (a i) U) (hF : DifferentiableOn ℂ F U)
    (hode : ∀ t ∈ U, iteratedDeriv s F t
      + ∑ i ∈ Finset.range s, a i t * iteratedDeriv i F t = 0) (m : ℕ) :
    ∃ b : ℕ → ℂ → ℂ, (∀ i < s, DifferentiableOn ℂ (b i) U) ∧
      ∀ t ∈ U, iteratedDeriv (s + m) F t = ∑ i ∈ Finset.range s, b i t * iteratedDeriv i F t := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  induction m with
  | zero =>
    refine ⟨fun i t => -a i t, fun i hi => (ha i hi).neg, fun t ht => ?_⟩
    have := hode t ht
    simp only [add_zero, neg_mul, Finset.sum_neg_distrib]
    linear_combination this
  | succ m ih =>
    obtain ⟨b, hb, hbeq⟩ := ih
    set D : ℕ → ℂ → ℂ := fun i => iteratedDeriv i F with hD
    refine ⟨fun i t => _root_.deriv (b i) t + (if i = 0 then 0 else b (i - 1) t)
      - b s' t * a i t, fun i hi => ?_, fun t ht => ?_⟩
    · refine (((hb i hi).deriv hU).add ?_).sub ((hb s' (by omega)).mul (ha i hi))
      by_cases h0 : i = 0
      · simp only [h0, ↓reduceIte]; exact differentiableOn_const 0
      · simp only [h0, ↓reduceIte]; exact hb (i - 1) (by omega)
    · have hev : iteratedDeriv (s' + 1 + m) F
          =ᶠ[𝓝 t] fun t => ∑ i ∈ Finset.range (s' + 1), b i t * iteratedDeriv i F t :=
        Filter.eventually_of_mem (hU.mem_nhds ht) fun y hy => hbeq y hy
      have hder : HasDerivAt (fun t => ∑ i ∈ Finset.range (s' + 1), b i t * iteratedDeriv i F t)
          (∑ i ∈ Finset.range (s' + 1), (_root_.deriv (b i) t * iteratedDeriv i F t
            + b i t * iteratedDeriv (i + 1) F t)) t := by
        refine HasDerivAt.fun_sum fun i hi => ?_
        have h1 : HasDerivAt (b i) (_root_.deriv (b i) t) t :=
          ((hb i (Finset.mem_range.mp hi)).differentiableAt (hU.mem_nhds ht)).hasDerivAt
        exact h1.mul (hasDerivAt_iteratedDeriv hU hF i ht)
      rw [show s' + 1 + (m + 1) = (s' + 1 + m) + 1 by omega, iteratedDeriv_succ, hev.deriv_eq,
        hder.deriv]
      have hs1 := hode t ht
      rw [Finset.sum_add_distrib,
        Finset.sum_range_succ (fun i => b i t * iteratedDeriv (i + 1) F t)]
      simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ'
        (fun i => (if i = 0 then 0 else b (i - 1) t) * iteratedDeriv i F t)]
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, zero_mul, add_zero]
      have e : ∑ i ∈ Finset.range (s' + 1), b s' t * a i t * iteratedDeriv i F t
          = b s' t * ∑ i ∈ Finset.range (s' + 1), a i t * iteratedDeriv i F t := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      linear_combination (b s' t) * hs1

/-- **Uniqueness**: a holomorphic solution of a linear holomorphic ODE on a connected open set
whose `(s−1)`-jet vanishes at one point vanishes identically. -/
theorem eqOn_zero_of_ode (hU : IsOpen U) (hUc : IsPreconnected U)
    (ha : ∀ i < s, DifferentiableOn ℂ (a i) U) (hF : DifferentiableOn ℂ F U)
    (hode : ∀ t ∈ U, iteratedDeriv s F t
      + ∑ i ∈ Finset.range s, a i t * iteratedDeriv i F t = 0)
    {t₀ : ℂ} (ht₀ : t₀ ∈ U) (hjet : ∀ i < s, iteratedDeriv i F t₀ = 0) : Set.EqOn F 0 U := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · intro t ht
    have := hode t ht
    simpa using this
  have hall : ∀ n, iteratedDeriv n F t₀ = 0 := by
    intro n
    by_cases hn : n < s
    · exact hjet n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = s + m := ⟨n - s, by omega⟩
      obtain ⟨b, -, hbeq⟩ := exists_higher_deriv_eq hU hs ha hF hode m
      rw [hbeq t₀ ht₀]
      exact Finset.sum_eq_zero fun i hi => by rw [hjet i (Finset.mem_range.mp hi), mul_zero]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU t₀ ht₀
  have hloc : F =ᶠ[𝓝 t₀] 0 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds t₀ hr) fun z hz => ?_
    have h := Complex.hasSum_taylorSeries_on_ball (hF.mono hball) hz
    simp only [hall, smul_zero] at h
    exact h.unique hasSum_zero
  exact (hF.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ht₀ hloc

/-- Two solutions with the same `(s−1)`-jet at one point agree. -/
theorem eqOn_of_ode (hU : IsOpen U) (hUc : IsPreconnected U)
    (ha : ∀ i < s, DifferentiableOn ℂ (a i) U) {G : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U)
    (hodeF : ∀ t ∈ U, iteratedDeriv s F t
      + ∑ i ∈ Finset.range s, a i t * iteratedDeriv i F t = 0)
    (hodeG : ∀ t ∈ U, iteratedDeriv s G t
      + ∑ i ∈ Finset.range s, a i t * iteratedDeriv i G t = 0)
    {t₀ : ℂ} (ht₀ : t₀ ∈ U) (hjet : ∀ i < s, iteratedDeriv i F t₀ = iteratedDeriv i G t₀) :
    Set.EqOn F G U := by
  have h := eqOn_zero_of_ode (F := fun t => F t - G t) hU hUc ha (hF.sub hG) (fun t ht => by
      simp only [iteratedDeriv_sub_on hU hF hG _ ht, mul_sub, Finset.sum_sub_distrib]
      linear_combination hodeF t ht - hodeG t ht) ht₀
    (fun i hi => by rw [iteratedDeriv_sub_on hU hF hG _ ht₀, hjet i hi, sub_self])
  intro t ht
  have := h ht
  simpa [sub_eq_zero] using this

end VOA.Huang.FrobeniusLog
