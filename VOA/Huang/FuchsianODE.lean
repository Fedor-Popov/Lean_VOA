/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.IndicialGrowth
import VOA.Modularity.SubexpSeriesRing
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Formal solutions of a Fuchsian equation converge

Let `G = Σₙ gₙ xⁿ ∈ ℂ⟦x⟧` and `λ ∈ ℂ`.  Write `θ_λ` for the Euler operator `x d/dx` *twisted by
`x^λ`*, i.e. the operator with `θ_λ(x^λ G) = x^λ (θ_λ G)`; on coefficients it is diagonal,
`θ_λ : gₙ ↦ (λ + n) gₙ`.  A **Fuchsian equation at `x = 0`** for the multivalued function `x^λ G` is

  `θ_λ^s G + Σ_{i<s} cᵢ(x) · θ_λ^i G = 0`,  `cᵢ ∈ ℂ⟦x⟧`

(monic in `θ`: this is exactly "`x = 0` is a regular singular point").

**Theorem** (`subexponential_of_fuchsianEq`, `summable_of_fuchsianEq`): if every coefficient
`cᵢ` converges on the open unit disc (has subexponential coefficients, `SubexpPS`), then so does
*every formal power series solution* `G`.  No non-resonance hypothesis is needed (the indicial
polynomial may vanish at finitely many `λ + n`; those `gₙ` are free), and no Frobenius *existence*
theory, no logarithms: this is the half of the Frobenius–Fuchs theory that Huang's convergence
theorem (CCM 7 (2005), Thm 3.5, first paragraph) actually uses.

The coefficient estimate is the library's majorant theorem
(`subexponential_of_indicial_recursion`, `tendsto_indicialDivisor_atTop`); this file only
supplies the passage from the operator identity in `ℂ⟦x⟧` to the coefficient recursion, so the
result is a general, VOA-free statement usable for genus zero (V3), genus one (V6) and elsewhere.

Rational coefficients with poles only at `x = 1` — the case produced by Huang's equations after the
homogeneity reduction (`Huang/Convergence.lean`) — lie in `SubexpPS`: `mem_subexpPS_of_mul_eq`.

## Main declarations
* `thetaShift lam` — `θ_λ` as a `ℂ`-linear endomorphism of `ℂ⟦x⟧`; `coeff_thetaShift_iterate`.
* `FuchsianEq lam s c G` — the Fuchsian equation above.
* `indicial_recursion_of_fuchsianEq` — its `xⁿ`-coefficient, in the library's `indicialP` form.
* `subexponential_of_fuchsianEq`, `summable_of_fuchsianEq`.
* `polynomial_mem_subexpPS`, `mk_one_mem_subexpPS`, `mem_subexpPS_of_mul_eq`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.FuchsianODE

open VOA PowerSeries
open scoped BigOperators

/-- The `x^λ`-twisted Euler operator `θ_λ` on `ℂ⟦x⟧`: `θ_λ(Σ gₙ xⁿ) = Σ (λ+n) gₙ xⁿ`, so that
`x d/dx (x^λ G) = x^λ θ_λ G`. -/
noncomputable def thetaShift (lam : ℂ) : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ where
  toFun G := PowerSeries.mk fun n => (lam + n) * coeff n G
  map_add' G H := by
    ext n; simp only [coeff_mk, map_add]; ring
  map_smul' a G := by
    ext n; simp only [coeff_mk, map_smul, smul_eq_mul, RingHom.id_apply]; ring

theorem coeff_thetaShift (lam : ℂ) (G : PowerSeries ℂ) (n : ℕ) :
    coeff n (thetaShift lam G) = (lam + n) * coeff n G := by
  simp [thetaShift]

theorem coeff_thetaShift_iterate (lam : ℂ) (i : ℕ) (G : PowerSeries ℂ) (n : ℕ) :
    coeff n ((thetaShift lam)^[i] G) = (lam + n) ^ i * coeff n G := by
  induction i generalizing G with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coeff_thetaShift, pow_succ]; ring

/-- **The Fuchsian equation at `x = 0`** for `x^λ G`, monic in `θ`:
`θ_λ^s G + Σ_{i<s} cᵢ · θ_λ^i G = 0` in `ℂ⟦x⟧`. -/
def FuchsianEq (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (G : PowerSeries ℂ) : Prop :=
  (thetaShift lam)^[s] G + ∑ i ∈ Finset.range s, c i * (thetaShift lam)^[i] G = 0

/-- Only the coefficients `cᵢ`, `i < s`, matter. -/
theorem fuchsianEq_congr {lam : ℂ} {s : ℕ} {c c' : ℕ → PowerSeries ℂ}
    (hcc : ∀ i < s, c i = c' i) {G : PowerSeries ℂ} :
    FuchsianEq lam s c G ↔ FuchsianEq lam s c' G := by
  unfold FuchsianEq
  rw [Finset.sum_congr rfl fun i hi => by rw [hcc i (Finset.mem_range.mp hi)]]

/-- **The coefficient recursion.**  The `xⁿ`-coefficient of a Fuchsian equation is the indicial
recursion `P(λ+n) gₙ = −Σ_{m<n} Σ_{i<s} c_{i,n−m} (λ+m)^i g_m` of `Modularity.IndicialRecursion`. -/
theorem indicial_recursion_of_fuchsianEq {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ}
    {G : PowerSeries ℂ} (h : FuchsianEq lam s c G) (n : ℕ) :
    indicialP lam s (fun i k => coeff k (c i)) n * coeff n G
      = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          coeff (n - m) (c i) * (lam + (m : ℂ)) ^ i * coeff m G := by
  have hE := congrArg (coeff n) h
  simp only [map_add, map_sum, map_zero] at hE
  rw [coeff_thetaShift_iterate] at hE
  have hconv : ∀ i ∈ Finset.range s, coeff n (c i * (thetaShift lam)^[i] G)
      = (∑ m ∈ Finset.range n, coeff (n - m) (c i) * (lam + (m : ℂ)) ^ i * coeff m G)
        + coeff 0 (c i) * (lam + (n : ℂ)) ^ i * coeff n G := by
    intro i _
    rw [mul_comm, coeff_mul_range, Finset.sum_range_succ, Nat.sub_self]
    simp only [coeff_thetaShift_iterate]
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by ring
    · ring
  rw [Finset.sum_congr rfl hconv, Finset.sum_add_distrib, Finset.sum_comm] at hE
  rw [indicialP, add_mul, Finset.sum_mul]
  linear_combination hE

/-- **Formal solutions of a Fuchsian equation with coefficients convergent on the unit disc
have subexponential coefficients** (hence converge on the unit disc). -/
theorem subexponential_of_fuchsianEq {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {G : PowerSeries ℂ} (h : FuchsianEq lam s c G) :
    Subexponential fun n => ‖coeff n G‖ := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hG : G = 0 := by simpa [FuchsianEq] using h
    subst hG
    simpa using subexponential_zero
  · set c' : ℕ → PowerSeries ℂ := fun i => if i < s then c i else 0 with hc'
    have h' : FuchsianEq lam s c' G :=
      (fuchsianEq_congr (fun i hi => by simp [hc', hi])).mp h
    have hg : ∀ i, Subexponential (fun k => ‖coeff k (c' i)‖) := by
      intro i
      by_cases hi : i < s
      · simpa [hc', hi] using hc i hi
      · simpa [hc', hi] using subexponential_zero
    exact subexponential_of_indicial_recursion lam hs _ hg
      (tendsto_indicialDivisor_atTop lam hs _) (indicial_recursion_of_fuchsianEq h')

/-- **Convergence on the unit disc.**  A formal power-series solution of a Fuchsian equation
whose coefficients converge on `‖x‖ < 1` converges absolutely there. -/
theorem summable_of_fuchsianEq {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {G : PowerSeries ℂ} (h : FuchsianEq lam s c G) {x : ℂ}
    (hx : ‖x‖ < 1) : Summable fun n => ‖coeff n G * x ^ n‖ := by
  have := summable_of_subexponential (fun n => norm_nonneg _)
    (subexponential_of_fuchsianEq hc h) (norm_nonneg x) hx
  simpa [norm_mul, norm_pow] using this

/-- The value: a formal solution of such an equation is a convergent series on `‖x‖ < 1`. -/
theorem summable_of_fuchsianEq' {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {G : PowerSeries ℂ} (h : FuchsianEq lam s c G) {x : ℂ}
    (hx : ‖x‖ < 1) : Summable fun n => coeff n G * x ^ n :=
  (summable_of_fuchsianEq hc h hx).of_norm

/-! ## Rational coefficients with poles only at `x = 1` -/

/-- Polynomials have subexponential coefficients. -/
theorem polynomial_mem_subexpPS (p : Polynomial ℂ) : (p : PowerSeries ℂ) ∈ SubexpPS := by
  classical
  rw [mem_subexpPS]
  intro r hr
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖, fun n => ?_⟩
  have hr1 : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
  have hS : 0 ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  change ‖coeff n (p : PowerSeries ℂ)‖ ≤ _
  rw [Polynomial.coeff_coe]
  by_cases hn : n ≤ p.natDegree
  · have : ‖p.coeff n‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ :=
      Finset.single_le_sum (f := fun i => ‖p.coeff i‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    nlinarith
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    positivity

/-- `(1 − x)⁻¹ = Σ xⁿ` has subexponential (constant) coefficients. -/
theorem mk_one_mem_subexpPS : (PowerSeries.mk 1 : PowerSeries ℂ) ∈ SubexpPS := by
  rw [mem_subexpPS]
  refine Subexponential.of_le (b := fun _ => 1) (fun n => ?_) (subexponential_const 1)
  simp

/-- **Rational coefficients with poles only at `x = 1` converge on the unit disc**: if
`(1 − x)^b · c` is a polynomial, then `c ∈ SubexpPS`. -/
theorem mem_subexpPS_of_mul_eq {c : PowerSeries ℂ} {b : ℕ} {p : Polynomial ℂ}
    (h : (1 - X) ^ b * c = (p : PowerSeries ℂ)) : c ∈ SubexpPS := by
  have hinv : (PowerSeries.mk 1 : PowerSeries ℂ) ^ b * (1 - X) ^ b = 1 := by
    rw [← mul_pow, mk_one_mul_one_sub_eq_one ℂ, one_pow]
  have hc : c = (PowerSeries.mk 1 : PowerSeries ℂ) ^ b * (p : PowerSeries ℂ) := by
    rw [← h, ← mul_assoc, hinv, one_mul]
  rw [hc]
  exact SubexpPS.mul_mem (SubexpPS.pow_mem mk_one_mem_subexpPS b) (polynomial_mem_subexpPS p)

/-- `(1 − a x)⁻¹ = Σ aⁿ xⁿ` has subexponential coefficients when `‖a‖ ≤ 1`. -/
theorem mk_pow_mem_subexpPS {a : ℂ} (ha : ‖a‖ ≤ 1) :
    (PowerSeries.mk fun n => a ^ n : PowerSeries ℂ) ∈ SubexpPS := by
  rw [mem_subexpPS]
  refine Subexponential.of_le (b := fun _ => 1) (fun n => ?_) (subexponential_const 1)
  simp only [coeff_mk, norm_pow]
  exact pow_le_one₀ (norm_nonneg a) ha

/-- **Rational coefficients with poles only at `x = 1/a`, `‖a‖ ≤ 1`, converge on the unit
disc**: if `(1 − a x)^b · c` is a polynomial, then `c ∈ SubexpPS`.  (`a = 1`: products,
`z₁ = z₂`; `a = −1`: iterates, `z₁ = 0` seen from `x = (z₁ − z₂)/z₂`.) -/
theorem mem_subexpPS_of_mul_eq' {a : ℂ} (ha : ‖a‖ ≤ 1) {c : PowerSeries ℂ} {b : ℕ}
    {p : Polynomial ℂ} (h : (1 - PowerSeries.C a * X) ^ b * c = (p : PowerSeries ℂ)) :
    c ∈ SubexpPS := by
  have hinv1 :
      (PowerSeries.mk fun n => a ^ n : PowerSeries ℂ) * (1 - PowerSeries.C a * X) = 1 := by
    have := congrArg (rescale a) (mk_one_mul_one_sub_eq_one ℂ)
    rw [map_mul, map_sub, map_one, rescale_X, rescale_mk] at this
    simpa using this
  have hinv : (PowerSeries.mk fun n => a ^ n : PowerSeries ℂ) ^ b
      * (1 - PowerSeries.C a * X) ^ b = 1 := by
    rw [← mul_pow, hinv1, one_pow]
  have hc : c = (PowerSeries.mk fun n => a ^ n : PowerSeries ℂ) ^ b * (p : PowerSeries ℂ) := by
    rw [← h, ← mul_assoc, hinv, one_mul]
  rw [hc]
  exact SubexpPS.mul_mem (SubexpPS.pow_mem (mk_pow_mem_subexpPS ha) b)
    (polynomial_mem_subexpPS p)

end VOA.Huang.FuchsianODE
