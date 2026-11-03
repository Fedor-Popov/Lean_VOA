/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningFactorial
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Leading coefficients for triangular differential equations

If every derivative away from one distinguished variable is a scalar multiple
of a higher derivative in that variable, a nonzero polynomial has a nonzero
pure power of the distinguished variable. The proof uses maximal total degree.
-/

namespace VOA.DerivativeLeadingCoefficient
open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

private theorem degree_add_single (d : σ →₀ ℕ) (a : σ) :
    (d + Finsupp.single a 1).sum (fun _ n => n) = d.sum (fun _ n => n) + 1 := by
  classical
  rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
  simp

/-- An iterated derivative cannot have a coefficient whose original total degree
would exceed the total degree of the input. -/
theorem coeff_iterate_pderiv_eq_zero (Q : MvPolynomial σ ℂ) (a : σ)
    (r : ℕ) (d : σ →₀ ℕ)
    (h : Q.totalDegree < d.sum (fun _ n => n) + r) :
    coeff d ((pderiv a)^[r] Q) = 0 := by
  induction r generalizing d with
  | zero => exact coeff_eq_zero_of_totalDegree_lt (by simpa using h)
  | succ r ih =>
    rw [Function.iterate_succ_apply', VOA.VirasoroScreening.screening_pderiv_coeff]
    rw [ih (d + Finsupp.single a 1) (by rw [degree_add_single]; omega), mul_zero]

/-- Triangular differential equations force every highest-degree monomial to
involve only the distinguished variable. -/
theorem top_support_is_pure (Q : MvPolynomial σ ℂ) (a : σ)
    (hPDE : ∀ j, j ≠ a → ∃ (r : ℕ) (c : ℂ), 2 ≤ r ∧
      pderiv j Q = c • ((pderiv a)^[r] Q))
    (d : σ →₀ ℕ) (hd : d ∈ Q.support)
    (hdeg : d.sum (fun _ n => n) = Q.totalDegree) :
    d = Finsupp.single a (d a) := by
  classical
  have hvan : ∀ j, j ≠ a → d j = 0 := by
    intro j hj
    by_contra hjd
    obtain ⟨r, c, hr, hpde⟩ := hPDE j hj
    let e := d - Finsupp.single j 1
    have he : e + Finsupp.single j 1 = d := by
      ext v
      by_cases hv : v = j
      · subst v; simp [e]; omega
      · simp [e, hv]
    have hed : e.sum (fun _ n => n) + 1 = Q.totalDegree := by
      rw [← degree_add_single e j, he, hdeg]
    have hz : coeff e ((pderiv a)^[r] Q) = 0 :=
      coeff_iterate_pderiv_eq_zero Q a r e (by omega)
    have hc := congrArg (coeff e) hpde
    rw [VOA.VirasoroScreening.screening_pderiv_coeff, he, coeff_smul, hz, smul_zero] at hc
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) (mem_support_iff.mp hd)) hc
  ext j
  by_cases hj : j = a
  · subst j; simp
  · simp [hj, hvan j hj]

/-- A nonzero solution of the triangular derivative system has a nonzero pure
power coefficient, including the constant case. -/
theorem exists_pure_coefficient_ne_zero (Q : MvPolynomial σ ℂ) (a : σ)
    (hQ : Q ≠ 0)
    (hPDE : ∀ j, j ≠ a → ∃ (r : ℕ) (c : ℂ), 2 ≤ r ∧
      pderiv j Q = c • ((pderiv a)^[r] Q)) :
    ∃ n : ℕ, coeff (Finsupp.single a n) Q ≠ 0 := by
  classical
  obtain ⟨d, hd, hdeg⟩ := Q.support.exists_mem_eq_sup
    (Finsupp.support_nonempty_iff.mpr hQ) (fun d => d.sum (fun _ n => n))
  have he := top_support_is_pure Q a hPDE d hd (by simpa [totalDegree] using hdeg.symm)
  exact ⟨d a, he ▸ mem_support_iff.mp hd⟩

end VOA.DerivativeLeadingCoefficient
