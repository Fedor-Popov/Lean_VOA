import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-!
# Explicit two-jet Hermite interpolation at distinct sites

Squaring ordinary Lagrange polynomials gives value/derivative idempotents.
These are the concrete length-two interpolation needed to separate shifted
current sites killed by the square of their local parameter. This supplies
constructive site isolation in the shifted-tensor cyclicity argument of
Fourier--Littelmann, Section 2.6, Lemma 2 (arXiv:math/0509276).

No current-module realization or graded character assertion is assumed here.
-/

namespace VOA.DeligneAudit.JetInterpolation

open Polynomial

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Lagrange polynomial at one site. -/
def lagrange (z : ι → K) (i : ι) : K[X] := Lagrange.basis Finset.univ z i

/-- Value one at i, value zero at all other sites, and derivative zero everywhere. -/
def valueBasis (z : ι → K) (i : ι) : K[X] :=
  (1 - C (2 * (lagrange z i).derivative.eval (z i)) * (X - C (z i))) * lagrange z i ^ 2

/-- Value zero everywhere, with derivative one exactly at i. -/
def tangentBasis (z : ι → K) (i : ι) : K[X] :=
  (X - C (z i)) * lagrange z i ^ 2

variable (z : ι → K) (hz : Function.Injective z)

include hz

theorem lagrange_eval (i j : ι) : (lagrange z i).eval (z j) = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst j
    simp only [lagrange, Lagrange.eval_basis_self hz.injOn (Finset.mem_univ i), if_true]
  · rw [if_neg h]
    exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)

theorem valueBasis_eval (i j : ι) : (valueBasis z i).eval (z j) = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst j
    simp only [valueBasis, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow,
      lagrange_eval z hz i i, if_true, sub_self, mul_zero, sub_zero, one_pow, mul_one]
  · simp only [valueBasis, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow,
      lagrange_eval z hz i j, if_neg h, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem tangentBasis_eval (i j : ι) : (tangentBasis z i).eval (z j) = 0 := by
  by_cases h : j = i
  · subst j
    simp only [tangentBasis, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  · simp only [tangentBasis, eval_mul, eval_sub, eval_X, eval_C, eval_pow,
      lagrange_eval z hz i j, if_neg h, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem valueBasis_derivative_eval (i j : ι) : (valueBasis z i).derivative.eval (z j) = 0 := by
  simp only [valueBasis, derivative_mul, derivative_sub, derivative_one, derivative_C,
    derivative_X, derivative_sq, eval_add, eval_mul, eval_sub, eval_one, eval_zero,
    eval_C, eval_pow, eval_X]
  by_cases h : j = i
  · subst j
    rw [lagrange_eval z hz i i]
    simp only [if_true]
    ring
  · rw [lagrange_eval z hz i j, if_neg h]
    ring

theorem tangentBasis_derivative_eval (i j : ι) :
    (tangentBasis z i).derivative.eval (z j) = if j = i then 1 else 0 := by
  simp only [tangentBasis, derivative_mul, derivative_sub, derivative_X, derivative_C,
    derivative_sq, eval_add, eval_mul, eval_sub, eval_one, eval_zero, eval_C, eval_pow, eval_X]
  by_cases h : j = i
  · subst j
    rw [lagrange_eval z hz i i]
    simp only [if_true]
    ring
  · rw [lagrange_eval z hz i j, if_neg h]
    ring

private theorem lagrange_natDegree (i : ι) :
    (lagrange z i).natDegree = Fintype.card ι - 1 := by
  exact (Lagrange.natDegree_basis hz.injOn (Finset.mem_univ i)).trans (by rw [Finset.card_univ])

/-- The value isolator uses only modes strictly below twice the site count. -/
theorem valueBasis_natDegree_lt (i : ι) : (valueBasis z i).natDegree < 2 * Fintype.card ι := by
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hlinear : (1 - C (2 * (lagrange z i).derivative.eval (z i)) *
      (X - C (z i))).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)))
  have hpow := natDegree_pow_le (p := lagrange z i) (n := 2)
  rw [lagrange_natDegree z hz i] at hpow
  have hmul := natDegree_mul_le (p := 1 - C (2 * (lagrange z i).derivative.eval (z i)) *
    (X - C (z i))) (q := lagrange z i ^ 2)
  change (valueBasis z i).natDegree ≤ _ at hmul
  omega

/-- The tangent isolator also uses only modes below twice the site count. -/
theorem tangentBasis_natDegree_lt (i : ι) :
    (tangentBasis z i).natDegree < 2 * Fintype.card ι := by
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hlinear := natDegree_X_sub_C_le (z i)
  have hpow := natDegree_pow_le (p := lagrange z i) (n := 2)
  rw [lagrange_natDegree z hz i] at hpow
  have hmul := natDegree_mul_le (p := X - C (z i)) (q := lagrange z i ^ 2)
  change (tangentBasis z i).natDegree ≤ _ at hmul
  omega

end
end VOA.DeligneAudit.JetInterpolation

#print axioms VOA.DeligneAudit.JetInterpolation.valueBasis_derivative_eval
#print axioms VOA.DeligneAudit.JetInterpolation.tangentBasis_derivative_eval
#print axioms VOA.DeligneAudit.JetInterpolation.valueBasis_natDegree_lt
#print axioms VOA.DeligneAudit.JetInterpolation.tangentBasis_natDegree_lt
