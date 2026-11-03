/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QBinomial
import Mathlib.Tactic.LinearCombination

/-!
# The formal q-binomial functional equation

Section 5.4 of Arakawa--Dai, arXiv:2609.33348, characterizes the q-binomial series by
`(1-z) B(z) = (1-a*z) B(q*z)` and `B(0)=1`. Here `q` is the inner formal variable
and `z` the outer one. We prove the recurrence and its uniqueness without convergence
assumptions. Identifying the solution with a quotient of infinite products is separate.
-/

namespace VOA.QSeries

variable {R : Type*} [CommRing R]

/-- The denominator recurrence after taking reciprocals. -/
theorem one_sub_X_pow_mul_reciprocalQFactorial (n : ℕ) :
    (1 - PowerSeries.X ^ (n + 1)) *
        (reciprocalQFactorial (n + 1) : PowerSeries R) = reciprocalQFactorial n := by
  apply (isUnit_qFactorial (R := R) n).mul_left_cancel
  rw [← mul_assoc, ← qFactorial_succ, qFactorial_mul_reciprocal,
    qFactorial_mul_reciprocal]

/-- The coefficients `(a;q)_n / (q)_n`, with division implemented by a proved unit inverse. -/
noncomputable def qBinomialCoeff (a : PowerSeries R) (n : ℕ) : PowerSeries R :=
  pochhammer a PowerSeries.X n * reciprocalQFactorial n

@[simp] theorem qBinomialCoeff_zero (a : PowerSeries R) : qBinomialCoeff a 0 = 1 := by
  have h := qFactorial_mul_reciprocal (R := R) 0
  simpa [qBinomialCoeff] using h

theorem qBinomialCoeff_recurrence (a : PowerSeries R) (n : ℕ) :
    (1 - PowerSeries.X ^ (n + 1)) * qBinomialCoeff a (n + 1) =
      (1 - a * PowerSeries.X ^ n) * qBinomialCoeff a n := by
  unfold qBinomialCoeff
  rw [pochhammer_succ]
  calc
    _ = (1 - a * PowerSeries.X ^ n) * pochhammer a PowerSeries.X n *
        ((1 - PowerSeries.X ^ (n + 1)) * reciprocalQFactorial (n + 1)) := by ring
    _ = _ := by rw [one_sub_X_pow_mul_reciprocalQFactorial]; ring

/-- The formal q-binomial series, as a power series in `z` over the coefficient ring `R[[q]]`. -/
noncomputable def qBinomialSeries (a : PowerSeries R) : PowerSeries (PowerSeries R) :=
  PowerSeries.mk (qBinomialCoeff a)

@[simp] theorem coeff_qBinomialSeries (a : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (qBinomialSeries a) = qBinomialCoeff a n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_qBinomialSeries (a : PowerSeries R) :
    PowerSeries.constantCoeff (qBinomialSeries a) = 1 := by
  simp [qBinomialSeries]

/-- The functional equation used to identify the infinite q-binomial product. -/
theorem qBinomialSeries_functional (a : PowerSeries R) :
    (1 - PowerSeries.X) * qBinomialSeries a =
      (1 - PowerSeries.C a * PowerSeries.X) *
        PowerSeries.rescale PowerSeries.X (qBinomialSeries a) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_zero, one_mul,
        mul_zero, sub_zero]
  | succ n =>
      simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
        mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
        coeff_qBinomialSeries]
      have h := qBinomialCoeff_recurrence a n
      linear_combination h

/-- The functional equation and constant coefficient determine the series uniquely. -/
theorem qBinomialSeries_unique (a : PowerSeries R)
    (B : PowerSeries (PowerSeries R))
    (hzero : PowerSeries.constantCoeff B = 1)
    (hfunctional : (1 - PowerSeries.X) * B =
      (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.rescale PowerSeries.X B) :
    B = qBinomialSeries a := by
  apply PowerSeries.ext
  intro n
  induction n with
  | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_qBinomialSeries] using hzero
  | succ n ih =>
      have hb := congrArg (PowerSeries.coeff (n + 1)) hfunctional
      simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
        mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale] at hb
      have hunit : IsUnit (1 - PowerSeries.X ^ (n + 1) : PowerSeries R) := by
        apply PowerSeries.isUnit_iff_constantCoeff.mpr
        simp
      apply hunit.mul_left_cancel
      rw [coeff_qBinomialSeries]
      rw [qBinomialCoeff_recurrence]
      rw [coeff_qBinomialSeries] at ih
      linear_combination hb + (1 - a * PowerSeries.X ^ n) * ih

/-- At a positive integral power of `q`, the series coefficients are Gaussian
polynomials. This connects the finite and formal q-binomial constructions. -/
theorem qBinomialCoeff_X_pow (n j : ℕ) :
    qBinomialCoeff (PowerSeries.X ^ (n + 1) : PowerSeries R) j =
      gaussian PowerSeries.X (n + j) j := by
  apply (isUnit_qFactorial (R := R) n).mul_left_cancel
  apply (isUnit_qFactorial (R := R) j).mul_left_cancel
  unfold qBinomialCoeff
  calc
    _ = (qFactorial PowerSeries.X n * pochhammer (PowerSeries.X ^ (n + 1))
        PowerSeries.X j) *
        (qFactorial PowerSeries.X j * (reciprocalQFactorial j : PowerSeries R)) := by ring
    _ = qFactorial PowerSeries.X (n + j) := by
      rw [qFactorial_mul_reciprocal, mul_one, ← qFactorial_add]
    _ = gaussian PowerSeries.X (n + j) j * qFactorial PowerSeries.X j *
        (qFactorial PowerSeries.X n : PowerSeries R) := by
      simpa only [Nat.add_sub_cancel] using
        (gaussian_mul_qFactorial (PowerSeries.X : PowerSeries R) (n + j) j (by omega)).symm
    _ = _ := by ring

end VOA.QSeries
