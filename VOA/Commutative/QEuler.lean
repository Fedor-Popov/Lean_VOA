/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QSeriesSum
import VOA.Commutative.QBinomialFiniteSum

/-!
# Euler's formal q-binomial summation

The positive-order specialization `sum_j q^(A*j)/(q)_j` equals
`(q)_(A-1)/(q)_infinity`. Every infinite sum is algebraically coefficientwise finite.
-/

namespace VOA.QSeries

open scoped BigOperators
variable {R : Type*} [CommRing R]
noncomputable section

/-- Euler's sum at the positive parameter `q^A`. -/
def eulerSum (A : ℕ) : PowerSeries R :=
  powerShiftSum A reciprocalQFactorial

/-- The Euler sum satisfies its first-order product recurrence. -/
theorem eulerSum_recurrence (A : ℕ) (hA : 0 < A) :
    (1 - PowerSeries.X ^ A) * (eulerSum A : PowerSeries R) = eulerSum (A + 1) := by
  let D : ℕ → PowerSeries R := fun j =>
    (1 - PowerSeries.X ^ j) * reciprocalQFactorial j
  have hD0 : D 0 = 0 := by simp [D]
  have hDsucc : ∀ j, D (j + 1) = reciprocalQFactorial j :=
    fun j => one_sub_X_pow_mul_reciprocalQFactorial j
  have hs := powerShiftSum_succ A hA D
  rw [hD0, zero_add] at hs
  have htail : powerShiftSum A (fun j => D (j + 1)) = eulerSum A :=
    powerShiftSum_congr A hDsucc
  rw [htail] at hs
  have hd : eulerSum A - eulerSum (A + 1) = powerShiftSum A D := by
    rw [eulerSum, eulerSum, powerShiftSum_add_exponent A 1]
    simp only [Nat.one_mul]
    rw [← powerShiftSum_sub A hA]
    apply powerShiftSum_congr
    intro j
    simp only [D]
    ring
  rw [hs] at hd
  linear_combination hd

/-- Iterating the first-order recurrence multiplies by a finite tail product. -/
theorem pochhammer_mul_eulerSum (A : ℕ) (hA : 0 < A) (n : ℕ) :
    pochhammer (PowerSeries.X ^ A) PowerSeries.X n * (eulerSum A : PowerSeries R) =
      eulerSum (A + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pochhammer_succ]
      calc
        _ = (1 - PowerSeries.X ^ (A + n)) *
            (pochhammer (PowerSeries.X ^ A) PowerSeries.X n * (eulerSum A : PowerSeries R)) := by
              rw [pow_add]; ring
        _ = (eulerSum (A + (n + 1)) : PowerSeries R) := by
          rw [ih, eulerSum_recurrence (A + n) (by omega)]
          simp only [Nat.add_assoc]

/-- For a sufficiently large starting exponent, the Euler sum is `1` through any
fixed coefficient cutoff. -/
theorem coeff_eulerSum_of_lt (A d : ℕ) (hd : d < A) :
    PowerSeries.coeff d (eulerSum A : PowerSeries R) = PowerSeries.coeff d 1 := by
  rw [eulerSum, coeff_powerShiftSum A (by omega) _ d d le_rfl, map_sum]
  rw [Finset.sum_eq_single 0]
  · have hzero := qFactorial_mul_reciprocal (R := R) 0
    simpa using congrArg (PowerSeries.coeff d) hzero
  · intro j _ hj
    rw [PowerSeries.coeff_X_pow_mul']
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hAj : A ≤ A * j := by nlinarith
    simp [show ¬ A * j ≤ d by omega]
  · simp

/-- A finite tail-product identity with all denominator factors cleared. -/
theorem qFactorial_mul_eulerSum (A : ℕ) (hA : 0 < A) (n : ℕ) :
    qFactorial PowerSeries.X (A - 1 + n) * (eulerSum A : PowerSeries R) =
      qFactorial PowerSeries.X (A - 1) * eulerSum (A + n) := by
  have hpred : A - 1 + 1 = A := by omega
  rw [qFactorial_add, hpred, mul_assoc, pochhammer_mul_eulerSum A hA]

/-- Euler's infinite formal product multiplied by its positive-order sum is the
finite prefix product. -/
theorem euler_mul_eulerSum (A : ℕ) (hA : 0 < A) :
    (euler : PowerSeries R) * eulerSum A = qFactorial PowerSeries.X (A - 1) := by
  apply PowerSeries.ext
  intro d
  let n := d + 1
  calc
    _ = PowerSeries.coeff d
        (qFactorial PowerSeries.X (A - 1 + n) * (eulerSum A : PowerSeries R)) := by
      apply coeff_mul_congr_left_upto
      intro i hi
      exact coeff_euler i (A - 1 + n) (by dsimp [n]; omega)
    _ = PowerSeries.coeff d
        (qFactorial PowerSeries.X (A - 1) * (eulerSum (A + n) : PowerSeries R)) := by
      rw [qFactorial_mul_eulerSum A hA n]
    _ = PowerSeries.coeff d (qFactorial PowerSeries.X (A - 1) * (1 : PowerSeries R)) := by
      rw [mul_comm, mul_comm (qFactorial _ _) (1 : PowerSeries R)]
      apply coeff_mul_congr_left_upto
      intro i hi
      exact coeff_eulerSum_of_lt (A + n) i (by dsimp [n]; omega)
    _ = _ := by rw [mul_one]

/-- Euler's q-binomial identity with the positive substitution `z=q^A`. -/
theorem eulerSum_eq (A : ℕ) (hA : 0 < A) :
    (eulerSum A : PowerSeries R) = qFactorial PowerSeries.X (A - 1) * reciprocalEuler := by
  apply (isUnit_euler (R := R)).mul_left_cancel
  rw [euler_mul_eulerSum A hA]
  calc
    _ = qFactorial PowerSeries.X (A - 1) * (euler * (reciprocalEuler : PowerSeries R)) := by simp
    _ = _ := by ring

end
end VOA.QSeries
