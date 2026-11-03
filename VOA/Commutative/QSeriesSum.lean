/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.LocallyFinitePowerSeriesSum
import VOA.Commutative.QPochhammer
import Mathlib.Tactic

/-!
# Positive-order coefficientwise sums

This supplies the algebraic sum and positive-order substitution API used by Section 5
of Arakawa--Dai. Every coefficient has an explicit finite cutoff.
-/

namespace VOA.QSeries

open scoped BigOperators
open VOA.LocallyFinitePowerSeriesSum

variable {R : Type*} [CommRing R]

noncomputable section

/-- Summing `q^(A*j) B_j`; mathematical uses require `A > 0`. -/
def powerShiftSum (A : ℕ) (B : ℕ → PowerSeries R) : PowerSeries R :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun j => PowerSeries.X ^ (A * j) * B j)

/-- All terms beyond the requested coefficient vanish. -/
theorem coeff_powerShift_term_eq_zero (A : ℕ) (hA : 0 < A)
    (B : ℕ → PowerSeries R) (d j : ℕ) (h : d < j) :
    PowerSeries.coeff d (PowerSeries.X ^ (A * j) * B j) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  have hj : j ≤ A * j := by nlinarith
  simp [show ¬ A * j ≤ d by omega]

/-- The family defining positive-order substitution is coefficientwise finite. -/
theorem powerShiftSum_finite (A : ℕ) (hA : 0 < A) (B : ℕ → PowerSeries R) :
    IsCoefficientwiseFinite (fun j => PowerSeries.X ^ (A * j) * B j) := by
  apply isCoefficientwiseFinite_of_mem_finset _ (fun d => Finset.range (d + 1))
  intro d j hj
  by_contra h
  have hdj : d < j := by simpa using h
  exact hj (coeff_powerShift_term_eq_zero A hA B d j hdj)

/-- Any cutoff at least the requested degree computes the sum coefficient. -/
theorem coeff_powerShiftSum (A : ℕ) (hA : 0 < A) (B : ℕ → PowerSeries R)
    (d N : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d (powerShiftSum A B) =
      PowerSeries.coeff d (∑ j ∈ Finset.range (N + 1), PowerSeries.X ^ (A * j) * B j) := by
  rw [powerShiftSum, coeff_sum, map_sum]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  have hjN : N < j := by simpa using h
  have hdj : d < j := hd.trans_lt hjN
  exact hj (coeff_powerShift_term_eq_zero A hA B d j hdj)

/-- Multiplication by a fixed series commutes with a positive-order sum. -/
theorem powerShiftSum_mul (A : ℕ) (hA : 0 < A) (B : ℕ → PowerSeries R)
    (g : PowerSeries R) :
    powerShiftSum A (fun j => B j * g) = powerShiftSum A B * g := by
  apply PowerSeries.ext
  intro d
  rw [coeff_powerShiftSum A hA _ d d le_rfl, PowerSeries.coeff_mul]
  calc
    _ = PowerSeries.coeff d
        ((∑ j ∈ Finset.range (d + 1), PowerSeries.X ^ (A * j) * B j) * g) := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = _ := by
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hijd : ij.1 ≤ d := (Finset.mem_antidiagonal.mp hij).le.trans' (Nat.le_add_right _ _)
      rw [← coeff_powerShiftSum A hA B ij.1 d hijd]

/-- Positive-order sums are additive in their coefficient family. -/
theorem powerShiftSum_add (A : ℕ) (hA : 0 < A) (B C : ℕ → PowerSeries R) :
    powerShiftSum A (fun j => B j + C j) = powerShiftSum A B + powerShiftSum A C := by
  apply PowerSeries.ext
  intro d
  simp only [map_add]
  rw [coeff_powerShiftSum A hA _ d d le_rfl,
    coeff_powerShiftSum A hA B d d le_rfl, coeff_powerShiftSum A hA C d d le_rfl]
  simp [mul_add, Finset.sum_add_distrib]

/-- Positive-order sums preserve subtraction. -/
theorem powerShiftSum_sub (A : ℕ) (hA : 0 < A) (B C : ℕ → PowerSeries R) :
    powerShiftSum A (fun j => B j - C j) = powerShiftSum A B - powerShiftSum A C := by
  apply PowerSeries.ext
  intro d
  simp only [map_sub]
  rw [coeff_powerShiftSum A hA _ d d le_rfl,
    coeff_powerShiftSum A hA B d d le_rfl, coeff_powerShiftSum A hA C d d le_rfl]
  simp [mul_sub, Finset.sum_sub_distrib]

/-- Split off the initial coefficient of a positive-order sum. -/
theorem powerShiftSum_succ (A : ℕ) (hA : 0 < A) (B : ℕ → PowerSeries R) :
    powerShiftSum A B = B 0 + PowerSeries.X ^ A * powerShiftSum A (fun j => B (j + 1)) := by
  apply PowerSeries.ext
  intro d
  rw [coeff_powerShiftSum A hA B d d le_rfl, map_add]
  have hm := powerShiftSum_mul A hA (fun j => B (j + 1)) (PowerSeries.X ^ A)
  rw [mul_comm (PowerSeries.X ^ A), ← hm, coeff_powerShiftSum A hA _ d d le_rfl]
  have hs := Finset.sum_range_succ' (fun j => PowerSeries.X ^ (A * j) * B j) d
  have ht := Finset.sum_range_succ
    (fun j => PowerSeries.X ^ (A * j) * (B (j + 1) * PowerSeries.X ^ A)) d
  rw [hs, ht]
  simp only [Nat.mul_zero, pow_zero, one_mul, map_add]
  have hz : PowerSeries.coeff d
      (PowerSeries.X ^ (A * d) * (B (d + 1) * PowerSeries.X ^ A)) = 0 := by
    have heq : PowerSeries.X ^ (A * d) * (B (d + 1) * PowerSeries.X ^ A) =
        PowerSeries.X ^ (A * (d + 1)) * B (d + 1) := by rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
    rw [heq]
    exact coeff_powerShift_term_eq_zero A hA B d (d + 1) (by omega)
  rw [hz, add_zero, add_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  ring

/-- Equality of the coefficient family gives equality of its sum. -/
theorem powerShiftSum_congr (A : ℕ) {B C : ℕ → PowerSeries R}
    (h : ∀ j, B j = C j) : powerShiftSum A B = powerShiftSum A C := by
  apply VOA.LocallyFinitePowerSeriesSum.sum_congr
  intro j
  rw [h j]

/-- Move a linear contribution to the exponent into the coefficient family. -/
theorem powerShiftSum_add_exponent (A b : ℕ) (B : ℕ → PowerSeries R) :
    powerShiftSum (A + b) B =
      powerShiftSum A (fun j => PowerSeries.X ^ (b * j) * B j) := by
  apply VOA.LocallyFinitePowerSeriesSum.sum_congr
  intro j
  rw [Nat.add_mul, pow_add, mul_assoc]

end
end VOA.QSeries
