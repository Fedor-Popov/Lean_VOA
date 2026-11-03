/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QBinomialAlternating
import VOA.Commutative.LocallyFinitePowerSeriesSum

/-!
# The Jacobi cube identity

The coefficientwise limit of the finite alternating identity, equation 5.20 of
Arakawa--Dai. Infinite sums are defined using finite coefficient support.
-/

namespace VOA.QSeries

open scoped BigOperators
open VOA.LocallyFinitePowerSeriesSum

section Definitions

variable {R : Type*} [CommRing R]

/-- The signed odd triangular summand. -/
noncomputable def alternatingTerm (r : ℕ) : PowerSeries R :=
  (-1 : PowerSeries R) ^ r * ((2 * r + 1 : ℕ) : PowerSeries R) *
    PowerSeries.X ^ ((r + 1).choose 2)

/-- Triangular exponents bound their own indices. -/
theorem le_triangular (r : ℕ) : r ≤ (r + 1).choose 2 := by
  have h := two_mul_choose_two_add (r + 1)
  nlinarith

/-- Terms indexed beyond a coefficient cannot contribute, even after multiplication. -/
theorem coeff_alternatingTerm_mul_eq_zero (m r : ℕ) (h : m < r) (B : PowerSeries R) :
    PowerSeries.coeff m (alternatingTerm r * B) = 0 := by
  have heq : alternatingTerm r * B = PowerSeries.X ^ ((r + 1).choose 2) *
      ((-1 : PowerSeries R) ^ r * ((2 * r + 1 : ℕ) : PowerSeries R) * B) := by
    unfold alternatingTerm
    ring
  rw [heq, PowerSeries.coeff_X_pow_mul']
  simp [show ¬ (r + 1).choose 2 ≤ m by have ht := le_triangular r; omega]

/-- The alternating triangular series is coefficientwise finite. -/
theorem alternatingTerm_finite :
    IsCoefficientwiseFinite (alternatingTerm (R := R)) := by
  apply isCoefficientwiseFinite_of_mem_finset _ (fun m => Finset.range (m + 1))
  intro m r hr
  by_contra h
  have hmr : m < r := by simpa using h
  have hz := coeff_alternatingTerm_mul_eq_zero (R := R) m r hmr 1
  exact hr (by simpa using hz)

/-- The alternating triangular series occurring in the Jacobi cube identity. -/
noncomputable def alternatingTheta : PowerSeries R :=
  VOA.LocallyFinitePowerSeriesSum.sum alternatingTerm

/-- A cutoff at the requested degree computes every coefficient. -/
theorem coeff_alternatingTheta (m N : ℕ) (h : m ≤ N) :
    PowerSeries.coeff m (alternatingTheta : PowerSeries R) =
      PowerSeries.coeff m
        (∑ r ∈ Finset.range (N + 1), (alternatingTerm r : PowerSeries R)) := by
  rw [alternatingTheta, coeff_sum, map_sum]
  apply finsum_eq_sum_of_support_subset
  intro r hr
  by_contra hn
  have hNr : N < r := by simpa using hn
  have hz := coeff_alternatingTerm_mul_eq_zero (R := R) m r (by omega) 1
  exact hr (by simpa using hz)

/-- The same cutoff works after multiplying the alternating series by an arbitrary series. -/
theorem coeff_alternatingTheta_mul (B : PowerSeries R) (m N : ℕ) (h : m ≤ N) :
    PowerSeries.coeff m (alternatingTheta * B) =
      PowerSeries.coeff m ((∑ r ∈ Finset.range (N + 1), alternatingTerm r) * B) := by
  apply coeff_mul_congr_left_upto
  intro i hi
  exact coeff_alternatingTheta i N (hi.trans h)

/-- The centered Gaussian coefficient tends coefficientwise to the reciprocal Euler product. -/
theorem coeff_gaussian_centered (m n r : ℕ) (h : m + r ≤ n) :
    PowerSeries.coeff m
      (gaussian (PowerSeries.X : PowerSeries R) (2 * n + 1) (n - r)) =
      PowerSeries.coeff m (reciprocalEuler : PowerSeries R) := by
  rw [coeff_gaussian_eq_reciprocalQFactorial (2 * n + 1) (n - r) m (by omega)]
  exact (coeff_reciprocalEuler m (n - r) (by omega)).symm

end Definitions

section Cube

variable {K : Type*} [Field K]

/-- The coefficientwise limit of the finite alternating identity before canceling the Euler unit. -/
theorem alternatingTheta_mul_reciprocalEuler :
    (alternatingTheta : PowerSeries K) * reciprocalEuler = euler ^ 2 := by
  apply PowerSeries.ext
  intro m
  have heuler : PowerSeries.coeff m ((euler : PowerSeries K) ^ 2) =
      PowerSeries.coeff m ((qFactorial PowerSeries.X (2 * m) : PowerSeries K) ^ 2) := by
    rw [pow_two, pow_two]
    calc
      _ = PowerSeries.coeff m (qFactorial PowerSeries.X (2 * m) * (euler : PowerSeries K)) := by
        apply coeff_mul_congr_left_upto
        intro i hi
        exact coeff_euler i (2 * m) (by omega)
      _ = _ := by
        rw [mul_comm (qFactorial PowerSeries.X (2 * m))]
        apply coeff_mul_congr_left_upto
        intro i hi
        exact coeff_euler i (2 * m) (by omega)
  rw [heuler, finite_alternating, coeff_alternatingTheta_mul _ m m le_rfl,
    Finset.sum_mul, map_sum, map_sum]
  change (∑ r ∈ Finset.range (m + 1),
      PowerSeries.coeff m ((alternatingTerm r : PowerSeries K) * reciprocalEuler)) =
    ∑ r ∈ Finset.range (2 * m + 1),
      PowerSeries.coeff m (alternatingTerm r *
        gaussian (PowerSeries.X : PowerSeries K) (2 * (2 * m) + 1) (2 * m - r))
  have hcut :
      (∑ r ∈ Finset.range (m + 1), PowerSeries.coeff m (alternatingTerm r *
        gaussian (PowerSeries.X : PowerSeries K) (2 * (2 * m) + 1) (2 * m - r))) =
      ∑ r ∈ Finset.range (2 * m + 1), PowerSeries.coeff m (alternatingTerm r *
        gaussian (PowerSeries.X : PowerSeries K) (2 * (2 * m) + 1) (2 * m - r)) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r hr hnot
    exact coeff_alternatingTerm_mul_eq_zero m r (by simpa using hnot) _
  rw [← hcut]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r ≤ m := by simpa using Finset.mem_range.mp hr
  rw [mul_comm (alternatingTerm r) reciprocalEuler, mul_comm (alternatingTerm r)]
  apply coeff_mul_congr_left_upto
  intro i hi
  exact (coeff_gaussian_centered i (2 * m) r (by omega)).symm

/-- Arakawa--Dai equation 5.20: the alternating triangular series
is the cube of the Euler product. -/
theorem jacobi_cube : (alternatingTheta : PowerSeries K) = euler ^ 3 := by
  have h := congrArg (fun f : PowerSeries K => f * euler)
    (alternatingTheta_mul_reciprocalEuler (K := K))
  dsimp only at h
  have hunit : (reciprocalEuler : PowerSeries K) * euler = 1 := by
    rw [mul_comm, euler_mul_reciprocal]
  rw [mul_assoc, hunit, mul_one] at h
  simpa only [pow_succ] using h

end Cube

end VOA.QSeries
