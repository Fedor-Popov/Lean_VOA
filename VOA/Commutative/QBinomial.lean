/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import VOA.Commutative.QPochhammer

/-!
# The finite q-binomial theorem

The coefficients of `∏ j < n, (1 + z * q ^ j)` admit a division-free recursion over any
commutative semiring.  The coefficient of `z ^ k` is the weighted Gaussian binomial
coefficient `q ^ (k * (k - 1) / 2) * [n choose k]_q`.  We use its recursion as the
definition, so that no invertibility hypotheses or rational functions are needed.
-/

namespace VOA.QSeries

open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- The weighted Gaussian binomial coefficient, defined by adjoining the factor
`1 + z * q ^ n`.  Its normalization includes `q ^ (k * (k - 1) / 2)`. -/
def weightedGaussian (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => weightedGaussian q n (k + 1) + q ^ n * weightedGaussian q n k

@[simp]
theorem weightedGaussian_zero_right (q : R) (n : ℕ) :
    weightedGaussian q n 0 = 1 := by
  cases n <;> rfl

@[simp]
theorem weightedGaussian_zero_succ (q : R) (k : ℕ) :
    weightedGaussian q 0 (k + 1) = 0 := rfl

/-- The Pascal recursion with the weight contributed by the newly adjoined factor. -/
theorem weightedGaussian_succ_succ (q : R) (n k : ℕ) :
    weightedGaussian q (n + 1) (k + 1) =
      weightedGaussian q n (k + 1) + q ^ n * weightedGaussian q n k := rfl

/-- There are no terms of degree greater than the number of factors. -/
theorem weightedGaussian_eq_zero_of_lt (q : R) {n k : ℕ} (h : n < k) :
    weightedGaussian q n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [weightedGaussian_succ_succ, ih (by omega), ih (by omega)]
          simp

/-- The finite, division-free q-binomial theorem. -/
theorem finite_qBinomial (q z : R) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 + z * q ^ j)) =
      ∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * z ^ k := by
  induction n with
  | zero => simp [weightedGaussian]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih,
        Finset.sum_range_succ' (fun k => weightedGaussian q (n + 1) k * z ^ k) (n + 1)]
      simp only [weightedGaussian_zero_right, pow_zero, mul_one,
        weightedGaussian_succ_succ, add_mul, Finset.sum_add_distrib]
      have hshift :
          (∑ k ∈ Finset.range (n + 1), weightedGaussian q n (k + 1) * z ^ (k + 1)) + 1 =
            ∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * z ^ k := by
        have h := Finset.sum_range_succ' (fun k => weightedGaussian q n k * z ^ k) (n + 1)
        rw [Finset.sum_range_succ] at h
        simpa [weightedGaussian_eq_zero_of_lt q (Nat.lt_succ_self n)] using h.symm
      have hmul :
          (∑ k ∈ Finset.range (n + 1), q ^ n * weightedGaussian q n k * z ^ (k + 1)) =
            (∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * z ^ k) * (z * q ^ n) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_succ]
        ring
      rw [hmul, add_right_comm, hshift]
      ring

/-- The ordinary Gaussian binomial coefficient, by its division-free Pascal recursion. -/
def gaussian (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gaussian q n (k + 1) + q ^ (n - k) * gaussian q n k

@[simp]
theorem gaussian_zero_right (q : R) (n : ℕ) : gaussian q n 0 = 1 := by
  cases n <;> rfl

@[simp]
theorem gaussian_zero_succ (q : R) (k : ℕ) : gaussian q 0 (k + 1) = 0 := rfl

/-- The Gaussian Pascal recursion. -/
theorem gaussian_succ_succ (q : R) (n k : ℕ) :
    gaussian q (n + 1) (k + 1) =
      gaussian q n (k + 1) + q ^ (n - k) * gaussian q n k := rfl

/-- Gaussian coefficients vanish outside the binomial triangle. -/
theorem gaussian_eq_zero_of_lt (q : R) {n k : ℕ} (h : n < k) :
    gaussian q n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [gaussian_succ_succ, ih (by omega), ih (by omega)]
          simp

@[simp]
theorem gaussian_self (q : R) (n : ℕ) : gaussian q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [gaussian_succ_succ, gaussian_eq_zero_of_lt q (Nat.lt_succ_self n), ih]

/-- The precise normalization relating the two recursive coefficients. -/
theorem weightedGaussian_eq (q : R) (n k : ℕ) :
    weightedGaussian q n k = q ^ (k.choose 2) * gaussian q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [weightedGaussian, gaussian]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          by_cases hk : k ≤ n
          · have hchoose : (k + 1).choose 2 = k + k.choose 2 := by
              simpa using Nat.choose_succ_succ k 1
            have hpower : q ^ n * q ^ (k.choose 2) =
                q ^ ((k + 1).choose 2) * q ^ (n - k) := by
              rw [← pow_add, ← pow_add, hchoose]
              congr 1
              omega
            rw [weightedGaussian_succ_succ, gaussian_succ_succ, ih, ih, mul_add]
            rw [← mul_assoc (q ^ n), hpower, mul_assoc]
          · rw [weightedGaussian_eq_zero_of_lt q (by omega),
                gaussian_eq_zero_of_lt q (by omega), mul_zero]

/-- The leading coefficient is the product of the geometric progression. -/
@[simp]
theorem weightedGaussian_self (q : R) (n : ℕ) :
    weightedGaussian q n n = q ^ (n.choose 2) := by
  simp [weightedGaussian_eq]

/-- At `q = 1`, Gaussian coefficients specialize to ordinary binomial coefficients. -/
@[simp]
theorem gaussian_one (n k : ℕ) : gaussian (1 : R) n k = (n.choose k : R) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussian]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          simp [gaussian_succ_succ, ih, Nat.choose_succ_succ, add_comm]

/-- The standard finite q-binomial theorem, valid without division in any commutative semiring. -/
theorem finite_qBinomial_gaussian (q z : R) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 + z * q ^ j)) =
      ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * gaussian q n k * z ^ k := by
  simpa only [weightedGaussian_eq] using finite_qBinomial q z n

/-- Applying a semiring homomorphism commutes with Gaussian coefficients. -/
theorem map_gaussian {S : Type*} [CommSemiring S] (f : R →+* S) (q : R) (n k : ℕ) :
    f (gaussian q n k) = gaussian (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussian]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k => simp [gaussian_succ_succ, ih]

/-- The weighted coefficients are also natural under semiring homomorphisms. -/
theorem map_weightedGaussian {S : Type*} [CommSemiring S] (f : R →+* S)
    (q : R) (n k : ℕ) :
    f (weightedGaussian q n k) = weightedGaussian (f q) n k := by
  simp [weightedGaussian_eq, map_gaussian]

section Ring

variable {A : Type*} [CommRing A]

/-- Finite q-Pochhammer products have the usual signed Gaussian expansion. -/
theorem pochhammer_eq_sum_gaussian (a q : A) (n : ℕ) :
    pochhammer a q n =
      ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * gaussian q n k * (-a) ^ k := by
  simpa only [pochhammer, neg_mul, sub_eq_add_neg] using
    finite_qBinomial_gaussian q (-a) n

/-- The corresponding finite Euler-product expansion. -/
theorem qFactorial_eq_sum_gaussian (q : A) (n : ℕ) :
    qFactorial q n =
      ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * gaussian q n k * (-q) ^ k :=
  pochhammer_eq_sum_gaussian q q n

/-- The factorial formula without division.  This remains valid even when the factors
`1 - q ^ j` are zero or are not units. -/
theorem gaussian_mul_qFactorial (q : A) (n k : ℕ) (hk : k ≤ n) :
    gaussian q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          by_cases hkn : k = n
          · subst k
            simp
          · have hlt : k + 1 ≤ n := by omega
            have hsub : n - k = n - (k + 1) + 1 := by omega
            have hfirst :
                gaussian q n (k + 1) * qFactorial q (k + 1) * qFactorial q (n - k) =
                  qFactorial q n * (1 - q ^ (n - k)) := by
              rw [hsub, qFactorial_succ q (n - (k + 1)), ← mul_assoc, ih (k + 1) hlt]
            have hsecond :
                q ^ (n - k) * gaussian q n k * qFactorial q (k + 1) *
                    qFactorial q (n - k) =
                  q ^ (n - k) * qFactorial q n * (1 - q ^ (k + 1)) := by
              rw [qFactorial_succ]
              calc
                _ = q ^ (n - k) *
                    (gaussian q n k * qFactorial q k * qFactorial q (n - k)) *
                    (1 - q ^ (k + 1)) := by ring
                _ = _ := by rw [ih k (by omega)]
            rw [gaussian_succ_succ, Nat.succ_sub_succ, add_mul, add_mul, hfirst, hsecond,
              qFactorial_succ]
            have hexp : n + 1 = (n - k) + (k + 1) := by omega
            rw [hexp, pow_add]
            ring

/-- A Gaussian polynomial acquires no new coefficients below the next Pascal weight. -/
theorem coeff_gaussian_succ (n k d : ℕ) (h : d + k ≤ n) :
    PowerSeries.coeff d (gaussian (PowerSeries.X : PowerSeries A) (n + 1) k) =
      PowerSeries.coeff d (gaussian (PowerSeries.X : PowerSeries A) n k) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [gaussian_succ_succ, map_add, PowerSeries.coeff_X_pow_mul']
      simp [show ¬ n - k ≤ d by omega]

/-- Each fixed Gaussian coefficient stabilizes as its upper index tends to infinity. -/
theorem coeff_gaussian_stable (n N k d : ℕ) (h : d + k ≤ n) (hN : n ≤ N) :
    PowerSeries.coeff d (gaussian (PowerSeries.X : PowerSeries A) N k) =
      PowerSeries.coeff d (gaussian (PowerSeries.X : PowerSeries A) n k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  clear hN
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, coeff_gaussian_succ (n + r) k d (by omega), ih]

/-- The Gaussian polynomial has constant coefficient one throughout the binomial triangle. -/
theorem constantCoeff_gaussian (n k : ℕ) (h : k ≤ n) :
    PowerSeries.constantCoeff (gaussian (PowerSeries.X : PowerSeries A) n k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_gaussian_stable k n k 0 (by omega) h, gaussian_self]
  simp

end Ring

end VOA.QSeries
