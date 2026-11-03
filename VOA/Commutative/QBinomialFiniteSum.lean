/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QBinomial
import VOA.Commutative.QBinomialSeries

/-!
# The finite Gaussian summation

The finite summation underlying Lemma 5.2 of Arakawa--Dai, arXiv:2609.33348.
-/

namespace VOA.QSeries

open scoped BigOperators

section Algebra

variable {R : Type*} [CommSemiring R]

/-- The Gaussian-weighted sum used in the finite q-binomial summation. -/
def gaussianSum (q : R) (r : ℕ → R) (n d : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), gaussian q n j * q ^ (j * (j + d)) * r (j + d)

@[simp] theorem gaussianSum_zero (q : R) (r : ℕ → R) (d : ℕ) :
    gaussianSum q r 0 d = r d := by
  simp [gaussianSum]

/-- Pascal's recursion simultaneously shifts the upper index and the denominator offset. -/
theorem gaussianSum_succ (q : R) (r : ℕ → R) (n d : ℕ) :
    gaussianSum q r (n + 1) d =
      gaussianSum q r n d + q ^ (n + 1 + d) * gaussianSum q r n (d + 1) := by
  unfold gaussianSum
  rw [Finset.sum_range_succ'
    (fun j => gaussian q (n + 1) j * q ^ (j * (j + d)) * r (j + d)) (n + 1)]
  simp only [gaussian_succ_succ, add_mul, Finset.sum_add_distrib,
    gaussian_zero_right, Nat.zero_mul, pow_zero, one_mul, Nat.zero_add]
  have hshift :
      (∑ j ∈ Finset.range (n + 1),
        gaussian q n (j + 1) * q ^ ((j + 1) * (j + 1 + d)) * r (j + 1 + d)) + r d =
      ∑ j ∈ Finset.range (n + 1), gaussian q n j * q ^ (j * (j + d)) * r (j + d) := by
    have h := Finset.sum_range_succ'
      (fun j => gaussian q n j * q ^ (j * (j + d)) * r (j + d)) (n + 1)
    rw [Finset.sum_range_succ] at h
    simpa [gaussian_eq_zero_of_lt q (Nat.lt_succ_self n)] using h.symm
  have hmul :
      (∑ j ∈ Finset.range (n + 1),
        q ^ (n - j) * gaussian q n j * q ^ ((j + 1) * (j + 1 + d)) * r (j + 1 + d)) =
      q ^ (n + 1 + d) *
        ∑ j ∈ Finset.range (n + 1), gaussian q n j * q ^ (j * (j + (d + 1))) *
          r (j + (d + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using (Finset.mem_range.mp hj)
    have hexp : n - j + (j + 1) * (j + 1 + d) = n + 1 + d + j * (j + (d + 1)) := by
      have hn : n - j + j = n := Nat.sub_add_cancel hjn
      nlinarith
    calc
      _ = gaussian q n j * q ^ (n - j + (j + 1) * (j + 1 + d)) * r (j + 1 + d) := by
        rw [pow_add]
        ring
      _ = _ := by rw [hexp, pow_add]; simp only [Nat.add_assoc, Nat.add_comm 1 d]; ring
  simp only [add_mul, one_mul] at hshift hmul
  rw [hmul, add_right_comm, hshift]

/-- Any denominator sequence satisfying the first-order recurrence satisfies the finite sum. -/
theorem gaussianSum_eq (q : R) (r : ℕ → R)
    (hr : ∀ m, r m + q ^ (m + 1) * r (m + 1) = r (m + 1)) (n d : ℕ) :
    gaussianSum q r n d = r (n + d) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
      rw [gaussianSum_succ, ih, ih]
      simpa [Nat.add_assoc, Nat.add_comm 1 d] using hr (n + d)

end Algebra

section FormalSeries

variable {R : Type*} [CommRing R]

/-- The normalized finite summation, with denominator units interpreted in `R[[q]]`. -/
theorem gaussianSum_reciprocalQFactorial (n d : ℕ) :
    gaussianSum PowerSeries.X (reciprocalQFactorial (R := R)) n d =
      reciprocalQFactorial (n + d) := by
  apply gaussianSum_eq
  intro m
  have h := one_sub_X_pow_mul_reciprocalQFactorial (R := R) m
  linear_combination -h

/-- A Gaussian coefficient is the ratio of three finite Euler products. -/
theorem gaussian_eq_qFactorial_ratio (n k : ℕ) (hk : k ≤ n) :
    gaussian (PowerSeries.X : PowerSeries R) n k =
      qFactorial PowerSeries.X n * reciprocalQFactorial k * reciprocalQFactorial (n - k) := by
  calc
    _ = gaussian (PowerSeries.X : PowerSeries R) n k *
        ((qFactorial PowerSeries.X k * reciprocalQFactorial k) *
          (qFactorial PowerSeries.X (n - k) * reciprocalQFactorial (n - k))) := by simp
    _ = (gaussian (PowerSeries.X : PowerSeries R) n k *
          qFactorial PowerSeries.X k * qFactorial PowerSeries.X (n - k)) *
        reciprocalQFactorial k * reciprocalQFactorial (n - k) := by ring
    _ = _ := by rw [gaussian_mul_qFactorial _ n k hk]

/-- Arakawa--Dai Lemma 5.2: the finite three-denominator summation identity.
The notation `reciprocalQFactorial k` means `1 / (q)_k`,
formed using a proved formal-series unit. -/
theorem finite_three_denominator_sum (n d : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (PowerSeries.X : PowerSeries R) ^ (j * (j + d)) *
        reciprocalQFactorial (n - j) * reciprocalQFactorial j * reciprocalQFactorial (j + d)) =
      reciprocalQFactorial n * reciprocalQFactorial (n + d) := by
  apply (isUnit_qFactorial (R := R) n).mul_left_cancel
  calc
    _ = gaussianSum PowerSeries.X (reciprocalQFactorial (R := R)) n d := by
      rw [Finset.mul_sum]
      unfold gaussianSum
      apply Finset.sum_congr rfl
      intro j hj
      rw [gaussian_eq_qFactorial_ratio n j (by simpa using Finset.mem_range.mp hj)]
      ring
    _ = reciprocalQFactorial (n + d) := gaussianSum_reciprocalQFactorial n d
    _ = _ := by rw [← mul_assoc, qFactorial_mul_reciprocal, one_mul]

/-- The shifted finite summation (equation 5.26), with `j = r + ℓ` and upper
endpoint `r + N`.  Reindexing this way makes all factorial arguments natural numbers. -/
theorem finite_shifted_three_denominator_sum (N r : ℕ) :
    (∑ ℓ ∈ Finset.range (N + 1),
      (PowerSeries.X : PowerSeries R) ^ ((r + ℓ) * (r + ℓ + 1)) *
        reciprocalQFactorial (N - ℓ) * reciprocalQFactorial ℓ *
          reciprocalQFactorial (ℓ + (2 * r + 1))) =
      PowerSeries.X ^ (r * (r + 1)) *
        reciprocalQFactorial N * reciprocalQFactorial (N + (2 * r + 1)) := by
  calc
    _ = (PowerSeries.X : PowerSeries R) ^ (r * (r + 1)) *
        (∑ ℓ ∈ Finset.range (N + 1),
          PowerSeries.X ^ (ℓ * (ℓ + (2 * r + 1))) *
            reciprocalQFactorial (N - ℓ) * reciprocalQFactorial ℓ *
              reciprocalQFactorial (ℓ + (2 * r + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hexp : (r + ℓ) * (r + ℓ + 1) = r * (r + 1) + ℓ * (ℓ + (2 * r + 1)) := by ring
      rw [hexp, pow_add]
      ring
    _ = _ := by rw [finite_three_denominator_sum]; ring

/-- Equation 5.26 with the paper's upper endpoint `n`, retaining the explicit
shifted index `ℓ = j - r` to avoid interval-subtraction side conditions. -/
theorem finite_shifted_three_denominator_sum_of_le (n r : ℕ) (hr : r ≤ n) :
    (∑ ℓ ∈ Finset.range (n - r + 1),
      (PowerSeries.X : PowerSeries R) ^ ((r + ℓ) * (r + ℓ + 1)) *
        reciprocalQFactorial (n - (r + ℓ)) * reciprocalQFactorial ℓ *
          reciprocalQFactorial (r + ℓ + r + 1)) =
      PowerSeries.X ^ (r * (r + 1)) *
        reciprocalQFactorial (n - r) * reciprocalQFactorial (n + r + 1) := by
  have h := finite_shifted_three_denominator_sum (R := R) (n - r) r
  have hend : n - r + (2 * r + 1) = n + r + 1 := by omega
  rw [hend] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [show n - (r + ℓ) = n - r - ℓ by omega,
    show r + ℓ + r + 1 = ℓ + (2 * r + 1) by omega]

/-- Multiplication preserves agreement through a fixed coefficient cutoff. -/
theorem coeff_mul_congr_left_upto (m : ℕ) (f g h : PowerSeries R)
    (hfg : ∀ i, i ≤ m → PowerSeries.coeff i f = PowerSeries.coeff i g) :
    PowerSeries.coeff m (f * h) = PowerSeries.coeff m (g * h) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hfg ij.1 (by have hsum := Finset.mem_antidiagonal.mp hij; omega)]

/-- The stable Gaussian coefficients equal those of the reciprocal finite Euler product. -/
theorem coeff_gaussian_eq_reciprocalQFactorial (n k m : ℕ) (h : m + k ≤ n) :
    PowerSeries.coeff m (gaussian (PowerSeries.X : PowerSeries R) n k) =
      PowerSeries.coeff m (reciprocalQFactorial k : PowerSeries R) := by
  rw [gaussian_eq_qFactorial_ratio n k (by omega), mul_assoc]
  calc
    _ = PowerSeries.coeff m
        (qFactorial PowerSeries.X (n - k) *
          (reciprocalQFactorial k * reciprocalQFactorial (n - k)) : PowerSeries R) := by
      apply coeff_mul_congr_left_upto
      intro i hi
      exact coeff_qFactorial_stable i (n - k) n (by omega) (by omega)
    _ = _ := by
      have heq : (qFactorial PowerSeries.X (n - k) *
          (reciprocalQFactorial k * reciprocalQFactorial (n - k)) : PowerSeries R) =
          reciprocalQFactorial k := by
        calc
          _ = reciprocalQFactorial k *
              (qFactorial PowerSeries.X (n - k) * reciprocalQFactorial (n - k)) := by ring
          _ = _ := by simp
      rw [heq]

/-- The infinite Durfee-rectangle identity, stated coefficientwise with an explicit
sufficient finite cutoff.  No topological infinite sum is required. -/
theorem coeff_durfee_sum (m d : ℕ) :
    PowerSeries.coeff m
      (∑ j ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries R) ^ (j * (j + d)) *
          reciprocalQFactorial j * reciprocalQFactorial (j + d)) =
      PowerSeries.coeff m (reciprocalEuler : PowerSeries R) := by
  calc
    _ = ∑ j ∈ Finset.range (m + 1), PowerSeries.coeff m
        (gaussian (PowerSeries.X : PowerSeries R) (2 * m) j *
          PowerSeries.X ^ (j * (j + d)) * reciprocalQFactorial (j + d)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := by simpa using Finset.mem_range.mp hj
      have heq := coeff_mul_congr_left_upto m
        (reciprocalQFactorial j : PowerSeries R)
        (gaussian PowerSeries.X (2 * m) j)
        (PowerSeries.X ^ (j * (j + d)) * reciprocalQFactorial (j + d))
        (fun i hi => (coeff_gaussian_eq_reciprocalQFactorial (2 * m) j i (by omega)).symm)
      convert heq using 1 <;> congr 1 <;> ring
    _ = ∑ j ∈ Finset.range (2 * m + 1), PowerSeries.coeff m
        (gaussian (PowerSeries.X : PowerSeries R) (2 * m) j *
          PowerSeries.X ^ (j * (j + d)) * reciprocalQFactorial (j + d)) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjnot
      have hjm : m < j := by simpa using hjnot
      have hexp : m < j * (j + d) := by nlinarith
      have heq : (gaussian (PowerSeries.X : PowerSeries R) (2 * m) j *
          PowerSeries.X ^ (j * (j + d)) * reciprocalQFactorial (j + d)) =
          PowerSeries.X ^ (j * (j + d)) *
            (gaussian PowerSeries.X (2 * m) j * reciprocalQFactorial (j + d)) := by ring
      rw [heq, PowerSeries.coeff_X_pow_mul']
      simp [show ¬ j * (j + d) ≤ m by omega]
    _ = PowerSeries.coeff m
        (gaussianSum PowerSeries.X (reciprocalQFactorial (R := R)) (2 * m) d) := by
      simp only [gaussianSum, map_sum]
    _ = PowerSeries.coeff m (reciprocalQFactorial (2 * m + d) : PowerSeries R) := by
      rw [gaussianSum_reciprocalQFactorial]
    _ = _ := (coeff_reciprocalEuler m (2 * m + d) (by omega)).symm

end FormalSeries

end VOA.QSeries
