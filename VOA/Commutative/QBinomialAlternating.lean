/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QBinomialFiniteSum
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.LaurentSeries

/-!
# The differentiated finite q-binomial identity

The algebraic foundation for the alternating identity in Section 5.5 of
Arakawa--Dai, arXiv:2609.33348.
-/

namespace VOA.QSeries

open scoped BigOperators

section Polynomial

variable {R : Type*} [CommRing R]

/-- Polynomial form of the finite q-binomial theorem. -/
theorem pochhammer_polynomial (q : R) (N : ℕ) :
    pochhammer (Polynomial.X : Polynomial R) (Polynomial.C q) N =
      ∑ k ∈ Finset.range (N + 1),
        Polynomial.C ((-1 : R) ^ k * q ^ (k.choose 2) * gaussian q N k) *
          Polynomial.X ^ k := by
  rw [pochhammer_eq_sum_gaussian]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← map_gaussian Polynomial.C]
  rw [neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- Logarithmic differentiation of a finite polynomial reads its weighted coefficients. -/
theorem eval_logDerivative_sum (a : ℕ → R) (N : ℕ) (z : R) :
    z * Polynomial.eval z
        (Polynomial.derivative (∑ k ∈ Finset.range (N + 1),
          Polynomial.C (a k) * Polynomial.X ^ k)) =
      ∑ k ∈ Finset.range (N + 1), (k : R) * a k * z ^ k := by
  rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.derivative_C_mul_X_pow]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring

/-- The finite q-binomial coefficient expression for the logarithmic derivative. -/
theorem pochhammer_logDerivative (q z : R) (N : ℕ) :
    z * Polynomial.eval z
      (Polynomial.derivative (pochhammer (Polynomial.X : Polynomial R) (Polynomial.C q) N)) =
      ∑ k ∈ Finset.range (N + 1),
        (k : R) * ((-1 : R) ^ k * q ^ (k.choose 2) * gaussian q N k) * z ^ k := by
  rw [pochhammer_polynomial]
  exact eval_logDerivative_sum _ _ _

/-- Split the odd finite product around its central factor. -/
theorem pochhammer_odd_split (a q : R) (n : ℕ) :
    pochhammer a q (2 * n + 1) =
      pochhammer a q n * (1 - a * q ^ n) * pochhammer (a * q ^ (n + 1)) q n := by
  rw [show 2 * n + 1 = (n + 1) + n by omega, pochhammer_add, pochhammer_succ]

/-- Evaluation commutes with a finite q-Pochhammer product. -/
theorem eval_pochhammer (a q : Polynomial R) (N : ℕ) (z : R) :
    Polynomial.eval z (pochhammer a q N) =
      pochhammer (Polynomial.eval z a) (Polynomial.eval z q) N := by
  simp [pochhammer, Polynomial.eval_prod]

/-- Finite q-Pochhammer products commute with ring homomorphisms. -/
theorem map_pochhammer {S : Type*} [CommRing S] (f : R →+* S) (a q : R) (n : ℕ) :
    f (pochhammer a q n) = pochhammer (f a) (f q) n := by
  simp [pochhammer, map_prod]

/-- Finite Euler products commute with ring homomorphisms. -/
theorem map_qFactorial {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n : ℕ) :
    f (qFactorial q n) = qFactorial (f q) n := map_pochhammer f q q n

end Polynomial

section Field

variable {K : Type*} [Field K]

/-- At the central root only the derivative of the central factor survives. -/
theorem pochhammer_logDerivative_at_root (q z : K) (n : ℕ) (hz : z * q ^ n = 1) :
    z * Polynomial.eval z
      (Polynomial.derivative (pochhammer (Polynomial.X : Polynomial K) (Polynomial.C q)
        (2 * n + 1))) = -pochhammer z q n * qFactorial q n := by
  have hzsucc : z * q ^ (n + 1) = q := by rw [pow_succ, ← mul_assoc, hz, one_mul]
  rw [pochhammer_odd_split]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X, ← map_pow, Polynomial.derivative_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C, zero_mul, mul_zero,
    add_zero, zero_add, zero_sub, Polynomial.eval_neg, eval_pochhammer,
    hz, hzsucc, sub_self]
  dsimp [qFactorial]
  calc
    _ = -(z * q ^ n) * pochhammer z q n * pochhammer q q n := by ring
    _ = _ := by rw [hz]; ring

/-- A triangular-number identity in a form convenient for exponent arithmetic. -/
theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith

/-- The central inverse q-Pochhammer product. -/
theorem pochhammer_inverse_power (q : K) (hq : q ≠ 0) (n : ℕ) :
    pochhammer ((q ^ n)⁻¹) q n =
      (-1 : K) ^ n * (q ^ ((n + 1).choose 2))⁻¹ * qFactorial q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega, pochhammer_add, pochhammer_one]
      have hinv : (q ^ (1 + n))⁻¹ * q = (q ^ n)⁻¹ := by
        rw [pow_add, pow_one, mul_inv_rev]
        field_simp
      rw [pow_one, hinv, ih, show 1 + n = n + 1 by omega]
      have htri : (n + 1 + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
        simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ (n + 1) 1
      rw [htri, pow_add q ((n + 1).choose 2) (n + 1), mul_inv_rev,
        qFactorial_succ, pow_succ (-1 : K) n]
      have hfactor : 1 - (q ^ (n + 1))⁻¹ =
          -(q ^ (n + 1))⁻¹ * (1 - q ^ (n + 1)) := by
        field_simp
        ring
      rw [hfactor]
      ring

/-- The evaluated logarithmic derivative, expressed in terms of the finite Euler product. -/
theorem pochhammer_logDerivative_inverse (q : K) (hq : q ≠ 0) (n : ℕ) :
    (q ^ n)⁻¹ * Polynomial.eval (q ^ n)⁻¹
      (Polynomial.derivative (pochhammer (Polynomial.X : Polynomial K) (Polynomial.C q)
        (2 * n + 1))) =
      (-1 : K) ^ (n + 1) * (q ^ ((n + 1).choose 2))⁻¹ * (qFactorial q n) ^ 2 := by
  rw [pochhammer_logDerivative_at_root q _ n (inv_mul_cancel₀ (pow_ne_zero n hq)),
    pochhammer_inverse_power q hq, pow_succ]
  ring

/-- Symmetry of the Gaussian coefficient when its two denominator products are nonzero. -/
theorem gaussian_symm_field (q : K) (n k : ℕ) (hk : k ≤ n)
    (hleft : qFactorial q k ≠ 0) (hright : qFactorial q (n - k) ≠ 0) :
    gaussian q n (n - k) = gaussian q n k := by
  apply mul_right_cancel₀ (mul_ne_zero hleft hright)
  calc
    _ = gaussian q n (n - k) * qFactorial q (n - k) * qFactorial q (n - (n - k)) := by
      rw [Nat.sub_sub_self hk]
      ring
    _ = qFactorial q n := gaussian_mul_qFactorial q n (n - k) (Nat.sub_le _ _)
    _ = _ := by rw [← gaussian_mul_qFactorial q n k hk]; ring

/-- Pair the lower and upper halves of an odd binomial row. -/
theorem sum_range_centered_pairs (f : ℕ → K) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1 + 1), f j) =
      ∑ r ∈ Finset.range (n + 1), (f (n - r) + f (n + r + 1)) := by
  rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega, Finset.sum_range_add,
    ← Finset.sum_range_reflect f (n + 1), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Nat.add_sub_cancel]
  rw [show n + 1 + r = n + r + 1 by omega]

/-- The lower paired exponent after centering the q-binomial expansion. -/
theorem centered_choose_left (n r : ℕ) (hr : r ≤ n) :
    (n - r).choose 2 + (n + 1).choose 2 = n * (n - r) + (r + 1).choose 2 := by
  have hnr := Nat.sub_add_cancel hr
  have h1 := two_mul_choose_two_add (n - r)
  have h2 := two_mul_choose_two_add (n + 1)
  have h3 := two_mul_choose_two_add (r + 1)
  nlinarith

/-- The upper paired exponent is equal to the lower one. -/
theorem centered_choose_right (n r : ℕ) :
    (n + r + 1).choose 2 + (n + 1).choose 2 =
      n * (n + r + 1) + (r + 1).choose 2 := by
  have h1 := two_mul_choose_two_add (n + r + 1)
  have h2 := two_mul_choose_two_add (n + 1)
  have h3 := two_mul_choose_two_add (r + 1)
  nlinarith

/-- Cancel the common inverse monomial in a centered q-binomial term. -/
theorem centered_power (q : K) (hq : q ≠ 0) (n j r : ℕ)
    (hexp : j.choose 2 + (n + 1).choose 2 = n * j + (r + 1).choose 2) :
    q ^ ((n + 1).choose 2) * (q ^ (j.choose 2) * ((q ^ n)⁻¹) ^ j) =
      q ^ ((r + 1).choose 2) := by
  rw [← mul_assoc, ← pow_add, Nat.add_comm ((n + 1).choose 2), hexp,
    pow_add, pow_mul, inv_pow]
  field_simp

/-- The sign of the lower centered index. -/
theorem centered_sign_left (n r : ℕ) (hr : r ≤ n) :
    (-1 : K) ^ (n + 1) * (-1 : K) ^ (n - r) = -((-1 : K) ^ r) := by
  rw [← pow_add, show n + 1 + (n - r) = 2 * (n - r) + (r + 1) by omega,
    pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_succ]
  ring

/-- The sign of the upper centered index. -/
theorem centered_sign_right (n r : ℕ) :
    (-1 : K) ^ (n + 1) * (-1 : K) ^ (n + r + 1) = (-1 : K) ^ r := by
  rw [← pow_add, show n + 1 + (n + r + 1) = 2 * (n + 1) + r by omega,
    pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- A term of the differentiated q-binomial expansion at the central root. -/
def logBinomialTerm (q : K) (n j : ℕ) : K :=
  (j : K) * ((-1 : K) ^ j * q ^ (j.choose 2) * gaussian q (2 * n + 1) j) *
    ((q ^ n)⁻¹) ^ j

/-- Normalizing one differentiated term removes its inverse q-power. -/
theorem scaled_logBinomialTerm (q : K) (hq : q ≠ 0) (n j r : ℕ)
    (hexp : j.choose 2 + (n + 1).choose 2 = n * j + (r + 1).choose 2) :
    ((-1 : K) ^ (n + 1) * q ^ ((n + 1).choose 2)) * logBinomialTerm q n j =
      (j : K) * ((-1 : K) ^ (n + 1) * (-1 : K) ^ j) *
        q ^ ((r + 1).choose 2) * gaussian q (2 * n + 1) j := by
  calc
    _ = (j : K) * ((-1 : K) ^ (n + 1) * (-1 : K) ^ j) *
        (q ^ ((n + 1).choose 2) * (q ^ (j.choose 2) * ((q ^ n)⁻¹) ^ j)) *
        gaussian q (2 * n + 1) j := by unfold logBinomialTerm; ring
    _ = _ := by rw [centered_power q hq n j r hexp]

/-- Each centered pair contributes the alternating odd coefficient. -/
theorem scaled_logBinomial_pair (q : K) (hq : q ≠ 0) (n r : ℕ) (hr : r ≤ n)
    (hf : ∀ j, j ≤ 2 * n + 1 → qFactorial q j ≠ 0) :
    ((-1 : K) ^ (n + 1) * q ^ ((n + 1).choose 2)) *
        (logBinomialTerm q n (n - r) + logBinomialTerm q n (n + r + 1)) =
      (-1 : K) ^ r * (2 * r + 1 : ℕ) * q ^ ((r + 1).choose 2) *
        gaussian q (2 * n + 1) (n - r) := by
  rw [mul_add, scaled_logBinomialTerm q hq n (n - r) r (centered_choose_left n r hr),
    scaled_logBinomialTerm q hq n (n + r + 1) r (centered_choose_right n r),
    centered_sign_left n r hr, centered_sign_right]
  have hsym : gaussian q (2 * n + 1) (n + r + 1) =
      gaussian q (2 * n + 1) (n - r) := by
    have h := gaussian_symm_field q (2 * n + 1) (n - r) (by omega)
      (hf (n - r) (by omega)) (hf (2 * n + 1 - (n - r)) (by omega))
    simpa [show 2 * n + 1 - (n - r) = n + r + 1 by omega] using h
  rw [hsym]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sub hr]
  ring

/-- The finite alternating q-binomial identity over a field at a nonzero parameter.
The nonvanishing hypotheses here allow the generic field proof; the formal-series
specialization below discharges them using the constant coefficient of each product. -/
theorem finite_alternating_field (q : K) (hq : q ≠ 0) (n : ℕ)
    (hf : ∀ j, j ≤ 2 * n + 1 → qFactorial q j ≠ 0) :
    (qFactorial q n) ^ 2 =
      ∑ r ∈ Finset.range (n + 1),
        (-1 : K) ^ r * (2 * r + 1 : ℕ) * q ^ ((r + 1).choose 2) *
          gaussian q (2 * n + 1) (n - r) := by
  have hm := pochhammer_logDerivative q ((q ^ n)⁻¹) (2 * n + 1)
  rw [pochhammer_logDerivative_inverse q hq n] at hm
  change (-1 : K) ^ (n + 1) * (q ^ ((n + 1).choose 2))⁻¹ * qFactorial q n ^ 2 =
    ∑ j ∈ Finset.range (2 * n + 1 + 1), logBinomialTerm q n j at hm
  have hs := congrArg (fun x => ((-1 : K) ^ (n + 1) * q ^ ((n + 1).choose 2)) * x) hm
  have hsign : (-1 : K) ^ (n + 1) * (-1 : K) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hscale :
      ((-1 : K) ^ (n + 1) * q ^ ((n + 1).choose 2)) *
        ((-1 : K) ^ (n + 1) * (q ^ ((n + 1).choose 2))⁻¹ * qFactorial q n ^ 2) =
      qFactorial q n ^ 2 := by
    calc
      _ = ((-1 : K) ^ (n + 1) * (-1 : K) ^ (n + 1)) *
          (q ^ ((n + 1).choose 2) * (q ^ ((n + 1).choose 2))⁻¹) * qFactorial q n ^ 2 := by ring
      _ = _ := by rw [hsign, mul_inv_cancel₀ (pow_ne_zero _ hq)]; ring
  dsimp only at hs
  rw [hscale, sum_range_centered_pairs, Finset.mul_sum] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro r hr
  exact scaled_logBinomial_pair q hq n r (by simpa using Finset.mem_range.mp hr) hf

end Field

section FormalSeries

variable {K : Type*} [Field K]

/-- Arakawa--Dai equation 5.19 as an unconditional formal power-series identity. -/
theorem finite_alternating (n : ℕ) :
    (qFactorial (PowerSeries.X : PowerSeries K) n) ^ 2 =
      ∑ r ∈ Finset.range (n + 1),
        (-1 : PowerSeries K) ^ r * ((2 * r + 1 : ℕ) : PowerSeries K) *
          PowerSeries.X ^ ((r + 1).choose 2) *
            gaussian PowerSeries.X (2 * n + 1) (n - r) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K))
  have hq : f PowerSeries.X ≠ 0 := by
    intro h
    have hx : (PowerSeries.X : PowerSeries K) = 0 :=
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K))
        (h.trans (map_zero f).symm)
    exact PowerSeries.X_ne_zero hx
  have hf (j : ℕ) : qFactorial (f PowerSeries.X) j ≠ 0 := by
    rw [← map_qFactorial]
    exact ((isUnit_qFactorial (R := K) j).map f).ne_zero
  have h := finite_alternating_field (f PowerSeries.X) hq n (fun j _ => hf j)
  simpa only [map_pow, map_qFactorial, map_sum, map_mul, map_neg, map_one, map_natCast,
    map_gaussian] using h

end FormalSeries

end VOA.QSeries
