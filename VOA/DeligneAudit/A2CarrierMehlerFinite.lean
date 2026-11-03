/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterStarReduction

/-!
# Finite identities for the shifted Mehler formula

* `gaussian_pascal2`: `[n+1, j+1] = q^{j+1} [n, j+1] + [n, j]`;
* `rsy c n = ∑_i [n,i] q^{c i}` is the Rogers–Szegő polynomial `H_n(q^c)`; `rsy_succ`
  (`H_{n+1}(x) = x H_n(x) + H_n(q x)`) and the Vandermonde-type expansion `rsy_add`
  (`H_{k+l}(q^c) = ∑_j [l,j] q^{c j} H_k(q^{l-j+c})`);
* `rogersSzego_add`: `G_{s+m} = ∑_{j ≤ m} [m,j] H_s(q^{m-j})`;
* `gaussian_succ_mul`: `[m+1,j](1 - q^{m+1-j}) = [m,j](1 - q^{m+1})`;
* `sum_gaussian_qFactorial`: `∑_{j < n} [n,j] (q)_{n-1-j} = n`.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.QSeries VOA.DeligneGaussian

noncomputable section

local notation "q" => (PowerSeries.X : PowerSeries ℤ)
local notation "cc" => (reciprocalQFactorial : ℕ → PowerSeries ℤ)

/-- The second q-Pascal rule. -/
theorem gaussian_pascal2 {R : Type*} [CommRing R] (x : R) (n j : ℕ) :
    gaussian x (n + 1) (j + 1) = x ^ (j + 1) * gaussian x n (j + 1) + gaussian x n j := by
  have h := gaussian_vandermonde x 1 n (j + 1)
  rw [show 1 + n = n + 1 by omega] at h
  rw [h, Finset.sum_range_succ', Finset.sum_range_succ']
  rw [Finset.sum_eq_zero]
  · simp [gaussian_self, add_comm]
  · intro k _
    rw [gaussian_eq_zero_of_lt x (show 1 < k + 1 + 1 by omega), mul_zero, zero_mul]

/-- The Rogers–Szegő polynomial `H_n(q^c)`. -/
def rsy (c n : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range (n + 1), gaussian q n i * q ^ (c * i)

theorem rsy_succ (c n : ℕ) : rsy c (n + 1) = q ^ c * rsy c n + rsy (c + 1) n := by
  have hA : rsy (c + 1) n =
      (∑ i ∈ Finset.range (n + 1), gaussian q n (i + 1) * q ^ ((c + 1) * (i + 1))) + 1 := by
    have h1 := Finset.sum_range_succ' (fun i => gaussian q n i * q ^ ((c + 1) * i)) (n + 1)
    have h2 := Finset.sum_range_succ (fun i => gaussian q n i * q ^ ((c + 1) * i)) (n + 1)
    rw [gaussian_eq_zero_of_lt q (Nat.lt_succ_self n), zero_mul, add_zero] at h2
    rw [rsy, ← h2, h1]
    simp
  have step : rsy c (n + 1) =
      (∑ i ∈ Finset.range (n + 1), gaussian q n (i + 1) * q ^ ((c + 1) * (i + 1))) +
        q ^ c * rsy c n + 1 := by
    rw [rsy, Finset.sum_range_succ', gaussian_zero_right, rsy, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    simp only [Nat.mul_zero, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gaussian_pascal2, show (c + 1) * (i + 1) = (i + 1) + c * (i + 1) by ring,
      show c * (i + 1) = c + c * i by ring, pow_add, pow_add, pow_add]
    ring
  rw [step, hA]
  ring

/-- **Vandermonde expansion of Rogers–Szegő polynomials.** -/
theorem rsy_add (k : ℕ) : ∀ l c, rsy c (k + l) =
    ∑ j ∈ Finset.range (l + 1), gaussian q l j * q ^ (c * j) * rsy (l - j + c) k
  | 0, c => by simp
  | l + 1, c => by
    set S := ∑ j ∈ Finset.range (l + 1), gaussian q l j * q ^ (c * j) * rsy (l - j + c) k
    set P := ∑ j ∈ Finset.range (l + 1),
      q ^ (j + 1) * gaussian q l (j + 1) * q ^ (c * (j + 1)) * rsy (l - j + c) k
    have hT : (∑ j ∈ Finset.range (l + 1 + 1),
        gaussian q (l + 1) j * q ^ (c * j) * rsy (l + 1 - j + c) k) =
        P + q ^ c * S + rsy (l + 1 + c) k := by
      rw [Finset.sum_range_succ', gaussian_zero_right, Finset.mul_sum, ← Finset.sum_add_distrib]
      simp only [Nat.mul_zero, pow_zero, mul_one, one_mul, Nat.sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [gaussian_pascal2, show l + 1 - (j + 1) = l - j by omega,
        show c * (j + 1) = c + c * j by ring, pow_add]
      ring
    have hB : (∑ j ∈ Finset.range (l + 1),
        gaussian q l j * q ^ ((c + 1) * j) * rsy (l - j + (c + 1)) k) =
        P + rsy (l + 1 + c) k := by
      have h1 := Finset.sum_range_succ' (fun j => gaussian q l j * q ^ ((c + 1) * j) *
        rsy (l - j + (c + 1)) k) (l + 1)
      have h2 := Finset.sum_range_succ (fun j => gaussian q l j * q ^ ((c + 1) * j) *
        rsy (l - j + (c + 1)) k) (l + 1)
      rw [gaussian_eq_zero_of_lt q (Nat.lt_succ_self l), zero_mul, zero_mul, add_zero] at h2
      rw [← h2, h1]
      simp only [Nat.mul_zero, pow_zero, mul_one, gaussian_zero_right, one_mul, Nat.sub_zero]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rcases Nat.lt_or_ge j l with hjl | hjl
        · rw [show l - (j + 1) + (c + 1) = l - j + c by omega,
            show (c + 1) * (j + 1) = (j + 1) + c * (j + 1) by ring, pow_add]
          ring
        · rw [gaussian_eq_zero_of_lt q (show l < j + 1 by omega)]
          ring
      · congr 1; omega
    rw [show k + (l + 1) = (k + l) + 1 by omega, rsy_succ, rsy_add k l c, rsy_add k l (c + 1),
      hB, hT]
    ring

theorem rogersSzego_eq_rsy (n : ℕ) : rogersSzego n = rsy 0 n := by
  rw [rogersSzego, rsy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qbinom_eq_gaussian, Nat.zero_mul, pow_zero, mul_one]

/-- `G_{s+m} = ∑_{j ≤ m} [m,j] H_s(q^{m-j})`. -/
theorem rogersSzego_add (s m : ℕ) :
    rogersSzego (s + m) =
      ∑ j ∈ Finset.range (m + 1), gaussian q m j * rsy (m - j) s := by
  rw [rogersSzego_eq_rsy, rsy_add s m 0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.zero_mul, pow_zero, mul_one, Nat.add_zero]

/-- `H_k(q^c)/(q)_k = ∑_{i ≤ k} q^{c i}/((q)_i (q)_{k-i})`. -/
theorem rsy_mul_c (c k : ℕ) :
    rsy c k * cc k = ∑ i ∈ Finset.range (k + 1), q ^ (c * i) * (cc i * cc (k - i)) := by
  rw [rsy, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← gauss_mul_c k i (by omega)]
  ring

/-- `[m+1,j](1 - q^{m+1-j}) = [m,j](1 - q^{m+1})`. -/
theorem gaussian_succ_mul (m j : ℕ) (hj : j ≤ m) :
    gaussian q (m + 1) j * (1 - q ^ (m + 1 - j)) = gaussian q m j * (1 - q ^ (m + 1)) := by
  rw [gaussian_eq_qFactorial_ratio (m + 1) j (by omega), gaussian_eq_qFactorial_ratio m j hj,
    qFactorial_succ, show m + 1 - j = (m - j) + 1 by omega]
  have h := one_sub_X_pow_mul_reciprocalQFactorial (R := ℤ) (m - j)
  calc qFactorial q m * (1 - q ^ (m + 1)) * cc j * cc (m - j + 1) * (1 - q ^ (m - j + 1))
      = qFactorial q m * (1 - q ^ (m + 1)) * cc j * ((1 - q ^ (m - j + 1)) * cc (m - j + 1)) := by
        ring
    _ = _ := by rw [h]; ring

/-- **The finite identity** `∑_{j < n} [n,j] (q)_{n-1-j} = n`. -/
theorem sum_gaussian_qFactorial {R : Type*} [CommRing R] (x : R) : ∀ n : ℕ,
    (∑ j ∈ Finset.range n, gaussian x n j * qFactorial x (n - 1 - j)) = (n : R)
  | 0 => by simp
  | n + 1 => by
    have ih := sum_gaussian_qFactorial x n
    set A := ∑ j ∈ Finset.range (n + 1), gaussian x n j * qFactorial x (n - j) with hA
    -- `∑_{j<n} [n,j+1] (q)_{n-1-j} = A - (q)_n`
    have h1 : (∑ j ∈ Finset.range n, gaussian x n (j + 1) * qFactorial x (n - (j + 1))) =
        A - qFactorial x n := by
      rw [hA, Finset.sum_range_succ']
      simp
    -- `∑_{j<n} [n,j] (q)_{n-j} = A - 1`
    have h2 : (∑ j ∈ Finset.range n, gaussian x n j * qFactorial x (n - j)) = A - 1 := by
      rw [hA, Finset.sum_range_succ]
      simp [gaussian_self]
    -- `x^{n-j} (q)_{n-1-j} = (q)_{n-1-j} - (q)_{n-j}`
    have h3 : ∀ j ∈ Finset.range n, x ^ (n - j) * gaussian x n j * qFactorial x (n - (j + 1)) =
        gaussian x n j * qFactorial x (n - 1 - j) - gaussian x n j * qFactorial x (n - j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show n - j = (n - 1 - j) + 1 by omega, qFactorial_succ,
        show n - (j + 1) = n - 1 - j by omega]
      ring
    rw [Finset.sum_range_succ', gaussian_zero_right]
    simp only [gaussian_succ_succ, add_mul, Finset.sum_add_distrib, Nat.add_sub_cancel,
      Nat.sub_zero]
    rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, h1, h2, ih]
    push_cast
    ring

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms gaussian_pascal2
#print axioms rsy_add
#print axioms rogersSzego_add
#print axioms gaussian_succ_mul
#print axioms sum_gaussian_qFactorial
end AxiomAudit
