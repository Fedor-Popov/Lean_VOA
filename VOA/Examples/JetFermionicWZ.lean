/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Commutative.QBinomialFiniteSum

/-!
# A terminating q-series identity by a WZ certificate

For every `j`,

  `Σ_{r=0}^{j} (-1)^r q^{r + C(j-r+1, 2)} (q)_{j+r} / ((q)_r (q)_{j-r}) = q^{3 C(j+1, 2)}`.

The proof is a Wilf–Zeilberger telescoping: with the certificate
`Ĝ(j, m+1) = (-1)^m q^{C(j-m+2,2)+m} (1 + q^{j+1}) (q)_{j+m+1} / ((q)_m (q)_{j-m})`,
`Ĝ(j, 0) = 0`, one has `T(j+1, r) - q^{3(j+1)} T(j, r) = Ĝ(j, r+1) - Ĝ(j, r)`.
Each step is a polynomial identity after clearing the unit denominators.

* `wzSum_eq` — the identity, proved outright over every commutative ring.
-/

namespace VOA.JetFermionic

open VOA.QSeries
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The summand `(-1)^r q^{r + C(j-r+1,2)} (q)_{j+r} / ((q)_r (q)_{j-r})`. -/
def wzTerm (j r : ℕ) : PowerSeries R :=
  (-1 : PowerSeries R) ^ r * PowerSeries.X ^ (r + (j - r + 1).choose 2) *
    qFactorial PowerSeries.X (j + r) * reciprocalQFactorial r * reciprocalQFactorial (j - r)

/-- The certificate value `Ĝ(j, m+1)`. -/
def wzCert (j m : ℕ) : PowerSeries R :=
  (-1 : PowerSeries R) ^ m * PowerSeries.X ^ ((j - m + 2).choose 2 + m) *
    (1 + PowerSeries.X ^ (j + 1)) * qFactorial PowerSeries.X (j + m + 1) *
      reciprocalQFactorial m * reciprocalQFactorial (j - m)

/-- The certificate `Ĝ(j, ·)` with `Ĝ(j, 0) = 0`. -/
def wzG (j : ℕ) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => wzCert j m

theorem rqf_shift (n : ℕ) :
    (reciprocalQFactorial n : PowerSeries R) =
      (1 - PowerSeries.X ^ (n + 1)) * reciprocalQFactorial (n + 1) :=
  (one_sub_X_pow_mul_reciprocalQFactorial n).symm

theorem choose_two_succ (k : ℕ) : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

/-- The WZ step at `r = 0`. -/
theorem wz_step_zero (j : ℕ) :
    (wzTerm (j + 1) 0 : PowerSeries R) - PowerSeries.X ^ (3 * (j + 1)) * wzTerm j 0 =
      wzG j 1 - wzG j 0 := by
  simp only [wzTerm, wzG, wzCert, pow_zero, one_mul, zero_add, Nat.sub_zero, add_zero,
    sub_zero]
  have h0 : (reciprocalQFactorial 0 : PowerSeries R) = 1 := by
    have h := qFactorial_mul_reciprocal (R := R) 0
    simpa using h
  rw [choose_two_succ j, rqf_shift (R := R) j, qFactorial_succ PowerSeries.X j, h0]
  ring

/-- The WZ step at `r = s + 1`, writing `j = s + 1 + k`. -/
theorem wz_step_succ (s k : ℕ) :
    (wzTerm (s + 1 + k + 1) (s + 1) : PowerSeries R) -
        PowerSeries.X ^ (3 * (s + 1 + k + 1)) * wzTerm (s + 1 + k) (s + 1) =
      wzG (s + 1 + k) (s + 1 + 1) - wzG (s + 1 + k) (s + 1) := by
  simp only [wzTerm, wzG, wzCert]
  have e1 : s + 1 + k + 1 - (s + 1) = k + 1 := by omega
  have e2 : s + 1 + k - (s + 1) = k := by omega
  have e3 : s + 1 + k - s = k + 1 := by omega
  have e4 : s + 1 + k + 1 + (s + 1) = (2 * s + k + 2) + 1 := by omega
  have e5 : s + 1 + k + (s + 1) = 2 * s + k + 2 := by omega
  have e7 : s + 1 + k + s + 1 = 2 * s + k + 2 := by omega
  have c1 : (k + 1 + 1).choose 2 = (k + 1).choose 2 + (k + 1) := choose_two_succ k
  have c3 : (k + 1 + 2).choose 2 = (k + 1).choose 2 + (k + 1) + (k + 2) := by
    rw [choose_two_succ (k + 1), choose_two_succ k]
  simp only [e1, e2, e3, e4, e5, e7, c1, c3]
  rw [qFactorial_succ PowerSeries.X (2 * s + k + 2), rqf_shift (R := R) s,
    rqf_shift (R := R) k]
  ring

/-- The WZ step for every `r ≤ j`. -/
theorem wz_step (j r : ℕ) (hr : r ≤ j) :
    (wzTerm (j + 1) r : PowerSeries R) - PowerSeries.X ^ (3 * (j + 1)) * wzTerm j r =
      wzG j (r + 1) - wzG j r := by
  cases r with
  | zero => exact wz_step_zero j
  | succ s =>
      obtain ⟨k, rfl⟩ : ∃ k, j = s + 1 + k := ⟨j - (s + 1), by omega⟩
      exact wz_step_succ s k

/-- The boundary term `T(j+1, j+1) = -Ĝ(j, j+1)`. -/
theorem wzTerm_diag (j : ℕ) :
    (wzTerm (j + 1) (j + 1) : PowerSeries R) = -wzCert j j := by
  simp only [wzTerm, wzCert, Nat.sub_self, zero_add]
  rw [show j + 1 + (j + 1) = (j + j + 1) + 1 by omega, qFactorial_succ,
    rqf_shift (R := R) j]
  have h0 : (reciprocalQFactorial 0 : PowerSeries R) = 1 := by
    have h := qFactorial_mul_reciprocal (R := R) 0
    simpa using h
  rw [h0, show j + j + 1 + 1 = 2 * (j + 1) by omega, show j + j + 1 = j + j + 1 by rfl]
  simp only [Nat.choose_self, Nat.choose_two_right]
  norm_num
  ring

/-- The WZ sum. -/
def wzSum (j : ℕ) : PowerSeries R := ∑ r ∈ Finset.range (j + 1), wzTerm j r

theorem wzSum_succ (j : ℕ) :
    (wzSum (j + 1) : PowerSeries R) = PowerSeries.X ^ (3 * (j + 1)) * wzSum j := by
  have htel : ∑ r ∈ Finset.range (j + 1),
      ((wzTerm (j + 1) r : PowerSeries R) - PowerSeries.X ^ (3 * (j + 1)) * wzTerm j r) =
        wzG j (j + 1) - wzG j 0 := by
    rw [← Finset.sum_range_sub (wzG (R := R) j) (j + 1)]
    apply Finset.sum_congr rfl
    intro r hr
    exact wz_step j r (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hr)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at htel
  rw [wzSum, Finset.sum_range_succ, wzTerm_diag, wzSum]
  simp only [wzG, sub_zero] at htel
  linear_combination htel

/-- The terminating identity `Σ_r T(j, r) = q^{3 C(j+1, 2)}`, proved outright. -/
theorem wzSum_eq (j : ℕ) :
    (wzSum j : PowerSeries R) = PowerSeries.X ^ (3 * (j + 1).choose 2) := by
  induction j with
  | zero =>
      have h0 : (reciprocalQFactorial 0 : PowerSeries R) = 1 := by
        have h := qFactorial_mul_reciprocal (R := R) 0
        simpa using h
      simp [wzSum, wzTerm, h0]
  | succ j ih =>
      rw [wzSum_succ, ih, ← pow_add, choose_two_succ j]
      congr 1
      ring

end

end VOA.JetFermionic
