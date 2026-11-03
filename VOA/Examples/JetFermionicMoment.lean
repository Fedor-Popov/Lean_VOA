/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Commutative.QChainTrace

/-!
# A Jacobi-cube moment identity for pairs of reciprocal Euler products

For every `N`,

  `(q;q)_∞³ · Σ_{a+b=N} 1/((q)_a (q)_b) = Σ_{t ≥ 0} (-1)^t (N+2t+1) q^{C(t+1,2)} [N+t, t]_q`.

At `N = 0` this is Jacobi's cube identity (`jacobi_cube`).  Both sides satisfy the recurrence
`(1 - q^{N+1}) X_{N+1} = 2 X_N - X_{N-1}` (with `X_{-1} = 0`): for the left side this is an
elementary antidiagonal computation; for the right side it is a telescoping sum with the
certificate `G_{t+1} = (-1)^{t+1} (N+2t+2) q^{C(t+2,2)} [N+t, t]_q`, `G_0 = 0`.

* `pairSum_rec` — the recurrence for `Σ_{a+b=N} 1/((q)_a (q)_b)`;
* `momentSeries_rec` — the recurrence for the alternating moment series;
* `euler_cube_mul_pairSum` — the identity, proved outright.
-/

namespace VOA.JetFermionic

open VOA.QSeries VOA.LocallyFinitePowerSeriesSum
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-! ### The pair sum -/

/-- `Σ_{a+b=N} 1/((q)_a (q)_b)`. -/
def pairSum (N : ℕ) : PowerSeries K :=
  ∑ p ∈ Finset.antidiagonal N, reciprocalQFactorial p.1 * reciprocalQFactorial p.2

/-- The previous pair sum, with `X_{-1} = 0`. -/
def pairMinus : ℕ → PowerSeries K
  | 0 => 0
  | N + 1 => pairSum N

theorem rqf_succ_shift (n : ℕ) :
    (1 - PowerSeries.X ^ (n + 1)) * (reciprocalQFactorial (n + 1) : PowerSeries K) =
      reciprocalQFactorial n :=
  one_sub_X_pow_mul_reciprocalQFactorial n

theorem rqf_zero : (reciprocalQFactorial 0 : PowerSeries K) = 1 := by
  have h := qFactorial_mul_reciprocal (R := K) 0
  simpa using h

/-- `Σ_{a+b=N} q^a / ((q)_a (q)_b)`. -/
def weightedPairSum (N : ℕ) : PowerSeries K :=
  ∑ p ∈ Finset.antidiagonal N,
    PowerSeries.X ^ p.1 * reciprocalQFactorial p.1 * reciprocalQFactorial p.2

theorem weightedPairSum_eq (N : ℕ) :
    (weightedPairSum N : PowerSeries K) = pairSum N - pairMinus N := by
  cases N with
  | zero => simp [weightedPairSum, pairSum, pairMinus]
  | succ M =>
      simp only [weightedPairSum, pairSum, pairMinus, Finset.Nat.sum_antidiagonal_succ]
      have h : ∀ a : ℕ, (PowerSeries.X : PowerSeries K) ^ (a + 1) *
          reciprocalQFactorial (a + 1) =
            reciprocalQFactorial (a + 1) - reciprocalQFactorial a := by
        intro a
        rw [← rqf_succ_shift (K := K) a]
        ring
      have hs : ∑ p ∈ Finset.antidiagonal M, (PowerSeries.X : PowerSeries K) ^ (p.1 + 1) *
          reciprocalQFactorial (p.1 + 1) * reciprocalQFactorial p.2 =
          ∑ p ∈ Finset.antidiagonal M, reciprocalQFactorial (p.1 + 1) *
            reciprocalQFactorial p.2 -
          ∑ p ∈ Finset.antidiagonal M, reciprocalQFactorial p.1 *
            reciprocalQFactorial p.2 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [h p.1]
        ring
      rw [hs]
      simp only [pow_zero, one_mul]
      ring

/-- The recurrence `(1 - q^{N+1}) P_{N+1} = 2 P_N - P_{N-1}`. -/
theorem pairSum_rec (N : ℕ) :
    (1 - PowerSeries.X ^ (N + 1)) * (pairSum (N + 1) : PowerSeries K) =
      2 * pairSum N - pairMinus N := by
  have hsplit : (1 - PowerSeries.X ^ (N + 1)) * (pairSum (N + 1) : PowerSeries K) =
      (∑ p ∈ Finset.antidiagonal (N + 1),
        ((1 - PowerSeries.X ^ p.1) * reciprocalQFactorial p.1) * reciprocalQFactorial p.2) +
      ∑ p ∈ Finset.antidiagonal (N + 1),
        PowerSeries.X ^ p.1 * reciprocalQFactorial p.1 *
          ((1 - PowerSeries.X ^ p.2) * reciprocalQFactorial p.2) := by
    rw [pairSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = N + 1 := Finset.mem_antidiagonal.mp hp
    rw [← hsum, pow_add]
    ring
  have h1 : (∑ p ∈ Finset.antidiagonal (N + 1),
      ((1 - PowerSeries.X ^ p.1) * reciprocalQFactorial p.1) *
        (reciprocalQFactorial p.2 : PowerSeries K)) = pairSum N := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [pow_zero, sub_self, zero_mul, zero_add, rqf_succ_shift, pairSum]
  have h2 : (∑ p ∈ Finset.antidiagonal (N + 1),
      PowerSeries.X ^ p.1 * reciprocalQFactorial p.1 *
        ((1 - PowerSeries.X ^ p.2) * (reciprocalQFactorial p.2 : PowerSeries K))) =
      weightedPairSum N := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [pow_zero, sub_self, zero_mul, mul_zero, zero_add, rqf_succ_shift,
      weightedPairSum]
  rw [hsplit, h1, h2, weightedPairSum_eq]
  ring

/-! ### The alternating moment series -/

/-- The summand `(-1)^t (N+2t+1) q^{C(t+1,2)} [N+t, t]_q`. -/
def momentTerm (N t : ℕ) : PowerSeries K :=
  (-1 : PowerSeries K) ^ t * ((N + 2 * t + 1 : ℕ) : PowerSeries K) *
    PowerSeries.X ^ ((t + 1).choose 2) * gaussian PowerSeries.X (N + t) t

/-- The summand of the previous moment series, `(-1)^t (N+2t) q^{C(t+1,2)} [N+t-1, t]_q`. -/
def momentMinusTerm (N t : ℕ) : PowerSeries K :=
  (-1 : PowerSeries K) ^ t * ((N + 2 * t : ℕ) : PowerSeries K) *
    PowerSeries.X ^ ((t + 1).choose 2) * gaussian PowerSeries.X (N + t - 1) t

/-- The alternating moment series. -/
def momentSeries (N : ℕ) : PowerSeries K := VOA.LocallyFinitePowerSeriesSum.sum (momentTerm N)

/-- The previous alternating moment series. -/
def momentMinus (N : ℕ) : PowerSeries K :=
  VOA.LocallyFinitePowerSeriesSum.sum (momentMinusTerm N)

/-- The telescoping certificate. -/
def momentCert (N : ℕ) : ℕ → PowerSeries K
  | 0 => 0
  | t + 1 => (-1 : PowerSeries K) ^ (t + 1) * ((N + 2 * t + 2 : ℕ) : PowerSeries K) *
      PowerSeries.X ^ ((t + 2).choose 2) * gaussian PowerSeries.X (N + t) t

theorem choose_two_add_two (k : ℕ) : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem coeff_X_pow_mul_eq_zero (e d : ℕ) (h : d < e) (B : PowerSeries K) :
    PowerSeries.coeff d (PowerSeries.X ^ e * B) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  simp [show ¬ e ≤ d by omega]

theorem coeff_momentTerm_eq_zero (N d t : ℕ) (h : d < t) :
    PowerSeries.coeff d (momentTerm (K := K) N t) = 0 := by
  have heq : momentTerm (K := K) N t = PowerSeries.X ^ ((t + 1).choose 2) *
      ((-1 : PowerSeries K) ^ t * ((N + 2 * t + 1 : ℕ) : PowerSeries K) *
        gaussian PowerSeries.X (N + t) t) := by
    unfold momentTerm
    ring
  rw [heq]
  exact coeff_X_pow_mul_eq_zero _ _ (by have := le_triangular t; omega) _

theorem coeff_momentMinusTerm_eq_zero (N d t : ℕ) (h : d < t) :
    PowerSeries.coeff d (momentMinusTerm (K := K) N t) = 0 := by
  have heq : momentMinusTerm (K := K) N t = PowerSeries.X ^ ((t + 1).choose 2) *
      ((-1 : PowerSeries K) ^ t * ((N + 2 * t : ℕ) : PowerSeries K) *
        gaussian PowerSeries.X (N + t - 1) t) := by
    unfold momentMinusTerm
    ring
  rw [heq]
  exact coeff_X_pow_mul_eq_zero _ _ (by have := le_triangular t; omega) _

/-- `(1 - q^{N+1}) [N+1+t, t] = (1 - q^{N+t+1}) [N+t, t]`. -/
theorem one_sub_mul_gaussian (N t : ℕ) :
    (1 - PowerSeries.X ^ (N + 1)) * gaussian (PowerSeries.X : PowerSeries K) (N + 1 + t) t =
      (1 - PowerSeries.X ^ (N + t + 1)) * gaussian PowerSeries.X (N + t) t := by
  have hu : IsUnit (qFactorial (PowerSeries.X : PowerSeries K) t *
      qFactorial PowerSeries.X N) :=
    (isUnit_qFactorial t).mul (isUnit_qFactorial N)
  rw [show N + 1 + t = N + t + 1 by omega]
  apply hu.mul_right_cancel
  have h1 := gaussian_mul_qFactorial (PowerSeries.X : PowerSeries K) (N + 1 + t) t (by omega)
  have h0 := gaussian_mul_qFactorial (PowerSeries.X : PowerSeries K) (N + t) t (by omega)
  rw [show N + 1 + t - t = N + 1 by omega, qFactorial_succ] at h1
  rw [show N + t - t = N by omega] at h0
  rw [show N + 1 + t = (N + t) + 1 by omega, qFactorial_succ] at h1
  rw [show N + t + 1 = (N + t) + 1 by rfl] at *
  linear_combination h1 - (1 - PowerSeries.X ^ (N + t + 1)) * h0

/-- The pointwise telescoping identity. -/
theorem moment_pointwise (N t : ℕ) :
    (1 - PowerSeries.X ^ (N + 1)) * momentTerm (K := K) (N + 1) t - 2 * momentTerm N t +
        momentMinusTerm N t =
      PowerSeries.X ^ N * (momentCert N (t + 1) - momentCert N t) := by
  cases t with
  | zero =>
      simp only [momentTerm, momentMinusTerm, momentCert, pow_zero, one_mul, add_zero,
        Nat.mul_zero, gaussian_zero_right, mul_one, zero_add, sub_zero]
      norm_num
      ring
  | succ s =>
      have hG := one_sub_mul_gaussian (K := K) N (s + 1)
      have hP : gaussian (PowerSeries.X : PowerSeries K) (N + (s + 1)) (s + 1) =
          gaussian PowerSeries.X (N + (s + 1) - 1) (s + 1) +
            PowerSeries.X ^ N * gaussian PowerSeries.X (N + s) s := by
        rw [show N + (s + 1) = (N + s) + 1 by omega, gaussian_succ_succ,
          show N + s + 1 - 1 = N + s by omega, show N + s - s = N by omega]
      simp only [momentTerm, momentMinusTerm, momentCert]
      have hc : (s + 1 + 2).choose 2 = (s + 1 + 1).choose 2 + (s + 2) := by
        rw [choose_two_add_two (s + 1)]
      rw [hc]
      push_cast
      linear_combination
        ((-1 : PowerSeries K) ^ (s + 1) * PowerSeries.X ^ ((s + 1 + 1).choose 2) *
            ((N : PowerSeries K) + 2 * s + 4)) * hG -
        ((-1 : PowerSeries K) ^ (s + 1) * PowerSeries.X ^ ((s + 1 + 1).choose 2) *
            ((N : PowerSeries K) + 2 * s + 2)) * hP

/-- The finite telescoping identity. -/
theorem moment_finite (N T : ℕ) :
    (1 - PowerSeries.X ^ (N + 1)) * (∑ t ∈ Finset.range T, momentTerm (K := K) (N + 1) t) -
        2 * (∑ t ∈ Finset.range T, momentTerm N t) +
        ∑ t ∈ Finset.range T, momentMinusTerm N t =
      PowerSeries.X ^ N * momentCert N T := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun t _ => moment_pointwise (K := K) N t), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_range_sub (momentCert (K := K) N) T]
  simp only [momentCert, sub_zero]

theorem coeff_momentCert_eq_zero (N d : ℕ) :
    PowerSeries.coeff d (PowerSeries.X ^ N * momentCert (K := K) N (d + 1)) = 0 := by
  have heq : PowerSeries.X ^ N * momentCert (K := K) N (d + 1) =
      PowerSeries.X ^ (N + (d + 2).choose 2) *
        ((-1 : PowerSeries K) ^ (d + 1) * ((N + 2 * d + 2 : ℕ) : PowerSeries K) *
          gaussian PowerSeries.X (N + d) d) := by
    simp only [momentCert, pow_add]
    ring
  rw [heq]
  have ht : d + 1 ≤ (d + 2).choose 2 := le_triangular (d + 1)
  exact coeff_X_pow_mul_eq_zero _ _ (by omega) _

/-- A coefficient of a product with an index-bounded sum only sees a finite cutoff. -/
theorem coeff_mul_indexBounded_sum (F : ℕ → PowerSeries K)
    (hF : ∀ d j, d < j → PowerSeries.coeff d (F j) = 0) (c : PowerSeries K) (d : ℕ) :
    PowerSeries.coeff d (c * VOA.LocallyFinitePowerSeriesSum.sum F) =
      PowerSeries.coeff d (c * ∑ t ∈ Finset.range (d + 1), F t) := by
  rw [mul_comm c, mul_comm c]
  apply coeff_mul_congr_left_upto
  intro i hi
  exact coeff_indexBounded_sum F hF i d hi

/-- The recurrence `(1 - q^{N+1}) M_{N+1} = 2 M_N - M_{N-1}` for the moment series. -/
theorem momentSeries_rec (N : ℕ) :
    (1 - PowerSeries.X ^ (N + 1)) * (momentSeries (N + 1) : PowerSeries K) =
      2 * momentSeries N - momentMinus N := by
  apply PowerSeries.ext
  intro d
  have hfin := congrArg (PowerSeries.coeff d) (moment_finite (K := K) N (d + 1))
  rw [coeff_momentCert_eq_zero, map_add, map_sub] at hfin
  rw [momentSeries, momentSeries, momentMinus, map_sub,
    coeff_mul_indexBounded_sum _ (coeff_momentTerm_eq_zero (N + 1)),
    coeff_mul_indexBounded_sum _ (coeff_momentTerm_eq_zero N),
    coeff_indexBounded_sum _ (coeff_momentMinusTerm_eq_zero N) d d le_rfl]
  linear_combination hfin

theorem momentMinus_succ (N : ℕ) :
    (momentMinus (N + 1) : PowerSeries K) = momentSeries N := by
  apply VOA.LocallyFinitePowerSeriesSum.sum_congr
  intro t
  simp only [momentMinusTerm, momentTerm]
  rw [show N + 1 + t - 1 = N + t by omega, show N + 1 + 2 * t = N + 2 * t + 1 by omega]

theorem momentMinus_zero : (momentMinus 0 : PowerSeries K) = 0 := by
  have hz : ∀ t, momentMinusTerm (K := K) 0 t = 0 := by
    intro t
    cases t with
    | zero => simp [momentMinusTerm]
    | succ s =>
        simp only [momentMinusTerm]
        rw [show 0 + (s + 1) - 1 = s by omega,
          gaussian_eq_zero_of_lt _ (Nat.lt_succ_self s), mul_zero]
  apply PowerSeries.ext
  intro d
  rw [momentMinus, coeff_sum]
  simp [hz]

theorem momentSeries_zero : (momentSeries 0 : PowerSeries K) = alternatingTheta := by
  apply VOA.LocallyFinitePowerSeriesSum.sum_congr
  intro t
  simp [momentTerm, alternatingTerm]

theorem pairSum_zero : (pairSum 0 : PowerSeries K) = 1 := by
  simp [pairSum, rqf_zero]

/-- **The moment identity**:
`(q;q)_∞³ Σ_{a+b=N} 1/((q)_a (q)_b) = Σ_t (-1)^t (N+2t+1) q^{C(t+1,2)} [N+t, t]_q`,
proved outright. -/
theorem euler_cube_mul_pairSum (N : ℕ) :
    (euler : PowerSeries K) ^ 3 * pairSum N = momentSeries N := by
  have key : ∀ N : ℕ, (euler : PowerSeries K) ^ 3 * pairSum N = momentSeries N ∧
      (euler : PowerSeries K) ^ 3 * pairMinus N = momentMinus N := by
    intro N
    induction N with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [pairSum_zero, mul_one, momentSeries_zero, jacobi_cube]
        · rw [momentMinus_zero]
          simp [pairMinus]
    | succ N ih =>
        refine ⟨?_, ?_⟩
        · have hu : IsUnit (1 - PowerSeries.X ^ (N + 1) : PowerSeries K) := by
            apply PowerSeries.isUnit_iff_constantCoeff.mpr
            simp
          apply hu.mul_left_cancel
          rw [momentSeries_rec, ← ih.1, ← ih.2]
          calc
            _ = (euler : PowerSeries K) ^ 3 *
                ((1 - PowerSeries.X ^ (N + 1)) * pairSum (N + 1)) := by ring
            _ = _ := by rw [pairSum_rec]; ring
        · rw [momentMinus_succ, ← ih.1]
          rfl
  exact (key N).1

end

end VOA.JetFermionic
