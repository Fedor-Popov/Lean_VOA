/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QJacobiCube
import VOA.Commutative.QDurfeeChain
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The fermionic chain trace

The actual descending-chain sum in equation 5.16 is expanded using the finite
alternating identity and evaluated using the chain collapse.
-/

namespace VOA.QSeries

open scoped BigOperators
open VOA.LocallyFinitePowerSeriesSum

noncomputable section

/-- Swap a finite triangular summation and shift the inner lower bound to zero. -/
theorem sum_triangle_shift {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1), f r j) =
      ∑ r ∈ Finset.range (n + 1), ∑ L ∈ Finset.range (n - r + 1), f r (r + L) := by
  have h := Finset.sum_Ico_Ico_comm 0 (n + 1) f
  simp only [Nat.Ico_zero_eq_range] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_Ico_eq_sum_range,
    show n + 1 - r = n - r + 1 by have := Finset.mem_range.mp hr; omega]

variable {K : Type*} [Field K]

/-- Cancel the numerator Euler product in a Gaussian coefficient. -/
theorem gaussian_mul_reciprocalQFactorial (n k : ℕ) (hk : k ≤ n) :
    gaussian (PowerSeries.X : PowerSeries K) n k * reciprocalQFactorial n =
      reciprocalQFactorial k * reciprocalQFactorial (n - k) := by
  rw [gaussian_eq_qFactorial_ratio n k hk]
  calc
    _ = (qFactorial PowerSeries.X n * (reciprocalQFactorial n : PowerSeries K)) *
        reciprocalQFactorial k * reciprocalQFactorial (n - k) := by ring
    _ = _ := by simp

/-- Equation 5.38: the finite alternating expansion of the terminal chain factor. -/
theorem terminal_factor_expansion (n : ℕ) :
    (qFactorial (PowerSeries.X : PowerSeries K) n) ^ 2 * reciprocalQFactorial (2 * n + 1) =
      ∑ r ∈ Finset.range (n + 1), alternatingTerm r * chainKernel (R := K) r 0 (n - r) := by
  rw [finite_alternating, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by simpa using Finset.mem_range.mp hr
  change alternatingTerm r * gaussian PowerSeries.X (2 * n + 1) (n - r) *
    reciprocalQFactorial (2 * n + 1) = _
  rw [mul_assoc, gaussian_mul_reciprocalQFactorial (2 * n + 1) (n - r) (by omega)]
  simp only [chainKernel]
  rw [show 2 * n + 1 - (n - r) = n - r + (2 * r + 1) by omega]

/-- The bounded inner kernel of the fermionic trace, with its actual terminal factor. -/
def fermionicKernel : ℕ → ℕ → PowerSeries K
  | 0, n => qFactorial PowerSeries.X n ^ 2 * reciprocalQFactorial (2 * n + 1)
  | ℓ + 1, n => ∑ j ∈ Finset.range (n + 1),
      PowerSeries.X ^ (j * (j + 1)) * reciprocalQFactorial (n - j) * fermionicKernel ℓ j

/-- Expanding the terminal factor turns a bounded fermionic chain into shifted kernels. -/
theorem fermionicKernel_expansion (ℓ n : ℕ) :
    fermionicKernel (K := K) ℓ n =
      ∑ r ∈ Finset.range (n + 1), alternatingTerm r * chainKernel r ℓ (n - r) := by
  induction ℓ generalizing n with
  | zero => exact terminal_factor_expansion n
  | succ ℓ ih =>
      simp only [fermionicKernel, ih, Finset.mul_sum]
      calc
        _ = ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1),
            alternatingTerm (R := K) r *
              (PowerSeries.X ^ (j * (j + 1)) * reciprocalQFactorial (n - j) *
                chainKernel r ℓ (j - r)) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = ∑ r ∈ Finset.range (n + 1), ∑ L ∈ Finset.range (n - r + 1),
            alternatingTerm (R := K) r *
              (PowerSeries.X ^ ((r + L) * (r + L + 1)) * reciprocalQFactorial (n - (r + L)) *
                chainKernel r ℓ (r + L - r)) := sum_triangle_shift _ n
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [chainKernel, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro L hL
          rw [Nat.add_sub_cancel_left, show n - (r + L) = n - r - L by omega]

/-- The fermionic trace `T_m` in equation 5.16, for positive chain length `m`. -/
def fermionicTrace (m : ℕ) : PowerSeries K :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun n =>
    PowerSeries.X ^ (n * (n + 1)) * fermionicKernel (m - 1) n)

theorem coeff_fermionicTrace_term_eq_zero (m d n : ℕ) (h : d < n) :
    PowerSeries.coeff d ((PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) *
      fermionicKernel (m - 1) n) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  have hbound : n ≤ n * (n + 1) := by nlinarith
  simp [show ¬ n * (n + 1) ≤ d by omega]

theorem fermionicTrace_finite (m : ℕ) :
    IsCoefficientwiseFinite (fun n => (PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) *
      fermionicKernel (m - 1) n) := indexBounded_finite _ (coeff_fermionicTrace_term_eq_zero m)

/-- The alternating sum of actual chain series occurring in equation 5.39. -/
def weightedChainSum (m : ℕ) : PowerSeries K :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun r => alternatingTerm r * chainSeries m r)

theorem weightedChainSum_finite (m : ℕ) :
    IsCoefficientwiseFinite (fun r => (alternatingTerm r : PowerSeries K) * chainSeries m r) :=
  indexBounded_finite _ (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _)

/-- A sharper chain cutoff takes account of its lower endpoint. -/
theorem coeff_chainSeries_cutoff (m r d N : ℕ) (h : d ≤ r + N) :
    PowerSeries.coeff d (chainSeries (R := K) m r) =
      PowerSeries.coeff d (∑ L ∈ Finset.range (N + 1),
        PowerSeries.X ^ ((r + L) * (r + L + 1)) * chainKernel r (m - 1) L) := by
  rw [chainSeries, coeff_sum, map_sum]
  apply finsum_eq_sum_of_support_subset
  intro L hL
  by_contra hnot
  have hNL : N < L := by simpa using hnot
  have hbound : r + L ≤ (r + L) * (r + L + 1) := by nlinarith
  apply hL
  dsimp only
  rw [PowerSeries.coeff_X_pow_mul']
  simp [show ¬ (r + L) * (r + L + 1) ≤ d by omega]

/-- Equation 5.39, proved by locally finite triangular reindexing of the actual trace. -/
theorem fermionicTrace_expansion (m : ℕ) :
    fermionicTrace (K := K) m = weightedChainSum m := by
  apply PowerSeries.ext
  intro d
  rw [fermionicTrace, coeff_indexBounded_sum _ (coeff_fermionicTrace_term_eq_zero m) d d le_rfl]
  have hfinite :
      (∑ n ∈ Finset.range (d + 1), (PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) *
        fermionicKernel (m - 1) n) =
      ∑ r ∈ Finset.range (d + 1), alternatingTerm r *
        (∑ L ∈ Finset.range (d - r + 1),
          PowerSeries.X ^ ((r + L) * (r + L + 1)) * chainKernel r (m - 1) L) := by
    simp only [fermionicKernel_expansion, Finset.mul_sum]
    calc
      _ = ∑ n ∈ Finset.range (d + 1), ∑ r ∈ Finset.range (n + 1),
          alternatingTerm (R := K) r *
            (PowerSeries.X ^ (n * (n + 1)) * chainKernel r (m - 1) (n - r)) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by
        rw [sum_triangle_shift]
        simp only [Nat.add_sub_cancel_left]
  rw [hfinite, weightedChainSum,
    coeff_indexBounded_sum _ (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _) d d le_rfl,
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ≤ d := by simpa using Finset.mem_range.mp hr
  rw [mul_comm (alternatingTerm r), mul_comm (alternatingTerm r)]
  apply coeff_mul_congr_left_upto
  intro i hi
  exact (coeff_chainSeries_cutoff m r i (d - r) (by omega)).symm

/-- Expansion of the triangular series is still computed at a finite coefficient cutoff. -/
theorem coeff_expand_alternatingTheta (p : ℕ) (hp : p ≠ 0) (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (PowerSeries.expand p hp (alternatingTheta : PowerSeries K)) =
      PowerSeries.coeff d (∑ r ∈ Finset.range (N + 1),
        PowerSeries.expand p hp (alternatingTerm r : PowerSeries K)) := by
  rw [← map_sum (PowerSeries.expand p hp), PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs
  · exact coeff_alternatingTheta (d / p) N ((Nat.div_le_self d p).trans h)
  · rfl

/-- The chain exponent converts the alternating summand into its odd dilation. -/
theorem expand_alternatingTerm (m r : ℕ) :
    PowerSeries.expand (2 * m + 1) (by omega) (alternatingTerm r : PowerSeries K) =
      alternatingTerm r * PowerSeries.X ^ (m * (r * (r + 1))) := by
  have ht : r * (r + 1) = 2 * (r + 1).choose 2 := by
    have h := two_mul_choose_two_add (r + 1)
    nlinarith
  have hexp : (2 * m + 1) * (r + 1).choose 2 =
      (r + 1).choose 2 + m * (r * (r + 1)) := by rw [ht]; ring
  simp only [alternatingTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    PowerSeries.expand_X]
  rw [← pow_mul, hexp, pow_add]
  ring

/-- The alternating sum after chain collapse is the dilated triangular series. -/
theorem sum_alternatingTerm_chain_power (m : ℕ) :
    VOA.LocallyFinitePowerSeriesSum.sum
      (fun r => (alternatingTerm r : PowerSeries K) * PowerSeries.X ^ (m * (r * (r + 1)))) =
      PowerSeries.expand (2 * m + 1) (by omega) (alternatingTheta : PowerSeries K) := by
  apply PowerSeries.ext
  intro d
  rw [coeff_indexBounded_sum _ (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _) d d le_rfl,
    coeff_expand_alternatingTheta (2 * m + 1) (by omega) d d le_rfl]
  simp only [expand_alternatingTerm]

/-- Equation 5.37: the complete actual fermionic trace is an odd Euler-product cube
multiplied by the reciprocal ordinary Euler product. -/
theorem fermionicTrace_eq (m : ℕ) (hm : 1 ≤ m) :
    fermionicTrace (K := K) m =
      (PowerSeries.expand (2 * m + 1) (by omega) (euler : PowerSeries K)) ^ 3 *
        reciprocalEuler := by
  rw [fermionicTrace_expansion, weightedChainSum]
  calc
    _ = VOA.LocallyFinitePowerSeriesSum.sum (fun r =>
        ((alternatingTerm r : PowerSeries K) * PowerSeries.X ^ (m * (r * (r + 1)))) *
          reciprocalEuler) := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro r
      rw [chainSeries_eq m r hm, mul_assoc]
    _ = VOA.LocallyFinitePowerSeriesSum.sum
        (fun r => (alternatingTerm r : PowerSeries K) * PowerSeries.X ^ (m * (r * (r + 1)))) *
          reciprocalEuler := indexBounded_sum_mul _
            (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _) _
    _ = _ := by
      rw [sum_alternatingTerm_chain_power, jacobi_cube, map_pow]

end
end VOA.QSeries
