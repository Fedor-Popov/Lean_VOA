/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QChainTrace
import VOA.Commutative.QBinomialResidual

/-!
# The Hilbert-bound product formula

Equation 5.33 of Arakawa--Dai.  The bound series is defined by the actual
successive descending-chain sums with the three-species residual sum at the endpoint.
-/

namespace VOA.QSeries

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-- The bounded inner chain with the three residual species at its endpoint. -/
def hilbertBoundKernel : ℕ → ℕ → PowerSeries K
  | 0, n => residualSum n
  | ℓ + 1, n => ∑ j ∈ Finset.range (n + 1),
      PowerSeries.X ^ (j * (j + 1)) * reciprocalQFactorial (n - j) * hilbertBoundKernel ℓ j

/-- Summing the residual variables reduces the actual bounded chain to its fermionic kernel. -/
theorem hilbertBoundKernel_eq (ℓ n : ℕ) :
    hilbertBoundKernel (K := K) ℓ n = fermionicKernel ℓ n * reciprocalEuler ^ 2 := by
  induction ℓ generalizing n with
  | zero =>
      rw [hilbertBoundKernel, residualSum_eq, fermionicKernel]
      ring
  | succ ℓ ih =>
      simp only [hilbertBoundKernel, fermionicKernel, ih, Finset.sum_mul, mul_assoc]

/-- The series `S_m` of equation 5.12: descending chains with the full residual sum.
For the paper's application the chain length `m` is positive. -/
def hilbertBoundSeries (m : ℕ) : PowerSeries K :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun n =>
    PowerSeries.X ^ (n * (n + 1)) * hilbertBoundKernel (m - 1) n)

/-- The outer summation is locally finite independently of the inner residual factors. -/
theorem hilbertBoundSeries_finite (m : ℕ) :
    VOA.LocallyFinitePowerSeriesSum.IsCoefficientwiseFinite (fun n =>
      (PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) * hilbertBoundKernel (m - 1) n) := by
  apply indexBounded_finite
  intro d n h
  rw [PowerSeries.coeff_X_pow_mul']
  have hbound : n ≤ n * (n + 1) := by nlinarith
  simp [show ¬ n * (n + 1) ≤ d by omega]

/-- Equation 5.16: the residual sums produce two reciprocal Euler factors. -/
theorem hilbertBoundSeries_eq_trace (m : ℕ) :
    hilbertBoundSeries (K := K) m = fermionicTrace m * reciprocalEuler ^ 2 := by
  unfold hilbertBoundSeries
  calc
    _ = VOA.LocallyFinitePowerSeriesSum.sum (fun n =>
        ((PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) * fermionicKernel (m - 1) n) *
          reciprocalEuler ^ 2) := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro n
      rw [hilbertBoundKernel_eq, mul_assoc]
    _ = _ := indexBounded_sum_mul _ (coeff_fermionicTrace_term_eq_zero m) _

/-- The dilated Euler series is the coefficientwise infinite product with factors
`1 - q^(p*j)`, verified directly against arbitrary sufficient finite truncations. -/
theorem coeff_expanded_euler (p : ℕ) (hp : p ≠ 0) (d n : ℕ) (h : d ≤ n) :
    PowerSeries.coeff d (PowerSeries.expand p hp (euler : PowerSeries K)) =
      PowerSeries.coeff d (qFactorial (PowerSeries.X ^ p : PowerSeries K) n) := by
  have hmap : PowerSeries.expand p hp (qFactorial (PowerSeries.X : PowerSeries K) n) =
      qFactorial (PowerSeries.X ^ p) n := by
    have hmap' := map_qFactorial (PowerSeries.expand p hp (R := K)).toRingHom PowerSeries.X n
    change PowerSeries.expand p hp (qFactorial (PowerSeries.X : PowerSeries K) n) =
      qFactorial (PowerSeries.expand p hp (PowerSeries.X : PowerSeries K)) n at hmap'
    rw [PowerSeries.expand_X] at hmap'
    exact hmap'
  rw [← hmap, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs
  · exact coeff_euler (d / p) n ((Nat.div_le_self d p).trans h)
  · rfl

/-- Equation 5.33: the actual Hilbert-bound series equals the quotient of Euler cubes.
The numerator is the proved coefficientwise product at `q^(2*m+1)`; the denominator
uses the proved unit inverse of the ordinary Euler product. -/
theorem hilbertBoundSeries_product (m : ℕ) (hm : 1 ≤ m) :
    hilbertBoundSeries (K := K) m =
      (PowerSeries.expand (2 * m + 1) (by omega) (euler : PowerSeries K)) ^ 3 *
        reciprocalEuler ^ 3 := by
  rw [hilbertBoundSeries_eq_trace, fermionicTrace_eq m hm]
  ring

/-- The same product identity with the denominator cleared. -/
theorem euler_cube_mul_hilbertBoundSeries (m : ℕ) (hm : 1 ≤ m) :
    (euler : PowerSeries K) ^ 3 * hilbertBoundSeries m =
      (PowerSeries.expand (2 * m + 1) (by omega) (euler : PowerSeries K)) ^ 3 := by
  rw [hilbertBoundSeries_product m hm]
  calc
    _ = (PowerSeries.expand (2 * m + 1) (by omega) (euler : PowerSeries K)) ^ 3 *
        ((euler : PowerSeries K) * reciprocalEuler) ^ 3 := by ring
    _ = _ := by rw [euler_mul_reciprocal, one_pow, mul_one]

end
end VOA.QSeries
