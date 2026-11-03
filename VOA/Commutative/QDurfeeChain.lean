/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QBinomialFiniteSum
import VOA.Commutative.LocallyFinitePowerSeriesSum

/-!
# Durfee sums and descending-chain collapse

Formal versions of equations 5.27 and 5.36 of Arakawa--Dai.  All sums are
coefficientwise locally finite; the chain is defined by summing its actual successive indices.
-/

namespace VOA.QSeries

open scoped BigOperators
open VOA.LocallyFinitePowerSeriesSum

variable {R : Type*} [CommRing R]

noncomputable section

/-- A degree bound by the summand index supplies finite coefficient support. -/
theorem indexBounded_finite (F : ℕ → PowerSeries R)
    (hF : ∀ d j, d < j → PowerSeries.coeff d (F j) = 0) :
    IsCoefficientwiseFinite F := by
  apply isCoefficientwiseFinite_of_mem_finset _ (fun d => Finset.range (d + 1))
  intro d j hj
  by_contra h
  exact hj (hF d j (by simpa using h))

/-- A uniform explicit cutoff for an index-bounded family. -/
theorem coeff_indexBounded_sum (F : ℕ → PowerSeries R)
    (hF : ∀ d j, d < j → PowerSeries.coeff d (F j) = 0)
    (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (VOA.LocallyFinitePowerSeriesSum.sum F) =
      PowerSeries.coeff d (∑ j ∈ Finset.range (N + 1), F j) := by
  rw [coeff_sum, map_sum]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hn
  have hNj : N < j := by simpa using hn
  exact hj (hF d j (by omega))

/-- Multiplication can be pulled out of an index-bounded coefficientwise sum. -/
theorem indexBounded_sum_mul (F : ℕ → PowerSeries R)
    (hF : ∀ d j, d < j → PowerSeries.coeff d (F j) = 0) (B : PowerSeries R) :
    VOA.LocallyFinitePowerSeriesSum.sum (fun j => F j * B) =
      VOA.LocallyFinitePowerSeriesSum.sum F * B := by
  have hmul : ∀ d j, d < j → PowerSeries.coeff d (F j * B) = 0 := by
    intro d j hdj
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [hF ij.1 j (by have hsum := Finset.mem_antidiagonal.mp hij; omega), zero_mul]
  apply PowerSeries.ext
  intro d
  rw [coeff_indexBounded_sum _ hmul d d le_rfl, ← Finset.sum_mul]
  symm
  apply coeff_mul_congr_left_upto
  intro i hi
  exact coeff_indexBounded_sum F hF i d hi

/-- Quadratic Durfee exponents dominate their summation index. -/
theorem le_durfee_exponent (j d : ℕ) : j ≤ j * (j + d) := by
  cases j with
  | zero => simp
  | succ j => nlinarith

/-- One Durfee-rectangle summand. -/
def durfeeTerm (d j : ℕ) : PowerSeries R :=
  PowerSeries.X ^ (j * (j + d)) * reciprocalQFactorial j * reciprocalQFactorial (j + d)

theorem coeff_durfeeTerm_eq_zero (d m j : ℕ) (h : m < j) :
    PowerSeries.coeff m (durfeeTerm (R := R) d j) = 0 := by
  rw [durfeeTerm, mul_assoc, PowerSeries.coeff_X_pow_mul']
  simp [show ¬ j * (j + d) ≤ m by have ht := le_durfee_exponent j d; omega]

/-- The infinite Durfee sum, defined by its locally finite coefficients. -/
def durfeeSum (d : ℕ) : PowerSeries R := VOA.LocallyFinitePowerSeriesSum.sum (durfeeTerm d)

theorem durfeeSum_finite (d : ℕ) : IsCoefficientwiseFinite (durfeeTerm (R := R) d) :=
  indexBounded_finite _ (coeff_durfeeTerm_eq_zero d)

/-- Equation 5.32 as an equality of formal series. -/
theorem durfeeSum_eq (d : ℕ) : durfeeSum (R := R) d = reciprocalEuler := by
  apply PowerSeries.ext
  intro m
  rw [durfeeSum, coeff_indexBounded_sum _ (coeff_durfeeTerm_eq_zero d) m m le_rfl]
  exact coeff_durfee_sum m d

/-- A summand of the shifted infinite identity, indexed by `j = r + N`. -/
def shiftedDurfeeTerm (r N : ℕ) : PowerSeries R :=
  PowerSeries.X ^ ((r + N) * (r + N + 1)) *
    reciprocalQFactorial N * reciprocalQFactorial (N + (2 * r + 1))

theorem coeff_shiftedDurfeeTerm_eq_zero (r m N : ℕ) (h : m < N) :
    PowerSeries.coeff m (shiftedDurfeeTerm (R := R) r N) = 0 := by
  rw [shiftedDurfeeTerm, mul_assoc, PowerSeries.coeff_X_pow_mul']
  have hbound : N ≤ (r + N) * (r + N + 1) := by nlinarith
  simp [show ¬ (r + N) * (r + N + 1) ≤ m by omega]

/-- The shifted infinite sum of equation 5.27. -/
def shiftedDurfeeSum (r : ℕ) : PowerSeries R :=
  VOA.LocallyFinitePowerSeriesSum.sum (shiftedDurfeeTerm r)

theorem shiftedDurfeeSum_finite (r : ℕ) :
    IsCoefficientwiseFinite (shiftedDurfeeTerm (R := R) r) :=
  indexBounded_finite _ (coeff_shiftedDurfeeTerm_eq_zero r)

/-- Equation 5.27, with all infinite sums interpreted coefficientwise. -/
theorem shiftedDurfeeSum_eq (r : ℕ) :
    shiftedDurfeeSum (R := R) r = PowerSeries.X ^ (r * (r + 1)) * reciprocalEuler := by
  unfold shiftedDurfeeSum
  calc
    _ = VOA.LocallyFinitePowerSeriesSum.sum
        (fun N => durfeeTerm (R := R) (2 * r + 1) N * PowerSeries.X ^ (r * (r + 1))) := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro N
      unfold shiftedDurfeeTerm durfeeTerm
      rw [show (r + N) * (r + N + 1) = r * (r + 1) + N * (N + (2 * r + 1)) by ring,
        pow_add]
      ring
    _ = durfeeSum (R := R) (2 * r + 1) * PowerSeries.X ^ (r * (r + 1)) :=
      indexBounded_sum_mul _ (coeff_durfeeTerm_eq_zero (2 * r + 1)) _
    _ = _ := by rw [durfeeSum_eq]; ring

/-- The bounded descending-chain kernel.  Its first index is the number of inner
summations; the outer endpoint is `r + N`. -/
def chainKernel (r : ℕ) : ℕ → ℕ → PowerSeries R
  | 0, N => reciprocalQFactorial N * reciprocalQFactorial (N + (2 * r + 1))
  | ℓ + 1, N => ∑ j ∈ Finset.range (N + 1),
      PowerSeries.X ^ ((r + j) * (r + j + 1)) *
        reciprocalQFactorial (N - j) * chainKernel r ℓ j

/-- Every bounded inner summation collapses by the finite shifted identity. -/
theorem chainKernel_eq (r ℓ N : ℕ) :
    chainKernel (R := R) r ℓ N = PowerSeries.X ^ (ℓ * (r * (r + 1))) *
      reciprocalQFactorial N * reciprocalQFactorial (N + (2 * r + 1)) := by
  induction ℓ generalizing N with
  | zero => simp [chainKernel]
  | succ ℓ ih =>
      simp only [chainKernel, ih]
      calc
        _ = PowerSeries.X ^ (ℓ * (r * (r + 1))) *
            (∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries R) ^
              ((r + j) * (r + j + 1)) * reciprocalQFactorial (N - j) *
                reciprocalQFactorial j * reciprocalQFactorial (j + (2 * r + 1))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by
          rw [finite_shifted_three_denominator_sum, Nat.add_mul, Nat.one_mul, pow_add]
          ring

/-- The paper's descending-chain sum `G_ℓ(r)`, for positive length `ℓ`.
The outer index is `r + N`, and `chainKernel` sums all remaining descending indices. -/
def chainSeries (ℓ r : ℕ) : PowerSeries R :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun N =>
    PowerSeries.X ^ ((r + N) * (r + N + 1)) * chainKernel r (ℓ - 1) N)

theorem chainSeries_finite (ℓ r : ℕ) :
    IsCoefficientwiseFinite (fun N =>
      (PowerSeries.X : PowerSeries R) ^ ((r + N) * (r + N + 1)) *
        chainKernel r (ℓ - 1) N) := by
  apply indexBounded_finite
  intro m N h
  rw [PowerSeries.coeff_X_pow_mul']
  have hbound : N ≤ (r + N) * (r + N + 1) := by nlinarith
  simp [show ¬ (r + N) * (r + N + 1) ≤ m by omega]

/-- Lemma 5.3 / equation 5.36: the complete descending-chain collapse. -/
theorem chainSeries_succ_eq (ℓ r : ℕ) :
    chainSeries (R := R) (ℓ + 1) r =
      PowerSeries.X ^ ((ℓ + 1) * (r * (r + 1))) * reciprocalEuler := by
  unfold chainSeries
  simp only [Nat.add_sub_cancel]
  calc
    _ = VOA.LocallyFinitePowerSeriesSum.sum
        (fun N => shiftedDurfeeTerm (R := R) r N * PowerSeries.X ^ (ℓ * (r * (r + 1)))) := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro N
      rw [chainKernel_eq]
      unfold shiftedDurfeeTerm
      ring
    _ = shiftedDurfeeSum (R := R) r * PowerSeries.X ^ (ℓ * (r * (r + 1))) :=
      indexBounded_sum_mul _ (coeff_shiftedDurfeeTerm_eq_zero r) _
    _ = _ := by
      rw [shiftedDurfeeSum_eq, Nat.add_mul, Nat.one_mul, pow_add]
      ring

/-- The chain-collapse theorem using the paper's positive-length convention. -/
theorem chainSeries_eq (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) :
    chainSeries (R := R) ℓ r =
      PowerSeries.X ^ (ℓ * (r * (r + 1))) * reciprocalEuler := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  exact chainSeries_succ_eq k r

end
end VOA.QSeries
