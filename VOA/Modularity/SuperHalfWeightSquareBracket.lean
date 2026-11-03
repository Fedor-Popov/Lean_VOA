/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSquareBracket
import VOA.Modularity.SquareBracketWitt
import VOA.Modularity.Twisted
import Mathlib.RingTheory.Binomial

/-!
# Complex- and half-weight square-bracket modes

This file is the coordinate-change layer for half-integral super conformal weights.  It is
completely sign-free: changing `z` to `exp z - 1` exchanges no states, so parity and Koszul
cyclicity do not occur here.

For `h : ℂ`, `complexBinomialSeries h` is the formal series `(1+X)^h`, defined by the existing
generalized binomial coefficients `cbinom h n`.  It replaces the integer power
`onePlusXUnit^(k-1)` in `sqBracketCoeffZ`.  The logarithmic unit `uUnit` and the square-bracket
mode index remain integer-valued.

No theta function or modular-form coefficient is postulated in this file.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

/-! ## Generalized binomial coefficients and their formal series -/

/-- The descending Pochhammer polynomial evaluated in `ℂ` is the product used by `cbinom`. -/
lemma descPochhammer_smeval_complex_eq_prod (x : ℂ) (n : ℕ) :
    (descPochhammer ℤ n).smeval x = ∏ k ∈ Finset.range n, (x - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
        Finset.prod_range_succ]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
        npow_one]
      ring

/-- The project-local `cbinom` agrees with Mathlib's generalized binomial coefficient. -/
theorem cbinom_eq_ringChoose (x : ℂ) (n : ℕ) : cbinom x n = Ring.choose x n := by
  rw [cbinom, ← descPochhammer_smeval_complex_eq_prod]
  rw [Ring.descPochhammer_eq_factorial_smul_choose]
  simp only [nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)

@[simp] theorem cbinom_zero (x : ℂ) : cbinom x 0 = 1 := by
  rw [cbinom_eq_ringChoose, Ring.choose_zero_right]

/-- Pascal's identity for a complex upper index. -/
theorem cbinom_pascal (x : ℂ) (n : ℕ) :
    cbinom (x + 1) (n + 1) = cbinom x n + cbinom x (n + 1) := by
  rw [cbinom_eq_ringChoose, cbinom_eq_ringChoose, cbinom_eq_ringChoose,
    Ring.choose_succ_succ]

/-- The formal binomial series `(1+X)^h = sum_n C(h,n) X^n`. -/
noncomputable def complexBinomialSeries (h : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (cbinom h)

@[simp] theorem coeff_complexBinomialSeries (h : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (complexBinomialSeries h) = cbinom h n := by
  rw [complexBinomialSeries, PowerSeries.coeff_mk]

/-- Every formal binomial series has constant coefficient one. -/
theorem constantCoeff_complexBinomialSeries (h : ℂ) :
    PowerSeries.constantCoeff (R := ℂ) (complexBinomialSeries h) = 1 := by
  rw [complexBinomialSeries, PowerSeries.constantCoeff_mk, cbinom_zero]

/-- Every complex binomial series is a formal power-series unit. -/
theorem isUnit_complexBinomialSeries (h : ℂ) : IsUnit (complexBinomialSeries h) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_complexBinomialSeries]
  exact isUnit_one

/-- The exponent-zero series is the multiplicative unit. -/
@[simp] theorem complexBinomialSeries_zero : complexBinomialSeries 0 = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_complexBinomialSeries, cbinom_eq_ringChoose, Ring.choose_zero_succ,
      PowerSeries.coeff_one]
    simp

/-- Formal Pascal identity: `(1+X)^(h+1) = (1+X)(1+X)^h`. -/
theorem complexBinomialSeries_add_one (h : ℂ) :
    complexBinomialSeries (h + 1) =
      (1 + PowerSeries.X) * complexBinomialSeries h := by
  ext n
  rcases n with _ | n
  · simp [constantCoeff_complexBinomialSeries]
  · rw [coeff_complexBinomialSeries, add_mul, map_add,
      PowerSeries.coeff_succ_X_mul, one_mul, coeff_complexBinomialSeries,
      coeff_complexBinomialSeries, cbinom_pascal, add_comm]

/-- At a natural exponent, the formal binomial series is the ordinary power. -/
theorem complexBinomialSeries_natCast (k : ℕ) :
    complexBinomialSeries (k : ℂ) = (1 + PowerSeries.X) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ, complexBinomialSeries_add_one, ih, pow_succ']

/-- The exponent `-1` series is the inverse of `1+X`. -/
theorem complexBinomialSeries_neg_one :
    complexBinomialSeries (-1 : ℂ) =
      (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) := by
  have hmul : (1 + PowerSeries.X) * complexBinomialSeries (-1 : ℂ) = 1 := by
    rw [← complexBinomialSeries_add_one (-1 : ℂ)]
    norm_num
  calc
    complexBinomialSeries (-1 : ℂ)
        = 1 * complexBinomialSeries (-1 : ℂ) := (one_mul _).symm
    _ = ((↑(onePlusXUnit⁻¹) : PowerSeries ℂ) *
          (onePlusXUnit : PowerSeries ℂ)) * complexBinomialSeries (-1 : ℂ) := by
          rw [Units.inv_mul]
    _ = (↑(onePlusXUnit⁻¹) : PowerSeries ℂ) *
          ((1 + PowerSeries.X) * complexBinomialSeries (-1 : ℂ)) := by
          rw [onePlusXUnit_coe, mul_assoc]
    _ = (↑(onePlusXUnit⁻¹) : PowerSeries ℂ) := by rw [hmul, mul_one]
    _ = (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) := by rw [zpow_neg_one]

/-- Compatibility of the complex formal power with the old exponent `k-1`, including the vacuum
case `k=0`. -/
theorem complexBinomialSeries_nat_sub_one (k : ℕ) :
    complexBinomialSeries ((k : ℂ) - 1) =
      (↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) := by
  rcases k with _ | k
  · simpa using complexBinomialSeries_neg_one
  · rw [show (((k + 1 : ℕ) : ℂ) - 1) = (k : ℂ) by push_cast; ring,
      show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega,
      complexBinomialSeries_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      onePlusXUnit_coe]

/-! ## Complex-weight square-bracket coefficients -/

/-- The all-mode square-bracket coefficient for a state of complex conformal weight `h`.
The mode indices `m,i` remain integral; only the exponent `h-1` is generalized. -/
noncomputable def sqBracketCoeffC (h : ℂ) (m i : ℤ) : ℂ :=
  if 0 ≤ i - m then
    PowerSeries.coeff (R := ℂ) (i - m).toNat
      (complexBinomialSeries (h - 1) * (↑(uUnit ^ m) : PowerSeries ℂ))
  else 0

theorem sqBracketCoeffC_of_lt (h : ℂ) {m i : ℤ} (hi : i < m) :
    sqBracketCoeffC h m i = 0 := by
  rw [sqBracketCoeffC, if_neg (by omega)]

/-- The leading coefficient is one for every complex conformal weight. -/
theorem sqBracketCoeffC_diag (h : ℂ) (m : ℤ) : sqBracketCoeffC h m m = 1 := by
  rw [sqBracketCoeffC, if_pos (by omega), sub_self, Int.toNat_zero,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    constantCoeff_complexBinomialSeries,
    constantCoeff_unit_zpow uUnit constantCoeff_uUnit, mul_one]

/-- At an integral conformal weight, the new coefficient is definitionally compatible with the
existing all-mode coefficient. -/
theorem sqBracketCoeffC_natCast (k : ℕ) (m i : ℤ) :
    sqBracketCoeffC (k : ℂ) m i = sqBracketCoeffZ k m i := by
  rw [sqBracketCoeffC, sqBracketCoeffZ, complexBinomialSeries_nat_sub_one]

/-- A doubled conformal weight `d` represents the half-integral weight `d/2`. -/
noncomputable def halfWeight (d : ℤ) : ℂ := (d : ℂ) / 2

theorem halfWeight_even (k : ℕ) : halfWeight (2 * (k : ℤ)) = (k : ℂ) := by
  rw [halfWeight]
  push_cast
  ring

/-! ## Complex-weight super square-bracket modes -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- Lower-index vanishing plus ordinary regularity makes every complex-weight square-bracket
mode locally finite. -/
theorem superSqModeC_support_finite (a : 𝒱) (h : ℂ) (m : ℤ) (b : 𝒱) :
    (Function.support fun i : ℤ => sqBracketCoeffC h m i • V.smul a i b).Finite := by
  obtain ⟨N, hN⟩ := V.regularity a b
  refine Set.Finite.subset (Set.finite_Ico m N) ?_
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact hi (by rw [sqBracketCoeffC_of_lt h (not_le.mp hc), zero_smul])
  · by_contra hc
    have hNi : N ≤ i := not_lt.mp hc
    have hz : V.smul a i b = 0 := hN i hNi
    exact hi (by rw [hz, smul_zero])

/-- The coordinate-changed mode `a[m]` for a state declared homogeneous of complex weight `h`.
Homogeneity is not bundled into the definition; it is used only by grading theorems. -/
noncomputable def superVSqC (a : 𝒱) (h : ℂ) (m : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun b := ∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a i b
  map_add' x y := by
    simp only [SuperVertexAlgebra.smul_add_right, smul_add]
    rw [finsum_add_distrib (V.superSqModeC_support_finite a h m x)
      (V.superSqModeC_support_finite a h m y)]
  map_smul' c x := by
    change (∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a i (c • x)) =
      c • ∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a i x
    rw [smul_finsum' c (V.superSqModeC_support_finite a h m x)]
    refine finsum_congr fun i => ?_
    rw [SuperVertexAlgebra.smul_smul_right, smul_comm]

@[simp] theorem superVSqC_apply (a : 𝒱) (h : ℂ) (m : ℤ) (b : 𝒱) :
    V.superVSqC a h m b = ∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a i b := rfl

/-- Integral-weight compatibility with the existing super square-bracket operator. -/
theorem superVSqC_natCast (a : 𝒱) (k : ℕ) (m : ℤ) :
    V.superVSqC a (k : ℂ) m = V.superVSqZ a k m := by
  ext b
  rw [V.superVSqC_apply, V.superVSqZ_apply]
  exact finsum_congr fun i => by rw [sqBracketCoeffC_natCast]

/-- The explicit doubled-weight wrapper for a weight `d/2` state. -/
noncomputable def superVSqHalf (a : 𝒱) (d : ℤ) (m : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  V.superVSqC a (halfWeight d) m

/-- Even doubled weights recover the old integral-weight construction. -/
theorem superVSqHalf_even (a : 𝒱) (k : ℕ) (m : ℤ) :
    V.superVSqHalf a (2 * (k : ℤ)) m = V.superVSqZ a k m := by
  rw [superVSqHalf, halfWeight_even, V.superVSqC_natCast]

/-- Each ordinary-mode summand has the expected ordinary conformal weight. -/
theorem sqBracketC_summand_mem_grading {a b : 𝒱} {h k : ℂ}
    (ha : a ∈ V.grading h) (hb : b ∈ V.grading k) (m i : ℤ) :
    sqBracketCoeffC h m i • V.smul a i b ∈ V.grading (h + k - i - 1) :=
  Submodule.smul_mem _ _ (V.smul_mem_grading ha hb i)

/-- In the original conformal grading, a square-bracket mode lies in the sum of its ordinary-mode
weight shifts.  It is generally not homogeneous for that original grading. -/
theorem superVSqC_mem_iSup_grading {a b : 𝒱} {h k : ℂ}
    (ha : a ∈ V.grading h) (hb : b ∈ V.grading k) (m : ℤ) :
    V.superVSqC a h m b ∈ ⨆ i : ℤ, V.grading (h + k - i - 1) := by
  rw [V.superVSqC_apply]
  refine finsum_mem_submodule_pd _ _ fun i => ?_
  exact Submodule.mem_iSup_of_mem i (V.sqBracketC_summand_mem_grading ha hb m i)

end SuperNearVOA

end VOA
