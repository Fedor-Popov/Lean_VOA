/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqGradedBlock

/-!
# The `L[0]` commutator with square-bracket modes

This file develops the all-weight coefficient collapse needed to transport the ordinary Borcherds
commutator through `w = exp(z) - 1`.  The first bricks are purely scalar power-series identities.
-/

namespace VOA

open PowerSeries
open scoped BigOperators

/-- The derivative rule for a natural power of a unit whose derivative is `1`. -/
theorem derivativeFun_unit_natZpow_of_derivative_one (U : (PowerSeries ℂ)ˣ)
    (hU : derivativeFun (U : PowerSeries ℂ) = 1) (k : ℕ) :
    derivativeFun (↑(U ^ (k : ℤ)) : PowerSeries ℂ)
      = (k : PowerSeries ℂ) * (↑(U ^ ((k : ℤ) - 1)) : PowerSeries ℂ) := by
  have hk : (↑(U ^ (k : ℤ)) : PowerSeries ℂ) = (U : PowerSeries ℂ) ^ k := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  rcases k with _ | k
  · rw [hk, pow_zero, derivativeFun_one]
    simp
  · have hk1 : (↑(U ^ (((k + 1 : ℕ) : ℤ) - 1)) : PowerSeries ℂ)
        = (U : PowerSeries ℂ) ^ k := by
      rw [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by push_cast; ring,
        zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hk, hk1]
    have h := PowerSeries.derivative_pow ℂ (U : PowerSeries ℂ) (k + 1)
    change derivativeFun ((U : PowerSeries ℂ) ^ (k + 1))
      = ((k + 1 : ℕ) : PowerSeries ℂ) * (U : PowerSeries ℂ) ^ k
    change derivativeFun ((U : PowerSeries ℂ) ^ (k + 1))
      = ((k + 1 : ℕ) : PowerSeries ℂ) * (U : PowerSeries ℂ) ^ k
        * derivativeFun (U : PowerSeries ℂ) at h
    rw [hU, mul_one] at h
    simpa only [smul_eq_mul] using h

/-- The nonnegative-integer version of the unit derivative rule. -/
theorem derivativeFun_unit_zpow_nonneg_of_derivative_one (U : (PowerSeries ℂ)ˣ)
    (hU : derivativeFun (U : PowerSeries ℂ) = 1) {m : ℤ} (hm : 0 ≤ m) :
    derivativeFun (↑(U ^ m) : PowerSeries ℂ)
      = (m : PowerSeries ℂ) * (↑(U ^ (m - 1)) : PowerSeries ℂ) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  exact_mod_cast derivativeFun_unit_natZpow_of_derivative_one U hU k

/-- The derivative of an integer power of a power-series unit whose derivative is `1`. -/
theorem derivativeFun_unit_zpow_of_derivative_one (U : (PowerSeries ℂ)ˣ)
    (hU : derivativeFun (U : PowerSeries ℂ) = 1) (m : ℤ) :
    derivativeFun (↑(U ^ m) : PowerSeries ℂ)
      = (m : PowerSeries ℂ) * (↑(U ^ (m - 1)) : PowerSeries ℂ) := by
  by_cases hm : 0 ≤ m
  · exact derivativeFun_unit_zpow_nonneg_of_derivative_one U hU hm
  · push Not at hm
    have h0 : (↑(U ^ m) : PowerSeries ℂ) * ↑(U ^ (-m)) = 1 := by
      rw [← Units.val_mul, ← zpow_add, show m + -m = (0 : ℤ) by ring, zpow_zero,
        Units.val_one]
    have hleib : (↑(U ^ m) : PowerSeries ℂ) * derivativeFun (↑(U ^ (-m)))
        + (↑(U ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(U ^ m)) = 0 := by
      have hmul := derivativeFun_mul (↑(U ^ m) : PowerSeries ℂ) (↑(U ^ (-m)))
      rw [h0, derivativeFun_one] at hmul
      simpa only [smul_eq_mul] using hmul.symm
    have dneg : derivativeFun (↑(U ^ (-m)) : PowerSeries ℂ)
        = ((-m : ℤ) : PowerSeries ℂ) * ↑(U ^ (-m - 1)) :=
      derivativeFun_unit_zpow_nonneg_of_derivative_one U hU (by omega)
    have e1 : (↑(U ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(U ^ m))
        = (m : PowerSeries ℂ) * (↑(U ^ (-1 : ℤ)) : PowerSeries ℂ) := by
      have h1 : (↑(U ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(U ^ m))
          = -((↑(U ^ m) : PowerSeries ℂ) * derivativeFun (↑(U ^ (-m)))) := by
        linear_combination hleib
      rw [h1, dneg,
        show (↑(U ^ m) : PowerSeries ℂ)
            * (((-m : ℤ) : PowerSeries ℂ) * (↑(U ^ (-m - 1)) : PowerSeries ℂ))
          = ((-m : ℤ) : PowerSeries ℂ)
            * ((↑(U ^ m) : PowerSeries ℂ) * ↑(U ^ (-m - 1))) by ring,
        ← Units.val_mul, ← zpow_add, show m + (-m - 1) = (-1 : ℤ) by ring]
      push_cast
      ring
    have e2 : (↑(U ^ (-m)) : PowerSeries ℂ)
          * ((m : PowerSeries ℂ) * (↑(U ^ (m - 1)) : PowerSeries ℂ))
        = (m : PowerSeries ℂ) * (↑(U ^ (-1 : ℤ)) : PowerSeries ℂ) := by
      rw [show (↑(U ^ (-m)) : PowerSeries ℂ)
          * ((m : PowerSeries ℂ) * (↑(U ^ (m - 1)) : PowerSeries ℂ))
        = (m : PowerSeries ℂ)
          * ((↑(U ^ (-m)) : PowerSeries ℂ) * ↑(U ^ (m - 1))) by ring,
        ← Units.val_mul, ← zpow_add, show -m + (m - 1) = (-1 : ℤ) by ring]
    exact mul_left_cancel₀ (Units.ne_zero (U ^ (-m))) (e1.trans e2.symm)

/-- Integer powers of `1+X` have the expected derivative. -/
theorem derivativeFun_onePlusXUnit_zpow (m : ℤ) :
    derivativeFun (↑(onePlusXUnit ^ m) : PowerSeries ℂ)
      = (m : PowerSeries ℂ) * (↑(onePlusXUnit ^ (m - 1)) : PowerSeries ℂ) := by
  apply derivativeFun_unit_zpow_of_derivative_one
  rw [onePlusXUnit_coe, derivativeFun_add, derivativeFun_one, derivativeFun_X, zero_add]

/-- Iterating the derivative on `(1+X)⁻¹`. -/
theorem iterate_derivativeFun_onePlusXUnit_inv (r : ℕ) :
    (derivativeFun^[r]) (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
      = (((-1 : ℂ) ^ r * (r.factorial : ℂ)) •
          (↑(onePlusXUnit ^ (-(r : ℤ) - 1)) : PowerSeries ℂ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, derivativeFun_smul,
        derivativeFun_onePlusXUnit_zpow]
      rw [show (-(r : ℤ) - 1) - 1 = -((r + 1 : ℕ) : ℤ) - 1 by push_cast; ring]
      have hz : ((-(r : ℤ) - 1 : ℤ) : PowerSeries ℂ)
          * (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ) - 1)) : PowerSeries ℂ)
        = (((-(r : ℤ) - 1 : ℤ) : ℂ) •
            (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ) - 1)) : PowerSeries ℂ)) := by
        rw [← zsmul_eq_mul]
        exact (Int.cast_smul_eq_zsmul ℂ (-(r : ℤ) - 1)
          (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ) - 1)) : PowerSeries ℂ)).symm
      rw [hz, smul_smul]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      push_cast
      congr 1
      ring

/-- Coefficients of an iterated formal derivative. -/
theorem coeff_iterate_derivativeFun (f : PowerSeries ℂ) (r s : ℕ) :
    coeff s ((derivativeFun^[r]) f)
      = coeff (s + r) f * ((s + r).factorial : ℂ) / (s.factorial : ℂ) := by
  induction r generalizing s with
  | zero =>
      have hs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
      simp only [Function.iterate_zero_apply, Nat.add_zero]
      field_simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', coeff_derivativeFun, ih (s := s + 1)]
      have hs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
      rw [show s + 1 + r = s + (r + 1) by omega]
      rw [Nat.factorial_succ]
      push_cast
      field_simp

/-! ## The positive-tail scalar collapse -/

/-- The first derivative of `w P₀(w)` in the exponential coordinate. -/
theorem derivativeFun_X_mul_Pw_zero :
    derivativeFun (X * Pw 0) = 1 + X * uSeries := by
  rw [derivativeFun_mul, derivativeFun_X, derivativeFun_Pw]
  simp only [zero_add, Int.cast_one, Pw, zpow_zero, Units.val_one, zpow_one,
    uUnit_coe, one_mul, mul_one, smul_eq_mul]
  have hODE := uSeries_ODE
  linear_combination hODE

/-- The second derivative of `w P₀(w)` is `(1+w)⁻¹`. -/
theorem iterate_derivativeFun_two_X_mul_Pw_zero :
    (derivativeFun^[2]) (X * Pw 0)
      = (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) := by
  rw [show (derivativeFun^[2]) (X * Pw 0)
      = derivativeFun (derivativeFun (X * Pw 0)) by rfl,
    derivativeFun_X_mul_Pw_zero, derivativeFun_add, derivativeFun_one,
    derivativeFun_mul, derivativeFun_X, zero_add]
  change X * derivativeFun uSeries + uSeries * 1 = _
  simp only [mul_one]
  rw [onePlusXUnit_inv_eq]
  ring

/-- The normalized `(q+1)`-st derivative of `w P₀(w)`.  Its coefficients encode the
`\binom{r+1}{q+1}`-weighted Virasoro change-of-coordinate coefficients. -/
noncomputable def sqOuterMoment (q : ℕ) : PowerSeries ℂ :=
  (((q + 1).factorial : ℂ)⁻¹) •
    (derivativeFun^[q + 1]) (X * Pw 0)

/-- Coefficient dictionary for the normalized outer moment. -/
theorem coeff_sqOuterMoment (q s : ℕ) :
    coeff s (sqOuterMoment q)
      = sqBracketCoeffZ 2 1 ((s + q + 1 : ℕ) : ℤ)
          * gBinom ((s + q + 1 : ℕ) : ℤ) (q + 1) := by
  rw [sqOuterMoment, map_smul, coeff_iterate_derivativeFun]
  have hfacq : (((q + 1).factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q + 1)
  have hfacs : (s.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s
  have hchoose := Nat.choose_mul_factorial_mul_factorial
    (show q + 1 ≤ s + q + 1 by omega)
  have hchooseN : (s + q + 1).choose (q + 1) * (q + 1).factorial * s.factorial
      = (s + q + 1).factorial := by
    simpa [show s + q + 1 - (q + 1) = s by omega] using hchoose
  have hchooseC : (((s + q + 1).choose (q + 1) : ℕ) : ℂ)
        * (((q + 1).factorial : ℕ) : ℂ) * (s.factorial : ℂ)
      = ((s + q + 1).factorial : ℂ) := by
    exact_mod_cast hchooseN
  rw [gBinom_natCast]
  have hcoeff : coeff (s + (q + 1)) (X * Pw 0) = coeff (s + q) (Pw 0) := by
    rw [show s + (q + 1) = (s + q) + 1 by omega, coeff_succ_X_mul]
  rw [hcoeff]
  have hd := sqBracketCoeffZ_two_eq_coeff_Pw (0 : ℤ) ((s + q : ℕ) : ℤ)
  norm_num at hd
  have hd' : sqBracketCoeffZ 2 1 ((s + q + 1 : ℕ) : ℤ) = coeff (s + q) (Pw 0) := by
    rw [show ((s + q + 1 : ℕ) : ℤ) = (s : ℤ) + q + 1 by push_cast; ring,
      hd, if_pos (by omega)]
    congr 1 <;> omega
  rw [hd']
  have hratio : ((s + q + 1).factorial : ℂ) * (s.factorial : ℂ)⁻¹
        * (((q + 1).factorial : ℂ))⁻¹
      = (((s + q + 1).choose (q + 1) : ℕ) : ℂ) := by
    field_simp
    calc
      ((s + q + 1).factorial : ℂ) =
          (((s + q + 1).choose (q + 1) : ℕ) : ℂ)
            * (((q + 1).factorial : ℕ) : ℂ) * (s.factorial : ℂ) := hchooseC.symm
      _ = _ := by ring
  change (((q + 1).factorial : ℂ))⁻¹
      * (coeff (s + q) (Pw 0) * ((s + q + 1).factorial : ℂ) / (s.factorial : ℂ))
    = coeff (s + q) (Pw 0) * (((s + q + 1).choose (q + 1) : ℕ) : ℂ)
  rw [div_eq_mul_inv]
  calc
    _ = coeff (s + q) (Pw 0) *
        (((s + q + 1).factorial : ℂ) * (s.factorial : ℂ)⁻¹
          * (((q + 1).factorial : ℂ))⁻¹) := by ring
    _ = _ := by rw [hratio]

/-- For positive `q`, the normalized outer moment is its constant coefficient times
`(1+w)⁻q`. -/
theorem sqOuterMoment_eq_smul_onePlusXUnit_zpow {q : ℕ} (hq : 1 ≤ q) :
    sqOuterMoment q = sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ) •
      (↑(onePlusXUnit ^ (-(q : ℤ))) : PowerSeries ℂ) := by
  rcases q with _ | r
  · omega
  let A : ℂ := (((r + 1 + 1).factorial : ℂ)⁻¹)
    * ((-1 : ℂ) ^ r * (r.factorial : ℂ))
  have hm : sqOuterMoment (r + 1) = A •
      (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ))) : PowerSeries ℂ) := by
    rw [sqOuterMoment, show r + 1 + 1 = r + 2 by omega,
      show r + 2 = r + 2 by rfl,
      Function.iterate_add_apply derivativeFun r 2,
      iterate_derivativeFun_two_X_mul_Pw_zero,
      iterate_derivativeFun_onePlusXUnit_inv, smul_smul]
    rw [show -(r : ℤ) - 1 = -((r + 1 : ℕ) : ℤ) by push_cast; ring]
  have hd : coeff 0 (sqOuterMoment (r + 1))
      = sqBracketCoeffZ 2 1 (((r + 1) + 1 : ℕ) : ℤ) := by
    have h := coeff_sqOuterMoment (r + 1) 0
    norm_num only [Nat.zero_add] at h
    rw [gBinom_natCast, Nat.choose_self, Nat.cast_one, mul_one] at h
    exact h
  have hA : A = sqBracketCoeffZ 2 1 (((r + 1) + 1 : ℕ) : ℤ) := by
    have h := congrArg (coeff 0) hm
    rw [map_smul] at h
    have hc : coeff 0 (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ))) : PowerSeries ℂ) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_unit_zpow onePlusXUnit constantCoeff_onePlusX]
    rw [hc] at h
    simpa only [smul_eq_mul, mul_one] using h.symm.trans hd
    
  simpa only [Nat.succ_eq_add_one] using hm.trans (congrArg (fun c ↦ c •
    (↑(onePlusXUnit ^ (-((r + 1 : ℕ) : ℤ))) : PowerSeries ℂ)) hA)

/-- Multiplying the outer moment into an ordinary weight-`k` square-mode generator simply lowers
that weight by `q`. -/
theorem sqOuterMoment_mul_sqGen {q k : ℕ} (hq : 1 ≤ q) (hqk : q ≤ k) (j : ℤ) :
    sqOuterMoment q * sqGen k j = sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ) •
      sqGen (k - q) j := by
  rw [sqOuterMoment_eq_smul_onePlusXUnit_zpow hq]
  simp only [sqGen, smul_mul_assoc]
  rw [show (↑(onePlusXUnit ^ (-(q : ℤ))) : PowerSeries ℂ) *
        ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) *
          (↑(uUnit ^ j) : PowerSeries ℂ))
      = ((↑(onePlusXUnit ^ (((k - q : ℕ) : ℤ) - 1)) : PowerSeries ℂ) *
          (↑(uUnit ^ j) : PowerSeries ℂ)) by
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add]
    congr 2
    rw [Nat.cast_sub hqk]
    ring]

/-- The positive-tail coefficient collapse.  This is the scalar identity needed for every
`L_q a` term (`q ≥ 1`) in the ordinary Borcherds commutator. -/
theorem sqBracketCoeffZ_gBinom_collapse {q k : ℕ} (hq : 1 ≤ q) (hqk : q ≤ k)
    (j : ℤ) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1),
        (sqBracketCoeffZ 2 1 ((s + q + 1 : ℕ) : ℤ)
          * gBinom ((s + q + 1 : ℕ) : ℤ) (q + 1))
          * sqBracketCoeffZ k j (j + ((t - s : ℕ) : ℤ))
      = sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ (k - q) j (j + (t : ℤ)) := by
  have h := congrArg (coeff t) (sqOuterMoment_mul_sqGen hq hqk j)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    map_smul] at h
  simp_rw [coeff_sqOuterMoment] at h
  have hgen : ∀ (K n : ℕ), coeff n (sqGen K j) =
      sqBracketCoeffZ K j (j + (n : ℤ)) := by
    intro K n
    exact (sqBracketCoeffZ_eq_coeff_sqGen K j n).symm
  simpa only [hgen] using h

/-! ## The translation/weight pair -/

/-- The generating-series identity which combines the `L₋₁ a` and `L₀ a` terms.  Their sum is
exactly the scalar `(k-j-1)` required by the square `L[0]` commutator. -/
theorem sqLowPair_powerSeries (k : ℕ) (j : ℤ) :
    PowerSeries.C (k : ℂ) * derivativeFun (X * Pw 0) * sqGen k j
        - PowerSeries.C ((j : ℂ) + 1) * Pw 0 * sqGen k j
        - X * derivativeFun (Pw 0 * sqGen k j)
      = PowerSeries.C ((k : ℂ) - (j : ℂ) - 1) * sqGen k j := by
  let G := sqGen k j
  change PowerSeries.C (k : ℂ) * derivativeFun (X * Pw 0) * G
        - PowerSeries.C ((j : ℂ) + 1) * Pw 0 * G
        - X * derivativeFun (Pw 0 * G)
      = PowerSeries.C ((k : ℂ) - (j : ℂ) - 1) * G
  have hD : Pw 0 = (1 + X) * uSeries := by
    rw [Pw, zero_add, zpow_one, uUnit_coe]
  have hA : (↑(onePlusXUnit ^ (k : ℤ)) : PowerSeries ℂ) =
      (1 + X) * (↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) := by
    calc
      (↑(onePlusXUnit ^ (k : ℤ)) : PowerSeries ℂ) =
          ↑(onePlusXUnit ^ (1 + ((k : ℤ) - 1))) := by congr 2 <;> ring
      _ = _ := by rw [zpow_add, Units.val_mul, zpow_one, onePlusXUnit_coe]
  have hU : (↑(uUnit ^ (j + 1)) : PowerSeries ℂ) =
      uSeries * (↑(uUnit ^ j) : PowerSeries ℂ) := by
    calc
      (↑(uUnit ^ (j + 1)) : PowerSeries ℂ) = ↑(uUnit ^ (1 + j)) := by congr 2 <;> ring
      _ = _ := by rw [zpow_add, Units.val_mul, zpow_one, uUnit_coe]
  have hDG : Pw 0 * G = sqGen (k + 1) (j + 1) := by
    dsimp only [G]
    rw [hD, sqGen, sqGen]
    rw [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by push_cast; ring, hA, hU]
    ring
  have hGj : (1 + X) * G = sqGen (k + 1) j := by
    dsimp only [G]
    rw [sqGen, sqGen]
    rw [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by push_cast; ring, hA]
    ring
  have hHG : (1 + X) * (derivativeFun (X * Pw 0) * G) - X * (Pw 0 * G)
      = (1 + X) * G := by
    rw [derivativeFun_X_mul_Pw_zero, hD]
    ring
  have hode := sqGen_ode (k := k + 1) (by omega) (j + 1)
  rw [show (((k + 1 : ℕ) : ℂ) - 1) = (k : ℂ) by push_cast; ring,
    show j + 1 - 1 = j by ring, ← hDG, ← hGj] at hode
  refine mul_left_cancel₀ (show (1 + X : PowerSeries ℂ) ≠ 0 by
    rw [← onePlusXUnit_coe]
    exact Units.ne_zero onePlusXUnit) ?_
  push_cast at hode ⊢
  simp only [map_sub, map_add, map_one] at hode ⊢
  linear_combination (PowerSeries.C (k : ℂ)) * hHG - hode

/-- The coefficient form of the combined `L₋₁`/`L₀` collapse. -/
theorem sqBracketCoeffZ_low_pair_collapse (k : ℕ) (j : ℤ) (t : ℕ) :
    ∑ r ∈ Finset.range (t + 1),
        sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + ((t - r : ℕ) : ℤ))
          * ((k : ℂ) * ((r : ℂ) + 1) - ((j : ℂ) + (t : ℂ) + 1))
      = ((k : ℂ) - (j : ℂ) - 1) * sqBracketCoeffZ k j (j + (t : ℤ)) := by
  have hps := sqLowPair_powerSeries k j
  rw [show PowerSeries.C (k : ℂ) * derivativeFun (X * Pw 0) * sqGen k j
        = PowerSeries.C (k : ℂ) * (derivativeFun (X * Pw 0) * sqGen k j) by ring,
      show PowerSeries.C ((j : ℂ) + 1) * Pw 0 * sqGen k j
        = PowerSeries.C ((j : ℂ) + 1) * (Pw 0 * sqGen k j) by ring] at hps
  have h := congrArg (coeff t) hps
  -- The three coefficient families are respectively `(r+1)d_r c_{t-r}`, `d_r c_{t-r}`,
  -- and `t d_r c_{t-r}`.
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_X_mul_derivativeFun, PowerSeries.coeff_C_mul] at h
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hDcoeff : ∀ r : ℕ, coeff r (Pw 0) =
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) := by
    intro r
    have hd := sqBracketCoeffZ_two_eq_coeff_Pw (0 : ℤ) (r : ℤ)
    norm_num at hd
    exact hd.symm
  have hHcoeff : ∀ r : ℕ, coeff r (derivativeFun (X * Pw 0)) =
      ((r : ℂ) + 1) * sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) := by
    intro r
    rw [coeff_derivativeFun, coeff_succ_X_mul, hDcoeff]
    push_cast
    ring
  have hGcoeff : ∀ n : ℕ, coeff n (sqGen k j) =
      sqBracketCoeffZ k j (j + (n : ℤ)) := by
    intro n
    exact (sqBracketCoeffZ_eq_coeff_sqGen k j n).symm
  simp_rw [hDcoeff, hHcoeff, hGcoeff] at h
  push_cast at h ⊢
  have hrange : Finset.range (t + 1) = Finset.range t.succ := rfl
  rw [hrange]
  let A : ℕ → ℂ := fun r ↦ sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
    * sqBracketCoeffZ k j (j + ((t - r : ℕ) : ℤ))
  have hlead : ∑ r ∈ Finset.range t.succ,
        A r * ((k : ℂ) * ((r : ℂ) + 1))
      = (k : ℂ) * ∑ r ∈ Finset.range t.succ,
          ((r : ℂ) + 1) * sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
            * sqBracketCoeffZ k j (j + ((t - r : ℕ) : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [A]
    ring
  have hconst : ∑ r ∈ Finset.range t.succ,
        A r * ((j : ℂ) + (t : ℂ) + 1)
      = ((j : ℂ) + 1) * ∑ r ∈ Finset.range t.succ, A r
          + (t : ℂ) * ∑ r ∈ Finset.range t.succ, A r := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  change (∑ r ∈ Finset.range t.succ,
      A r * ((k : ℂ) * ((r : ℂ) + 1) - ((j : ℂ) + (t : ℂ) + 1))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hlead, hconst]
  dsimp only [A]
  simpa only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, neg_add_rev,
    add_assoc, add_comm, add_left_comm] using h

/-! ## The ordinary Virasoro commutator, uniformly in the mode -/

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The ordinary commutator `[L_r,a_i]`, with its Borcherds sum collapsed to
`0 ≤ ℓ ≤ r+1`. -/
theorem L_nat_mode_comm (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (r : ℕ) (i : ℤ) :
    ⁅W.L (r : ℤ), mode (W.Y a) i⁆ =
      ∑ ℓ ∈ Finset.range (r + 2), gBinom ((r + 1 : ℕ) : ℤ) ℓ •
        mode (W.Y (W.L ((ℓ : ℤ) - 1) a))
          ((r + 1 : ℕ) + i - (ℓ : ℕ)) := by
  obtain ⟨N, hzero, hcomm⟩ :=
    VertexOperatorAlgebra.commBound W W.conformalVector a ((r + 1 : ℕ) : ℤ) i
  have hL : W.L (r : ℤ) = mode (W.Y W.conformalVector) ((r + 1 : ℕ) : ℤ) := by
    simp only [VertexOperatorAlgebra.L_def]
    congr 2
  rw [hL, hcomm]
  rw [VertexOperatorAlgebra.finN_gBinom_collapse (r + 1) N
    (fun ℓ ↦ mode (W.Y (W.smul W.conformalVector (ℓ : ℤ) a))
      (((r + 1 : ℕ) : ℤ) + i - (ℓ : ℤ)))
    (fun ℓ hN ↦ by
      change mode (W.Y (W.smul W.conformalVector (ℓ : ℤ) a))
        (((r + 1 : ℕ) : ℤ) + i - (ℓ : ℤ)) = 0
      rw [hzero ℓ hN, map_zero, mode_zero])]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 2
  rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  congr 2
  ring

/-! ## Locally finite antidiagonal regrouping -/

/-- A finitely supported `ℕ × ℕ` sum may be regrouped by total degree. -/
theorem finsum_prod_eq_finsum_antidiagonal_sq {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) (hf : (Function.support f).Finite) :
    (∑ᶠ p : ℕ × ℕ, f p) = ∑ᶠ t : ℕ, ∑ p ∈ Finset.antidiagonal t, f p := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ p ∈ Function.support f, p.1 + p.2 < B := by
    refine ⟨(hf.toFinset.image (fun p ↦ p.1 + p.2)).sup id + 1, fun p hp ↦ ?_⟩
    have hp' : p ∈ hf.toFinset := by rwa [Set.Finite.mem_toFinset]
    have hle : p.1 + p.2 ≤ (hf.toFinset.image (fun p ↦ p.1 + p.2)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hp')
    omega
  have hsub : Function.support f ⊆
      ↑((Finset.range B).biUnion Finset.antidiagonal) := by
    intro p hp
    rw [Finset.coe_biUnion, Set.mem_iUnion₂]
    exact ⟨p.1 + p.2, by simpa using hB p hp, Finset.mem_antidiagonal.mpr rfl⟩
  rw [finsum_eq_finsetSum_of_support_subset f hsub,
    Finset.sum_biUnion (by
      intro s _ t _ hst
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hps hpt
      exact hst ((Finset.mem_antidiagonal.mp hps).symm.trans
        (Finset.mem_antidiagonal.mp hpt)))]
  rw [finsum_eq_finsetSum_of_support_subset
    (fun t : ℕ ↦ ∑ p ∈ Finset.antidiagonal t, f p) (s := Finset.range B) ?_]
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hlt
  rw [Finset.coe_range, Set.mem_Iio, not_lt] at hlt
  refine ht (Finset.sum_eq_zero fun p hp ↦ ?_)
  by_contra hfp
  exact absurd (hB p hfp) (by rw [Finset.mem_antidiagonal] at hp; omega)

/-- The coefficient Cauchy product, evaluated against any finitely supported vector family. -/
theorem finsum_coeff_mul_smul {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (A B : PowerSeries ℂ) (x : ℕ → M) (hx : (Function.support x).Finite) :
    (∑ᶠ p : ℕ × ℕ, (coeff p.1 A * coeff p.2 B) • x (p.1 + p.2))
      = ∑ᶠ t : ℕ, coeff t (A * B) • x t := by
  have hpair : (Function.support fun p : ℕ × ℕ ↦
      (coeff p.1 A * coeff p.2 B) • x (p.1 + p.2)).Finite := by
    refine Set.Finite.subset (hx.toFinset.biUnion Finset.antidiagonal).finite_toSet ?_
    intro p hp
    have hxp : x (p.1 + p.2) ≠ 0 := by
      intro hz
      rw [Function.mem_support] at hp
      exact hp (by rw [hz, smul_zero])
    rw [Finset.coe_biUnion, Set.mem_iUnion₂]
    exact ⟨p.1 + p.2, (Set.Finite.mem_toFinset hx).mpr hxp,
      Finset.mem_antidiagonal.mpr rfl⟩
  rw [finsum_prod_eq_finsum_antidiagonal_sq _ hpair]
  refine finsum_congr fun t ↦ ?_
  rw [PowerSeries.coeff_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [hp]

/-- Finite support pulled back along addition: every fiber over a finite subset of `ℕ` is a finite
antidiagonal. -/
theorem support_pair_smul_add_finite {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (c : ℕ × ℕ → ℂ) (x : ℕ → M) (hx : (Function.support x).Finite) :
    (Function.support fun p : ℕ × ℕ ↦ c p • x (p.1 + p.2)).Finite := by
  refine Set.Finite.subset (hx.toFinset.biUnion Finset.antidiagonal).finite_toSet ?_
  intro p hp
  have hxp : x (p.1 + p.2) ≠ 0 := by
    intro hz
    rw [Function.mem_support] at hp
    exact hp (by rw [hz, smul_zero])
  rw [Finset.coe_biUnion, Set.mem_iUnion₂]
  exact ⟨p.1 + p.2, (Set.Finite.mem_toFinset hx).mpr hxp,
    Finset.mem_antidiagonal.mpr rfl⟩

/-- The module-valued version of the exceptional `L₋₁`/`L₀` collapse. -/
theorem sqLowPair_vector_collapse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (k : ℕ) (j : ℤ) (x : ℕ → M) (hx : (Function.support x).Finite) :
    (∑ᶠ p : ℕ × ℕ,
        (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (p.2 : ℤ))
          * ((k : ℂ) * ((p.1 : ℂ) + 1)
            - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) • x (p.1 + p.2))
      = ∑ᶠ t : ℕ,
          (((k : ℂ) - (j : ℂ) - 1) * sqBracketCoeffZ k j (j + (t : ℤ))) • x t := by
  rw [finsum_prod_eq_finsum_antidiagonal_sq _
    (support_pair_smul_add_finite _ x hx)]
  refine finsum_congr fun t ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hc := sqBracketCoeffZ_low_pair_collapse k j t
  rw [← hc, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrt : r ≤ t := by rw [Finset.mem_range] at hr; omega
  rw [Nat.add_sub_of_le hrt]

/-- The module-valued positive-tail collapse for one fixed `q`. -/
theorem sqPositiveTail_vector_collapse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {q k : ℕ} (hq : 1 ≤ q) (hqk : q ≤ k) (j : ℤ)
    (x : ℕ → M) (hx : (Function.support x).Finite) :
    (∑ᶠ p : ℕ × ℕ,
        ((sqBracketCoeffZ 2 1 ((p.1 + q + 1 : ℕ) : ℤ)
          * gBinom ((p.1 + q + 1 : ℕ) : ℤ) (q + 1))
          * sqBracketCoeffZ k j (j + (p.2 : ℤ))) • x (p.1 + p.2))
      = ∑ᶠ t : ℕ,
          (sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ)
            * sqBracketCoeffZ (k - q) j (j + (t : ℤ))) • x t := by
  rw [finsum_prod_eq_finsum_antidiagonal_sq _
    (support_pair_smul_add_finite _ x hx)]
  refine finsum_congr fun t ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hc := sqBracketCoeffZ_gBinom_collapse hq hqk j t
  rw [← hc, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro s hs
  have hst : s ≤ t := by rw [Finset.mem_range] at hs; omega
  rw [Nat.add_sub_of_le hst]

/-! ## Natural-index expansions of the two square modes -/

/-- Reindex an integer `finsum` supported on `j ≤ i` by `i = j+n`. -/
theorem finsum_int_ge_eq_nat_shift {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : ℤ → M) (j : ℤ) (hzero : ∀ i, i < j → F i = 0) :
    (∑ᶠ i : ℤ, F i) = ∑ᶠ n : ℕ, F (j + (n : ℤ)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ j + (n : ℤ)) := by
    intro a b h
    have hab : (a : ℤ) = (b : ℤ) := add_left_cancel h
    exact_mod_cast hab
  have hsub : Function.support F ⊆ Set.range (fun n : ℕ ↦ j + (n : ℤ)) := by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hrange
    apply hi
    apply hzero i
    by_contra hge
    push Not at hge
    refine hrange ⟨(i - j).toNat, ?_⟩
    change j + (((i - j).toNat : ℕ) : ℤ) = i
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [← VertexOperatorAlgebra.finsum_mem_of_support_subset' F _ hsub,
    finsum_mem_range hinj]

/-- Drop a membership restriction when it already contains the support. -/
theorem finsum_mem_of_support_subset_sq {α M : Type*} [AddCommGroup M]
    (F : α → M) (s : Set α) (h : Function.support F ⊆ s) :
    (∑ᶠ i ∈ s, F i) = ∑ᶠ i, F i := by
  rw [← finsum_mem_inter_support F s, ← finsum_mem_univ (f := F),
    ← finsum_mem_inter_support F Set.univ, Set.univ_inter, Set.inter_eq_right.mpr h]

/-- `a[j]` for ordinary-homogeneous `a`, written as a natural tail `i=j+n`. -/
theorem vSqZ_eq_nat_finsum (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (k : ℕ) (j : ℤ) (v : 𝒱) :
    vSqZ W a k j v = ∑ᶠ n : ℕ,
      sqBracketCoeffZ k j (j + (n : ℤ)) • mode (W.Y a) (j + (n : ℤ)) v := by
  rw [vSqZ_apply, finsum_int_ge_eq_nat_shift]
  intro i hi
  rw [sqBracketCoeffZ_of_lt k hi, zero_smul]

/-- `L[0]` written as its natural Virasoro tail `Σ_{r≥0} d_r L_r`. -/
theorem Lsq_zero_eq_nat_finsum (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    Lsq W 0 v = ∑ᶠ r : ℕ,
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • W.L (r : ℤ) v := by
  rw [Lsq_apply, show (0 : ℤ) + 1 = 1 by ring,
    sqBracketCoeffZ_vacuum_of_ne 1 (by norm_num), mul_zero, zero_smul, sub_zero,
    show (1 : ℤ) = 0 + 1 by ring, vSqZ_omega_apply W 0 v]
  symm
  apply VertexOperatorAlgebra.finsum_nat_to_int
  · intro r hr
    rw [sqBracketCoeffZ_of_lt 2 (by omega), zero_smul]
  · intro r
    congr 2

/-! ## The locally finite commutator expansion -/

theorem dLNat_support_finite (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    (Function.support fun r : ℕ ↦
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • W.L (r : ℤ) v).Finite := by
  have h := (dL_support_finite W 0 v).preimage
    (f := fun r : ℕ ↦ (r : ℤ)) (Function.Injective.injOn Int.ofNat_injective)
  refine h.subset fun r hr ↦ ?_
  simpa only [Set.mem_preimage] using hr

theorem sqNat_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    (Function.support fun n : ℕ ↦
      sqBracketCoeffZ k j (j + (n : ℤ)) • mode (W.Y a) (j + (n : ℤ)) v).Finite := by
  have h := (sqModeZ_support_finite W a k j v).preimage
    (f := fun n : ℕ ↦ j + (n : ℤ)) (by
      intro r s hrs
      have : (r : ℤ) = (s : ℤ) := add_left_cancel hrs
      exact_mod_cast this : Function.Injective fun n : ℕ ↦ j + (n : ℤ)).injOn
  refine h.subset fun n hn ↦ ?_
  simpa only [Set.mem_preimage] using hn

/-- Swap two nested `finsum`s from joint finite support. -/
theorem finsum_finsum_comm_sq {α β M : Type*} [AddCommMonoid M] (F : α → β → M)
    (hF : (Function.support fun p : α × β ↦ F p.1 p.2).Finite) :
    ∑ᶠ b : β, ∑ᶠ a : α, F a b = ∑ᶠ a : α, ∑ᶠ b : β, F a b := by
  have hswap : (Function.support fun q : β × α ↦ F q.2 q.1).Finite := by
    have hpre : Function.support (fun q : β × α ↦ F q.2 q.1)
        = (Equiv.prodComm β α) ⁻¹' (Function.support fun p : α × β ↦ F p.1 p.2) := rfl
    rw [hpre]
    exact hF.preimage ((Equiv.prodComm β α).injective.injOn)
  calc
    (∑ᶠ b : β, ∑ᶠ a : α, F a b) = ∑ᶠ q : β × α, F q.2 q.1 :=
      (finsum_curry (fun q : β × α ↦ F q.2 q.1) hswap).symm
    _ = ∑ᶠ p : α × β, F p.1 p.2 :=
      finsum_comp_equiv (Equiv.prodComm β α) (f := fun p : α × β ↦ F p.1 p.2)
    _ = ∑ᶠ a : α, ∑ᶠ b : β, F a b :=
      finsum_curry (fun p : α × β ↦ F p.1 p.2) hF

/-- The composite `L[0] ∘ a[j]` as a natural double sum. -/
theorem Lsq_zero_vSqZ_comp (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    Lsq W 0 (vSqZ W a k j v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v) := by
  rw [vSqZ_eq_nat_finsum,
    map_finsum (Lsq W 0) (sqNat_support_finite W a k j v)]
  refine finsum_congr fun n ↦ ?_
  rw [map_smul, Lsq_zero_eq_nat_finsum,
    smul_finsum' _ (dLNat_support_finite W (mode (W.Y a) (j + (n : ℤ)) v))]
  refine finsum_congr fun r ↦ ?_
  rw [smul_smul, mul_comm]

/-- Joint finiteness for the `a[j] ∘ L[0]` composite. -/
theorem sqLJoint_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    (Function.support fun p : ℕ × ℕ ↦
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
          mode (W.Y a) (j + (p.2 : ℤ)) (W.L (p.1 : ℤ) v)).Finite := by
  refine Set.Finite.subset
    ((dLNat_support_finite W v).biUnion fun r _ ↦
      (sqNat_support_finite W a k j (W.L (r : ℤ) v)).image fun n ↦ (r, n)) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff, mul_ne_zero_iff] at hp
  obtain ⟨⟨hdr, hcn⟩, hvec⟩ := hp
  simp only [Set.mem_iUnion, Set.mem_image, Function.mem_support, ne_eq,
    smul_ne_zero_iff, exists_prop]
  refine ⟨p.1, ⟨hdr, fun hz ↦ hvec (by rw [hz, map_zero])⟩, p.2, ?_, rfl⟩
  exact ⟨hcn, hvec⟩

/-- The composite `a[j] ∘ L[0]`, put in the same `(n,r)` order. -/
theorem vSqZ_Lsq_zero_comp (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    vSqZ W a k j (Lsq W 0 v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v) := by
  have hraw : vSqZ W a k j (Lsq W 0 v) = ∑ᶠ r : ℕ, ∑ᶠ n : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v) := by
    rw [Lsq_zero_eq_nat_finsum,
      map_finsum (vSqZ W a k j) (dLNat_support_finite W v)]
    refine finsum_congr fun r ↦ ?_
    rw [map_smul, vSqZ_eq_nat_finsum,
      smul_finsum' _ (sqNat_support_finite W a k j (W.L (r : ℤ) v))]
    refine finsum_congr fun n ↦ ?_
    rw [smul_smul]
  rw [hraw]
  exact (finsum_finsum_comm_sq
    (fun r n : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v))
    (sqLJoint_support_finite W a k j v)).symm

/-- The square/ordinary commutator expanded as a locally finite natural double sum of ordinary
Virasoro commutators. -/
theorem Lsq_zero_vSqZ_comm_double (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    Lsq W 0 (vSqZ W a k j v) - vSqZ W a k j (Lsq W 0 v) =
      ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            (W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)
              - mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)) := by
  rw [Lsq_zero_vSqZ_comp, vSqZ_Lsq_zero_comp]
  have hout1 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)).Finite := by
    refine (sqNat_support_finite W a k j v).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)) =
        sqBracketCoeffZ k j (j + (n : ℤ)) •
          Lsq W 0 (mode (W.Y a) (j + (n : ℤ)) v) := by
      rw [Lsq_zero_eq_nat_finsum,
        smul_finsum' _ (dLNat_support_finite W (mode (W.Y a) (j + (n : ℤ)) v))]
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    apply hn
    rw [heq, ← map_smul, hzero, map_zero]
  have hout2 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)).Finite := by
    refine (sqNat_support_finite W a k j (Lsq W 0 v)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have hfinmap : (Function.support fun r : ℕ ↦
        sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)).Finite := by
      refine (dLNat_support_finite W v).subset ?_
      intro r hr
      simp only [Function.mem_support, ne_eq] at hr ⊢
      intro hz
      apply hr
      have hz' := congrArg (fun x ↦ mode (W.Y a) (j + (n : ℤ)) x) hz
      simpa only [map_smul, map_zero] using hz'
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)) =
        sqBracketCoeffZ k j (j + (n : ℤ)) •
          mode (W.Y a) (j + (n : ℤ)) (Lsq W 0 v) := by
      rw [Lsq_zero_eq_nat_finsum,
        map_finsum (mode (W.Y a) (j + (n : ℤ))) (dLNat_support_finite W v)]
      simp_rw [map_smul]
      rw [smul_finsum' _ hfinmap]
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    exact hn (heq.trans hzero)
  rw [← finsum_sub_distrib hout1 hout2]
  refine finsum_congr fun n ↦ ?_
  have hin1 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)).Finite := by
    refine (dLNat_support_finite W (mode (W.Y a) (j + (n : ℤ)) v)).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)
        = sqBracketCoeffZ k j (j + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hbase, smul_zero]
  have hin2 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)).Finite := by
    refine (dLNat_support_finite W v).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    have hmap : sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
        mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v) = 0 := by
      rw [← map_smul, hbase, map_zero]
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)
        = sqBracketCoeffZ k j (j + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hmap, smul_zero]
  rw [← finsum_sub_distrib hin1 hin2]
  refine finsum_congr fun r ↦ ?_
  rw [smul_sub]

/-- The ordinary commutator split into the combined translation/weight term and the strictly
positive Virasoro tail. -/
theorem L_nat_mode_comm_split (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (r : ℕ) (i : ℤ) (v : 𝒱) :
    W.L (r : ℤ) (mode (W.Y a) i v) - mode (W.Y a) i (W.L (r : ℤ) v) =
      ((k : ℂ) * ((r : ℂ) + 1) - ((r : ℂ) + (i : ℂ) + 1)) •
          mode (W.Y a) ((r : ℤ) + i) v
        + ∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
            mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
              ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
  have h := LinearMap.congr_fun (L_nat_mode_comm W a r i) v
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, LinearMap.sum_apply] at h
  simp only [LinearMap.smul_apply] at h
  have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
      mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
        ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply finsum_eq_finsetSum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hqr
    push Not at hqr
    apply hq
    rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
  rw [htail, h]
  rw [Finset.sum_range_succ' (n := r + 1),
    Finset.sum_range_succ' (f := fun ℓ : ℕ ↦
      gBinom ((r + 1 : ℕ) : ℤ) (ℓ + 1) •
        mode (W.Y (W.L (((ℓ + 1 : ℕ) : ℤ) - 1) a))
          ((r + 1 : ℕ) + i - (ℓ + 1 : ℕ)) v) (n := r)]
  have hg0 : gBinom ((r + 1 : ℕ) : ℤ) 0 = 1 := gBinom_zero _
  have hg1 : gBinom ((r + 1 : ℕ) : ℤ) 1 = ((r : ℂ) + 1) := by
    rw [gBinom_natCast]
    simp
  rw [hg0, hg1, one_smul,
    show (((0 : ℕ) : ℤ) - 1) = -1 by norm_num,
    show (((1 : ℕ) : ℤ) - 1) = 0 by norm_num]
  have hcastL : ∀ q : ℕ, ((((q + 1 : ℕ) + 1 : ℕ) : ℤ) - 1)
      = ((q + 1 : ℕ) : ℤ) := by intro q; push_cast; ring
  have hcastI : ∀ q : ℕ, ((r + 1 : ℕ) : ℤ) + i - ((q + 1 : ℕ) : ℤ)
      = (r : ℤ) + i - q := by intro q; push_cast; ring
  simp_rw [hcastL, hcastI]
  simp only [Nat.cast_zero, sub_zero]
  rw [show mode (W.Y (W.L (-1) a)) (((r + 1 : ℕ) : ℤ) + i) v =
      (-(((r + 1 : ℕ) : ℤ) + i)) • mode (W.Y a) ((r : ℤ) + i) v by
    simpa only [PreVertexAlgebra.smul_def, show (((r + 1 : ℕ) : ℤ) + i - 1)
      = (r : ℤ) + i by push_cast; ring] using
        smul_L_neg_one W a v (((r + 1 : ℕ) : ℤ) + i),
    W.L_zero_grading a ha, map_smul, mode_smul, LinearMap.smul_apply,
    smul_smul]
  have htailsame : (∑ x ∈ Finset.range r,
      gBinom ((r + 1 : ℕ) : ℤ) (x + 1 + 1) •
        mode (W.Y (W.L ((x + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((x + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply Finset.sum_congr rfl
    intro q _
    congr 3 <;> omega
  rw [htailsame]
  push_cast
  module

/-! ## Collapse of the vector-valued commutator pieces -/

theorem modeNat_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (j : ℤ) (v : 𝒱) :
    (Function.support fun t : ℕ ↦ mode (W.Y a) (j + (t : ℤ)) v).Finite := by
  obtain ⟨R, hR⟩ := W.regularity a v
  refine Set.Finite.subset (Set.finite_Iio ((R - j).toNat + 1)) ?_
  intro t ht
  simp only [Function.mem_support, ne_eq] at ht
  rw [Set.mem_Iio]
  by_contra hlarge
  push Not at hlarge
  apply ht
  apply hR
  have hself := Int.self_le_toNat (R - j)
  omega

/-- The complete low (`L₋₁` plus `L₀`) double sum collapses to
`(k-j-1)a[j]v`. -/
theorem sqLow_comm_collapse (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    (∑ᶠ p : ℕ × ℕ,
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))
        * ((k : ℂ) * ((p.1 : ℂ) + 1)
          - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
            mode (W.Y a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      ((k : ℂ) - (j : ℂ) - 1) • vSqZ W a k j v := by
  rw [sqLowPair_vector_collapse k j
    (fun t : ℕ ↦ mode (W.Y a) (j + (t : ℤ)) v)
    (modeNat_support_finite W a j v), vSqZ_eq_nat_finsum,
    smul_finsum' _ (sqNat_support_finite W a k j v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

/-- For fixed `Q≥1`, the reindexed positive-tail double sum collapses to
`d_Q·(L_Qa)[j]v`. -/
theorem sqPositive_comm_collapse (W : VertexOperatorAlgebra 𝒱) {a : 𝒱}
    {Q k : ℕ} (hQ : 1 ≤ Q) (hQk : Q ≤ k) (j : ℤ) (v : 𝒱) :
    (∑ᶠ p : ℕ × ℕ,
      ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
        * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
          mode (W.Y (W.L (Q : ℤ) a))
            (j + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        vSqZ W (W.L (Q : ℤ) a) (k - Q) j v := by
  rw [sqPositiveTail_vector_collapse hQ hQk j
    (fun t : ℕ ↦ mode (W.Y (W.L (Q : ℤ) a)) (j + (t : ℤ)) v)
    (modeNat_support_finite W (W.L (Q : ℤ) a) j v),
    vSqZ_eq_nat_finsum,
    smul_finsum' _ (sqNat_support_finite W (W.L (Q : ℤ) a) (k - Q) j v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

/-- The low commutator summand, indexed as `(n,r)` for the nested square-mode expansion. -/
noncomputable def sqLowCommTerm (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) (p : ℕ × ℕ) : 𝒱 :=
  (sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffZ k j (j + (p.1 : ℤ))
    * ((k : ℂ) * ((p.2 : ℂ) + 1)
      - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
        mode (W.Y a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v

/-- The positive commutator summand before the shift `r=Q+s`, indexed as `(n,r)`. -/
noncomputable def sqPositiveCommTerm (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) (Q : ℕ) (p : ℕ × ℕ) : 𝒱 :=
  ((sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffZ k j (j + (p.1 : ℤ)))
    * gBinom ((p.2 + 1 : ℕ) : ℤ) (Q + 1)) •
      mode (W.Y (W.L (Q : ℤ) a))
        (j + ((p.1 + (p.2 - Q) : ℕ) : ℤ)) v

/-- The same positive summand after `r=Q+s`, indexed as `(s,n)`. -/
noncomputable def sqPositiveReindexedTerm (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) (Q : ℕ) (p : ℕ × ℕ) : 𝒱 :=
  ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
    * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
    * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
      mode (W.Y (W.L (Q : ℤ) a))
        (j + ((p.1 + p.2 : ℕ) : ℤ)) v

theorem sqLowCommTerm_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    (Function.support (sqLowCommTerm W a k j v)).Finite := by
  let g : ℕ × ℕ → 𝒱 := fun p ↦
    (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffZ k j (j + (p.2 : ℤ))
      * ((k : ℂ) * ((p.1 : ℂ) + 1)
        - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
          mode (W.Y a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v
  have h : (Function.support g).Finite := support_pair_smul_add_finite
    (fun p : ℕ × ℕ ↦ sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffZ k j (j + (p.2 : ℤ))
      * ((k : ℂ) * ((p.1 : ℂ) + 1)
        - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1)))
    (fun t : ℕ ↦ mode (W.Y a) (j + (t : ℤ)) v)
    (modeNat_support_finite W a j v)
  have hswap := h.preimage (f := Prod.swap) (Function.Injective.injOn Prod.swap_injective)
  refine hswap.subset fun p hp ↦ ?_
  change g (Prod.swap p) ≠ 0
  rcases p with ⟨n, r⟩
  simpa only [g, sqLowCommTerm, Prod.swap_prod_mk, Prod.fst, Prod.snd,
    Nat.add_comm] using hp

theorem sqPositiveReindexedTerm_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) (Q : ℕ) :
    (Function.support (sqPositiveReindexedTerm W a k j v Q)).Finite := by
  exact support_pair_smul_add_finite _ _
    (modeNat_support_finite W (W.L (Q : ℤ) a) j v)

theorem sqPositiveCommTerm_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) (Q : ℕ) :
    (Function.support (sqPositiveCommTerm W a k j v Q)).Finite := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hR := sqPositiveReindexedTerm_support_finite W a k j v Q
  refine Set.Finite.subset (hR.image φ) ?_
  intro p hp
  have hrQ : Q ≤ p.2 := by
    by_contra hr
    push Not at hr
    rw [Function.mem_support] at hp
    apply hp
    rw [sqPositiveCommTerm, gBinom_natCast,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
  let s := p.2 - Q
  have hs : Q + s = p.2 := Nat.add_sub_of_le hrQ
  have hterm : sqPositiveReindexedTerm W a k j v Q (s, p.1) ≠ 0 := by
    change sqPositiveCommTerm W a k j v Q p ≠ 0 at hp
    simpa only [sqPositiveCommTerm, sqPositiveReindexedTerm, Prod.fst, Prod.snd,
      hs, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      mul_assoc, mul_comm, mul_left_comm] using hp
  exact ⟨(s, p.1), hterm, by ext <;> simp [φ, hs]⟩

/-- Reindex the full fixed-`Q` positive contribution by `r=Q+s`, then apply the positive scalar
collapse. -/
theorem sqPositiveCommTerm_collapse (W : VertexOperatorAlgebra 𝒱) {a : 𝒱}
    {Q k : ℕ} (hQ : 1 ≤ Q) (hQk : Q ≤ k) (j : ℤ) (v : 𝒱) :
    (∑ᶠ p : ℕ × ℕ, sqPositiveCommTerm W a k j v Q p) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        vSqZ W (W.L (Q : ℤ) a) (k - Q) j v := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hinj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · have := congrArg Prod.snd hpq
      dsimp only [φ] at this
      omega
    · have := congrArg Prod.fst hpq
      exact this
  have hsub : Function.support (sqPositiveCommTerm W a k j v Q) ⊆ Set.range φ := by
    intro p hp
    have hrQ : Q ≤ p.2 := by
      by_contra hr
      push Not at hr
      rw [Function.mem_support] at hp
      apply hp
      rw [sqPositiveCommTerm, gBinom_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
    exact ⟨(p.2 - Q, p.1), by ext <;> simp [φ, Nat.add_sub_of_le hrQ]⟩
  rw [← finsum_mem_of_support_subset_sq
      (sqPositiveCommTerm W a k j v Q) _ hsub,
    finsum_mem_range hinj]
  have hreindex : ∀ p : ℕ × ℕ,
      sqPositiveCommTerm W a k j v Q (φ p) =
        sqPositiveReindexedTerm W a k j v Q p := by
    rintro ⟨s, n⟩
    simp only [φ, sqPositiveCommTerm, sqPositiveReindexedTerm, Prod.fst, Prod.snd,
      Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      mul_assoc, mul_comm, mul_left_comm]
  rw [finsum_congr hreindex]
  exact sqPositive_comm_collapse W hQ hQk j v

theorem sqLowCommTerm_collapse (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (k : ℕ) (j : ℤ) (v : 𝒱) :
    (∑ᶠ p : ℕ × ℕ, sqLowCommTerm W a k j v p) =
      ((k : ℂ) - (j : ℂ) - 1) • vSqZ W a k j v := by
  rw [← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  have heq : ∀ p : ℕ × ℕ,
      sqLowCommTerm W a k j v ((Equiv.prodComm ℕ ℕ) p) =
        (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (p.2 : ℤ))
          * ((k : ℂ) * ((p.1 : ℂ) + 1)
            - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
              mode (W.Y a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v := by
    rintro ⟨r, n⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, sqLowCommTerm,
      Prod.fst, Prod.snd, Nat.add_comm]
  rw [finsum_congr heq]
  exact sqLow_comm_collapse W a k j v

/-! ## Reassembly as the square mode of `L[0]a` -/

theorem L_nat_eq_zero_of_lt (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {k Q : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (hkQ : k < Q) : W.L (Q : ℤ) a = 0 := by
  have hmem := L_mem_grading W ha (Q : ℤ)
  rw [W.positivity ((k : ℤ) - Q) (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- Every natural Virasoro descendant is interpreted by the linearly extended square mode with
its correct ordinary weight, including the zero region `Q>k`. -/
theorem sqMode_L_nat_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (Q : ℕ) (j : ℤ) :
    sqMode W j (W.L (Q : ℤ) a) = vSqZ W (W.L (Q : ℤ) a) (k - Q) j := by
  by_cases hQk : Q ≤ k
  · have hmem := L_mem_grading W ha (Q : ℤ)
    have hgrade : W.L (Q : ℤ) a ∈ W.grading ((k - Q : ℕ) : ℤ) := by
      convert hmem using 1
      rw [Nat.cast_sub hQk]
    simpa using sqMode_of_mem_grading W hgrade j
  · have hzero := L_nat_eq_zero_of_lt W ha (by omega : k < Q)
    rw [hzero, map_zero, vSqZ_zero_left]

/-- The square mode of `L[0]a` is the locally finite sum of the square modes of its ordinary
Virasoro descendants. -/
theorem sqMode_Lsq_zero_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) :
    sqMode W j (Lsq W 0 a) = ∑ᶠ Q : ℕ,
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        vSqZ W (W.L (Q : ℤ) a) (k - Q) j := by
  rw [Lsq_zero_eq_nat_finsum,
    map_finsum (sqMode W j) (dLNat_support_finite W a)]
  refine finsum_congr fun Q ↦ ?_
  rw [map_smul, sqMode_L_nat_of_mem_grading W ha]

/-- The full homogeneous commutator after the finite Borcherds sum has been split and regrouped. -/
theorem Lsq_zero_vSqZ_comm_collapsed (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : 𝒱) :
    Lsq W 0 (vSqZ W a k j v) - vSqZ W a k j (Lsq W 0 v) =
      ((k : ℂ) - (j : ℂ) - 1) • vSqZ W a k j v
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              vSqZ W (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j v := by
  rw [Lsq_zero_vSqZ_comm_double]
  let H : ℕ × ℕ → 𝒱 := fun p ↦ sqLowCommTerm W a k j v p
    + ∑ Q ∈ Finset.range k, sqPositiveCommTerm W a k j v (Q + 1) p
  have hterm : ∀ n r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          (W.L (r : ℤ) (mode (W.Y a) (j + (n : ℤ)) v)
            - mode (W.Y a) (j + (n : ℤ)) (W.L (r : ℤ) v)) = H (n, r) := by
    intro n r
    rw [L_nat_mode_comm_split W ha r (j + (n : ℤ)) v, smul_add]
    have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + (j + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v) =
        ∑ q ∈ Finset.range k, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
          mode (W.Y (W.L ((q + 1 : ℕ) : ℤ) a))
            ((r : ℤ) + (j + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v := by
      apply finsum_eq_finsetSum_of_support_subset
      intro q hq
      simp only [Function.mem_support, ne_eq] at hq
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hqk
      push Not at hqk
      exact hq (by rw [L_nat_eq_zero_of_lt W ha (by omega : k < q + 1), map_zero,
        mode_zero, LinearMap.zero_apply, smul_zero])
    rw [htail, Finset.smul_sum]
    change _ = sqLowCommTerm W a k j v (n, r)
      + ∑ Q ∈ Finset.range k, sqPositiveCommTerm W a k j v (Q + 1) (n, r)
    congr 1
    · simp only [sqLowCommTerm, Prod.fst, Prod.snd, smul_smul]
      have hidx : (r : ℤ) + (j + (n : ℤ)) = j + ((n + r : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hidx]
      congr 1
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro Q hQ
      by_cases hQr : Q + 1 ≤ r
      · have hidx : (r : ℤ) + (j + (n : ℤ)) - ((Q + 1 : ℕ) : ℤ) =
            j + ((n + (r - (Q + 1)) : ℕ) : ℤ) := by
          push_cast [hQr]
          ring
        simp only [sqPositiveCommTerm, Prod.fst, Prod.snd, smul_smul,
          Nat.add_sub_of_le hQr]
        rw [hidx]
      · have hbin : gBinom ((r + 1 : ℕ) : ℤ) (Q + 1 + 1) = 0 := by
          rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        rw [hbin, zero_smul, smul_zero, sqPositiveCommTerm, hbin, mul_zero, zero_smul]
  simp_rw [hterm]
  have hposUnion : (Function.support fun p : ℕ × ℕ ↦
      ∑ Q ∈ Finset.range k, sqPositiveCommTerm W a k j v (Q + 1) p).Finite := by
    refine Set.Finite.subset
      ((Finset.range k).finite_toSet.biUnion fun Q _ ↦
        sqPositiveCommTerm_support_finite W a k j v (Q + 1)) ?_
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    obtain ⟨Q, hQ, hQne⟩ : ∃ Q ∈ Finset.range k,
        sqPositiveCommTerm W a k j v (Q + 1) p ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hp (Finset.sum_eq_zero fun Q hQ ↦ hnone Q hQ)
    rw [Set.mem_iUnion]
    refine ⟨Q, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hQ, hQne⟩
  have hH : (Function.support H).Finite := by
    refine Set.Finite.subset
      ((sqLowCommTerm_support_finite W a k j v).union hposUnion) ?_
    intro p hp
    by_cases hlow : sqLowCommTerm W a k j v p = 0
    · right
      change (∑ Q ∈ Finset.range k,
        sqPositiveCommTerm W a k j v (Q + 1) p) ≠ 0
      intro hpos
      change H p ≠ 0 at hp
      exact hp (by simp only [H, hlow, hpos, add_zero])
    · left
      exact hlow
  rw [← finsum_curry H hH]
  change (∑ᶠ p : ℕ × ℕ,
      (sqLowCommTerm W a k j v p
        + ∑ Q ∈ Finset.range k, sqPositiveCommTerm W a k j v (Q + 1) p)) = _
  rw [finsum_add_distrib (sqLowCommTerm_support_finite W a k j v) hposUnion,
    sqLowCommTerm_collapse,
    finsum_sum_comm (Finset.range k)
      (fun p Q ↦ sqPositiveCommTerm W a k j v (Q + 1) p)
      (fun Q _ ↦ sqPositiveCommTerm_support_finite W a k j v (Q + 1))]
  apply congrArg (fun z ↦ ((k : ℂ) - (j : ℂ) - 1) • vSqZ W a k j v + z)
  apply Finset.sum_congr rfl
  intro Q hQ
  exact sqPositiveCommTerm_collapse W (by omega) (by rw [Finset.mem_range] at hQ; omega) j v

/-! ## The `L[0]` commutator -/

/-- On an ordinary-homogeneous input, the square mode of `L[0]a` is the scalar weight term plus
the same positive Virasoro tail which occurs in the collapsed commutator. -/
theorem sqMode_Lsq_zero_of_mem_grading_explicit (W : VertexOperatorAlgebra 𝒱)
    {a : 𝒱} {k : ℕ} (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : 𝒱) :
    sqMode W j (Lsq W 0 a) v =
      (k : ℂ) • vSqZ W a k j v
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              vSqZ W (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j v := by
  have hmap : sqMode W j (Lsq W 0 a) =
      (k : ℂ) • vSqZ W a k j
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              vSqZ W (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j := by
    rw [sqMode_Lsq_zero_of_mem_grading W ha]
    have hsub : Function.support (fun Q : ℕ ↦
        sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
          vSqZ W (W.L (Q : ℤ) a) (k - Q) j) ⊆ Finset.range (k + 1) := by
      intro Q hQ
      simp only [Function.mem_support, ne_eq] at hQ
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hQk
      push Not at hQk
      exact hQ (by rw [L_nat_eq_zero_of_lt W ha (by omega : k < Q),
        vSqZ_zero_left, smul_zero])
    rw [finsum_eq_finsetSum_of_support_subset _ hsub, Finset.sum_range_succ']
    have hd0 : sqBracketCoeffZ 2 1 (1 : ℤ) = 1 := by
      simpa using sqBracketCoeff_zero_diag
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.zero_add, Nat.sub_zero]
    rw [hd0, one_smul, W.L_zero_grading a ha, vSqZ_smul_left]
    abel
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply] using
    congrArg (fun T : Module.End ℂ 𝒱 ↦ T v) hmap

/-- The `L[0]` commutator for an ordinary-homogeneous first input. -/
theorem Lsq_zero_sqMode_comm_of_mem_grading (W : VertexOperatorAlgebra 𝒱)
    {a : 𝒱} {k : ℕ} (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : 𝒱) :
    Lsq W 0 (sqMode W j a v) - sqMode W j a (Lsq W 0 v) =
      sqMode W j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode W j a v := by
  have hsq : sqMode W j a = vSqZ W a k j := by
    simpa using sqMode_of_mem_grading W ha j
  rw [hsq]
  rw [Lsq_zero_vSqZ_comm_collapsed W ha,
    sqMode_Lsq_zero_of_mem_grading_explicit W ha]
  module

/-- Zhu's square-bracket grading keystone:
`[L[0], a[j]] = (L[0]a)[j] - (j+1)a[j]`, with no homogeneity hypothesis. -/
theorem Lsq_zero_sqMode_comm (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (j : ℤ) (v : 𝒱) :
    Lsq W 0 (sqMode W j a v) - sqMode W j a (Lsq W 0 v) =
      sqMode W j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode W j a v := by
  refine ordinaryGrading_induction W (P := fun a ↦
    Lsq W 0 (sqMode W j a v) - sqMode W j a (Lsq W 0 v) =
      sqMode W j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode W j a v) ?_ ?_ ?_ a
  · intro k x hx
    by_cases hk : k < 0
    · have hx0 : x = 0 := by
        rw [W.positivity k hk, Submodule.mem_bot] at hx
        exact hx
      subst hx0
      simp
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
      exact Lsq_zero_sqMode_comm_of_mem_grading W hx j v
  · simp
  · intro x y hx hy
    calc
      Lsq W 0 (sqMode W j (x + y) v) - sqMode W j (x + y) (Lsq W 0 v) =
          (Lsq W 0 (sqMode W j x v) - sqMode W j x (Lsq W 0 v))
            + (Lsq W 0 (sqMode W j y v) - sqMode W j y (Lsq W 0 v)) := by
              simp only [map_add, LinearMap.add_apply]
              module
      _ = (sqMode W j (Lsq W 0 x) v - ((j : ℂ) + 1) • sqMode W j x v)
            + (sqMode W j (Lsq W 0 y) v - ((j : ℂ) + 1) • sqMode W j y v) := by
              rw [hx, hy]
      _ = sqMode W j (Lsq W 0 (x + y)) v
            - ((j : ℂ) + 1) • sqMode W j (x + y) v := by
              simp only [map_add, LinearMap.add_apply]
              module

/-! ## Square-weight covariance -/

/-- Zhu's square-bracket modes carry square weights on the full, linearly extended first slot. -/
theorem sqMode_mem_sqWeightSpace (W : VertexOperatorAlgebra 𝒱)
    {K n : ℤ} {a v : 𝒱} (ha : a ∈ sqWeightSpace W (K : ℂ))
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (j : ℤ) :
    sqMode W j a v ∈ sqWeightSpace W ((K + n - j - 1 : ℤ) : ℂ) := by
  rw [mem_sqWeightSpace_iff] at ha hv ⊢
  have hcomm := Lsq_zero_sqMode_comm W a j v
  rw [ha, hv, map_smul, map_smul, LinearMap.smul_apply] at hcomm
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm]
  push_cast
  module

/-- The source-correct square-mode grading datum, quantified over every square-homogeneous first
input and every integer mode. -/
def SqModeWeighted' (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K n : ℤ) (a : 𝒱), a ∈ sqWeightSpace W (K : ℂ) →
    ∀ v : 𝒱, v ∈ sqWeightSpace W (n : ℂ) → ∀ j : ℤ,
      sqMode W j a v ∈ sqWeightSpace W ((K + n - j - 1 : ℤ) : ℂ)

/-- The source-correct square-mode grading datum is unconditional. -/
theorem sqModeWeighted'_holds (W : VertexOperatorAlgebra 𝒱) : SqModeWeighted' W :=
  fun _ _ _ ha _ hv j ↦ sqMode_mem_sqWeightSpace W ha hv j

/-- The two-mode carried datum `SqModeWeighted` follows from the stronger source-correct theorem. -/
theorem sqModeWeighted_holds (W : VertexOperatorAlgebra 𝒱) : SqModeWeighted W := by
  intro ka hka a ha K n haK v hv
  have hmode (j : ℤ) : sqMode W j a = vSqZ W a ka j := by
    simpa only [Int.toNat_natCast] using sqMode_of_mem_grading W ha j
  constructor
  · rw [← hmode (-2)]
    convert sqMode_mem_sqWeightSpace W haK hv (-2) using 1 <;> push_cast <;> ring
  · intro m
    rw [← hmode (2 * (m + 2) - 2 : ℤ)]
    convert sqMode_mem_sqWeightSpace W haK hv (2 * (m + 2) - 2 : ℤ) using 1 <;>
      push_cast <;> ring

end VOA
