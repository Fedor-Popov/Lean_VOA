/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SquareBracketVirasoro

/-!
# The Gel'fand–Fuks cocycle of the square-bracket modes  (`CentralMomentClosed`)

This file closes the last open item of GOAL B: the closed form of the central moment
`S(m,n) = Σ_a d[m,a]·d[n,−a]·(a³−a)`, namely
`S(m,n) = (m³−m)·δ_{m+n,0} − ((m−n)/2)·δ_{m+n,−2}`.

## The proof (purely scalar — formal power series only, no Laurent series)

Conceptually this is the classical Witt cocycle transported through `1+w = e^z`; the Schwarzian of
`e^z − 1` is the constant `−1/2`, and a constant Schwarzian contributes exactly a `δ_{m+n,−2}` term
with coefficient `−(m−n)/2`.  Formally we never leave the `w`-coordinate:

With the **Euler operator** `D = w·d/dw` (so `[wᵖ](D F) = p·[wᵖ]F`, `coeff_X_mul_derivativeFun`), the
cubic weight `(m+p)³−(m+p)` applied to `P_m = (1+w)u^{m+1}` is `A_m := (D+m−1)(D+m)(D+m+1) P_m`, and
three ODE computations (`uSeries_ODE`, `derivativeFun_uUnit_zpow`) give the **closed form**

* `(D+m+1) P_m = w·u^{m+1} + (m+1)·u^m`                                  (`eulerStep_one`)
* `(D+m)(…)   = (m+1)·(1+w)^{−1}·(w·u^m + m·u^{m−1})`                    (`eulerStep_two`)
* `(D+m−1)(…) = (m+1)·(1+w)^{−2}·(m(m−1)·u^{m−2} − w²·u^m) =: A_m`       (`eulerStep_three`)

(the `w`-coordinate image of `f_m‴` for `f_m = (1+w)(log(1+w))^{m+1} = w^{m+1}P_m`).  Multiplying by
`P_n` collapses the `(1+w)^{−2}` against `P_n`'s `(1+w)`:

* `A_m·P_n = (m+1)·(1+w)^{−1}·(m(m−1)·u^{m+n−1} − w²·u^{m+n+1})`         (`Am_mul_Pw`)

whose `[wᴶ]`-coefficient (`J = −m−n`) is `(m+1)·(m(m−1)·s(m+n−1) − s(m+n+1))` — because
`s(k) = [w^{−1−k}]((1+w)^{−1}u^k)` is *exactly* `sqBracketCoeffZ 0 k (-1)`, whose value `δ_{k,−1}` is
already proved (`sqBracketCoeffZ_vacuum_of_ne`, `sqBracketCoeffZ_vacuum_neg_one`).  Since
`−1−(m+n−1) = J` and `−1−(m+n+1) = J−2`, the two windows `m+n = 0` and `m+n = −2` are exactly the two
surviving cases, giving `(m³−m)δ_{m+n,0} − (m+1)δ_{m+n,−2}` (and `(m−n)/2 = m+1` when `m+n = −2`).

## Status
`pbw`-free, axiom-clean.  Engine-confirmed (exact rationals) at every step.

## References
* Gannon §5.3.5 (5.3.15); Zhu, J. AMS 9 (1996) §4; the Gel'fand–Fuks cocycle.
-/

namespace VOA

open PowerSeries
open scoped BigOperators

/-! ## Scalar helpers -/

/-- Coefficients of an integer-constant multiple. -/
theorem coeff_intCast_mul (c : ℤ) (g : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff (R := ℂ) k ((c : PowerSeries ℂ) * g)
      = (c : ℂ) * PowerSeries.coeff (R := ℂ) k g := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

/-- `[wᵖ]((D + c)F) = (p + c)·[wᵖ]F`, where `(D+c)F = w·F′ + c·F`. -/
theorem coeff_eulerStep (c : ℤ) (F : PowerSeries ℂ) (p : ℕ) :
    PowerSeries.coeff (R := ℂ) p (PowerSeries.X * derivativeFun F + (c : PowerSeries ℂ) * F)
      = ((p : ℂ) + (c : ℂ)) * PowerSeries.coeff (R := ℂ) p F := by
  rw [map_add, coeff_X_mul_derivativeFun, coeff_intCast_mul]
  ring

theorem derivativeFun_onePlusX : derivativeFun (1 + PowerSeries.X : PowerSeries ℂ) = 1 := by
  rw [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_one, zero_add, derivativeFun_X]

/-- Product of integer powers of the unit `1+w`. -/
theorem onePlusXUnit_val_zpow_mul (a b : ℤ) :
    (↑(onePlusXUnit ^ a) : PowerSeries ℂ) * ↑(onePlusXUnit ^ b) = ↑(onePlusXUnit ^ (a + b)) := by
  rw [zpow_add, Units.val_mul]

/-- `(1+w)^{−1}·(1+w) = 1`. -/
theorem onePlusXUnit_inv_mul : (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
    * (1 + PowerSeries.X) = 1 := by
  rw [← onePlusXUnit_coe, ← Units.val_mul, zpow_neg_one, inv_mul_cancel, Units.val_one]

/-- `d((1+w)^{−1}) = −(1+w)^{−2}`. -/
theorem derivativeFun_onePlusXUnit_inv :
    derivativeFun (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
      = -(↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ) := by
  have hV := onePlusXUnit_inv_mul
  have hd := congrArg derivativeFun hV
  rw [PowerSeries.derivativeFun_mul, derivativeFun_onePlusX, PowerSeries.derivativeFun_one] at hd
  simp only [smul_eq_mul, mul_one] at hd
  have hsq : (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * ↑(onePlusXUnit ^ (-1 : ℤ))
      = ↑(onePlusXUnit ^ (-2 : ℤ)) := by
    rw [onePlusXUnit_val_zpow_mul]; norm_num
  calc derivativeFun (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
      = ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * (1 + PowerSeries.X))
          * derivativeFun (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) := by rw [hV, one_mul]
    _ = -((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * ↑(onePlusXUnit ^ (-1 : ℤ))) := by
        linear_combination (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * hd
    _ = -(↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ) := by rw [hsq]

/-- `w·u′ = (1+w)^{−1} − u` — the ODE in "solved" form. -/
theorem X_mul_derivativeFun_uSeries :
    PowerSeries.X * derivativeFun uSeries
      = (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) - uSeries := by
  rw [onePlusXUnit_inv_eq]; ring

/-! ## The three Euler-operator steps -/

/-- **Step 1:** `(D + (m+1)) P_m = w·u^{m+1} + (m+1)·u^m`. -/
theorem eulerStep_one (m : ℤ) :
    PowerSeries.X * derivativeFun (Pw m) + (((m + 1 : ℤ)) : PowerSeries ℂ) * Pw m
      = PowerSeries.X * (↑(uUnit ^ (m + 1)) : PowerSeries ℂ)
        + (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ) := by
  have hA : (↑(uUnit ^ m) : PowerSeries ℂ) * uSeries = (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
  have hODE := uSeries_ODE
  rw [derivativeFun_Pw m]
  simp only [Pw]
  rw [← hA]
  linear_combination (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ) * hODE

theorem derivativeFun_intCast (c : ℤ) : derivativeFun ((c : PowerSeries ℂ)) = 0 := by
  rw [show ((c : ℤ) : PowerSeries ℂ) = PowerSeries.C ((c : ℤ) : ℂ) from
    (map_intCast (PowerSeries.C (R := ℂ)) c).symm, PowerSeries.derivativeFun_C]

theorem derivativeFun_intCast_mul (c : ℤ) (F : PowerSeries ℂ) :
    derivativeFun ((c : PowerSeries ℂ) * F) = (c : PowerSeries ℂ) * derivativeFun F := by
  rw [PowerSeries.derivativeFun_mul, derivativeFun_intCast]
  simp only [smul_eq_mul, mul_zero, add_zero]

/-- **Step 2:** `(D + m)(w·u^{m+1} + (m+1)u^m) = (m+1)·(1+w)^{−1}·(w·u^m + m·u^{m−1})`. -/
theorem eulerStep_two (m : ℤ) :
    PowerSeries.X * derivativeFun (PowerSeries.X * (↑(uUnit ^ (m + 1)) : PowerSeries ℂ)
        + (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ))
      + ((m : ℤ) : PowerSeries ℂ) * (PowerSeries.X * (↑(uUnit ^ (m + 1)) : PowerSeries ℂ)
        + (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ))
      = (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (PowerSeries.X * (↑(uUnit ^ m) : PowerSeries ℂ)
           + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)) := by
  have hA : (↑(uUnit ^ m) : PowerSeries ℂ) * uSeries = (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
  have hC : (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * uSeries = (↑(uUnit ^ m) : PowerSeries ℂ) := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one, show m - 1 + 1 = m from by ring]
  have hXu := X_mul_derivativeFun_uSeries
  rw [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_mul PowerSeries.X
      (↑(uUnit ^ (m + 1)) : PowerSeries ℂ), derivativeFun_X, derivativeFun_intCast_mul,
    derivativeFun_uUnit_zpow (m + 1), derivativeFun_uUnit_zpow m,
    show (m + 1 - 1) = m from by ring]
  simp only [smul_eq_mul, mul_one]
  push_cast
  linear_combination ((((m : ℤ) : PowerSeries ℂ) + 1) * ((↑(uUnit ^ m) : PowerSeries ℂ)
      * PowerSeries.X + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ))) * hXu
    + (-(((m : ℤ) : PowerSeries ℂ) + 1) * PowerSeries.X) * hA
    + (-(((m : ℤ) : PowerSeries ℂ) + 1) * ((m : ℤ) : PowerSeries ℂ)) * hC

theorem onePlusXUnit_inv_sq : (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
    * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
    = (↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ) := by
  rw [onePlusXUnit_val_zpow_mul]; norm_num

/-- **Step 3 (reduced, constant factored out):**
`(D + (m−1))[(1+w)^{−1}(w·u^m + m·u^{m−1})] = (1+w)^{−2}(m(m−1)u^{m−2} − w²u^m)`. -/
theorem eulerStep_three' (m : ℤ) :
    PowerSeries.X * derivativeFun ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (PowerSeries.X * (↑(uUnit ^ m) : PowerSeries ℂ)
           + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)))
      + (((m - 1 : ℤ)) : PowerSeries ℂ) * ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (PowerSeries.X * (↑(uUnit ^ m) : PowerSeries ℂ)
           + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)))
      = (↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ)
        * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
             * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ)
           - PowerSeries.X ^ 2 * (↑(uUnit ^ m) : PowerSeries ℂ)) := by
  have hC : (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * uSeries = (↑(uUnit ^ m) : PowerSeries ℂ) := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one, show m - 1 + 1 = m from by ring]
  have hD2 : (↑(uUnit ^ (m - 2)) : PowerSeries ℂ) * uSeries
      = (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one, show m - 2 + 1 = m - 1 from by ring]
  have hXu := X_mul_derivativeFun_uSeries
  have hVsq := onePlusXUnit_inv_sq
  rw [PowerSeries.derivativeFun_mul (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ),
    derivativeFun_onePlusXUnit_inv, PowerSeries.derivativeFun_add,
    PowerSeries.derivativeFun_mul PowerSeries.X (↑(uUnit ^ m) : PowerSeries ℂ), derivativeFun_X,
    derivativeFun_intCast_mul, derivativeFun_uUnit_zpow m, derivativeFun_uUnit_zpow (m - 1),
    show m - 1 - 1 = m - 2 from by ring]
  simp only [smul_eq_mul, mul_one]
  push_cast
  linear_combination
    ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
      * (((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * PowerSeries.X
        + ((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
          * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ))) * hXu
    + (-(↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * ((m : ℤ) : PowerSeries ℂ)
        * PowerSeries.X) * hC
    + (-(↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * ((m : ℤ) : PowerSeries ℂ)
        * (((m : ℤ) : PowerSeries ℂ) - 1)) * hD2
    + (((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * PowerSeries.X
        + ((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
          * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ)) * hVsq

/-- **Step 3:** the same with the constant `(m+1)` carried through. -/
theorem eulerStep_three (m : ℤ) :
    PowerSeries.X * derivativeFun ((((m + 1 : ℤ)) : PowerSeries ℂ)
        * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (PowerSeries.X * (↑(uUnit ^ m) : PowerSeries ℂ)
           + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)))
      + (((m - 1 : ℤ)) : PowerSeries ℂ) * ((((m + 1 : ℤ)) : PowerSeries ℂ)
        * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (PowerSeries.X * (↑(uUnit ^ m) : PowerSeries ℂ)
           + ((m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)))
      = (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ)
        * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
             * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ)
           - PowerSeries.X ^ 2 * (↑(uUnit ^ m) : PowerSeries ℂ)) := by
  have h' := eulerStep_three' m
  rw [mul_assoc (((m + 1 : ℤ)) : PowerSeries ℂ), derivativeFun_intCast_mul]
  linear_combination (((m + 1 : ℤ)) : PowerSeries ℂ) * h'

/-! ## `A_m` and its coefficient property -/

/-- **`A_m = (D+m−1)(D+m)(D+m+1) P_m`** in closed form: `(m+1)(1+w)^{−2}(m(m−1)u^{m−2} − w²u^m)`
— the `w`-coordinate image of `f_m‴`. -/
noncomputable def Am (m : ℤ) : PowerSeries ℂ :=
  (((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ)
    * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
         * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ)
       - PowerSeries.X ^ 2 * (↑(uUnit ^ m) : PowerSeries ℂ))

/-- **The cubic weight:** `[wᵖ]A_m = ((m+p)³ − (m+p))·[wᵖ]P_m` — three applications of
`coeff_eulerStep` along the three Euler steps. -/
theorem coeff_Am (m : ℤ) (p : ℕ) :
    PowerSeries.coeff (R := ℂ) p (Am m)
      = (((p : ℂ) + (m : ℂ)) ^ 3 - ((p : ℂ) + (m : ℂ)))
        * PowerSeries.coeff (R := ℂ) p (Pw m) := by
  have h1 := congrArg (PowerSeries.coeff (R := ℂ) p) (eulerStep_one m)
  have h2 := congrArg (PowerSeries.coeff (R := ℂ) p) (eulerStep_two m)
  have h3 := congrArg (PowerSeries.coeff (R := ℂ) p) (eulerStep_three m)
  rw [coeff_eulerStep] at h1 h2 h3
  simp only [Am]
  rw [← h3, ← h2, ← h1]
  push_cast
  ring

/-! ## The product `A_m · P_n` and the endgame -/

/-- `A_m·P_n = (m+1)(1+w)^{−1}(m(m−1)u^{m+n−1} − w²u^{m+n+1})` — the `(1+w)^{−2}` collapses
against `P_n`'s `(1+w)`. -/
theorem Am_mul_Pw (m n : ℤ) :
    Am m * Pw n = (((m + 1 : ℤ)) : PowerSeries ℂ)
      * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
      * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
           * (↑(uUnit ^ (m + n - 1)) : PowerSeries ℂ)
         - PowerSeries.X ^ 2 * (↑(uUnit ^ (m + n + 1)) : PowerSeries ℂ)) := by
  have h1 : (↑(onePlusXUnit ^ (-2 : ℤ)) : PowerSeries ℂ) * (1 + PowerSeries.X)
      = (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) := by
    rw [← onePlusXUnit_coe, ← Units.val_mul, ← zpow_add_one]
    norm_num
  have h2 : (↑(uUnit ^ (m - 2)) : PowerSeries ℂ) * (↑(uUnit ^ (n + 1)) : PowerSeries ℂ)
      = (↑(uUnit ^ (m + n - 1)) : PowerSeries ℂ) := by
    rw [uUnit_val_zpow_mul, show m - 2 + (n + 1) = m + n - 1 from by ring]
  have h3 : (↑(uUnit ^ m) : PowerSeries ℂ) * (↑(uUnit ^ (n + 1)) : PowerSeries ℂ)
      = (↑(uUnit ^ (m + n + 1)) : PowerSeries ℂ) := by
    rw [uUnit_val_zpow_mul, show m + (n + 1) = m + n + 1 from by ring]
  simp only [Am, Pw]
  linear_combination
    ((((m + 1 : ℤ)) : PowerSeries ℂ)
      * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1)
          * (↑(uUnit ^ (m - 2)) : PowerSeries ℂ) * (↑(uUnit ^ (n + 1)) : PowerSeries ℂ)
        - PowerSeries.X ^ 2 * (↑(uUnit ^ m) : PowerSeries ℂ)
          * (↑(uUnit ^ (n + 1)) : PowerSeries ℂ))) * h1
    + ((((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * (((m : ℤ) : PowerSeries ℂ) * (((m : ℤ) : PowerSeries ℂ) - 1))) * h2
    + (-(((m + 1 : ℤ)) : PowerSeries ℂ) * (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
        * PowerSeries.X ^ 2) * h3

/-- `[wᴶ]((1+w)^{−1}u^k) = s(k)` when `J = −1−k`. -/
theorem coeff_vacuumScalar (k : ℤ) (J : ℕ) (hJ : (J : ℤ) = -1 - k) :
    PowerSeries.coeff (R := ℂ) J
        ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ k) : PowerSeries ℂ))
      = sqBracketCoeffZ 0 k (-1) := by
  rw [sqBracketCoeffZ, if_pos (by omega), show (((0 : ℕ) : ℤ) - 1) = (-1 : ℤ) from by norm_num,
    show ((-1 : ℤ) - k).toNat = J from by omega]

/-- `[wᴶ](w²·(1+w)^{−1}u^k) = s(k)` when `J = 1−k` (both sides vanish for `J < 2`). -/
theorem coeff_X2_vacuumScalar (k : ℤ) (J : ℕ) (hJ : (J : ℤ) = 1 - k) :
    PowerSeries.coeff (R := ℂ) J
        (PowerSeries.X ^ 2 * ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
          * (↑(uUnit ^ k) : PowerSeries ℂ)))
      = sqBracketCoeffZ 0 k (-1) := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : 2 ≤ J
  · rw [if_pos h, sqBracketCoeffZ, if_pos (by omega),
      show (((0 : ℕ) : ℤ) - 1) = (-1 : ℤ) from by norm_num,
      show ((-1 : ℤ) - k).toNat = J - 2 from by omega]
  · rw [if_neg h, sqBracketCoeffZ, if_neg (by omega)]

/-! ## The antidiagonal identification and the closed form -/

/-- **`S(m,n) = [wᴶ](A_m·P_n)`** for `J = −m−n ≥ 0` — the `∑ᶠ a : ℤ → Finset.antidiagonal J`
reindex `a ↦ (a−m, −a−n)` (the same template as `sqBracketCoeff_witt_identity`). -/
theorem centralMoment_eq_coeff (m n : ℤ) (J : ℕ) (hJ : (J : ℤ) = -m - n) :
    centralMoment m n = PowerSeries.coeff (R := ℂ) J (Am m * Pw n) := by
  rw [PowerSeries.coeff_mul, centralMoment]
  have hsupp : (Function.support fun a : ℤ => sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) ((-a) + 1) * (((a ^ 3 - a : ℤ)) : ℂ))
      ⊆ ↑(Finset.Icc m (-n)) := by
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    push_neg at hc
    by_cases h1 : m ≤ a
    · exact ha (by
        rw [sqBracketCoeffZ_of_lt 2 (show (-a) + 1 < n + 1 by omega), mul_zero, zero_mul])
    · exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul])
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_nbij' (fun a => ((a - m).toNat, (-a - n).toNat))
    (fun p => m + (p.1 : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    rw [Finset.mem_antidiagonal]; dsimp only; omega
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    dsimp only; omega
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨p1, p2⟩ := p
    dsimp only
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    dsimp only
    rw [sqBracketCoeffZ_two_eq_coeff_Pw m a, if_pos (by omega),
      sqBracketCoeffZ_two_eq_coeff_Pw n (-a), if_pos (by omega), coeff_Am]
    have e1c : ((((a - m).toNat : ℕ) : ℂ) + ((m : ℤ) : ℂ)) = ((a : ℤ) : ℂ) := by
      rw [show ((((a - m).toNat : ℕ)) : ℂ) = (((((a - m).toNat : ℕ)) : ℤ) : ℂ) from by push_cast; ring,
        show ((((a - m).toNat : ℕ)) : ℤ) = a - m from Int.toNat_of_nonneg (by omega)]
      push_cast; ring
    rw [e1c]
    push_cast
    ring

/-- **The Gel'fand–Fuks closed form** — `CentralMomentClosed` is a theorem:
`S(m,n) = (m³−m)·δ_{m+n,0} − ((m−n)/2)·δ_{m+n,−2}`.

Proof: `S(m,n) = [wᴶ](A_m·P_n) = (m+1)·(m(m−1)·s(m+n−1) − s(m+n+1))` with `J = −m−n`, and
`s(k) = δ_{k,−1}` — so only `m+n = 0` (giving `(m+1)m(m−1) = m³−m`) and `m+n = −2` (giving `−(m+1) =
−(m−n)/2`) survive.  Engine-confirmed at every step. -/
theorem centralMomentClosed_holds : CentralMomentClosed := by
  intro m n
  by_cases h : 0 ≤ -m - n
  · obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = -m - n := ⟨(-m - n).toNat, Int.toNat_of_nonneg h⟩
    have hexp : Am m * Pw n
        = ((((m + 1) * (m * (m - 1)) : ℤ)) : PowerSeries ℂ)
            * ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
              * (↑(uUnit ^ (m + n - 1)) : PowerSeries ℂ))
          - (((m + 1 : ℤ)) : PowerSeries ℂ)
            * (PowerSeries.X ^ 2 * ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
              * (↑(uUnit ^ (m + n + 1)) : PowerSeries ℂ))) := by
      rw [Am_mul_Pw]; push_cast; ring
    rw [centralMoment_eq_coeff m n J hJ, hexp, map_sub, coeff_intCast_mul, coeff_intCast_mul,
      coeff_vacuumScalar (m + n - 1) J (by omega),
      coeff_X2_vacuumScalar (m + n + 1) J (by omega)]
    by_cases h0 : m + n = 0
    · rw [if_pos h0, if_neg (show ¬(m + n = -2) by omega),
        show m + n - 1 = (-1 : ℤ) from by omega, sqBracketCoeffZ_vacuum_neg_one,
        show m + n + 1 = (1 : ℤ) from by omega,
        sqBracketCoeffZ_vacuum_of_ne 1 (by norm_num)]
      push_cast; ring
    · by_cases h2 : m + n = -2
      · rw [if_neg h0, if_pos h2,
          show m + n - 1 = (-3 : ℤ) from by omega,
          sqBracketCoeffZ_vacuum_of_ne (-3) (by norm_num),
          show m + n + 1 = (-1 : ℤ) from by omega, sqBracketCoeffZ_vacuum_neg_one,
          show (n : ℂ) = -2 - (m : ℂ) from by
            rw [show n = -2 - m from by omega]; push_cast; ring]
        push_cast; ring
      · rw [if_neg h0, if_neg h2, sqBracketCoeffZ_vacuum_of_ne (m + n - 1) (by omega),
          sqBracketCoeffZ_vacuum_of_ne (m + n + 1) (by omega)]
        ring
  · push_neg at h
    rw [centralMoment_of_pos m n (by omega), if_neg (by omega), if_neg (by omega)]
    ring

/-! ## The unconditional square-bracket Virasoro relation -/

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The square-bracket Virasoro relation, unconditional** (applied form).
`⁅L[m], L[n]⁆x = (m−n)·L[m+n]x + δ_{m+n,0}·((m³−m)/12)·c·x` — Gannon 5.3.15.  No hypotheses. -/
theorem Lsq_virasoro_apply' (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    Lsq W m (Lsq W n x) - Lsq W n (Lsq W m x)
      = ((m - n : ℤ) : ℂ) • Lsq W (m + n) x
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12 * W.centralCharge) else 0) • x :=
  Lsq_virasoro_apply W centralMomentClosed_holds m n x

/-- **The square-bracket Virasoro relation, unconditional** (operator form, matching
`VertexOperatorAlgebra.L_virasoro`):
`⁅L[m], L[n]⁆ = (m−n)·L[m+n] + δ_{m+n,0}·((m³−m)/12·c)·1`.
The torus (square-bracket) modes satisfy Virasoro with **the same central charge `c`** — Gannon 5.3.15,
Zhu §4.  The `ω̃` vacuum term is what cancels the Schwarzian anomaly at `m+n = −2`. -/
theorem Lsq_virasoro (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) :
    ⁅Lsq W m, Lsq W n⁆
      = ((m : ℂ) - (n : ℂ)) • Lsq W (m + n)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12 * W.centralCharge)
             • (1 : Module.End ℂ 𝒱) else 0) := by
  ext x
  have hl : ⁅Lsq W m, Lsq W n⁆ x = Lsq W m (Lsq W n x) - Lsq W n (Lsq W m x) := by
    rw [Ring.lie_def]; rfl
  rw [hl, Lsq_virasoro_apply' W m n x]
  by_cases h0 : m + n = 0
  · rw [if_pos h0, if_pos h0]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    push_cast
    ring_nf
  · rw [if_neg h0, if_neg h0]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, zero_smul]
    push_cast
    ring_nf

end VOA
