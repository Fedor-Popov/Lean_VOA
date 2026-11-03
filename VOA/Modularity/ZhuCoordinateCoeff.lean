/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.SquareBracketWitt

/-!
# Coefficient identities for Zhu's square-bracket modes

The square-bracket coefficient is `c(k,m,m+p) = [wᵖ]((1+w)^{k-1}·uᵐ)` with `u = log(1+w)/w`
(`sqBracketCoeffZ`).  This file proves the four identities behind the square-bracket current
calculus (`ZhuCoordinateCurrent`):

* `antidiag_coeff_one` — `Σ_{p+r=t} c(1,m,m+p)·c(1,n,n+r) = c(1,m+n,m+n+t)`
  (the product `uᵐ·uⁿ = u^{m+n}`);
* `antidiag_central` — `Σ_{p+r=t} (m+p)·c(1,m,m+p)·c(1,n,n+r) = m·δ_{t,0}` when `m+n+t = 0`
  (the residue of `d(log^m)·logⁿ`);
* `antidiag_virasoro` — `Σ_{p+r=t} c(2,m+1,m+1+p)·(n+r)·c(1,n,n+r) = n·c(1,m+n,m+n+t)`
  (the residue `Res f_m·g_n'` with `f_m = (1+w)logᵐ⁺¹`, `g_n = logⁿ`);
* `deriv_coeff` — `(n+s)·c(p+2,n,n+s) = n·c(p+1,n-1,n-1+s) + (p+1)·[s ≥ 1]·c(p+1,n,n+s-1)`
  (the translation rule `(L₋₁a)[n] = -n a[n-1] - wt(a) a[n]`).

Each is the coefficient extraction of a one-line power-series identity that collapses to the ODE
`(1+w)(u + w u') = 1` (`uSeries_ODE`).  Also the explicit low coefficients
`c(1,-1,0) = 1/2`, `c(1,-1,1) = -1/12`, `c(1,-2,-1) = 1`.
-/

namespace VOA.ZhuCoordinate

open PowerSeries VOA

noncomputable section

/-- `uᵐ` as a power series, for `m : ℤ`. -/
abbrev U (m : ℤ) : PowerSeries ℂ := ↑(uUnit ^ m)

/-- `(1+w)^{k-1}` as a power series (unit `zpow`). -/
abbrev O (k : ℕ) : PowerSeries ℂ := ↑(onePlusXUnit ^ ((k : ℤ) - 1))

/-- `(1+w)⁻¹` as a power series. -/
abbrev Oinv : PowerSeries ℂ := ↑(onePlusXUnit ^ (-1 : ℤ))

theorem U_mul (m n : ℤ) : U m * U n = U (m + n) := by
  show (↑(uUnit ^ m) : PowerSeries ℂ) * ↑(uUnit ^ n) = ↑(uUnit ^ (m + n))
  rw [← Units.val_mul, ← zpow_add]

theorem U_succ (m : ℤ) : U (m + 1) = U m * uSeries := by
  rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]

theorem O_one : O 1 = 1 := by
  simp [O]

theorem O_two : O 2 = 1 + PowerSeries.X := by
  rw [O, show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num, zpow_one, onePlusXUnit_coe]

theorem O_succ_succ (p : ℕ) : O (p + 2) = (1 + PowerSeries.X) ^ (p + 1) := by
  rw [O, onePlusXUnit_zpow_of_one_le (by omega)]
  rfl

theorem O_succ (p : ℕ) : O (p + 1) = (1 + PowerSeries.X) ^ p := by
  rw [O, onePlusXUnit_zpow_of_one_le (by omega)]
  rfl

/-- `c(k, m, m+p) = [wᵖ]((1+w)^{k-1} uᵐ)`. -/
theorem coeffZ_add (k : ℕ) (m : ℤ) (p : ℕ) :
    sqBracketCoeffZ k m (m + p) = PowerSeries.coeff (R := ℂ) p (O k * U m) := by
  rw [sqBracketCoeffZ, if_pos (by omega), show (m + (p : ℤ) - m).toNat = p by omega]

theorem coeffZ_one_add (m : ℤ) (p : ℕ) :
    sqBracketCoeffZ 1 m (m + p) = PowerSeries.coeff (R := ℂ) p (U m) := by
  rw [coeffZ_add, O_one, one_mul]

/-- The Euler operator `n + w d/dw` on coefficients. -/
theorem coeff_euler (B : PowerSeries ℂ) (n : ℂ) (r : ℕ) :
    PowerSeries.coeff (R := ℂ) r (PowerSeries.C n * B + PowerSeries.X * derivativeFun B)
      = (n + r) * PowerSeries.coeff (R := ℂ) r B := by
  rw [map_add, PowerSeries.coeff_C_mul, coeff_X_mul_derivativeFun]
  ring

/-- `uᵐ` under the Euler operator: `m uᵐ + w (uᵐ)' = m u^{m-1}·(1+w)⁻¹`. -/
theorem euler_U (m : ℤ) :
    PowerSeries.C (m : ℂ) * U m + PowerSeries.X * derivativeFun (U m)
      = PowerSeries.C (m : ℂ) * U (m - 1) * Oinv := by
  rw [Oinv, derivativeFun_uUnit_zpow m, onePlusXUnit_inv_eq]
  have hU : U m = U (m - 1) * uSeries := by
    rw [← U_succ]; congr 1; ring
  rw [hU]
  have : ((m : PowerSeries ℂ)) = PowerSeries.C (m : ℂ) := by
    rw [← map_intCast (PowerSeries.C (R := ℂ))]
  rw [this]
  ring

theorem onePlusX_mul_inv :
    (1 + PowerSeries.X) * Oinv = 1 := by
  rw [← onePlusXUnit_coe, ← Units.val_mul, zpow_neg_one, mul_inv_cancel, Units.val_one]

/-! ## The four antidiagonal identities -/

/-- **Product**: `Σ_{p+r=t} c(1,m,m+p) c(1,n,n+r) = c(1,m+n,m+n+t)`. -/
theorem antidiag_coeff_one (m n : ℤ) (t : ℕ) :
    ∑ x ∈ Finset.antidiagonal t,
        sqBracketCoeffZ 1 m (m + x.1) * sqBracketCoeffZ 1 n (n + x.2)
      = sqBracketCoeffZ 1 (m + n) (m + n + t) := by
  simp only [coeffZ_one_add]
  rw [← PowerSeries.coeff_mul, U_mul]

/-- **Central term**: if `m + n + t = 0` then `Σ_{p+r=t} (m+p) c(1,m,m+p) c(1,n,n+r) = m δ_{t,0}`. -/
theorem antidiag_central (m n : ℤ) (t : ℕ) (hmn : m + n + t = 0) :
    ∑ x ∈ Finset.antidiagonal t,
        ((m : ℂ) + x.1) * sqBracketCoeffZ 1 m (m + x.1) * sqBracketCoeffZ 1 n (n + x.2)
      = if t = 0 then (m : ℂ) else 0 := by
  simp only [coeffZ_one_add]
  have h1 : ∀ x ∈ Finset.antidiagonal t,
      ((m : ℂ) + x.1) * PowerSeries.coeff (R := ℂ) x.1 (U m) * PowerSeries.coeff (R := ℂ) x.2 (U n)
        = PowerSeries.coeff (R := ℂ) x.1
            (PowerSeries.C (m : ℂ) * U m + PowerSeries.X * derivativeFun (U m))
          * PowerSeries.coeff (R := ℂ) x.2 (U n) := by
    intro x _
    rw [coeff_euler]
  rw [Finset.sum_congr rfl h1, ← PowerSeries.coeff_mul, euler_U]
  have h2 : PowerSeries.C (m : ℂ) * U (m - 1) * Oinv * U n
      = PowerSeries.C (m : ℂ) * (O 0 * U (-(t : ℤ) - 1)) := by
    have : U (m - 1) * U n = U (-(t : ℤ) - 1) := by
      rw [U_mul]; congr 1; omega
    rw [O, show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, ← this]
    ring
  rw [h2, PowerSeries.coeff_C_mul]
  have h3 : PowerSeries.coeff (R := ℂ) t (O 0 * U (-(t : ℤ) - 1))
      = sqBracketCoeffZ 0 (-(t : ℤ) - 1) (-1) := by
    rw [sqBracketCoeffZ, if_pos (by omega), show ((-1 : ℤ) - (-(t : ℤ) - 1)).toNat = t by omega]
  rw [h3]
  split_ifs with ht
  · subst ht
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num, sqBracketCoeffZ_vacuum_neg_one, mul_one]
  · rw [sqBracketCoeffZ_vacuum_of_ne _ (by omega), mul_zero]

/-- **Virasoro–current**: `Σ_{p+r=t} c(2,m+1,m+1+p)·(n+r)·c(1,n,n+r) = n·c(1,m+n,m+n+t)`. -/
theorem antidiag_virasoro (m n : ℤ) (t : ℕ) :
    ∑ x ∈ Finset.antidiagonal t,
        sqBracketCoeffZ 2 (m + 1) (m + 1 + x.1) * (((n : ℂ) + x.2) * sqBracketCoeffZ 1 n (n + x.2))
      = (n : ℂ) * sqBracketCoeffZ 1 (m + n) (m + n + t) := by
  simp only [coeffZ_add, O_one, one_mul]
  have h1 : ∀ x ∈ Finset.antidiagonal t,
      PowerSeries.coeff (R := ℂ) x.1 (O 2 * U (m + 1))
          * (((n : ℂ) + x.2) * PowerSeries.coeff (R := ℂ) x.2 (U n))
        = PowerSeries.coeff (R := ℂ) x.1 (O 2 * U (m + 1))
          * PowerSeries.coeff (R := ℂ) x.2
            (PowerSeries.C (n : ℂ) * U n + PowerSeries.X * derivativeFun (U n)) := by
    intro x _
    rw [coeff_euler]
  rw [Finset.sum_congr rfl h1, ← PowerSeries.coeff_mul, euler_U, O_two]
  have h2 : (1 + PowerSeries.X) * U (m + 1)
        * (PowerSeries.C (n : ℂ) * U (n - 1) * Oinv)
      = PowerSeries.C (n : ℂ) * U (m + n) := by
    have hu : U (m + 1) * U (n - 1) = U (m + n) := by rw [U_mul]; congr 1; ring
    calc (1 + PowerSeries.X) * U (m + 1)
          * (PowerSeries.C (n : ℂ) * U (n - 1) * Oinv)
        = PowerSeries.C (n : ℂ) * (U (m + 1) * U (n - 1))
          * ((1 + PowerSeries.X) * Oinv) := by ring
      _ = _ := by rw [hu, onePlusX_mul_inv, mul_one]
  rw [h2, PowerSeries.coeff_C_mul]

/-- **Translation rule** as a power-series identity: with `F = (1+w)^{p+1} uⁿ`,
`n F + w F' = n (1+w)ᵖ u^{n-1} + (p+1) w (1+w)ᵖ uⁿ`. -/
theorem euler_deriv (p : ℕ) (n : ℤ) :
    PowerSeries.C (n : ℂ) * (O (p + 2) * U n) + PowerSeries.X * derivativeFun (O (p + 2) * U n)
      = PowerSeries.C (n : ℂ) * (O (p + 1) * U (n - 1))
        + PowerSeries.C ((p : ℂ) + 1) * (PowerSeries.X * (O (p + 1) * U n)) := by
  rw [O_succ_succ, O_succ, PowerSeries.derivativeFun_mul]
  have hd : derivativeFun ((1 + PowerSeries.X : PowerSeries ℂ) ^ (p + 1))
      = PowerSeries.C ((p : ℂ) + 1) * (1 + PowerSeries.X) ^ p := by
    have h := PowerSeries.derivative_pow ℂ (1 + PowerSeries.X : PowerSeries ℂ) (p + 1)
    change derivativeFun _ = _ at h
    rw [h, Nat.add_sub_cancel, map_add, Derivation.map_one_eq_zero, zero_add,
      PowerSeries.derivative_X, mul_one, map_add, map_one, map_natCast]
    push_cast
    ring
  rw [hd, derivativeFun_uUnit_zpow n, smul_eq_mul, smul_eq_mul]
  have hU : U n = U (n - 1) * uSeries := by
    rw [← U_succ]; congr 1; ring
  have hODE := uSeries_ODE
  have hcast : ((n : PowerSeries ℂ)) = PowerSeries.C (n : ℂ) := by
    rw [← map_intCast (PowerSeries.C (R := ℂ))]
  rw [hcast]
  change _ = PowerSeries.C (n : ℂ) * ((1 + PowerSeries.X) ^ p * U (n - 1))
      + PowerSeries.C ((p : ℂ) + 1) * (PowerSeries.X * ((1 + PowerSeries.X) ^ p * U n))
  rw [hU]
  rw [pow_succ]
  linear_combination
    PowerSeries.C (n : ℂ) * (1 + PowerSeries.X) ^ p * U (n - 1) * hODE

/-- **Translation rule on coefficients**:
`(n+s) c(p+2,n,n+s) = n c(p+1,n-1,n-1+s) + (p+1)·[s≥1] c(p+1,n,n+(s-1))`. -/
theorem deriv_coeff (p : ℕ) (n : ℤ) (s : ℕ) :
    ((n : ℂ) + s) * sqBracketCoeffZ (p + 2) n (n + s)
      = (n : ℂ) * sqBracketCoeffZ (p + 1) (n - 1) (n - 1 + s)
        + (if s = 0 then 0 else ((p : ℂ) + 1) * sqBracketCoeffZ (p + 1) n (n + (s - 1 : ℕ))) := by
  rw [coeffZ_add, coeffZ_add]
  have h := congrArg (PowerSeries.coeff (R := ℂ) s) (euler_deriv p n)
  rw [coeff_euler] at h
  rw [h, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  congr 1
  rcases s with _ | s
  · simp [PowerSeries.coeff_zero_X_mul]
  · rw [PowerSeries.coeff_succ_X_mul, if_neg (Nat.succ_ne_zero s), coeffZ_add,
      show s + 1 - 1 = s by omega]

/-! ## Explicit low coefficients -/

theorem coeff_uSeries_zero : PowerSeries.coeff (R := ℂ) 0 uSeries = 1 := by
  rw [uSeries, PowerSeries.coeff_mk]; norm_num

theorem coeff_uSeries_one : PowerSeries.coeff (R := ℂ) 1 uSeries = -1 / 2 := by
  rw [uSeries, PowerSeries.coeff_mk]; norm_num

theorem coeff_uSeries_two : PowerSeries.coeff (R := ℂ) 2 uSeries = 1 / 3 := by
  rw [uSeries, PowerSeries.coeff_mk]; norm_num

/-- The first three coefficients of `u⁻¹`: `1, 1/2, -1/12`. -/
theorem coeff_U_neg_one :
    PowerSeries.coeff (R := ℂ) 0 (U (-1)) = 1 ∧ PowerSeries.coeff (R := ℂ) 1 (U (-1)) = 1 / 2 ∧
      PowerSeries.coeff (R := ℂ) 2 (U (-1)) = -1 / 12 := by
  have hinv : uSeries * U (-1) = 1 := by
    show uSeries * (↑(uUnit ^ (-1 : ℤ)) : PowerSeries ℂ) = 1
    rw [← uUnit_coe, ← Units.val_mul, zpow_neg_one, mul_inv_cancel, Units.val_one]
  have h0 := congrArg (PowerSeries.coeff (R := ℂ) 0) hinv
  have h1 := congrArg (PowerSeries.coeff (R := ℂ) 1) hinv
  have h2 := congrArg (PowerSeries.coeff (R := ℂ) (1 + 1)) hinv
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at h0
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at h1
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at h2
  simp only [coeff_uSeries_zero, coeff_uSeries_one, PowerSeries.coeff_one,
    zero_add] at h0 h1 h2
  rw [show (1 + 1 : ℕ) = 2 from rfl, coeff_uSeries_two] at h2
  norm_num at h0 h1 h2
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · linear_combination h1 + (1 / 2 : ℂ) * h0
  · linear_combination h2 + (1 / 2 : ℂ) * h1 - (1 / 12 : ℂ) * h0

/-- The first two coefficients of `u⁻²`: `1, 1`. -/
theorem coeff_U_neg_two_one : PowerSeries.coeff (R := ℂ) 1 (U (-2)) = 1 := by
  have h : U (-2) = U (-1) * U (-1) := by rw [U_mul]; norm_num
  obtain ⟨h0, h1, -⟩ := coeff_U_neg_one
  rw [h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp only [zero_add]
  rw [h0, h1]
  norm_num

/-- `c(1,-1,0) = 1/2`. -/
theorem c_one_neg_one_zero : sqBracketCoeffZ 1 (-1) 0 = 1 / 2 := by
  have h := coeffZ_one_add (-1) 1
  rw [show (-1 : ℤ) + ((1 : ℕ) : ℤ) = 0 by norm_num] at h
  rw [h]
  exact coeff_U_neg_one.2.1

/-- `c(1,-1,1) = -1/12`. -/
theorem c_one_neg_one_one : sqBracketCoeffZ 1 (-1) 1 = -1 / 12 := by
  have h := coeffZ_one_add (-1) 2
  rw [show (-1 : ℤ) + ((2 : ℕ) : ℤ) = 1 by norm_num] at h
  rw [h]
  exact coeff_U_neg_one.2.2

/-- `c(1,-2,-1) = 1`. -/
theorem c_one_neg_two_neg_one : sqBracketCoeffZ 1 (-2) (-1) = 1 := by
  have h := coeffZ_one_add (-2) 1
  rw [show (-2 : ℤ) + ((1 : ℕ) : ℤ) = -1 by norm_num] at h
  rw [h]
  exact coeff_U_neg_two_one

end

end VOA.ZhuCoordinate

section AxiomAudit
#print axioms VOA.ZhuCoordinate.antidiag_coeff_one
#print axioms VOA.ZhuCoordinate.antidiag_central
#print axioms VOA.ZhuCoordinate.antidiag_virasoro
#print axioms VOA.ZhuCoordinate.deriv_coeff
#print axioms VOA.ZhuCoordinate.c_one_neg_one_one
end AxiomAudit
