/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointFunctions
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The Witt bracket for the square-bracket modes  (Zhu §4; Gannon 5.3.16)

This file proves the **bracket half** of the torus-Virasoro relations for Zhu's square-bracket
modes `L[n]` — Gannon's `(i)` coefficient identity — via the **power-series product rule**, the
formalization route the physics dictates ("the Witt bracket transported through `w = e^z − 1`").

The square-bracket coefficients `d[m,a] = sqBracketCoeffZ 2 (m+1) (a+1) = [w^{a−m}]((1+w)·u^{m+1})`
(`OnePointFunctions`) are the coefficients of the **Laurent** series `f_m(w) = (1+w)(log(1+w))^{m+1}
= w^{m+1}·P m`, where `P m := (1+w)·u^{m+1}` is a genuine power series (`u = log(1+w)/w` a unit).
The Witt relation `f_m f_n′ − f_m′ f_n = (n−m) f_{m+n}` collapses, after clearing the `w`-powers, to
the single power-series identity (independent of `m,n`)

  `(1 + w)·(u + w·u′) = 1`                                             (`uSeries_ODE`)

— the ODE satisfied by `u = log(1+w)/w`.  Extracting the `w^{j+1}` coefficient of the Witt relation
then gives Gannon's identity `(i)`:  `Σ_a d[m,a] d[n,j−a] (2a−j) = (m−n) d[m+n,j]`.

## Status
Gannon's bracket identity `(i)` is proved, `pbw`-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`:
* Brick 1 — `uSeries_ODE : (1+w)(u + w·u′) = 1` (elementary coefficients, no `log`/`algebraMap` detour);
* Brick 2 — `derivativeFun_uUnit_zpow` (the `zpow` derivative `d(uᵐ) = m·u^{m−1}·u′`, all `m : ℤ`, by
  cases: `derivative_pow` for `m ≥ 0`, the Leibniz trick `d(uᵐ·u^{−m}) = d 1 = 0` for `m < 0`) and
  `Pw_witt` — the **Witt-bracket identity `(★)`** `(m−n)(P_m P_n − P_{m+n}) + w(P_m′ P_n − P_m P_n′) = 0`,
  which collapses to `uSeries_ODE` by `linear_combination`;
* Brick 3 (bridge) — `sqBracketCoeffZ_two_eq_coeff_Pw : d[m,a] = [w^{a−m}] P_m`;
* Brick 4 — `coeff_X_mul_derivativeFun` (the `p·`/`q·` weight bookkeeping), `witt_antidiag` (the antidiagonal
  form of `(i)`, i.e. the `[wᴶ]`-coefficient of `Pw_witt`), and `sqBracketCoeff_witt_identity` —
  **Gannon's `(i)`** `Σ_a d[m,a] d[n,j−a] (2a−j) = (m−n) d[m+n,j]`, via the `∑ᶠ a:ℤ → Finset.antidiagonal J`
  reindex (support `⊆ Icc m (j−n)`, `Finset.sum_nbij'` with `a ↦ (a−m, j−n−a)`; the `j < m+n` case vanishes
  structurally since `d` is lower-triangular).

This is the **bracket half** of the torus-Virasoro relation.  Downstream (`OnePointFunctions`): the
double-finsum commutator `⁅Lsq m, Lsq n⁆ = Σ_{a,b} d[m,a] d[n,b] ⁅L a, L b⁆` (B(iii)) then feeds this
identity + `L_virasoro` into `[Lsq m, Lsq n] = (m−n) Lsq (m+n) + (central)`; the central term is the
deferred Gel'fand–Fuks/Schwarzian cocycle `S(m,n) = (m³−m)δ_{m+n,0} − ((m−n)/2)δ_{m+n,−2}`.

## References
* Gannon §5.3.4–5, eq. (5.3.16); Zhu, J. AMS 9 (1996) §4; Mathlib `RingTheory/PowerSeries/Derivative`.
-/

namespace VOA

open PowerSeries

/-! ## Brick 1 — the ODE `(1+w)(u + w·u′) = 1` for `u = log(1+w)/w`

`u = uSeries = Σ_i (−1)ⁱ/(i+1) wⁱ`.  Its "Euler operator" combination `u + w·u′` has the strikingly
simple coefficients `[wⁱ](u + w·u′) = (−1)ⁱ` (the geometric series `1/(1+w)`), whence
`(1+w)(u + w·u′) = 1`. -/

/-- The geometric series `Σ_i (−1)ⁱ wⁱ = 1/(1+w)`. -/
noncomputable def geomSeries : PowerSeries ℂ := PowerSeries.mk (fun i => (-1 : ℂ) ^ i)

/-- `[wⁱ](u + w·u′) = (−1)ⁱ`: the Euler-operator combination of `u = log(1+w)/w` is the geometric
series.  (For `i ≥ 1`: `(−1)ⁱ/(i+1) + i·(−1)ⁱ/(i+1) = (−1)ⁱ`; for `i = 0`: `1`.) -/
theorem coeff_uSeries_euler (i : ℕ) :
    coeff (R := ℂ) i (uSeries + PowerSeries.X * derivativeFun uSeries) = (-1 : ℂ) ^ i := by
  rw [map_add]
  have huc : coeff (R := ℂ) i uSeries = (-1 : ℂ) ^ i / (i + 1 : ℂ) := by
    rw [uSeries, coeff_mk]
  rcases i with _ | j
  · rw [huc, PowerSeries.coeff_zero_X_mul]
    norm_num
  · rw [huc, PowerSeries.coeff_succ_X_mul, coeff_derivativeFun, uSeries, coeff_mk]
    have hne : ((↑(j + 1) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (j + 1)
    rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
    push_cast
    ring

/-- `u + w·u′ = Σ_i (−1)ⁱ wⁱ = 1/(1+w)` (the Euler-operator combination is the geometric series). -/
theorem uSeries_euler_eq_geom :
    uSeries + PowerSeries.X * derivativeFun uSeries = geomSeries := by
  ext i
  rw [coeff_uSeries_euler, geomSeries, coeff_mk]

/-- `(1+w)·(Σ_i (−1)ⁱ wⁱ) = 1` — the geometric series is the inverse of `1+w`. -/
theorem onePlusX_mul_geom : (1 + PowerSeries.X) * geomSeries = 1 := by
  ext k
  rw [add_mul, one_mul, map_add, geomSeries]
  rcases k with _ | j
  · simp [PowerSeries.coeff_zero_X_mul]
  · rw [coeff_mk, PowerSeries.coeff_succ_X_mul, coeff_mk, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero j), pow_succ]
    ring

/-- **The ODE for `u = log(1+w)/w`:** `(1+w)·(u + w·u′) = 1`.  This single power-series identity
(independent of `m,n`) is what the Witt relation `f_m f_n′ − f_m′ f_n = (n−m) f_{m+n}` — with
`f_m = (1+w)(log(1+w))^{m+1}` — collapses to after clearing the `w`-powers.  It is the analytic
heart of Gannon's bracket identity `(i)`. -/
theorem uSeries_ODE :
    (1 + PowerSeries.X) * (uSeries + PowerSeries.X * derivativeFun uSeries) = 1 := by
  rw [uSeries_euler_eq_geom, onePlusX_mul_geom]

/-! ## Brick 2 — the `zpow` derivative of the unit `u`, and the identity `(★)`

`d(uᵐ) = m·u^{m−1}·u′` for the unit `u = uSeries`, `m : ℤ`.  (Mathlib's `Derivation.leibniz_zpow`
needs a *field*, and `ℂ⟦X⟧` is not one, so we prove it by cases: `derivative_pow` for `m ≥ 0`,
`derivative_inv` for `m < 0`.) -/

/-- Product of two integer unit-powers of `u`. -/
theorem uUnit_val_zpow_mul (a b : ℤ) :
    (↑(uUnit ^ a) : PowerSeries ℂ) * ↑(uUnit ^ b) = ↑(uUnit ^ (a + b)) := by
  rw [zpow_add, Units.val_mul]

/-- Square of an integer unit-power of `u`. -/
theorem uUnit_val_zpow_sq (a : ℤ) :
    (↑(uUnit ^ a) : PowerSeries ℂ) ^ 2 = ↑(uUnit ^ (2 * a)) := by
  rw [sq, uUnit_val_zpow_mul, two_mul]

/-- The `zpow` derivative for a **natural** exponent (clean via `derivative_pow`). -/
theorem derivativeFun_uUnit_natZpow (k : ℕ) :
    derivativeFun (↑(uUnit ^ (k : ℤ)) : PowerSeries ℂ)
      = (k : PowerSeries ℂ) * (↑(uUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) * derivativeFun uSeries := by
  have hk : (↑(uUnit ^ (k : ℤ)) : PowerSeries ℂ) = uSeries ^ k := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, uUnit_coe]
  rcases k with _ | j
  · rw [hk, pow_zero, PowerSeries.derivativeFun_one]; simp
  · have hk1 : (↑(uUnit ^ (((j + 1 : ℕ) : ℤ) - 1)) : PowerSeries ℂ) = uSeries ^ j := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = ((j : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        Units.val_pow_eq_pow_val, uUnit_coe]
    rw [hk, hk1]
    have h := PowerSeries.derivative_pow ℂ uSeries (j + 1)
    rw [Nat.add_sub_cancel] at h
    exact h

/-- The `zpow` derivative for a **nonnegative** integer exponent. -/
theorem derivativeFun_uUnit_zpow_nonneg {a : ℤ} (ha : 0 ≤ a) :
    derivativeFun (↑(uUnit ^ a) : PowerSeries ℂ)
      = (a : PowerSeries ℂ) * (↑(uUnit ^ (a - 1)) : PowerSeries ℂ) * derivativeFun uSeries := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  exact_mod_cast derivativeFun_uUnit_natZpow k

/-- **The `zpow` derivative of the unit** `d(uᵐ) = m·u^{m−1}·u′` for **all** `m : ℤ`.  The negative
case uses `d(uᵐ·u^{−m}) = d(1) = 0` (Leibniz) to reduce to the nonnegative rule at `−m`, then cancels
the unit `u^{−m}`. -/
theorem derivativeFun_uUnit_zpow (m : ℤ) :
    derivativeFun (↑(uUnit ^ m) : PowerSeries ℂ)
      = (m : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * derivativeFun uSeries := by
  by_cases hm : 0 ≤ m
  · exact derivativeFun_uUnit_zpow_nonneg hm
  · push_neg at hm
    have h0 : (↑(uUnit ^ m) : PowerSeries ℂ) * ↑(uUnit ^ (-m)) = 1 := by
      rw [uUnit_val_zpow_mul, show (m + -m) = (0 : ℤ) by ring, zpow_zero, Units.val_one]
    have hleib : (↑(uUnit ^ m) : PowerSeries ℂ) * derivativeFun (↑(uUnit ^ (-m)))
        + (↑(uUnit ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(uUnit ^ m)) = 0 := by
      have hmul := PowerSeries.derivativeFun_mul (↑(uUnit ^ m) : PowerSeries ℂ) (↑(uUnit ^ (-m)))
      rw [h0, PowerSeries.derivativeFun_one] at hmul
      simpa only [smul_eq_mul] using hmul.symm
    have dneg : derivativeFun (↑(uUnit ^ (-m)) : PowerSeries ℂ)
        = ((-m : ℤ) : PowerSeries ℂ) * ↑(uUnit ^ (-m - 1)) * derivativeFun uSeries :=
      derivativeFun_uUnit_zpow_nonneg (by omega)
    have e1 : (↑(uUnit ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(uUnit ^ m))
        = (m : PowerSeries ℂ) * (↑(uUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * derivativeFun uSeries := by
      have h1 : (↑(uUnit ^ (-m)) : PowerSeries ℂ) * derivativeFun (↑(uUnit ^ m))
          = -((↑(uUnit ^ m) : PowerSeries ℂ) * derivativeFun (↑(uUnit ^ (-m)))) := by
        linear_combination hleib
      rw [h1, dneg,
        show (↑(uUnit ^ m) : PowerSeries ℂ)
              * (((-m : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ (-m - 1)) : PowerSeries ℂ)
                * derivativeFun uSeries)
            = ((-m : ℤ) : PowerSeries ℂ)
              * ((↑(uUnit ^ m) : PowerSeries ℂ) * (↑(uUnit ^ (-m - 1)) : PowerSeries ℂ))
              * derivativeFun uSeries from by ring,
        uUnit_val_zpow_mul, show (m + (-m - 1)) = (-1 : ℤ) from by ring]
      push_cast; ring
    have e2 : (↑(uUnit ^ (-m)) : PowerSeries ℂ)
          * ((m : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * derivativeFun uSeries)
        = (m : PowerSeries ℂ) * (↑(uUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * derivativeFun uSeries := by
      rw [show (↑(uUnit ^ (-m)) : PowerSeries ℂ)
              * ((m : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ) * derivativeFun uSeries)
            = (m : PowerSeries ℂ)
              * ((↑(uUnit ^ (-m)) : PowerSeries ℂ) * (↑(uUnit ^ (m - 1)) : PowerSeries ℂ))
              * derivativeFun uSeries from by ring,
        uUnit_val_zpow_mul, show (-m + (m - 1)) = (-1 : ℤ) from by ring]
    exact mul_left_cancel₀ (Units.ne_zero (uUnit ^ (-m))) (by rw [e1, e2])

/-- `d(X) = 1`. -/
theorem derivativeFun_X : derivativeFun (PowerSeries.X : PowerSeries ℂ) = 1 := by
  ext n
  rw [coeff_derivativeFun, PowerSeries.coeff_X]
  rcases n with _ | j <;> simp [PowerSeries.coeff_one]

/-- **The power series `P_m := (1+w)·u^{m+1}`** — the "de-Laurented" square-bracket generating series:
`f_m(w) = (1+w)(log(1+w))^{m+1} = w^{m+1}·P_m`, so `d[m,a] = [w^{a−m}] P_m`. -/
noncomputable def Pw (m : ℤ) : PowerSeries ℂ :=
  (1 + PowerSeries.X) * (↑(uUnit ^ (m + 1)) : PowerSeries ℂ)

/-- The derivative of `P_m` (Leibniz + the `zpow` derivative). -/
theorem derivativeFun_Pw (m : ℤ) :
    derivativeFun (Pw m)
      = (1 + PowerSeries.X)
          * (((m + 1 : ℤ) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ) * derivativeFun uSeries)
        + (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) := by
  have hdX : derivativeFun (1 + PowerSeries.X : PowerSeries ℂ) = 1 := by
    rw [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_one, zero_add, derivativeFun_X]
  simp only [Pw]
  rw [PowerSeries.derivativeFun_mul, derivativeFun_uUnit_zpow (m + 1),
    show (m + 1 - 1) = m from by ring, hdX]
  simp only [smul_eq_mul, mul_one]

/-- **The identity `(★)`** — the power-series form of the Witt relation `f_m f_n′ − f_m′ f_n =
`(n−m) f_{m+n}`, transported to the `P`-series:
`(m−n)(P_m P_n − P_{m+n}) + w(P_m′ P_n − P_m P_n′) = 0`.
It **collapses to the ODE** `uSeries_ODE`: after reducing every `uᵏ` to `↑(uUnit^m)·↑(uUnit^n)·uⁱ`,
the whole expression is `(m−n)(1+w)·↑(uUnit^m)·↑(uUnit^n)·u·[(1+w)(u+w·u′) − 1]`. -/
theorem Pw_witt (m n : ℤ) :
    ((m - n : ℤ) : PowerSeries ℂ) * (Pw m * Pw n - Pw (m + n))
      + PowerSeries.X * (derivativeFun (Pw m) * Pw n - Pw m * derivativeFun (Pw n)) = 0 := by
  -- reduce all unit-powers to a := ↑(uUnit^m), b := ↑(uUnit^n), u := uSeries
  have ha1 : (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) = (↑(uUnit ^ m) : PowerSeries ℂ) * uSeries := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
  have hb1 : (↑(uUnit ^ (n + 1)) : PowerSeries ℂ) = (↑(uUnit ^ n) : PowerSeries ℂ) * uSeries := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
  have hab1 : (↑(uUnit ^ (m + n + 1)) : PowerSeries ℂ)
      = (↑(uUnit ^ m) : PowerSeries ℂ) * ↑(uUnit ^ n) * uSeries := by
    rw [← uUnit_coe, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add_one]
  rw [derivativeFun_Pw m, derivativeFun_Pw n]
  simp only [Pw]
  rw [ha1, hb1, hab1]
  have hODE := uSeries_ODE
  push_cast
  linear_combination
    (((m : ℤ) : PowerSeries ℂ) - ((n : ℤ) : PowerSeries ℂ)) * (1 + PowerSeries.X)
      * (↑(uUnit ^ m) : PowerSeries ℂ) * (↑(uUnit ^ n) : PowerSeries ℂ) * uSeries * hODE

/-! ## Brick 3 (bridge) — the square-bracket coefficient `d[m,a]` is a coefficient of `P_m`

`D m a := sqBracketCoeffZ 2 (m+1) (a+1)` — the Gannon coefficient `d[m,a]` (Virasoro weight `2`) — is
exactly `[w^{a−m}] P_m` (`0` when `a < m`).  This bridges the abstract coefficient identities to the
concrete power series `P_m`, so that Gannon's identity `(i)` becomes the `[w^{j−m−n}]`-coefficient of
`Pw_witt`. -/

/-- **`d[m,a] = [w^{a−m}] P_m`** (with `d[m,a] = 0` for `a < m`). -/
theorem sqBracketCoeffZ_two_eq_coeff_Pw (m a : ℤ) :
    sqBracketCoeffZ 2 (m + 1) (a + 1)
      = if 0 ≤ a - m then PowerSeries.coeff (R := ℂ) (a - m).toNat (Pw m) else 0 := by
  have h2 : (↑(onePlusXUnit ^ (((2 : ℕ) : ℤ) - 1)) : PowerSeries ℂ) = 1 + PowerSeries.X := by
    rw [show (((2 : ℕ) : ℤ) - 1) = (1 : ℤ) from by norm_num, zpow_one, onePlusXUnit_coe]
  unfold sqBracketCoeffZ Pw
  rw [show ((a + 1) - (m + 1)) = a - m from by ring, h2]

/-! ## Brick 4 — the coefficient extraction of `Pw_witt` to Gannon's identity `(i)`

The weight `p·[wᵖ]f = [wᵖ](w·f′)` bookkeeping, then the `∑ᶠ a:ℤ → Finset.antidiagonal J` reindex. -/

/-- **`[wᵏ](w·f′) = k·[wᵏ]f`** — the Euler-operator coefficient identity (the `p·`/`q·` weights). -/
theorem coeff_X_mul_derivativeFun (f : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff (R := ℂ) k (PowerSeries.X * derivativeFun f)
      = (k : ℂ) * PowerSeries.coeff (R := ℂ) k f := by
  rcases k with _ | s
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_derivativeFun]; push_cast; ring

/-! ### The vacuum square-bracket scalar `s(k) = c(0,k,−1) = δ_{k,−1}`

`𝟙[k]` is the scalar `s(k) = [w^{−1−k}]((1+w)^{−1}u^k) = Res_w[(1+w)^{−1}(log(1+w))^k]`.  Classically
the substitution `z = log(1+w)` turns this into `Res_z[z^k dz] = δ_{k,−1}`; here we prove it by an
**elementary** argument from the ODE: `(1+w)^{−1} = u + w·u′` gives
`(k+1)·(1+w)^{−1}u^k = (k+1)u^{k+1} + w·d(u^{k+1})`, and taking `[wʲ]` with `j = −1−k` produces the
factor `(k+1) + j = 0`.  (This is exactly the term that cancels the `m+n = −2` Schwarzian anomaly.) -/

/-- `(1+w)^{−1} = u + w·u′` — the ODE `uSeries_ODE` read as an inverse. -/
theorem onePlusXUnit_inv_eq : (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ)
    = uSeries + PowerSeries.X * derivativeFun uSeries := by
  have hne : (1 + PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    rw [← onePlusXUnit_coe]; exact Units.ne_zero onePlusXUnit
  refine mul_left_cancel₀ hne ?_
  rw [uSeries_ODE, ← onePlusXUnit_coe, ← Units.val_mul, zpow_neg_one, mul_inv_cancel,
    Units.val_one]

/-- **`s(k) = 0` for `k ≠ −1`** — the vacuum square-bracket mode vanishes except at `k = −1`. -/
theorem sqBracketCoeffZ_vacuum_of_ne (k : ℤ) (hk : k ≠ -1) : sqBracketCoeffZ 0 k (-1) = 0 := by
  by_cases hj : 0 ≤ (-1 : ℤ) - k
  · -- `j := (−1−k).toNat` is a genuine index; use the ODE identity
    obtain ⟨j, hjz⟩ : ∃ j : ℕ, (j : ℤ) = -1 - k := ⟨((-1 : ℤ) - k).toNat, Int.toNat_of_nonneg hj⟩
    have hA : (↑(uUnit ^ k) : PowerSeries ℂ) * uSeries = (↑(uUnit ^ (k + 1)) : PowerSeries ℂ) := by
      rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
    have hkey : (((k + 1 : ℤ)) : PowerSeries ℂ)
          * ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ k) : PowerSeries ℂ))
        = (((k + 1 : ℤ)) : PowerSeries ℂ) * (↑(uUnit ^ (k + 1)) : PowerSeries ℂ)
          + PowerSeries.X * derivativeFun (↑(uUnit ^ (k + 1)) : PowerSeries ℂ) := by
      rw [onePlusXUnit_inv_eq, derivativeFun_uUnit_zpow (k + 1),
        show (k + 1 - 1) = k from by ring, ← hA]
      ring
    have hcoeff := congrArg (PowerSeries.coeff (R := ℂ) j) hkey
    have hInt : ∀ (c : ℤ) (g : PowerSeries ℂ),
        PowerSeries.coeff (R := ℂ) j ((c : PowerSeries ℂ) * g)
          = (c : ℂ) * PowerSeries.coeff (R := ℂ) j g := by
      intro c g; rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
    rw [map_add, hInt, hInt, coeff_X_mul_derivativeFun] at hcoeff
    have hzero : ((k + 1 : ℤ) : ℂ)
        * PowerSeries.coeff (R := ℂ) j
            ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) * ↑(uUnit ^ k)) = 0 := by
      rw [hcoeff, show ((j : ℂ)) = ((j : ℤ) : ℂ) from by push_cast; ring, hjz]
      push_cast
      ring
    have hne : ((k + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hfin := (mul_eq_zero.mp hzero).resolve_left hne
    rw [sqBracketCoeffZ, if_pos hj, show ((-1 : ℤ) - k).toNat = j from by omega]
    exact hfin
  · rw [sqBracketCoeffZ, if_neg hj]

/-- The constant coefficient of any integer power of a unit with constant coefficient `1` is `1`. -/
theorem constantCoeff_unit_zpow (U : (PowerSeries ℂ)ˣ)
    (hU : PowerSeries.constantCoeff (R := ℂ) (U : PowerSeries ℂ) = 1) (k : ℤ) :
    PowerSeries.constantCoeff (R := ℂ) ((↑(U ^ k) : PowerSeries ℂ)) = 1 := by
  have hnat : ∀ j : ℕ,
      PowerSeries.constantCoeff (R := ℂ) ((↑(U ^ (j : ℤ)) : PowerSeries ℂ)) = 1 := by
    intro j
    rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, hU, one_pow]
  by_cases hk : 0 ≤ k
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact hnat j
  · push_neg at hk
    have h1 : (↑(U ^ k) : PowerSeries ℂ) * (↑(U ^ (-k)) : PowerSeries ℂ) = 1 := by
      rw [← Units.val_mul, ← zpow_add, show k + -k = (0 : ℤ) from by ring, zpow_zero, Units.val_one]
    have h2 := congrArg (PowerSeries.constantCoeff (R := ℂ)) h1
    rw [map_mul, map_one] at h2
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -k by omega)
    rw [hj, hnat j, mul_one] at h2
    exact h2

theorem constantCoeff_onePlusX : PowerSeries.constantCoeff (R := ℂ) (onePlusXUnit : PowerSeries ℂ)
    = 1 := by
  rw [onePlusXUnit_coe, map_add, map_one, PowerSeries.constantCoeff_X, add_zero]

theorem constantCoeff_uUnit : PowerSeries.constantCoeff (R := ℂ) (uUnit : PowerSeries ℂ) = 1 := by
  rw [uUnit_coe, uSeries, PowerSeries.constantCoeff_mk]; norm_num

/-- **`s(−1) = 1`** — the surviving vacuum scalar (`𝟙[−1] = id`). -/
theorem sqBracketCoeffZ_vacuum_neg_one : sqBracketCoeffZ 0 (-1) (-1) = 1 := by
  rw [sqBracketCoeffZ, if_pos (by norm_num), show ((-1 : ℤ) - (-1)).toNat = 0 from by norm_num,
    show (((0 : ℕ) : ℤ) - 1) = (-1 : ℤ) from by norm_num,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    constantCoeff_unit_zpow onePlusXUnit constantCoeff_onePlusX,
    constantCoeff_unit_zpow uUnit constantCoeff_uUnit, mul_one]

/-- **The general diagonal coefficient is `1`**: `c(k, m, m) = 1` for every `k` and every `m`.

Both power-series factors `(1+w)^{k−1}` and `u^m` are units with constant term `1`, so the
`[w⁰]`-coefficient of their product is `1`.  In particular `c(k, −1, −1) = 1`
(`sqBracketCoeffZ_neg_one_diag`), which is the coefficient with which the two-point term enters
Zhu's recursion. -/
theorem sqBracketCoeffZ_diag' (k : ℕ) (m : ℤ) : sqBracketCoeffZ k m m = 1 := by
  rw [sqBracketCoeffZ, if_pos (by omega),
    show ((m : ℤ) - m).toNat = 0 from by simp,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    constantCoeff_unit_zpow onePlusXUnit constantCoeff_onePlusX,
    constantCoeff_unit_zpow uUnit constantCoeff_uUnit, mul_one]

/-- **`c(k, −1, −1) = 1`** — the leading square-bracket coefficient of `a[−1]v`.  This is the
coefficient with which `tr o(a)o(v)q^{L₀−c/24}` enters Zhu's recursion. -/
theorem sqBracketCoeffZ_neg_one_diag (k : ℕ) : sqBracketCoeffZ k (-1) (-1) = 1 :=
  sqBracketCoeffZ_diag' k (-1)

/-- **`d[m,m] = 1`** — the diagonal normalization `[w⁰]P_m = 1` (the `k = 2` case of
`sqBracketCoeffZ_diag'`). -/
theorem sqBracketCoeffZ_diag (m : ℤ) : sqBracketCoeffZ 2 (m + 1) (m + 1) = 1 := by
  rw [sqBracketCoeffZ, if_pos (by omega),
    show ((m + 1) - (m + 1) : ℤ).toNat = 0 from by norm_num,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    constantCoeff_unit_zpow onePlusXUnit constantCoeff_onePlusX,
    constantCoeff_unit_zpow uUnit constantCoeff_uUnit, mul_one]

/-- **The antidiagonal form of Gannon's identity `(i)`** — the `[wᴶ]`-coefficient of `Pw_witt`, with the
weight `2a−j` written in reindexed form `(m−n) + (p₁ − p₂)` (`p₁ = a−m`, `p₂ = j−a−n`, `p₁+p₂ = J`).
Proved from `Pw_witt` + `coeff_mul` + `coeff_X_mul_derivativeFun`, all at the `ℂ` (coefficient) level. -/
theorem witt_antidiag (m n : ℤ) (J : ℕ) :
    ∑ p ∈ Finset.antidiagonal J,
        PowerSeries.coeff (R := ℂ) p.1 (Pw m) * PowerSeries.coeff (R := ℂ) p.2 (Pw n)
          * (((m - n : ℤ) : ℂ) + (p.1 : ℂ) - (p.2 : ℂ))
      = ((m - n : ℤ) : ℂ) * PowerSeries.coeff (R := ℂ) J (Pw (m + n)) := by
  have hInt : ∀ (c : ℤ) (g : PowerSeries ℂ) (k : ℕ),
      PowerSeries.coeff (R := ℂ) k ((c : PowerSeries ℂ) * g)
        = (c : ℂ) * PowerSeries.coeff (R := ℂ) k g := by
    intro c g k
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hsplit : ∀ p ∈ Finset.antidiagonal J,
      PowerSeries.coeff (R := ℂ) p.1 (Pw m) * PowerSeries.coeff (R := ℂ) p.2 (Pw n)
          * (((m - n : ℤ) : ℂ) + (p.1 : ℂ) - (p.2 : ℂ))
      = ((m - n : ℤ) : ℂ)
          * (PowerSeries.coeff (R := ℂ) p.1 (Pw m) * PowerSeries.coeff (R := ℂ) p.2 (Pw n))
        + PowerSeries.coeff (R := ℂ) p.1 (PowerSeries.X * derivativeFun (Pw m))
            * PowerSeries.coeff (R := ℂ) p.2 (Pw n)
        - PowerSeries.coeff (R := ℂ) p.1 (Pw m)
            * PowerSeries.coeff (R := ℂ) p.2 (PowerSeries.X * derivativeFun (Pw n)) := by
    intro p _
    rw [coeff_X_mul_derivativeFun, coeff_X_mul_derivativeFun]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← coeff_mul, ← coeff_mul, ← coeff_mul]
  have hw := congrArg (PowerSeries.coeff (R := ℂ) J) (Pw_witt m n)
  rw [map_add, map_zero, hInt, map_sub] at hw
  have hbr : PowerSeries.coeff (R := ℂ) J (PowerSeries.X * derivativeFun (Pw m) * Pw n)
      - PowerSeries.coeff (R := ℂ) J (Pw m * (PowerSeries.X * derivativeFun (Pw n)))
      = PowerSeries.coeff (R := ℂ) J
          (PowerSeries.X * (derivativeFun (Pw m) * Pw n - Pw m * derivativeFun (Pw n))) := by
    rw [← map_sub]; congr 1; ring
  rw [add_sub_assoc, hbr]
  linear_combination hw

/-- **Gannon's bracket identity `(i)`** (the bracket half of the torus-Virasoro relation):
`Σ_a d[m,a]·d[n,j−a]·(2a−j) = (m−n)·d[m+n,j]`, with `d[m,a] = sqBracketCoeffZ 2 (m+1) (a+1)`.

Proved by extracting the `[w^{j−m−n}]`-coefficient of the Witt-bracket identity `Pw_witt`: the `∑ᶠ a:ℤ`
is supported on `Icc m (j−n)` and reindexes (`a ↦ ((a−m), (j−n−a))`) onto `Finset.antidiagonal J`
(`J = j−m−n`), where it is exactly `witt_antidiag`.  For `j < m+n` (`J < 0`) both sides vanish
structurally (the coefficient is lower-triangular, `d[m,a]=0` for `a<m`). -/
theorem sqBracketCoeff_witt_identity (m n j : ℤ) :
    ∑ᶠ a : ℤ, sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((j - a) + 1)
        * ((2 * a - j : ℤ) : ℂ)
      = ((m - n : ℤ) : ℂ) * sqBracketCoeffZ 2 (m + n + 1) (j + 1) := by
  by_cases hJ : m + n ≤ j
  · -- J := j − m − n ≥ 0
    obtain ⟨J, hJz⟩ : ∃ J : ℕ, (J : ℤ) = j - m - n :=
      ⟨(j - m - n).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hRHS : sqBracketCoeffZ 2 (m + n + 1) (j + 1)
        = PowerSeries.coeff (R := ℂ) J (Pw (m + n)) := by
      rw [sqBracketCoeffZ_two_eq_coeff_Pw, if_pos (by omega),
        show (j - (m + n)).toNat = J from by omega]
    rw [hRHS, ← witt_antidiag m n J]
    have hsupp : (Function.support fun a : ℤ =>
        sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((j - a) + 1)
          * ((2 * a - j : ℤ) : ℂ)) ⊆ ↑(Finset.Icc m (j - n)) := by
      intro a ha
      simp only [Function.mem_support, ne_eq] at ha
      simp only [Finset.coe_Icc, Set.mem_Icc]
      by_contra hc
      push_neg at hc
      by_cases h1 : m ≤ a
      · exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show (j - a) + 1 < n + 1 by omega),
          mul_zero, zero_mul])
      · exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul])
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
    refine Finset.sum_nbij' (fun a => ((a - m).toNat, (j - n - a).toNat))
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
        sqBracketCoeffZ_two_eq_coeff_Pw n (j - a), if_pos (by omega)]
      have hjn : ((j - a) - n).toNat = (j - n - a).toNat := by omega
      have e1 : ((a - m).toNat : ℤ) = a - m := Int.toNat_of_nonneg (by omega)
      have e2 : ((j - n - a).toNat : ℤ) = j - n - a := Int.toNat_of_nonneg (by omega)
      rw [hjn]
      congr 1
      have hwt : ((2 * a - j : ℤ) : ℂ)
          = ((m - n : ℤ) : ℂ) + (((a - m).toNat : ℤ) : ℂ) - (((j - n - a).toNat : ℤ) : ℂ) := by
        rw [e1, e2]; push_cast; ring
      rw [hwt]; push_cast; ring
  · -- J < 0: both sides vanish
    push_neg at hJ
    rw [sqBracketCoeffZ_of_lt 2 (show j + 1 < m + n + 1 by omega), mul_zero]
    have hzero : (fun a : ℤ => sqBracketCoeffZ 2 (m + 1) (a + 1)
        * sqBracketCoeffZ 2 (n + 1) ((j - a) + 1) * ((2 * a - j : ℤ) : ℂ)) = fun _ => 0 := by
      funext a
      by_cases h1 : m ≤ a
      · rw [sqBracketCoeffZ_of_lt 2 (show (j - a) + 1 < n + 1 by omega), mul_zero, zero_mul]
      · rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul]
    rw [hzero, finsum_zero]

end VOA
