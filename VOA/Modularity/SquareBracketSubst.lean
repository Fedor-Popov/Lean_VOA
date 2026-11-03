/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuAssembly
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The square bracket in the `z`-coordinate: `u` **is** the Bernoulli generating function

Zhu's square bracket is built from the unit `uSeries = log(1+w)/w` in the coordinate `w`, while the
constants his recursion produces — `−B_{2m}/(2m)!` — are Bernoulli numbers, i.e. coefficients in the
coordinate `z` with `w = e^z − 1`.  `zhuG_zero_eq_neg_coeff_bernoulli` recorded that coincidence
numerically; this file **proves** it is not a coincidence:

  `uSeries` substituted at `w = e^z − 1` **is** `B(z) = z/(e^z − 1)`
  (`subst_expMinusOne_uSeries`).

So the Bernoulli constants are not imported into Zhu's recursion from outside — they are what
`uSeries` *is*, read in the `z`-coordinate, and every square-bracket coefficient is built from
`uSeries`.

## The route

Everything rests on `log(e^z) = z`, i.e. `subst (e^z − 1) (log) = X`, which this file proves
(`log_subst_expMinusOne`).  Mathlib has no `log ∘ exp = id` for formal power series, but it has all
the parts:

* `PowerSeries.HasSubst.exp_sub_one` — `e^z − 1` may be substituted (zero constant term);
* `PowerSeries.derivative_subst` — the **chain rule** `d(f ∘ g) = (df ∘ g)·dg`;
* `PowerSeries.deriv_log` — `d(log(1+X)) = Σ (−1)ⁿXⁿ`, the geometric series;
* `PowerSeries.derivative.ext` — two series with the same derivative and constant term are equal.

Differentiating `log ∘ exp` gives `(geometric ∘ (e^z−1)) · e^z`, and substituting `e^z − 1` into the
geometric identity `(1+X)·Σ(−1)ⁿXⁿ = 1` turns that into `e^z⁻¹·e^z = 1 = d(X)`.  Both sides have
zero constant term, so they agree.

## Status
Proved, axiom-clean and `pbw`-free.  This is the coordinate bridge the weight matching of Zhu's
recursion needs; the matching itself is still the named residual (see `ZhuAssembly`).

## References
* Zhu, J. AMS 9 (1996), §4; Gannon §5.3.5; Mathlib `RingTheory/PowerSeries/{Substitution,Log}`.
-/

namespace VOA

open scoped BigOperators

/-! ## The geometric series `Σ (−1)ⁿ Xⁿ` -/

/-- The geometric series `1 − X + X² − ⋯ = (1+X)⁻¹`. -/
noncomputable def geoAltSeries : PowerSeries ℂ := PowerSeries.mk fun n => ((-1 : ℂ) ^ n)

/-- `d(log(1+X))` is the alternating geometric series (Mathlib's `deriv_log`, with the
`algebraMap ℚ ℂ` discharged). -/
theorem derivative_log_eq_geoAltSeries :
    (PowerSeries.derivative ℂ) (PowerSeries.log ℂ) = geoAltSeries := by
  rw [PowerSeries.deriv_log]
  refine PowerSeries.ext (fun n => ?_)
  rw [PowerSeries.coeff_mk, geoAltSeries, PowerSeries.coeff_mk, eq_ratCast]
  push_cast
  ring

/-- **`(1 + X)·Σ(−1)ⁿXⁿ = 1`** — the geometric series inverts `1 + X`. -/
theorem onePlusX_mul_geoAltSeries :
    (1 + PowerSeries.X : PowerSeries ℂ) * geoAltSeries = 1 := by
  have hsplit : (1 + PowerSeries.X : PowerSeries ℂ) * geoAltSeries
      = geoAltSeries + PowerSeries.X * geoAltSeries := by ring
  rw [hsplit]
  refine PowerSeries.ext (fun n => ?_)
  cases n with
  | zero =>
      rw [map_add, PowerSeries.coeff_zero_X_mul, add_zero, geoAltSeries,
        PowerSeries.coeff_mk, PowerSeries.coeff_zero_one]
      norm_num
  | succ m =>
      rw [map_add, PowerSeries.coeff_succ_X_mul, geoAltSeries, PowerSeries.coeff_mk,
        PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), pow_succ]
      ring

/-! ## `log(e^z) = z` -/

/-- `e^z − 1` may be substituted: it has zero constant term. -/
theorem hasSubst_expMinusOne : PowerSeries.HasSubst expMinusOne := by
  rw [expMinusOne]
  exact PowerSeries.HasSubst.exp_sub_one

/-- `d(e^z − 1) = e^z`. -/
theorem derivative_expMinusOne' :
    (PowerSeries.derivative ℂ) expMinusOne = PowerSeries.exp ℂ := by
  rw [expMinusOne, map_sub, Derivation.map_one_eq_zero, sub_zero]
  exact PowerSeries.derivative_exp ℂ

/-- The geometric series composed with `e^z − 1` inverts `e^z`. -/
theorem subst_expMinusOne_geoAltSeries_mul_exp :
    geoAltSeries.subst expMinusOne * PowerSeries.exp ℂ = 1 := by
  have h := congrArg (PowerSeries.substAlgHom hasSubst_expMinusOne) onePlusX_mul_geoAltSeries
  rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X hasSubst_expMinusOne,
    PowerSeries.coe_substAlgHom hasSubst_expMinusOne] at h
  have hexp : (1 : PowerSeries ℂ) + expMinusOne = PowerSeries.exp ℂ := by
    rw [expMinusOne]; ring
  rw [hexp] at h
  rw [mul_comm]
  exact h

/-- **`log(e^z) = z`** for formal power series: `subst (e^z − 1) log(1+X) = X`.

Mathlib has the pieces but not this composite.  Proof: differentiate with the chain rule
(`derivative_subst`), use `deriv_log` and the geometric identity substituted at `e^z − 1`
(`subst_expMinusOne_geoAltSeries_mul_exp`) to get derivative `1 = d(X)`, then compare constant
terms (`derivative.ext`). -/
theorem log_subst_expMinusOne :
    (PowerSeries.log ℂ).subst expMinusOne = PowerSeries.X := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [PowerSeries.derivative_subst ℂ hasSubst_expMinusOne, derivative_log_eq_geoAltSeries,
      derivative_expMinusOne', subst_expMinusOne_geoAltSeries_mul_exp, PowerSeries.derivative_X]
  · have hcc : PowerSeries.constantCoeff expMinusOne = 0 := by
      rw [expMinusOne, map_sub, PowerSeries.constantCoeff_exp, map_one, sub_self]
    rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero hcc _ PowerSeries.constantCoeff_log

/-! ## `uSeries` in the `z`-coordinate -/

/-- The repo's `logOnePlusXSeries` is Mathlib's `PowerSeries.log ℂ`. -/
theorem logOnePlusXSeries_eq_log : logOnePlusXSeries = PowerSeries.log ℂ := by
  refine PowerSeries.ext (fun n => ?_)
  rw [logOnePlusXSeries, PowerSeries.coeff_mk, PowerSeries.coeff_log]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, eq_ratCast]
    push_cast
    ring

/-- **`uSeries` read in the `z`-coordinate IS the Bernoulli generating function.**

Substituting `w = e^z − 1` into `u = log(1+w)/w` gives `z/(e^z − 1) = Σ B_n zⁿ/n!`.  Together with
`zhuG_zero_eq_neg_coeff_bernoulli` this shows the constants of Zhu's recursion are exactly the
coefficients of the unit out of which every square-bracket weight is built — the identity the weight
matching rests on, **proved** rather than observed. -/
theorem subst_expMinusOne_uSeries :
    uSeries.subst expMinusOne = bernoulliPowerSeries ℂ := by
  have hprod : (uSeries.subst expMinusOne) * expMinusOne = PowerSeries.X := by
    have h1 : uSeries.subst expMinusOne * expMinusOne
        = (PowerSeries.X * uSeries).subst expMinusOne := by
      rw [PowerSeries.subst_mul hasSubst_expMinusOne,
        PowerSeries.subst_X hasSubst_expMinusOne, mul_comm]
    rw [h1, ← logOnePlusX_eq_X_mul_u, logOnePlusXSeries_eq_log, log_subst_expMinusOne]
  have hB : bernoulliPowerSeries ℂ * expMinusOne = PowerSeries.X :=
    bernoulliPowerSeries_mul_expMinusOne
  have hne : expMinusOne ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff (R := ℂ) 1) h
    rw [expMinusOne, map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one,
      if_neg (one_ne_zero), sub_zero, map_zero] at this
    norm_num [eq_ratCast] at this
  exact mul_right_cancel₀ hne (hprod.trans hB.symm)

/-! ## Transporting the square-bracket generating function to the `z`-coordinate

Every square-bracket coefficient is a `w`-coefficient of `(1+w)^{k−1}·u^m` (`sqBracketCoeffZ`).
Substitution is a ring homomorphism, so that whole generating function transports:
`(1+w) ↦ e^z` and `u ↦ B(z)`, giving `e^{(k−1)z}·B(z)^m`.  Since both `1+w` and `u` are *units*, the
transport is valid for **integer** exponents, which is what `sqBracketCoeffZ` uses. -/

/-- The substitution `w ↦ e^z − 1` as an algebra endomorphism of `ℂ⟦X⟧`. -/
noncomputable def substExpHom : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom hasSubst_expMinusOne

@[simp] theorem substExpHom_apply (f : PowerSeries ℂ) : substExpHom f = f.subst expMinusOne :=
  congrFun (PowerSeries.coe_substAlgHom hasSubst_expMinusOne) f

/-- A ring hom carries units to units, compatibly with **integer** powers. -/
theorem subst_units_zpow (U : (PowerSeries ℂ)ˣ) (m : ℤ) :
    ((U ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ).subst expMinusOne
      = ((Units.map (substExpHom : PowerSeries ℂ →* PowerSeries ℂ) U ^ m :
          (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
  rw [← map_zpow (Units.map (substExpHom : PowerSeries ℂ →* PowerSeries ℂ)) U m,
    Units.coe_map, MonoidHom.coe_coe, substExpHom_apply]

/-- `B(z)` has constant term `B₀ = 1`, hence is a unit. -/
theorem constantCoeff_bernoulliPowerSeries :
    PowerSeries.constantCoeff (bernoulliPowerSeries ℂ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_bernoulliPowerSeries]
  norm_num

theorem bernoulliPowerSeries_isUnit : IsUnit (bernoulliPowerSeries ℂ) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [constantCoeff_bernoulliPowerSeries]; exact isUnit_one)

/-- `B(z)` as a unit of `ℂ⟦z⟧`, so `B^m` makes sense for `m : ℤ`. -/
noncomputable def bernoulliUnit : (PowerSeries ℂ)ˣ := bernoulliPowerSeries_isUnit.unit

@[simp] theorem bernoulliUnit_coe : (bernoulliUnit : PowerSeries ℂ) = bernoulliPowerSeries ℂ :=
  IsUnit.unit_spec _

/-- `e^z` as a unit of `ℂ⟦z⟧`. -/
noncomputable def expUnit : (PowerSeries ℂ)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [PowerSeries.constantCoeff_exp]; exact isUnit_one)).unit

@[simp] theorem expUnit_coe : (expUnit : PowerSeries ℂ) = PowerSeries.exp ℂ := IsUnit.unit_spec _

/-- The substitution carries `u` to `B`, as units. -/
theorem map_substExpHom_uUnit :
    Units.map (substExpHom : PowerSeries ℂ →* PowerSeries ℂ) uUnit = bernoulliUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, substExpHom_apply, uUnit_coe, bernoulliUnit_coe]
  exact subst_expMinusOne_uSeries

/-- The substitution carries `1 + w` to `e^z`, as units. -/
theorem map_substExpHom_onePlusXUnit :
    Units.map (substExpHom : PowerSeries ℂ →* PowerSeries ℂ) onePlusXUnit = expUnit := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, substExpHom_apply, onePlusXUnit_coe, expUnit_coe,
    PowerSeries.subst_add hasSubst_expMinusOne]
  rw [show ((1 : PowerSeries ℂ)).subst expMinusOne = 1 from by
      rw [← substExpHom_apply]; exact map_one _,
    PowerSeries.subst_X hasSubst_expMinusOne, expMinusOne]
  ring

/-- **`u^m` in the `z`-coordinate is `B(z)^m`**, for every integer `m`. -/
theorem subst_expMinusOne_uUnit_zpow (m : ℤ) :
    ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ).subst expMinusOne
      = ((bernoulliUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
  rw [subst_units_zpow, map_substExpHom_uUnit]

/-- **`(1+w)^k` in the `z`-coordinate is `e^{kz}`**, for every integer `k`. -/
theorem subst_expMinusOne_onePlusXUnit_zpow (k : ℤ) :
    ((onePlusXUnit ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ).subst expMinusOne
      = ((expUnit ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
  rw [subst_units_zpow, map_substExpHom_onePlusXUnit]

/-- **The square-bracket generating function, transported.**

`sqBracketCoeffZ k m i` is the `w`-coefficient `[w^{i−m}]` of `(1+w)^{k−1}·u^m`.  That entire
generating function, read in the coordinate `z` with `w = e^z − 1`, is

  `e^{(k−1)z} · B(z)^m`,

with `B` the Bernoulli generating function.  This is the coefficient transport the weight matching
needs: it converts every statement about square-bracket weights into a statement about `exp` and
Bernoulli series in `z`, where `zhuG`'s constants live (`zhuG_zero_eq_neg_coeff_bernoulli`). -/
theorem subst_expMinusOne_sqBracketGen (k : ℕ) (m : ℤ) :
    (((onePlusXUnit ^ ((k : ℤ) - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
        * ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)).subst expMinusOne
      = ((expUnit ^ ((k : ℤ) - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
        * ((bernoulliUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
  rw [PowerSeries.subst_mul hasSubst_expMinusOne, subst_expMinusOne_onePlusXUnit_zpow,
    subst_expMinusOne_uUnit_zpow]

/-- **The coefficient transport, explicitly.**  `coeff_subst'` expresses a `z`-coefficient of a
substituted series as a (finite) sum over the `w`-coefficients — the concrete dictionary between the
two coordinates. -/
theorem coeff_subst_expMinusOne (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (f.subst expMinusOne)
      = ∑ᶠ d : ℕ, PowerSeries.coeff (R := ℂ) d f •
          PowerSeries.coeff (R := ℂ) n (expMinusOne ^ d) :=
  PowerSeries.coeff_subst' hasSubst_expMinusOne f n

/-! ## The dictionary for the square-bracket weights themselves -/

/-- `sqBracketCoeffZ` at an index `m + d` (`d : ℕ`) is literally the `d`-th `w`-coefficient of
the generating function — the `if` in its definition is discharged. -/
theorem sqBracketCoeffZ_eq_coeff (k : ℕ) (m : ℤ) (d : ℕ) :
    sqBracketCoeffZ k m (m + d)
      = PowerSeries.coeff (R := ℂ) d
          (((onePlusXUnit ^ ((k : ℤ) - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
            * ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) := by
  rw [sqBracketCoeffZ, if_pos (by omega), show (m + (d : ℤ) - m).toNat = d from by omega]

/-- **The full dictionary between square-bracket weights and the `z`-coordinate.**

  `[zⁿ](e^{(k−1)z}·B(z)^m) = Σᶠ_d c(k,m,m+d)·[zⁿ]((e^z−1)^d)`.

The left side lives entirely in the world where `zhuG`'s constants are defined
(`coeff_bernoulliPowerSeries_gt_one`); the right side is a sum over the square-bracket weights.
This is the last engine before the weight matching: it converts any statement about the `c(k,m,i)`
into a statement about `exp` and Bernoulli coefficients, and back. -/
theorem coeff_sqBracketGen_transport (k : ℕ) (m : ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n
        (((expUnit ^ ((k : ℤ) - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
          * ((bernoulliUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))
      = ∑ᶠ d : ℕ, sqBracketCoeffZ k m (m + d)
          • PowerSeries.coeff (R := ℂ) n (expMinusOne ^ d) := by
  rw [← subst_expMinusOne_sqBracketGen k m, coeff_subst_expMinusOne]
  exact finsum_congr (fun d => by rw [sqBracketCoeffZ_eq_coeff])

/-! ## Where `zhuG`'s constants sit inside `B(z)`

`B(z) = Σ B_n zⁿ/n!` has a very rigid shape: `B₀ = 1`, `B₁ = −1/2`, and **every** higher odd
Bernoulli number vanishes.  So

  `B(z) = 1 − z/2 + Σ_{m ≥ 1} (B_{2m}/(2m)!) z^{2m}`,

and the numbers `B_{2m}/(2m)!` appearing there are exactly (minus) the constant terms of Zhu's
`G_{2m}` (`zhuG_zero_eq_neg_coeff_bernoulli`) — which is why the recursion's tail is indexed by
`2m − 1` and by nothing else.

Note also the `−1/2` in degree `1`: it is the **same** `−1/2` as `schwarzian_expMinusOne`
(`{e^z−1; z} = −1/2`), which is the coordinate-side source of the `δ_{m+n,−2}` anomaly that `Lsq`'s
`ω̃` term cancels.  The two `−1/2`s are one number seen twice. -/

/-- **The shape of `B(z)`**: `1` in degree `0`, `−1/2` in degree `1`, `B_n/n!` in even degrees,
and **zero** in every odd degree `> 1`.  The odd vanishing is `bernoulli_eq_zero_of_odd`. -/
theorem coeff_bernoulliPowerSeries_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) :
    PowerSeries.coeff (R := ℂ) n (bernoulliPowerSeries ℂ) = 0 := by
  rw [coeff_bernoulliPowerSeries, bernoulli_eq_zero_of_odd hodd hn]
  norm_num

/-- The degree-`1` coefficient of `B(z)` is `−1/2` — the same `−1/2` as the Schwarzian of the
cylinder→torus map (`schwarzian_expMinusOne`). -/
theorem coeff_one_bernoulliPowerSeries :
    PowerSeries.coeff (R := ℂ) 1 (bernoulliPowerSeries ℂ) = -(1 / 2) := by
  rw [coeff_bernoulliPowerSeries, bernoulli_one]
  norm_num

/-- The degree-`0` coefficient of `B(z)` is `1`. -/
theorem coeff_zero_bernoulliPowerSeries :
    PowerSeries.coeff (R := ℂ) 0 (bernoulliPowerSeries ℂ) = 1 := by
  rw [coeff_bernoulliPowerSeries]
  norm_num

/-- **The tail of `B(z)` beyond degree 1 is even, with coefficients `−zhuG j 0`.**

For `n > 1`, the `n`-th coefficient of `B(z)` is zero unless `n = 2j` is even, in which case it is
`−zhuG j 0`.  This is precisely the statement that Zhu's recursion can only have a tail indexed by
even weights `2j`, with the constants that `ZhuNormalization` pinned. -/
theorem coeff_bernoulliPowerSeries_gt_one {n : ℕ} (hn : 1 < n) :
    PowerSeries.coeff (R := ℂ) n (bernoulliPowerSeries ℂ)
      = if h : Even n then -zhuG (n / 2) 0 else 0 := by
  by_cases hev : Even n
  · obtain ⟨j, hj⟩ := hev
    have hn2 : n / 2 = j := by omega
    rw [dif_pos ⟨j, hj⟩, hn2, zhuG_zero_eq_neg_coeff_bernoulli, neg_neg,
      show 2 * j = n from by omega]
  · rw [dif_neg hev, coeff_bernoulliPowerSeries_odd (Nat.not_even_iff_odd.mp hev) hn]

end VOA
