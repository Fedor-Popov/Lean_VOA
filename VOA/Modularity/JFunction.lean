/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LambertSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The modular `j`-function as a formal `q`-series

Gannon's main corollary is `χ_{V♮}(τ) = J(τ)`.  Mathlib has **no** `j`-invariant, so the
right-hand side of that statement is not available there.  This file builds it at the
**formal** level, where the formal modularity layer lives: `E₄`, `E₆`, `Δ`, and

  `j = E₄³/Δ`,  `J = j − 744`.

## The pole, and how it is handled

`j` has a simple pole at the cusp (`Δ = q − 24q² + ⋯` vanishes to order one), so `j` is not a power
series.  Rather than introduce Laurent series, we record `j` through its **shift**

  `jShift := q·j = E₄³/(Δ/q)`,

an honest `PowerSeries ℂ` — `Δ/q` has constant term `1`, hence is a unit.  Then
`[qⁿ] jShift = [q^{n−1}] j`, so `jShift = 1 + 744q + 196884q² + ⋯` encodes `j` exactly, and
`JShift = jShift − 744·q` encodes `J = j − 744`.

## What is proved here
* `E4Series`, `E6Series` — the normalised Eisenstein series of weight `4` and `6`, with their
  classical coefficients `1 + 240σ₃(n)qⁿ` and `1 − 504σ₅(n)qⁿ`;
* `deltaSeries := (E₄³ − E₆²)/1728`, and `constantCoeff_deltaSeries` (`Δ` has no constant term)
  and `coeff_one_deltaSeries` (`[q¹]Δ = 1`) — the two facts that make `Δ/q` a unit;
* `deltaOverQ`, `deltaOverQ_isUnit`, and hence `jShift`, `JShift`, with `constantCoeff_jShift`.

## What is *not* proved
The higher coefficients (`[q²] jShift = 196884` and beyond) are pure arithmetic in this setup but
are not computed here; and **uniqueness** — that `J` is the unique hauptmodul — is an *analytic*
statement (Mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` at weight `0`), so it becomes
available only after the analytic upgrade of `ConvergenceBridge`.  See the residual.

## References
* Gannon §2.2, §5.3.5; Serre, *A Course in Arithmetic* VII; Apostol, *Modular Functions* Ch. 1.
-/

namespace VOA

open scoped BigOperators

/-! ## A `[q¹]` product rule -/

/-- The degree-one coefficient of a product. -/
theorem coeff_one_mul' (f g : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 1 (f * g)
      = PowerSeries.constantCoeff f * PowerSeries.coeff (R := ℂ) 1 g
        + PowerSeries.coeff (R := ℂ) 1 f * PowerSeries.constantCoeff g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

/-! ## The Eisenstein series of weight 4 and 6 -/

/-- `E₄ = 1 + 240·Σ σ₃(n)qⁿ`. -/
noncomputable def E4Series : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * lambertCoeff 3 n

/-- `E₆ = 1 − 504·Σ σ₅(n)qⁿ`. -/
noncomputable def E6Series : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * lambertCoeff 5 n

@[simp] theorem constantCoeff_E4Series : PowerSeries.constantCoeff E4Series = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4Series, PowerSeries.coeff_mk, if_pos rfl]

@[simp] theorem constantCoeff_E6Series : PowerSeries.constantCoeff E6Series = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, E6Series, PowerSeries.coeff_mk, if_pos rfl]

@[simp] theorem coeff_one_E4Series : PowerSeries.coeff (R := ℂ) 1 E4Series = 240 := by
  rw [E4Series, PowerSeries.coeff_mk, if_neg one_ne_zero, lambertCoeff_one, mul_one]

@[simp] theorem coeff_one_E6Series : PowerSeries.coeff (R := ℂ) 1 E6Series = -504 := by
  rw [E6Series, PowerSeries.coeff_mk, if_neg one_ne_zero, lambertCoeff_one, mul_one]

/-! ## The discriminant `Δ = (E₄³ − E₆²)/1728` -/

/-- The modular discriminant, in its Eisenstein form `Δ = (E₄³ − E₆²)/1728`. -/
noncomputable def deltaSeries : PowerSeries ℂ :=
  (1728 : ℂ)⁻¹ • (E4Series ^ 3 - E6Series ^ 2)

/-- `Δ` has **no constant term** — it vanishes at the cusp. -/
@[simp] theorem constantCoeff_deltaSeries : PowerSeries.constantCoeff deltaSeries = 0 := by
  have hcc : PowerSeries.constantCoeff (E4Series ^ 3 - E6Series ^ 2) = 0 := by
    rw [map_sub, map_pow, map_pow, constantCoeff_E4Series, constantCoeff_E6Series, one_pow,
      one_pow, sub_self]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deltaSeries, PowerSeries.coeff_smul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hcc, smul_zero]

/-- `[q¹]Δ = 1` — the discriminant vanishes to order **exactly** one.

`[q¹]E₄³ = 3·240 = 720` and `[q¹]E₆² = 2·(−504) = −1008`, so `[q¹](E₄³ − E₆²) = 1728`. -/
@[simp] theorem coeff_one_deltaSeries : PowerSeries.coeff (R := ℂ) 1 deltaSeries = 1 := by
  have h4 : PowerSeries.coeff (R := ℂ) 1 (E4Series ^ 3) = 720 := by
    rw [pow_succ, pow_succ, pow_one, coeff_one_mul', coeff_one_mul', map_mul,
      constantCoeff_E4Series, coeff_one_E4Series]
    ring
  have h6 : PowerSeries.coeff (R := ℂ) 1 (E6Series ^ 2) = -1008 := by
    rw [pow_succ, pow_one, coeff_one_mul', constantCoeff_E6Series, coeff_one_E6Series]
    ring
  rw [deltaSeries, PowerSeries.coeff_smul, map_sub, h4, h6]
  norm_num

/-! ## `Δ/q`, and the `j`-function -/

/-- `Δ = q·(Δ/q)`: the cofactor of the simple zero of `Δ` at the cusp. -/
noncomputable def deltaOverQ : PowerSeries ℂ :=
  Classical.choose (PowerSeries.X_dvd_iff.mpr constantCoeff_deltaSeries)

theorem deltaSeries_eq : deltaSeries = PowerSeries.X * deltaOverQ :=
  Classical.choose_spec (PowerSeries.X_dvd_iff.mpr constantCoeff_deltaSeries)

/-- `Δ/q` has constant term `1`, hence is a **unit** — this is exactly the statement that the zero
of `Δ` at the cusp is simple, and it is what lets `j = E₄³/Δ` be written as `q⁻¹·(power series)`. -/
@[simp] theorem constantCoeff_deltaOverQ : PowerSeries.constantCoeff deltaOverQ = 1 := by
  have h := coeff_one_deltaSeries
  rw [deltaSeries_eq, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff] at h
  exact h

theorem deltaOverQ_isUnit : IsUnit deltaOverQ :=
  PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [constantCoeff_deltaOverQ]; exact isUnit_one)

/-- `Δ/q` as a unit of `ℂ⟦q⟧`. -/
noncomputable def deltaOverQUnit : (PowerSeries ℂ)ˣ := deltaOverQ_isUnit.unit

@[simp] theorem deltaOverQUnit_coe : (deltaOverQUnit : PowerSeries ℂ) = deltaOverQ :=
  IsUnit.unit_spec _

/-- **`q·j`**, an honest power series: `jShift = E₄³/(Δ/q)`, so that `j = q⁻¹·jShift`.

`[qⁿ] jShift = [q^{n−1}] j`; in particular `jShift = 1 + 744q + 196884q² + ⋯`. -/
noncomputable def jShift : PowerSeries ℂ :=
  E4Series ^ 3 * ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

/-- `jShift` has constant term `1` — i.e. `j` has a **simple pole** with residue `1` at the cusp,
which is the normalisation that makes `j` the hauptmodul. -/
@[simp] theorem constantCoeff_jShift : PowerSeries.constantCoeff jShift = 1 := by
  have hinv : PowerSeries.constantCoeff
      ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 := by
    have h : ((deltaOverQUnit : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
        * ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 := congrArg (PowerSeries.constantCoeff (R := ℂ)) h
    rw [map_mul, map_one, deltaOverQUnit_coe, constantCoeff_deltaOverQ, one_mul] at h2
    exact h2
  rw [jShift, map_mul, map_pow, constantCoeff_E4Series, one_pow, one_mul, hinv]

/-- **`q·J`** for `J = j − 744`: subtracting the constant `744` from `j` subtracts `744q` from
`q·j`. -/
noncomputable def JShift : PowerSeries ℂ := jShift - (744 : ℂ) • PowerSeries.X

@[simp] theorem constantCoeff_JShift : PowerSeries.constantCoeff JShift = 1 := by
  have hX : PowerSeries.constantCoeff ((744 : ℂ) • PowerSeries.X : PowerSeries ℂ) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_X, smul_zero]
  rw [JShift, map_sub, constantCoeff_jShift, hX, sub_zero]

/-- `J` and `j` differ by the constant `744`, i.e. their shifts differ by `744q`. -/
theorem JShift_add : JShift + (744 : ℂ) • PowerSeries.X = jShift := by
  rw [JShift, sub_add_cancel]

/-! ## The Moonshine coefficient `[q²] jShift = 196884` -/

/-- The degree-two coefficient of a product. -/
theorem coeff_two_mul' (f g : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 2 (f * g)
      = PowerSeries.coeff (R := ℂ) 0 f * PowerSeries.coeff (R := ℂ) 2 g
        + PowerSeries.coeff (R := ℂ) 1 f * PowerSeries.coeff (R := ℂ) 1 g
        + PowerSeries.coeff (R := ℂ) 2 f * PowerSeries.coeff (R := ℂ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- The degree-three coefficient of a product. -/
theorem coeff_three_mul' (f g : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 3 (f * g)
      = PowerSeries.coeff (R := ℂ) 0 f * PowerSeries.coeff (R := ℂ) 3 g
        + PowerSeries.coeff (R := ℂ) 1 f * PowerSeries.coeff (R := ℂ) 2 g
        + PowerSeries.coeff (R := ℂ) 2 f * PowerSeries.coeff (R := ℂ) 1 g
        + PowerSeries.coeff (R := ℂ) 3 f * PowerSeries.coeff (R := ℂ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem lambertCoeff_three_two : lambertCoeff 3 2 = 9 := by
  rw [lambertCoeff_eq_sigma, show ArithmeticFunction.sigma 3 2 = 9 from by decide]; norm_num
theorem lambertCoeff_three_three : lambertCoeff 3 3 = 28 := by
  rw [lambertCoeff_eq_sigma, show ArithmeticFunction.sigma 3 3 = 28 from by decide]; norm_num
theorem lambertCoeff_five_two : lambertCoeff 5 2 = 33 := by
  rw [lambertCoeff_eq_sigma, show ArithmeticFunction.sigma 5 2 = 33 from by decide]; norm_num
theorem lambertCoeff_five_three : lambertCoeff 5 3 = 244 := by
  rw [lambertCoeff_eq_sigma, show ArithmeticFunction.sigma 5 3 = 244 from by decide]; norm_num

theorem coeff_zero_E4Series : PowerSeries.coeff (R := ℂ) 0 E4Series = 1 := by
  rw [E4Series, PowerSeries.coeff_mk, if_pos rfl]
theorem coeff_two_E4Series : PowerSeries.coeff (R := ℂ) 2 E4Series = 2160 := by
  rw [E4Series, PowerSeries.coeff_mk, if_neg (by norm_num), lambertCoeff_three_two]; norm_num
theorem coeff_three_E4Series : PowerSeries.coeff (R := ℂ) 3 E4Series = 6720 := by
  rw [E4Series, PowerSeries.coeff_mk, if_neg (by norm_num), lambertCoeff_three_three]; norm_num
theorem coeff_zero_E6Series : PowerSeries.coeff (R := ℂ) 0 E6Series = 1 := by
  rw [E6Series, PowerSeries.coeff_mk, if_pos rfl]
theorem coeff_two_E6Series : PowerSeries.coeff (R := ℂ) 2 E6Series = -16632 := by
  rw [E6Series, PowerSeries.coeff_mk, if_neg (by norm_num), lambertCoeff_five_two]; norm_num
theorem coeff_three_E6Series : PowerSeries.coeff (R := ℂ) 3 E6Series = -122976 := by
  rw [E6Series, PowerSeries.coeff_mk, if_neg (by norm_num), lambertCoeff_five_three]; norm_num

/-- `E₄³ = 1 + 720q + 179280q² + 16954560q³ + ⋯`. -/
theorem coeff_E4_cube :
    PowerSeries.coeff (R := ℂ) 0 (E4Series ^ 3) = 1
    ∧ PowerSeries.coeff (R := ℂ) 1 (E4Series ^ 3) = 720
    ∧ PowerSeries.coeff (R := ℂ) 2 (E4Series ^ 3) = 179280
    ∧ PowerSeries.coeff (R := ℂ) 3 (E4Series ^ 3) = 16954560 := by
  have h0 := coeff_zero_E4Series
  have h1 := coeff_one_E4Series
  have h2 := coeff_two_E4Series
  have h3 := coeff_three_E4Series
  have hsq0 : PowerSeries.coeff (R := ℂ) 0 (E4Series ^ 2) = 1 := by
    rw [pow_two, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_E4Series,
      one_mul]
  have hsq1 : PowerSeries.coeff (R := ℂ) 1 (E4Series ^ 2) = 480 := by
    rw [pow_two, coeff_one_mul', constantCoeff_E4Series, h1]; norm_num
  have hsq2 : PowerSeries.coeff (R := ℂ) 2 (E4Series ^ 2) = 61920 := by
    rw [pow_two, coeff_two_mul', h0, h1, h2]; norm_num
  have hsq3 : PowerSeries.coeff (R := ℂ) 3 (E4Series ^ 2) = 1050240 := by
    rw [pow_two, coeff_three_mul', h0, h1, h2, h3]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hsq0, constantCoeff_E4Series, one_mul]
  · rw [pow_succ, coeff_one_mul', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hsq0, hsq1,
      constantCoeff_E4Series, h1]; norm_num
  · rw [pow_succ, coeff_two_mul', hsq0, hsq1, hsq2, h0, h1, h2]; norm_num
  · rw [pow_succ, coeff_three_mul', hsq0, hsq1, hsq2, hsq3, h0, h1, h2, h3]; norm_num

/-- `E₆² = 1 − 1008q + 220752q² + 16519104q³ + ⋯`. -/
theorem coeff_E6_sq :
    PowerSeries.coeff (R := ℂ) 2 (E6Series ^ 2) = 220752
    ∧ PowerSeries.coeff (R := ℂ) 3 (E6Series ^ 2) = 16519104 := by
  have h0 := coeff_zero_E6Series
  have h1 := coeff_one_E6Series
  have h2 := coeff_two_E6Series
  have h3 := coeff_three_E6Series
  refine ⟨?_, ?_⟩
  · rw [pow_two, coeff_two_mul', h0, h1, h2]; norm_num
  · rw [pow_two, coeff_three_mul', h0, h1, h2, h3]; norm_num

/-- `Δ = q − 24q² + 252q³ + ⋯`. -/
theorem coeff_deltaSeries_two_three :
    PowerSeries.coeff (R := ℂ) 2 deltaSeries = -24
    ∧ PowerSeries.coeff (R := ℂ) 3 deltaSeries = 252 := by
  obtain ⟨-, -, h42, h43⟩ := coeff_E4_cube
  obtain ⟨h62, h63⟩ := coeff_E6_sq
  refine ⟨?_, ?_⟩
  · rw [deltaSeries, PowerSeries.coeff_smul, map_sub, h42, h62]; norm_num
  · rw [deltaSeries, PowerSeries.coeff_smul, map_sub, h43, h63]; norm_num

/-- `Δ/q = 1 − 24q + 252q² + ⋯`. -/
theorem coeff_deltaOverQ_one_two :
    PowerSeries.coeff (R := ℂ) 1 deltaOverQ = -24
    ∧ PowerSeries.coeff (R := ℂ) 2 deltaOverQ = 252 := by
  obtain ⟨h2, h3⟩ := coeff_deltaSeries_two_three
  rw [deltaSeries_eq, PowerSeries.coeff_succ_X_mul] at h2 h3
  exact ⟨h2, h3⟩

/-- `(Δ/q)⁻¹ = 1 + 24q + 324q² + ⋯`. -/
theorem coeff_deltaOverQ_inv :
    PowerSeries.coeff (R := ℂ) 0 ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1
    ∧ PowerSeries.coeff (R := ℂ) 1 ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 24
    ∧ PowerSeries.coeff (R := ℂ) 2 ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 324 := by
  set u : PowerSeries ℂ := ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) with hu
  have hprod : deltaOverQ * u = 1 := by
    rw [hu, ← deltaOverQUnit_coe, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨hd1, hd2⟩ := coeff_deltaOverQ_one_two
  have hd0 : PowerSeries.coeff (R := ℂ) 0 deltaOverQ = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_deltaOverQ]
  have hu0 : PowerSeries.coeff (R := ℂ) 0 u = 1 := by
    have h := congrArg (PowerSeries.coeff (R := ℂ) 0) hprod
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_deltaOverQ, one_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_one] at h
    exact h
  have hu1 : PowerSeries.coeff (R := ℂ) 1 u = 24 := by
    have h := congrArg (PowerSeries.coeff (R := ℂ) 1) hprod
    rw [coeff_one_mul', constantCoeff_deltaOverQ, hd1, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hu0, PowerSeries.coeff_one, if_neg one_ne_zero] at h
    linear_combination h
  have hu2 : PowerSeries.coeff (R := ℂ) 2 u = 324 := by
    have h := congrArg (PowerSeries.coeff (R := ℂ) 2) hprod
    rw [coeff_two_mul', hd0, hd1, hd2, hu0, hu1, PowerSeries.coeff_one, if_neg (by norm_num)] at h
    linear_combination h
  exact ⟨hu0, hu1, hu2⟩

/-- **THE MOONSHINE COEFFICIENT**: `[q²] jShift = 196884`, i.e. `j = q⁻¹ + 744 + 196884q + ⋯`
— `196884 = 196883 + 1`, McKay's observation. -/
theorem coeff_two_jShift : PowerSeries.coeff (R := ℂ) 2 jShift = 196884 := by
  obtain ⟨h0, h1, h2, -⟩ := coeff_E4_cube
  obtain ⟨hu0, hu1, hu2⟩ := coeff_deltaOverQ_inv
  rw [jShift, coeff_two_mul', h0, h1, h2, hu0, hu1, hu2]
  norm_num

/-- `[q²] JShift = 196884` as well: `J = j − 744` differs from `j` only in the constant term. -/
theorem coeff_two_JShift : PowerSeries.coeff (R := ℂ) 2 JShift = 196884 := by
  rw [JShift, map_sub, coeff_two_jShift, PowerSeries.coeff_smul, PowerSeries.coeff_X,
    if_neg (by norm_num), smul_zero, sub_zero]

/-! ## Residual

* **The higher coefficients** beyond `[q²]` (`21493760`, …) are the same arithmetic.
* **Uniqueness of the hauptmodul.**  That a weight-`0` modular function, holomorphic on `ℍ` with a
  simple pole at the cusp and no constant term, is *unique* — hence equal to `J` — is Mathlib's
  `CuspForm.rank_eq_zero_of_weight_lt_twelve` at weight `0`.  That statement is about **analytic**
  modular forms, so it applies only after the `FormalQSeries → ℍ` upgrade of `ConvergenceBridge`;
  the formal `J` built here has no analytic content on its own.
* **`χ_{V♮} = J` via Zhu's theorem.**  Not done here.  `V♮` is built in `VOA/Moonshine/`, where
  `χ_{V♮} = J` is proved by a direct character computation
  (`finrank_gradingNat_eq_coeff_JShift`), not through Zhu's theorem.
  `GradedDimEqJAdd` (in `ZhuTheorem`) is the abstract statement, and `JShift` is a concrete
  candidate to instantiate its `J`.
-/

end VOA
