/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Character
import VOA.Modules.C2Cofinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# One-point functions and chiral blocks on the torus  (Gannon §5.3.4, pp. 339–342)

The geometric setup behind modularity: VOA characters are **chiral blocks on the
torus** `ℂ/(ℤ + ℤτ)`, and the mapping class group `SL₂(ℤ)` acts on them. This file sets
up the change-of-coordinate operators and the `n`-point blocks; `ZhuTheorem` proves the
modularity.

* **Change of coordinates** (eq. 5.3.15): a holomorphic `f` with `f(0)=0` acts on
  vertex operators by `Y(v,z) ↦ T_f ∘ Y(v,z) ∘ T_f⁻¹`, where `T_f = exp(∑_{n≥0} aₙ Lₙ)`
  for `f(z) = exp(∑ aₙ z^{n+1} d/dz) z`. On primaries `T_f Y(v,z) T_f⁻¹ = Y(v,z) f'(z)ᵏ`
  (5.3.15d); on the stress tensor the **Schwarzian** `{f,z}` appears with coefficient
  `c/12` (5.3.15e–f).
* **The map to the annulus/torus**: `w = f(z) = e^{2πiz} - 1`. Then
  `ω_f = 4π²(ω - c/24)` (5.3.16a), giving the famous `-c/24` shift; the squared modes
  `L[n] = (ω_f)₍ₙ₊₁₎` satisfy `L[-1] = 2πi(L₋₁+L₀)` (5.3.16c) and `L'_n = L[n] - δ_{n,0} c/24`.
* **Partition function** `𝒵(τ) = tr_ℋ q^{L₀-c/24} q̄^{L̄₀-c̄/24}`, required invariant under
  `SL₂(ℤ)`; the chiral part is `tr_M q^{L₀-c/24} = χ_M(τ)` (Gannon p. 341).
* **`n`-point chiral blocks** (eq. 5.3.17a): for `L[0]`-homogeneous `uⁱ ∈ 𝒱_{[kᵢ]}`,
  `e^{2πi z₁ k₁}⋯ tr_M Y_M(u¹, e^{2πiz₁})⋯Y_M(uⁿ, e^{2πizₙ}) q^{L₀-c/24}`, period `1` in
  each `zᵢ`. The one-point block is `χ_M(τ, u)` (eq. 5.3.17b), "hence the name."

## Design / target declarations

```lean
variable {𝒱} [...] (W : VertexOperatorAlgebra 𝒱)

/-- The change-of-coordinate operator `T_f` (Gannon 5.3.15). -/
noncomputable def changeCoord (f : ...) : 𝒱 ≃ₗ[ℂ] 𝒱 := ...

/-- The squared (torus) Virasoro modes `L[n] = (ω_f)₍ₙ₊₁₎` for `w = e^{2πiz}-1`. -/
noncomputable def Lsq (n : ℤ) : Module.End ℂ 𝒱 := ...

theorem Lsq_neg_one : Lsq W (-1) = (2 * Real.pi * Complex.I) • (W.L (-1) + W.L 0) := ...  -- 5.3.16c

/-- The `n`-point chiral block on the torus (Gannon 5.3.17a). -/
noncomputable def chiralBlock {M} (N : Module W M) (u : Fin n → 𝒱) : ... := ...
```

## Dependencies
* `VOA.Modules.Character`, `VOA.Modules.C2Cofinite`.

## Status
This file supplies the base square-bracket and torus objects; the
companion modules `SquareBracketWitt`, `SquareBracketVirasoro`, `GelfandFuks`,
`SquareBracketGrading`, `Schwarzian`, `ChangeCoord`, and `ChiralBlock` close the listed row targets.
All are `sorry`-free, axiom-clean, and `pbw`-free.  Scoped footnote only: the full conjugation laws
5.3.15d–f relating `changeCoord` to `Y` remain open, but are not used by `ZhuTheorem`; the required
square-bracket Virasoro relation is proved independently.

## References
* Gannon §5.3.4, eqs. (5.3.15)–(5.3.17); Zhu [574]; Huang [295]; di Francesco–Mathieu–
  Sénéchal (CFT).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## GOAL 1 (building blocks) — the shifted conformal vector and the graded exponential `e^{zL₀}`

The square-bracket structure (Gannon 5.3.15) is the reparametrization `Y[v,z] = Y(e^{zL₀}v, e^z−1)`.
Its two ingredients are the **`c/24`-shifted conformal vector** `ω̃ = ω − (c/24)𝟙` (Gannon 5.3.16a) and
the **graded exponential** `e^{zL₀}` — a semisimple (block-scalar) operator, so built from the `𝒱`-grading
`L₀ = k` on `𝒱ₖ` (`L_zero_grading`) rather than from the locally-nilpotent `expEquiv`.  On a homogeneous
`v ∈ 𝒱ₖ`, `e^{zL₀}v = e^{zk}v` (`gradedExpL0_of_mem_grading`).

These are the building blocks used below to construct all square-bracket modes.  The companion
modules named in the status section prove the torus Virasoro relation, Schwarzian calculation,
change-of-coordinate equivalence, grading, and full `n`-point chiral block interface. -/

section
variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `c/24`-shifted conformal vector** `ω̃ = ω − (c/24)·𝟙` (Gannon 5.3.16a): the conformal vector
of the theory in the torus coordinate `w = e^{2πiz}−1`, whose `−c/24` produces the modular shift. -/
noncomputable def torusConformalVector : 𝒱 :=
  W.conformalVector - (W.centralCharge / 24) • W.vacuum

/-- The weight-`k` slice of `e^{zL₀}`: the scalar `e^{zk}` on `𝒱ₖ`. -/
noncomputable def gradedExpL0Family (z : ℂ) (k : ℤ) : (W.grading k) →ₗ[ℂ] 𝒱 :=
  (Complex.exp (z * (k : ℂ))) • (W.grading k).subtype

/-- **The graded exponential `e^{zL₀}`** (Gannon 5.3.15): the block-scalar operator acting as `e^{zk}`
on `𝒱ₖ`, assembled over the (finite) `𝒱`-grade decomposition (mirrors `Modules.Character.oMod`). -/
noncomputable def gradedExpL0 (z : ℂ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (gradedExpL0Family W z)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- **`e^{zL₀}v = e^{zk}v` on a homogeneous `v ∈ 𝒱ₖ`** (`L₀ = k` there). -/
theorem gradedExpL0_of_mem_grading (z : ℂ) {k : ℤ} (v : 𝒱) (hv : v ∈ W.grading k) :
    gradedExpL0 W z v = Complex.exp (z * (k : ℂ)) • v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : gradedExpL0 W z v = gradedExpL0Family W z k ⟨v, hv⟩ := by
    change (DFinsupp.lsum ℂ (gradedExpL0Family W z)) (DirectSum.decompose W.grading v) = _
    rw [DirectSum.decompose_of_mem W.grading hv]
    exact DFinsupp.lsum_single ℂ (gradedExpL0Family W z) k ⟨v, hv⟩
  rw [hcollapse, gradedExpL0Family, LinearMap.smul_apply, Submodule.coe_subtype]

end

/-! ### The square-bracket coefficients (engine-verified closed form)

Zhu's square-bracket vertex operator `Y[v,z] = Y(e^{zL₀}v, e^z−1)` needs **no** general power-series
substitution: for homogeneous `v ∈ 𝒱ₖ`, the change of variable `w = e^z−1` gives the explicit residue
`v[m] = Res_w Y(v,w)(1+w)^{k−1}(log(1+w))^m = Σᵢ c(k,m,i)·v₍ᵢ₎`, a **locally finite** combination of the
ordinary modes (`(log(1+w))^m` has lowest order `w^m`, and `v₍ᵢ₎` lowers the grade to `⊥` for large `i`).
The coefficients `c(k,m,i) = [wⁱ](1+w)^{k−1}(log(1+w))^m` are Stirling-of-the-first-kind combinations.

Verified on the free-boson / Virasoro engines (`certificates/mathematica/sqbracket_verify.wl`, SMAX=14):
the coefficient table; `L[−1] = L₋₁ + L₀` (i.e. `d[-1,·] = δ₋₁ + δ₀` where `d[n,m] = c(2,n+1,m+1)`);
and — for `L[n] = ω[n+1] = Σₘ d[n,m]Lₘ` — the full **Virasoro relations with the same central charge**:
`Σ_a d[m,a]d[n,j−a](a−(j−a)) = (m−n)d[m+n,j]` (all `j`) and `Σ_a d[m,a]d[n,−a](a³−a) = δ_{m+n,0}(m³−m)`. -/

/-- `log(1+w) = Σ_{i≥1} (−1)^{i+1}/i · wⁱ` as a formal power series over `ℂ`. -/
noncomputable def logOnePlusXSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun i => if i = 0 then 0 else (-1 : ℂ) ^ (i + 1) / (i : ℂ))

/-! ### The unit `1 + w` (so `(1+w)^{k−1}` makes sense for the vacuum `k = 0`)

⚠ **The `k = 0` truncation defect.** Writing `(1 + w) ^ (k − 1)` with `k : ℕ` uses **truncated**
subtraction, so at the vacuum `k = 0` it computes `(1+w)^0 = 1` instead of the required `(1+w)^{−1}`
(the square bracket of `𝟙` sits at weight `0`).  `1 + w` has constant coefficient `1`, hence is a
**unit** of `ℂ⟦w⟧`; using the unit `zpow` `((1+w) : (ℂ⟦w⟧)ˣ) ^ ((k : ℤ) − 1)` gives the honest
`(1+w)^{k−1}` for **every** `k : ℕ`, agreeing with the ordinary power for `k ≥ 1`. -/

theorem onePlusX_isUnit : IsUnit (1 + PowerSeries.X : PowerSeries ℂ) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [map_add, map_one, PowerSeries.constantCoeff_X, add_zero]; exact isUnit_one)

/-- `1 + w` as a unit of `ℂ⟦w⟧` (so `(1+w)^{k−1}` makes sense for `k = 0` via `zpow`). -/
noncomputable def onePlusXUnit : (PowerSeries ℂ)ˣ := onePlusX_isUnit.unit

theorem onePlusXUnit_coe : (onePlusXUnit : PowerSeries ℂ) = 1 + PowerSeries.X :=
  IsUnit.unit_spec _

/-- For `k ≥ 1` the unit `zpow` is the ordinary power `(1+w)^{k−1}`. -/
theorem onePlusXUnit_zpow_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    (↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) = (1 + PowerSeries.X) ^ (k - 1) := by
  have hkz : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [hkz, zpow_natCast, Units.val_pow_eq_pow_val, onePlusXUnit_coe]

/-- **The Zhu square-bracket coefficient** `c(k,m,i) = [wⁱ] (1+w)^{k−1}(log(1+w))^m` (the
power-series case `m, i : ℕ`; engine-verified), with `(1+w)^{k−1}` taken as the **unit `zpow`** so
that the vacuum case `k = 0` correctly reads `(1+w)^{−1}` (see the `k = 0` note above).  On
homogeneous `v ∈ 𝒱ₖ` the square-bracket mode is `v[m] = Σᵢ c(k,m,i)·v₍ᵢ₎`.  For `k ≥ 1` at `m = 0`
it is the binomial `(k−1).choose i` (`sqBracketCoeff_zero`). -/
noncomputable def sqBracketCoeff (k m i : ℕ) : ℂ :=
  PowerSeries.coeff (R := ℂ) i
    ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) * logOnePlusXSeries ^ m)

/-- **`c(k,0,i) = C(k−1, i)` for `k ≥ 1`** — at `m = 0` the log factor is `1`, so the coefficient is
the plain binomial (this is the source of `L[−1] = L₋₁ + L₀`: `d[-1,m] = c(2,0,m+1) = C(1,m+1)`).
Requires `k ≥ 1`; at `k = 0` the coefficient is instead `[wⁱ](1+w)^{−1} = (−1)ⁱ`. -/
theorem sqBracketCoeff_zero (k i : ℕ) (hk : 1 ≤ k) :
    sqBracketCoeff k 0 i = ((k - 1).choose i : ℂ) := by
  have hc : ((1 + PowerSeries.X : PowerSeries ℂ) ^ (k - 1))
      = (((1 + Polynomial.X : Polynomial ℂ) ^ (k - 1) : Polynomial ℂ) : PowerSeries ℂ) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [sqBracketCoeff, pow_zero, mul_one, onePlusXUnit_zpow_of_one_le hk, hc,
    Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-! ### GOAL A′ — negative (raising) modes via the unit `u = log(1+w)/w`

`log(1+w) = w·u(w)` with `u(0) = 1`, so `u` is a **unit** in `ℂ⟦w⟧`; hence `(log(1+w))^m = w^m·u^m` is
a genuine power series for **every** `m : ℤ` (`zpow` of the unit).  The all-modes coefficient is then
`c(k,m,i) = [w^{i−m}]((1+w)^{k−1}·u^m)` (`sqBracketCoeffZ`), agreeing with `sqBracketCoeff` for `m ≥ 0`
(`sqBracketCoeffZ_of_nonneg`).  Engine-verified for `m < 0` (`certificates/mathematica/sqbracket_neg_verify.wl`). -/

/-- `u = log(1+w)/w = Σ_{i≥0} (−1)ⁱ/(i+1) · wⁱ`, constant term `1` (a unit). -/
noncomputable def uSeries : PowerSeries ℂ := PowerSeries.mk (fun i => (-1 : ℂ) ^ i / (i + 1 : ℂ))

/-- `log(1+w) = w · u`. -/
theorem logOnePlusX_eq_X_mul_u : logOnePlusXSeries = PowerSeries.X * uSeries := by
  ext i
  rcases i with _ | j
  · rw [PowerSeries.coeff_zero_X_mul]
    simp [logOnePlusXSeries]
  · rw [logOnePlusXSeries, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero j),
      PowerSeries.coeff_succ_X_mul, uSeries, PowerSeries.coeff_mk]
    congr 1
    · rw [pow_succ, pow_succ]; ring
    · push_cast; ring

theorem uSeries_isUnit : IsUnit uSeries :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [uSeries, PowerSeries.constantCoeff_mk]; norm_num)

/-- `u` as a unit of `ℂ⟦w⟧` (so `u^m` makes sense for `m : ℤ`). -/
noncomputable def uUnit : (PowerSeries ℂ)ˣ := uSeries_isUnit.unit

theorem uUnit_coe : (uUnit : PowerSeries ℂ) = uSeries := IsUnit.unit_spec _

/-- **The all-modes square-bracket coefficient** `c(k,m,i) = [w^{i−m}]((1+w)^{k−1}·u^m)`, `m i : ℤ`,
with `(1+w)^{k−1}` the unit `zpow` (so the vacuum case `k = 0` reads `(1+w)^{−1}`). -/
noncomputable def sqBracketCoeffZ (k : ℕ) (m i : ℤ) : ℂ :=
  if 0 ≤ i - m then
    PowerSeries.coeff (R := ℂ) (i - m).toNat
      ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ))
  else 0

/-- `↑(uUnit^m) = uᵐ` for a natural `m` (so the all-modes coefficient extends the `ℕ` one). -/
theorem uUnit_zpow_natCast (m : ℕ) : (↑(uUnit ^ (m : ℤ)) : PowerSeries ℂ) = uSeries ^ m := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, uUnit_coe]

/-- **`sqBracketCoeffZ` agrees with `sqBracketCoeff` on `m ≥ 0`** — nothing already banked breaks. -/
theorem sqBracketCoeffZ_of_nonneg (k m i : ℕ) :
    sqBracketCoeffZ k (m : ℤ) (i : ℤ) = sqBracketCoeff k m i := by
  have hQ : sqBracketCoeff k m i
      = PowerSeries.coeff (R := ℂ) i
          (PowerSeries.X ^ m
            * ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) * uSeries ^ m)) := by
    rw [sqBracketCoeff, logOnePlusX_eq_X_mul_u, mul_pow]
    congr 1
    ring
  rw [sqBracketCoeffZ, hQ, PowerSeries.coeff_X_pow_mul']
  by_cases h : m ≤ i
  · rw [if_pos (by omega), if_pos h, uUnit_zpow_natCast,
      show ((i : ℤ) - (m : ℤ)).toNat = i - m from by omega]
  · rw [if_neg (by omega), if_neg h]

/-! ### GOAL A — the square-bracket mode operator `v[n]` (lowering modes)

For homogeneous `v ∈ 𝒱ₖ` and `n : ℕ`, the square-bracket mode is `v[n] = Σᵢ c(k,n,i)·v₍ᵢ₎`, a
**locally finite** sum: `sqCoeffZ k n i = 0` for `i < 0` (the coefficient has no negative-power terms
for `n ≥ 0`), and `v₍ᵢ₎ = mode (Y v) i = 0` for `i ≥ N` (VA5 `regularity`).  So `∑ᶠ i` is a genuine
`finsum`, and `vSqHom v k n` is a `ℂ`-linear operator.  The integer-indexed raising modes are
constructed below as `sqBracketCoeffZ` and `vSqZ`. -/

section
variable (W : VertexOperatorAlgebra 𝒱)

/-- The mode-`i` (integer) square-bracket coefficient for a lowering mode `n : ℕ` (`0` for `i < 0`). -/
noncomputable def sqCoeffZ (k n : ℕ) (i : ℤ) : ℂ :=
  if 0 ≤ i then sqBracketCoeff k n i.toNat else 0

theorem sqCoeffZ_of_neg (k n : ℕ) {i : ℤ} (hi : i < 0) : sqCoeffZ k n i = 0 := by
  simp only [sqCoeffZ, not_le.mpr hi, if_false]

/-- The summand `i ↦ c(k,n,i)·v₍ᵢ₎x` has finite support: `c = 0` below `0`, and `v₍ᵢ₎x = 0` above `N`
(regularity). -/
theorem sqMode_support_finite (v : 𝒱) (k n : ℕ) (x : 𝒱) :
    (Function.support (fun i : ℤ => sqCoeffZ k n i • mode (W.Y v) i x)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity v x
  refine Set.Finite.subset (Set.finite_Ico 0 N) ?_
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hi (by rw [sqCoeffZ_of_neg k n (not_le.mp h), zero_smul])
  · by_contra h
    push_neg at h
    exact hi (by rw [hN i h, smul_zero])

/-- **The square-bracket mode operator** `v[n]` for a weight-`k` (homogeneous) `v` and lowering mode
`n : ℕ` — the locally-finite `finsum` `Σᵢ c(k,n,i)·v₍ᵢ₎`. -/
noncomputable def vSqHom (v : 𝒱) (k n : ℕ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := ∑ᶠ i : ℤ, sqCoeffZ k n i • mode (W.Y v) i x
  map_add' x y := by
    simp only [map_add, smul_add]
    rw [finsum_add_distrib (sqMode_support_finite W v k n x)
      (sqMode_support_finite W v k n y)]
  map_smul' c x := by
    show (∑ᶠ i : ℤ, sqCoeffZ k n i • mode (W.Y v) i (c • x))
      = c • ∑ᶠ i : ℤ, sqCoeffZ k n i • mode (W.Y v) i x
    rw [smul_finsum' c (sqMode_support_finite W v k n x)]
    refine finsum_congr (fun i => ?_)
    rw [map_smul, smul_comm]

@[simp] theorem vSqHom_apply (v : 𝒱) (k n : ℕ) (x : 𝒱) :
    vSqHom W v k n x = ∑ᶠ i : ℤ, sqCoeffZ k n i • mode (W.Y v) i x := rfl

/-! #### The all-modes operator `vSqZ` (`n : ℤ`), extending `vSqHom` -/

theorem sqBracketCoeffZ_of_lt (k : ℕ) {m i : ℤ} (h : i < m) : sqBracketCoeffZ k m i = 0 := by
  rw [sqBracketCoeffZ, if_neg (by omega)]

/-- `sqBracketCoeffZ` reduces to `sqCoeffZ` at a natural mode index (so `vSqZ` extends `vSqHom`). -/
theorem sqBracketCoeffZ_natCast (k m : ℕ) (i : ℤ) : sqBracketCoeffZ k (m : ℤ) i = sqCoeffZ k m i := by
  by_cases h : 0 ≤ i
  · rw [sqCoeffZ, if_pos h]
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [sqBracketCoeffZ_of_nonneg, Int.toNat_natCast]
  · push_neg at h
    rw [sqBracketCoeffZ_of_lt k (by omega), sqCoeffZ_of_neg k m h]

theorem sqModeZ_support_finite (v : 𝒱) (k : ℕ) (m : ℤ) (x : 𝒱) :
    (Function.support fun i : ℤ => sqBracketCoeffZ k m i • mode (W.Y v) i x).Finite := by
  obtain ⟨N, hN⟩ := W.regularity v x
  refine Set.Finite.subset (Set.finite_Ico m N) ?_
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  refine ⟨?_, ?_⟩
  · by_contra h; exact hi (by rw [sqBracketCoeffZ_of_lt k (not_le.mp h), zero_smul])
  · by_contra h; push_neg at h; exact hi (by rw [hN i h, smul_zero])

/-- **The all-modes square-bracket operator** `v[m]` (`m : ℤ`), extending `vSqHom` to raising modes. -/
noncomputable def vSqZ (v : 𝒱) (k : ℕ) (m : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (W.Y v) i x
  map_add' x y := by
    simp only [map_add, smul_add]
    rw [finsum_add_distrib (sqModeZ_support_finite W v k m x)
      (sqModeZ_support_finite W v k m y)]
  map_smul' c x := by
    show (∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (W.Y v) i (c • x))
      = c • ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (W.Y v) i x
    rw [smul_finsum' c (sqModeZ_support_finite W v k m x)]
    refine finsum_congr (fun i => ?_)
    rw [map_smul, smul_comm]

@[simp] theorem vSqZ_apply (v : 𝒱) (k : ℕ) (m : ℤ) (x : 𝒱) :
    vSqZ W v k m x = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (W.Y v) i x := rfl

/-- **`vSqZ` extends `vSqHom`** at natural mode indices. -/
theorem vSqZ_natCast (v : 𝒱) (k m : ℕ) : vSqZ W v k (m : ℤ) = vSqHom W v k m := by
  ext x
  rw [vSqZ_apply, vSqHom_apply]
  exact finsum_congr (fun i => by rw [sqBracketCoeffZ_natCast])

/-! ### GOAL B — `Lsq` and the identity `L[−1] = L₋₁ + L₀` (Gannon 5.3.16c) -/

/-- **`𝟙[0] = 0`** — the vacuum's `n=0` square-bracket mode vanishes (its only nonzero mode is `𝟙₍₋₁₎`,
where the coefficient `sqCoeffZ 0 0 (-1) = 0`). -/
theorem vSqHom_vacuum_zero : vSqHom W W.vacuum 0 0 = 0 := by
  ext x
  rw [vSqHom_apply, LinearMap.zero_apply]
  have h0 : (fun i : ℤ => sqCoeffZ 0 0 i • mode (W.Y W.vacuum) i x) = fun _ => 0 := by
    funext i
    rw [W.vacuum_Y, mode_one]
    rcases eq_or_ne i (-1) with rfl | hi
    · rw [sqCoeffZ_of_neg 0 0 (by norm_num), zero_smul]
    · rw [if_neg hi, LinearMap.zero_apply, smul_zero]
  rw [h0, finsum_zero]

/-- **`ω[0] = ω₍₀₎ + ω₍₁₎ = L₋₁ + L₀`** — the coefficient `sqCoeffZ 2 0 i` is supported on `{0,1}`
(both `= 1`), so the finsum collapses. -/
theorem vSqHom_omega_zero (x : 𝒱) :
    vSqHom W W.conformalVector 2 0 x
      = mode (W.Y W.conformalVector) 0 x + mode (W.Y W.conformalVector) 1 x := by
  rw [vSqHom_apply]
  have hsupp : (Function.support fun i : ℤ =>
      sqCoeffZ 2 0 i • mode (W.Y W.conformalVector) i x) ⊆ ↑({0, 1} : Finset ℤ) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    push_neg at h
    refine hi ?_
    rcases lt_trichotomy i 0 with hlt | rfl | hgt
    · rw [sqCoeffZ_of_neg 2 0 hlt, zero_smul]
    · exact absurd rfl h.1
    · rw [sqCoeffZ, if_pos (le_of_lt hgt), sqBracketCoeff_zero 2 _ (by norm_num),
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
  rw [finsum_eq_finset_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num)]
  have c0 : sqCoeffZ 2 0 0 = 1 := by
    rw [sqCoeffZ, if_pos le_rfl, sqBracketCoeff_zero 2 _ (by norm_num)]; norm_num
  have c1 : sqCoeffZ 2 0 1 = 1 := by
    rw [sqCoeffZ, if_pos (by norm_num), sqBracketCoeff_zero 2 _ (by norm_num)]; norm_num
  rw [c0, c1, one_smul, one_smul]

/-- **The torus (square-bracket) Virasoro modes** `L[n] = ω̃[n+1]` (Gannon 5.3.16a–c), the square
bracket of the **`c/24`-shifted** conformal vector `ω̃ = ω − (c/24)𝟙` (`torusConformalVector`), correct
for all `n : ℤ`.  Because `ω̃` is not homogeneous, `L[n]` is its two homogeneous pieces' square brackets:
`ω` at weight `2` and `𝟙` at weight `0`, i.e. `L[n] = ω[n+1] − (c/24)·𝟙[n+1]`.

⚠ **The `𝟙` term is essential — it is NOT a convention choice.**  The `ω`-only modes `ω[n+1]` satisfy
a *deformed* Virasoro algebra whose central term carries an extra Schwarzian anomaly
`−((m−n)/2)·δ_{m+n,−2}` (a genuine cocycle, engine-verified in exact rationals:
`Σ_a d[m,a]d[n,−a](a³−a) = (m³−m)δ_{m+n,0} − ((m−n)/2)δ_{m+n,−2}`).  The `−(c/24)·𝟙[n+1]` piece — which
is nonzero **only at `n = −2`** (`𝟙[−1] = id`) — cancels that anomaly exactly, restoring the **clean**
Virasoro algebra with central charge `c`.  (Dropping the `𝟙` term
would leave the anomaly.)  The modular `−c/24` of the trace `q^{L₀−c/24}`
(`torusOnePoint`) is a *separate* shift. -/
noncomputable def Lsq (n : ℤ) : Module.End ℂ 𝒱 :=
  vSqZ W W.conformalVector 2 (n + 1)
    - (W.centralCharge / 24) • vSqZ W W.vacuum 0 (n + 1)

/-- **`L[−1] = L₋₁ + L₀`** (Gannon 5.3.16c, in the `w = e^z−1` convention — Gannon's `2πi` is the
`w = e^{2πiz}−1` torus normalization).  The `ω̃` correction vanishes at `n = −1` (`𝟙[0] = 0`,
`vSqHom_vacuum_zero`), so only `ω[0] = ω₍₀₎ + ω₍₁₎ = L₋₁ + L₀` (`vSqHom_omega_zero`) survives. -/
theorem Lsq_neg_one : Lsq W (-1) = W.L (-1) + W.L 0 := by
  have h0 : ((-1 : ℤ) + 1) = ((0 : ℕ) : ℤ) := by norm_num
  have hvac : vSqZ W W.vacuum 0 ((-1 : ℤ) + 1) = 0 := by
    rw [h0, vSqZ_natCast, vSqHom_vacuum_zero]
  have hom : vSqZ W W.conformalVector 2 ((-1 : ℤ) + 1) = W.L (-1) + W.L 0 := by
    ext x
    simp only [h0, vSqZ_natCast, vSqHom_omega_zero, LinearMap.add_apply, VertexOperatorAlgebra.L]
    norm_num
  rw [show Lsq W (-1)
        = vSqZ W W.conformalVector 2 ((-1 : ℤ) + 1)
          - (W.centralCharge / 24) • vSqZ W W.vacuum 0 ((-1 : ℤ) + 1) from rfl,
    hvac, smul_zero, sub_zero, hom]

end

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## GOAL 3 — the torus one-point function and partition function (Gannon 5.3.13–14)

The formal `q`-series `Modules.Character.onePoint N v` is already the **torus one-point function**
`𝒵_M(v; τ) = tr_M (o(v) · q^{L₀ − c/24})`: its coefficient of `q^e` is the graded trace of the zero
mode `o(v)` on the weight space `M_{e + c/24}`, i.e. the `q^{L₀ − c/24}`-graded trace (`q = e^{2πiτ}`).
This section re-exposes it in the modular namespace with the partition function `𝒵(τ)` and records the
vacuum value `𝒵_M(𝟙; τ) = q^{−c/24} χ_M(τ)` and `ℂ`-linearity in `v`. -/

/-- **The torus one-point function** `𝒵_M(v; τ) = tr_M (o(v) q^{L₀ − c/24})` (Gannon 5.3.13), as a
formal `q`-series (the `−c/24` shift is carried in the weight index). -/
noncomputable def torusOnePoint (N : OrdVModule W M) (v : 𝒱) : FormalQSeries := onePoint N v

/-- **The (chiral) torus partition function** `𝒵(τ) = tr_ℋ q^{L₀ − c/24} = χ_M(τ)` (Gannon p. 341). -/
noncomputable def torusPartition (N : OrdVModule W M) : FormalQSeries := gradedDim N

/-- **`𝒵_M(𝟙; τ) = 𝒵(τ)`** — the one-point function at the vacuum is the partition function. -/
theorem torusOnePoint_vacuum (N : OrdVModule W M) : torusOnePoint N W.vacuum = torusPartition N :=
  onePoint_vacuum N

/-- The torus one-point function is **additive in `v`**. -/
theorem torusOnePoint_add (N : OrdVModule W M) (v w : 𝒱) :
    torusOnePoint N (v + w) = torusOnePoint N v + torusOnePoint N w := onePoint_add N v w

/-- The torus one-point function is **homogeneous in `v`** (so, `ℂ`-linear). -/
theorem torusOnePoint_smul (N : OrdVModule W M) (c : ℂ) (v : 𝒱) :
    torusOnePoint N (c • v) = c • torusOnePoint N v := onePoint_smul N c v

/-! ## GOAL 4 — the one-point chiral block (Gannon 5.3.17b) -/

/-- **The one-point chiral block** `χ_M(τ, u)` on the torus (Gannon 5.3.17b) — the `n = 1` case of
the `n`-point block, and "hence the name" one-point function.  Equal to `torusOnePoint`. -/
noncomputable def chiralBlockOne (N : OrdVModule W M) (v : 𝒱) : FormalQSeries := torusOnePoint N v

@[simp] theorem chiralBlockOne_eq (N : OrdVModule W M) (v : 𝒱) :
    chiralBlockOne N v = torusOnePoint N v := rfl

/-! ## GOAL E — the Zhu-recursion interface (toward Thm 5.3.8) -/

/-- **The torus two-point trace term** `tr_M(o(a)·o(v)·q^{L₀−c/24})` — the leading term of Zhu's
recursion (Gannon 5.3.17 / Zhu §4), as a formal `q`-series. -/
noncomputable def torusTwoPoint (N : OrdVModule W M) (a v : 𝒱) : FormalQSeries :=
  fun e =>
    haveI := N.finrank (e + W.centralCharge / 24)
    LinearMap.trace ℂ _
      (weightBlock N ((oMod N a).comp (oMod N v)) (e + W.centralCharge / 24))

/-- **The Zhu-recursion interface** (Gannon 5.3.17 / Zhu §4), for homogeneous `a ∈ 𝒱_{kₐ}`:
`𝒵_M(a[−1]v; τ) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k≥1} G_{2k}(τ)·𝒵_M(a[2k−1]v; τ)`, with `G` the (weight
`2k`) Eisenstein family, as **intended**.  ⚠ As written, `G (k + 1) * torusOnePoint …` is the
**pointwise** product of two functions `ℂ → ℂ`, not the product (convolution `qConv`) of `q`-series,
so this `Prop` is **not** Zhu's recursion.  It has no consumers.  The recursion actually used and
proved is `ZhuRecursionAt` (with `qConv`) at the pinned family `zhuG`: `ZhuRecursionPinned`,
`zhuRecursionPinned_holds` (`Modularity/ZhuRecursionClose.lean`). -/
def ZhuRecursion (N : OrdVModule W M) (G : ℕ → FormalQSeries) (a v : 𝒱) (ka : ℕ) : Prop :=
  torusOnePoint N (vSqZ W a ka (-1) v)
    = torusTwoPoint N a v
      + ∑ᶠ k : ℕ, G (k + 1) * torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) v)

end

/-! ## Row closure and scoped footnote

The declarations in this base file are completed by the imported companion modules:
`SquareBracketWitt` and `SquareBracketVirasoro` prove the bracket and Virasoro laws;
`SquareBracketGrading` supplies the internal square grading; `Schwarzian` proves the formal
Schwarzian identity; `ChangeCoord` constructs the coordinate operator as a linear equivalence; and
`ChiralBlock` supplies the multilinear `n`-point block.  The Zhu recursion and its analytic bridge
are proved further downstream.

The only scoped footnote is the full conjugation formula 5.3.15d–f through `changeCoord`.
It is not a
prerequisite of the modularity proof: the square-bracket Virasoro relation used there is established
independently.  This footnote is not an active residual for the completed row.
-/

end VOA
