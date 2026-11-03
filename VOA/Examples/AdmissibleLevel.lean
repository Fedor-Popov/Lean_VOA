/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VOA

/-!
# Admissible levels for affine `𝔰𝔩₂`, and their arithmetic

The simple affine vertex operator algebras `L_k(𝔰𝔩₂)` are interesting precisely at the
**admissible** levels of Kac–Wakimoto: there the associated variety of `L_k(𝔰𝔩₂)` is the
nilpotent cone `𝒩 = ℂ²/ℤ₂` of `𝔰𝔩₂` (two symplectic leaves, so the algebra is *quasi-lisse*
but not *lisse*), the characters are modular, and the category `O` is semisimple.  This file
isolates the **purely arithmetic** layer of that story: the predicate `AdmissibleLevel` on a
complex level `k`, and everything about it that can be settled by `norm_num`/`omega`.

Nothing here depends on the vertex-algebra structure of `WakModule k`; the single import
`Examples.AffineSl2VOA` is used only to talk about the repository's own central charge
`AffineVOA.centralChargeA k = 3k/(k+2)` rather than a private copy of that formula.  In
particular this file is completely independent of the `YA` reconstruction, and it
does not use the `PreVertexAlgebra (WakModule k)` instance.

## The definition, and its source

For a simple Lie algebra `𝔤` with dual Coxeter number `h^∨`, Kac–Wakimoto call a level `k`
**principal admissible** when `k + h^∨ = p/q` with `p, q` coprime positive integers and
`p ≥ h^∨` (for simply-laced `𝔤`; in general `p ≥ h^∨` is replaced by `p ≥ h` when
`q` is divisible by the lacing number `r^∨`).  For `𝔤 = 𝔰𝔩₂` we have `h^∨ = 2` and `r^∨ = 1`,
so both branches collapse to the single condition

  `k + 2 = p/q`,  `p, q ∈ ℤ_{>0}`,  `gcd(p,q) = 1`,  `p ≥ 2`.

Sources consulted, all agreeing on exactly this statement for `𝔰𝔩₂`:

* V. Kac, M. Wakimoto, *Modular invariant representations of infinite-dimensional Lie algebras
  and superalgebras*, PNAS 85 (1988) 4956 — the original definition of admissible weights.
* T. Arakawa, *Rationality of admissible affine vertex algebras in the category `O`*,
  arXiv:1207.4857 — Def. of admissible level; for simply-laced `𝔤`, `k` is admissible iff
  `k + h^∨ = m/u` in lowest terms with `m ≥ h^∨`.
* T. Creutzig–D. Ridout et al., *Tensor categories of weight modules of `ŝ𝔩₂` at admissible
  level*, arXiv:2311.10240 — "`ℓ + 2 = p/q` for coprime positive integers `p ≥ 2`, `q ≥ 1`".

⚠ Note that `p ≥ 2` and `p ≥ h^∨` are the *same* condition here, so no ambiguity arises for
`𝔰𝔩₂`.  The bound is not vacuous: `p = 1` (e.g. `k + 2 = 1/2`, `k = -3/2`) is **not**
admissible, and `p = 0` would be the critical level.

⚠ One convention nuance, deliberately resolved in favour of the inclusive reading.  Papers
that are only interested in the *fractional* admissible levels — e.g. arXiv:2311.10240, eq. (8),
"`k + 2 = u/v`, `u ∈ ℤ_{≥2}`, `v ∈ ℤ_{>1}`, `gcd(u,v) = 1`" — impose `q ≥ 2`, which excludes
the integrable levels `k ∈ ℤ_{≥0}` (those are `q = 1`).  Kac–Wakimoto admissibility itself
takes `q ≥ 1`, so that the integrable levels are admissible; that is the convention used here,
and `admissibleLevel_natCast` is the theorem that records it.  If a later file needs the
fractional-only notion it should say `1 < q`, not silently reinterpret this predicate.

Since `k : ℂ`, the predicate must assert *both* that `k` is rational *and* that its
`p/q` normal form obeys the bounds; `AdmissibleLevel` below is the existential statement of
exactly that, and `admissible_witness_unique` shows the witnesses `(p,q)` are unique, so
"the numerator" and "the denominator" of an admissible level are well defined.

## Main results

* `AdmissibleLevel` — the predicate, as above.
* `admissibleLevel_neg_four_thirds : AdmissibleLevel (-4/3)` — the flagship level, with
  `(p,q) = (2,3)`; this is the level at which `Examples.AffineSl2Singular` produces the
  weight-`3` singular vector `sl2Singular`.
* `admissibleLevel_natCast : AdmissibleLevel (n : ℂ)` for every `n : ℕ` — the classical
  integrable levels are the special case `q = 1`, `p = n + 2`.
* `AdmissibleLevel.add_two_ne_zero : AdmissibleLevel k → k + 2 ≠ 0` — admissible levels are
  never critical.  This is *exactly* the hypothesis `hk : k + 2 ≠ 0` that
  `AffineVOA.affineSl2VOA_closed` and the whole Sugawara construction take, so an admissible
  level feeds the repository's affine machinery directly.
* `centralChargeA_of_add_two_eq : k + 2 = p/q → centralChargeA k = 3 - 6q/p`, the
  admissible-level form of `c = 3k/(k+2)`, with the integral variant
  `centralChargeA_eq_of_admissible' : c = 3(p - 2q)/p`.
* `centralChargeA_neg_four_thirds : centralChargeA (-4/3) = -6` — **verified twice**, once
  from `3k/(k+2)` directly and once from `3 - 6q/p` with `(p,q) = (2,3)`.
* `admissible_witness_unique` — the pair `(p,q)` is determined by `k`.
* `AdmissibleLevel.exists_rat` — an admissible level is `-2` plus a *positive rational*.
* `admissibleLevel_boundary` — the boundary-admissible family `p = 2`: `k = -2 + 2/(2m+1)`
  is admissible for every `m : ℕ` (`m = 1` is the flagship `-4/3`).

## Status

Complete and hole-free: no `sorry`, no `admit`, no `native_decide`, no new axioms.  Every
declaration below is pure arithmetic in `ℂ` and `ℕ`.  §5 records, as a **remark only**, the
Drinfeld–Sokolov dictionary that relates the denominator `q` to a Virasoro minimal model; the
identity it quotes is already proved elsewhere in the repository
(`VOA.DSsl2.dsCentralCharge_eq_minimalModel`) and is deliberately *not* re-proved or
re-stated as a theorem here, to keep this file's import surface minimal.
-/

namespace VOA.Admissible

open VOA.AffineVOA

/-! ## §1  The predicate -/

/-- **Admissible level for affine `𝔰𝔩₂`** (Kac–Wakimoto).  A complex number `k` is admissible
when `k + 2 = p/q` for coprime positive integers `p, q` with `p ≥ 2 = h^∨`.

The shift by `2` is the dual Coxeter number `h^∨(𝔰𝔩₂) = 2` (`AffineVOA.dualCoxeter`), so the
condition is the `𝔰𝔩₂` case of `k + h^∨ = p/q`.  Note that `1 ≤ q` and `2 ≤ p` together force
`k + 2` to be a *positive* rational, whence `k ≠ -2`: see `AdmissibleLevel.add_two_ne_zero`. -/
def AdmissibleLevel (k : ℂ) : Prop :=
  ∃ p q : ℕ, 2 ≤ p ∧ 1 ≤ q ∧ Nat.Coprime p q ∧ k + 2 = (p : ℂ) / (q : ℂ)

/-- The numerator of an admissible level is nonzero in `ℂ`. -/
theorem cast_num_ne_zero {p : ℕ} (hp : 2 ≤ p) : (p : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

/-- The denominator of an admissible level is nonzero in `ℂ`. -/
theorem cast_den_ne_zero {q : ℕ} (hq : 1 ≤ q) : (q : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

/-! ## §2  The flagship level `k = -4/3`, and the other named examples -/

/-- **The flagship admissible level.**  `k = -4/3` is admissible, with `(p,q) = (2,3)`:
indeed `-4/3 + 2 = 2/3`, and `gcd(2,3) = 1` with `2 ≥ 2`.

This is the level of `Examples.AffineSl2Singular`, where the weight-`3` singular vector
`sl2Singular` exists and `exists_singular_iff` *derives* `3k + 4 = 0`. -/
theorem admissibleLevel_neg_four_thirds : AdmissibleLevel (-4 / 3 : ℂ) :=
  ⟨2, 3, le_rfl, by omega, by decide, by norm_num⟩

/-- `k = -1/2` is admissible, with `(p,q) = (3,2)`: `-1/2 + 2 = 3/2`.  This is the level
flagged in `Examples.AffineSl2Singular` §D as the next admissible level after `-4/3`; it is
the Feigin–Frenkel dual `k + 2 ↦ (k+2)⁻¹` of the flagship. -/
theorem admissibleLevel_neg_half : AdmissibleLevel (-1 / 2 : ℂ) :=
  ⟨3, 2, by omega, by omega, by decide, by norm_num⟩

/-- `k = -8/5` is admissible, with `(p,q) = (2,5)`.  This is the level whose Drinfeld–Sokolov
reduction is the Lee–Yang `(2,5)` minimal model; see the remark in §5. -/
theorem admissibleLevel_neg_eight_fifths : AdmissibleLevel (-8 / 5 : ℂ) :=
  ⟨2, 5, le_rfl, by omega, by decide, by norm_num⟩

/-- **The integrable levels are admissible.**  Every non-negative integer `n`, viewed as a
complex level, is admissible with `q = 1` and `p = n + 2 ≥ 2`.  This is the classical case:
`L_n(𝔰𝔩₂)` for `n ∈ ℤ_{≥0}` is the rational, lisse, integrable-level affine VOA, and it
validates the definition against a case whose answer is known independently. -/
theorem admissibleLevel_natCast (n : ℕ) : AdmissibleLevel (n : ℂ) :=
  ⟨n + 2, 1, by omega, le_rfl, Nat.coprime_one_right _, by push_cast; ring⟩

/-- The level `0` is admissible (`(p,q) = (2,1)`). -/
theorem admissibleLevel_zero : AdmissibleLevel (0 : ℂ) := by
  simpa using admissibleLevel_natCast 0

/-- The level `1` is admissible (`(p,q) = (3,1)`). -/
theorem admissibleLevel_one : AdmissibleLevel (1 : ℂ) := by
  simpa using admissibleLevel_natCast 1

/-- **The boundary-admissible family.**  Taking the smallest allowed numerator `p = h^∨ = 2`
forces `q` odd (coprimality with `2`), and every such level `k = -2 + 2/(2m+1)` is admissible.
`m = 0` gives `k = 0`, `m = 1` gives the flagship `k = -4/3`, `m = 2` gives `k = -8/5`. -/
theorem admissibleLevel_boundary (m : ℕ) :
    AdmissibleLevel (-2 + 2 / ((2 * m + 1 : ℕ) : ℂ)) := by
  refine ⟨2, 2 * m + 1, le_rfl, by omega, ?_, ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  · push_cast
    ring

/-! ## §3  Admissible levels avoid the critical level -/

/-- **An admissible level is never critical**: `k + 2 ≠ 0`.

Both `p ≥ 2 > 0` and `q ≥ 1 > 0`, so `k + 2 = p/q ≠ 0`.  This matters everywhere downstream:
the Sugawara construction divides by `2(k+2)` and the central charge is `3k/(k+2)`, and
`AffineVOA.affineSl2VOA_closed` literally takes `hk : k + 2 ≠ 0` as its hypothesis.  So this
lemma is what lets an admissible level be fed to the repository's affine machinery. -/
theorem AdmissibleLevel.add_two_ne_zero {k : ℂ} (h : AdmissibleLevel k) : k + 2 ≠ 0 := by
  obtain ⟨p, q, hp, hq, -, hk⟩ := h
  rw [hk]
  exact div_ne_zero (cast_num_ne_zero hp) (cast_den_ne_zero hq)

/-- Restatement of `AdmissibleLevel.add_two_ne_zero`: an admissible level is not the critical
level `k = -2` of `𝔰𝔩₂`. -/
theorem AdmissibleLevel.ne_neg_two {k : ℂ} (h : AdmissibleLevel k) : k ≠ -2 := by
  intro hk
  exact h.add_two_ne_zero (by rw [hk]; ring)

/-- The critical level is **not** admissible. -/
theorem not_admissibleLevel_neg_two : ¬ AdmissibleLevel (-2 : ℂ) :=
  fun h => h.ne_neg_two rfl

/-- An admissible level is rational, and `k + 2` is a *positive* rational. -/
theorem AdmissibleLevel.exists_rat {k : ℂ} (h : AdmissibleLevel k) :
    ∃ r : ℚ, 0 < r ∧ k + 2 = (r : ℂ) := by
  obtain ⟨p, q, hp, hq, -, hk⟩ := h
  refine ⟨(p : ℚ) / (q : ℚ), ?_, ?_⟩
  · have hp' : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
    have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
    exact div_pos hp' hq'
  · rw [hk]; push_cast; ring

/-! ## §4  The central charge at an admissible level -/

/-- **The central charge in admissible-level form.**  If `k + 2 = p/q` with `p, q ≠ 0`, then

  `c = 3k/(k+2) = 3 - 6q/p`.

Stated for arbitrary nonzero complex `p, q` so that it applies verbatim to the natural-number
witnesses of `AdmissibleLevel`.  The repository's `AffineVOA.centralChargeA` is
`dim 𝔰𝔩₂ · k /(k + h^∨) = 3k/(k+2)` (`AffineVOA.centralChargeA_eq`). -/
theorem centralChargeA_of_add_two_eq {k p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : k + 2 = p / q) : centralChargeA k = 3 - 6 * q / p := by
  have hk' : k = p / q - 2 := by rw [← hk]; ring
  subst hk'
  rw [centralChargeA_eq]
  have h : p / q - 2 + 2 = p / q := by ring
  rw [h]
  field_simp
  ring

/-- The same identity in the integral form `c = 3(p - 2q)/p`, which is manifestly the
statement that `p ∣ 6q` controls the denominator of `c`. -/
theorem centralChargeA_of_add_two_eq' {k p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : k + 2 = p / q) : centralChargeA k = 3 * (p - 2 * q) / p := by
  rw [centralChargeA_of_add_two_eq hp hq hk]
  field_simp
  ring

/-- The central charge of an admissible level, packaged with its witnesses: for `k` admissible
there are coprime `p ≥ 2`, `q ≥ 1` with `k + 2 = p/q` and `c = 3 - 6q/p`. -/
theorem AdmissibleLevel.centralChargeA_eq {k : ℂ} (h : AdmissibleLevel k) :
    ∃ p q : ℕ, 2 ≤ p ∧ 1 ≤ q ∧ Nat.Coprime p q ∧ k + 2 = (p : ℂ) / (q : ℂ) ∧
      centralChargeA k = 3 - 6 * (q : ℂ) / (p : ℂ) := by
  obtain ⟨p, q, hp, hq, hcop, hk⟩ := h
  exact ⟨p, q, hp, hq, hcop, hk,
    centralChargeA_of_add_two_eq (cast_num_ne_zero hp) (cast_den_ne_zero hq) hk⟩

/-- **The flagship central charge, computed from `c = 3k/(k+2)` directly**:
`c(-4/3) = 3·(-4/3)/(2/3) = -4·(3/2) = -6`. -/
theorem centralChargeA_neg_four_thirds : centralChargeA (-4 / 3 : ℂ) = -6 := by
  rw [centralChargeA_eq]
  norm_num

/-- **The flagship central charge, computed a second time from the admissible-level
formula** `c = 3 - 6q/p` at `(p,q) = (2,3)`: `3 - 6·3/2 = 3 - 9 = -6`.  Agreement with
`centralChargeA_neg_four_thirds` is an independent check. -/
theorem centralChargeA_neg_four_thirds' :
    centralChargeA (-4 / 3 : ℂ) = 3 - 6 * ((3 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) := by
  rw [centralChargeA_of_add_two_eq (p := ((2 : ℕ) : ℂ)) (q := ((3 : ℕ) : ℂ))
    (by norm_num) (by norm_num) (by norm_num)]

/-- The two computations agree: `3 - 6·3/2 = -6`. -/
theorem centralChargeA_neg_four_thirds_val :
    (3 : ℂ) - 6 * ((3 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) = -6 := by
  norm_num

/-- The central charge at the Lee–Yang level `k = -8/5` (`(p,q) = (2,5)`):
`c = 3 - 6·5/2 = -12`. -/
theorem centralChargeA_neg_eight_fifths : centralChargeA (-8 / 5 : ℂ) = -12 := by
  rw [centralChargeA_eq]
  norm_num

/-- The central charge at `k = -1/2` (`(p,q) = (3,2)`): `c = 3 - 6·2/3 = -1`. -/
theorem centralChargeA_neg_half : centralChargeA (-1 / 2 : ℂ) = -1 := by
  rw [centralChargeA_eq]
  norm_num

/-- The central charge at an integrable level `k = n`: `c = 3n/(n+2)`, e.g. `c = 1` at
`n = 1` (the `𝔰𝔩₂` level-one WZW model, matching the `A₁` lattice VOA). -/
theorem centralChargeA_one : centralChargeA (1 : ℂ) = 1 := by
  rw [centralChargeA_eq]
  norm_num

/-! ## §5  Uniqueness of the witnesses, and the Drinfeld–Sokolov remark -/

/-- **The pair `(p,q)` is determined by `k`.**  Two coprime representations of the same
positive rational with nonzero numerators and denominators coincide.  Consequently "the
numerator `p`" and "the denominator `q`" of an admissible level are well defined, which is
what makes the `(p,q)` labelling of the minimal model in §5's remark meaningful. -/
theorem admissible_witness_unique {p q p' q' : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hcop : Nat.Coprime p q) (hcop' : Nat.Coprime p' q')
    (h : (p : ℂ) / (q : ℂ) = (p' : ℂ) / (q' : ℂ)) : p = p' ∧ q = q' := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hq'C : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq'
  have hmulC : (p : ℂ) * (q' : ℂ) = (p' : ℂ) * (q : ℂ) := (div_eq_div_iff hqC hq'C).mp h
  have hmul : p * q' = p' * q := by exact_mod_cast hmulC
  have hpp' : p = p' := by
    have h1 : p ∣ p' * q := ⟨q', hmul.symm⟩
    have h2 : p' ∣ p * q' := ⟨q, hmul⟩
    exact Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right h1) (hcop'.dvd_of_dvd_mul_right h2)
  refine ⟨hpp', ?_⟩
  subst hpp'
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) hmul.symm

/-- The witnesses of `AdmissibleLevel` are unique. -/
theorem AdmissibleLevel.witness_unique {k : ℂ} {p q p' q' : ℕ}
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime p q) (hcop' : Nat.Coprime p' q')
    (hk : k + 2 = (p : ℂ) / (q : ℂ)) (hk' : k + 2 = (p' : ℂ) / (q' : ℂ)) :
    p = p' ∧ q = q' :=
  admissible_witness_unique (by omega) (by omega) (by omega) hcop hcop' (hk ▸ hk')

/-!
### Remark (not a theorem here): the denominator `q` and the minimal models

The Drinfeld–Sokolov reduction of the affine `𝔰𝔩₂` algebra at level `k` produces a Virasoro
algebra at

  `c_W(k) = 13 − 6(k+2) − 6/(k+2)`,

and `Examples/DSReductionSl2` already contains the arithmetic bridge as a *proved* theorem,
`VOA.DSsl2.dsCentralCharge_eq_minimalModel`: for `k + 2 = p/q` with `p, q ≠ 0`,

  `c_W(-2 + p/q) = 1 − 6(p−q)²/(pq)`,

the `(p,q)` Virasoro minimal-model central charge.  So the pair `(p,q)` of an admissible level
— well defined by `admissible_witness_unique` — is exactly the minimal-model label of its
`W`-algebra.  Nothing about that identity is re-proved here; this file deliberately does not
import `Examples/DSReductionSl2`, whose own import surface (BRST cohomology, ghosts, screening
operators, the general-`c` free boson) is far heavier than anything the present arithmetic
needs.

⚠ **A correction to a natural expectation.**  The flagship level
`k = -4/3` has `(p,q) = (2,3)`, hence `c_W = 1 − 6(2−3)²/6 = 0`: its Drinfeld–Sokolov
reduction is the *trivial* `(2,3)` minimal model, **not** Lee–Yang.  The Lee–Yang `(2,5)`
model, `c_W = 1 − 6·9/10 = −22/5` (`VOA.DSsl2.dsCentralCharge_leeYang`, and
`Examples/LeeYangSingular`), is the reduction of the *different* admissible level
`k + 2 = 2/5`, i.e. `k = -8/5` (`admissibleLevel_neg_eight_fifths` above, at affine central
charge `c = -12` by `centralChargeA_neg_eight_fifths`).  Both `k = -4/3` and `k = -8/5` are
boundary admissible (`p = h^∨ = 2`), which is the family `admissibleLevel_boundary`
parametrises; they differ in the denominator `q = 3` versus `q = 5`.  The `𝔰𝔩₂` central
charges `-6` and `-12` are *not* the minimal-model ones and should not be confused with them.
-/

end VOA.Admissible
