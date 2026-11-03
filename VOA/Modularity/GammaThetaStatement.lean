/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.SlashSubgroup
import VOA.Modularity.ThetaGroup
import VOA.Modularity.SqGradedBlock
import VOA.Modularity.TraceNonvanish
import VOA.Modularity.GNProp8Closure

/-!
# `Γ_θ`-modularity for super and half-integer-weight vertex operator algebras — the
statement

Zhu's theorem, as proved in this library (`Modularity.ZhuTheorem`,
`Modularity.ZhuModularityPinned`, `zhuModularity_pinned_of_C2Cofinite`), produces characters
modular for the **full** modular group `SL₂(ℤ)`.  That conclusion is special to *bosonic*,
`ℤ`-graded vertex operator algebras.  This file writes down — as `def`s, `structure`s and
`Prop`s, never as theorems with holes — what the correct statement is when the grading is
allowed to be half-integral, proves the specializations that are reachable today, and records
what is missing.

## ⚠ The single most important fact in this file

**The mechanism is the half-integer WEIGHT, not the parity.**  These are two different
generalizations and they land on two different groups.  Conflating them is a category error, and
the project has already exhibited a family where they fall on complementary classes: for the
doublet algebra `A(p)` of `Examples/DoubletGenerators.lean` the generators `a^±` have deformed
weight `(3p−2)/4` and `⟨g,g⟩ = p/2`, so

* `4 ∣ p` — the half-lattice is even, the ambient algebra is **bosonic** (purely even), and
  `(3p−2)/4 ∈ ℤ + ½`.  Spin–statistics is *violated*.  **This is the `Γ_θ` case:** `T` is
  broken, `S` survives, the group is `⟨S, T²⟩ = Γ_θ`.
* `p ≡ 2 (mod 4)` — the algebra is **super**, but `(3p−2)/4 ∈ ℤ`, i.e. it is a `ℤ`-graded VOSA.
  **This is NOT the `Γ_θ` case:** by Dong–Zhao (2006) the *super*traces on `g`-twisted sectors
  span a full `SL₂(ℤ)`-module, and the *plain* traces are stabilised by `Γ₀(2)`.  Writing a
  `Γ_θ` theorem here would be wrong.
* `p` odd — `⟨g,g⟩ = p/2 ∉ ℤ` and `(3p−2)/4` is a *quarter*-integer.  `⟨S, T⁴⟩` is a Hecke group
  of **infinite** index in `SL₂(ℤ)`; `Γ_θ` is the wrong group and nothing here applies.  Do not
  silently extend.

Accordingly this file states the two forms **separately**:
`GammaThetaModularityHolds` (half-integer weight, `Conjecture_HalfWeight`) and
`SL2ZSuperModularityHolds` / `Gamma0TwoPlainTraceModularityHolds` (`ℤ`-graded super,
`Conjecture_ZGradedSuper`).

## Main definitions

* `IsIntegerGraded`, `IsHalfIntegerGraded`, `HasStrictHalfWeight`, `IsPurelyEven`,
  `IsGenuinelySuper` — the grading/parity predicates that separate the two mechanisms.
* `superO₂`, `SuperC2Cofinite` — `C₂`-cofiniteness for a `SuperVertexOperatorAlgebra`
  (the repo's `C2Cofinite` is bosonic only), agreeing with it on `W.toSuper`.
* `SuperCharacterSystem` — the data a `Γ_θ` statement needs: a **square-bracket** (`L[0]`)
  weight grading, carried as data because the repo builds `sqWeightSpace` only for
  `VertexOperatorAlgebra`, together with the family of one-point functions.
* `ModularLawOn` / `IsGammaThetaModular` — the half-integral transformation law on a subgroup.
* `IntegerWeightModularLawOn` — the integral-weight law (the shape of `ZhuModularityAnalytic`,
  restricted to a subgroup); this is the right vehicle for the `ℤ`-graded super case.
* `CharacterModularOn`, `character` — the **weight-zero** statement.  At `v = 𝟙` the
  automorphy factor is `(cτ+d)⁰ = 1`, so the *character* statement needs **no** half-integral
  slash at all.  This is the cheapest honest form of Höhn's Korollar 1.4.7.
* `Conjecture_HalfWeight`, `Conjecture_ZGradedSuper` — the conjectures, with every hypothesis
  named and visible.
* `CharacterIndependent` — linear independence of the one-point functions; the expressible part
  of "complete irredundant family", and what pins `ρ` down.
* `ThetaHalfAutFactorExists` — existence of a `Γ_θ` half-automorphy factor; proved as
  `thetaHalfAutFactorExists` (`Modularity/ThetaHalfAutFactor.lean`).

## Main results (all proved, no `sorry`, no new axioms)

* `thetaGroupProper` — **discharges `SlashSub.ThetaGroupProper`**, which
  `Modularity/SlashSubgroup.lean` carried as an unproved `def`, using
  `ThetaGroup.T_not_mem_genSTsq`.  With `thetaGroup_eq`, `thetaGroup_index` and
  `thetaGroup_ne_top` this is what makes the whole programme non-vacuous: `Γ_θ ⊊ SL₂(ℤ)` of index 3.
* `tPhase_half`, `tPhase_half_of_odd`, `tSqPhase_half` — **the mechanism in three lines.**
  The `T`-phase of a state of conformal weight `m/2` is `(−1)^m`, hence `−1` for odd `m`; the
  `T²`-phase is always `1`.  `⟨S, T²⟩ = Γ_θ` is the whole story.
* `sqWeightSpace_eq_bot_of_not_natCast` — the repo's `sqWeightSpace_eq_bot_of_neg` generalized
  from negative integers to every non-`ℕ` complex weight.  This is what makes the
  odd-`m` branch of the specialization below go through.
* `modularLawOn_thetaGroup_of_zhuModularityAnalytic` — **the consistency check demanded of
  the statement.**  A bosonic (purely even, integer-graded) VOA satisfying Zhu's theorem
  satisfies the half-integral `Γ_θ` law of this file, for *every* half-automorphy factor `J`:
  on even doubled weight `m = 2n` the factor collapses to `(cτ+d)ⁿ` by
  `HalfAutFactor.zpow_even`, and on odd `m` the weight space is `⊥`, so both sides vanish.
* `characterModularOn_thetaGroup_of_C2Cofinite` — the characters of a `C₂`-cofinite,
  rational bosonic VOA are `Γ_θ`-modular, chained directly off
  `zhuModularity_pinned_of_C2Cofinite`.  This is the bosonic shadow of the target statement.
* `translationHalfAutFactor` — a genuine `SlashSub.HalfAutFactor` on `⟨T²⟩ ≤ Γ_θ`, so the
  structure is demonstrably satisfiable and not malformed.
* `rho_unique_of_characterIndependent` — the modular representation realising the
  half-integral law is **unique**, so the conjectures below are about a canonical object.  The
  only extra input over the repo's bosonic `rho_unique` is `J.sq_ne_zero`, which lets
  `J.sq A τ ^ m` be cancelled for every `m : ℤ`, negative `m` included.
* `modularLawOn_iff_superRealisesLawOn` — the bridge to `SlashSub.SuperRealisesLawOn`, and the
  repair of its stated defect (it quantifies over the `L₀` grading `W.grading`; Zhu's law is in
  the `L[0]` grading, which is why `SuperCharacterSystem` carries `sqWt` as data).

## ⚠ What is NOT claimed

No proof of `Γ_θ`-modularity for any genuinely half-integer-weight object is claimed, offered or
implied.  `Conjecture_HalfWeight` is a `def`.  Every proved theorem below is either
group-theoretic, arithmetic, or a *restriction* of the already-proved bosonic `SL₂(ℤ)` theorem —
and restriction, as `SlashSub.realisesLawOn_thetaGroup_of_S` already records, buys nothing
mathematically.  Its value here is as a type-check on the statement.

## The `Γ_θ` programme: what is proved and what remains

* **T1 — `T ∉ Γ_θ`: proved.**  `Modularity/ThetaGroup.lean` (`GammaTheta`, `T_not_mem`,
  `GammaTheta_eq_genSTsq`, `index_eq_three`), discharged into `SlashSub` here as
  `thetaGroupProper`.
* **T2 — index 3 and `IsCongruenceSubgroup`: proved, up to the Mathlib phrasing.**
  `ThetaGroup.index_eq_three` and
  `ThetaGroup.Gamma_two_le` (`Γ(2) ≤ Γ_θ`, so `Γ_θ` is a congruence subgroup of level 2).  Not
  phrased as Mathlib's `IsCongruenceSubgroup`.
* **T3 — `Subgroup.closure {S, T²} = Γ_θ^{cong}`: proved.**  `ThetaGroup.GammaTheta_eq_genSTsq`.
* **T4 — the cheapest *genuine* `Γ_θ` theorem: the `ℤ/2`-extension route (not formalized).**
  No new analysis is needed.  Take `D : ModularData W ι` with `ZhuModularityAnalytic D`
  for a **bosonic** `W` (already proved).  For a multiplicity vector `u : ι → ℂ` set
  `charSum u v τ := ∑ i, u i * traceFun D.Mfam D.h i v τ`.  Then
  `stab u := {A | ∀ j, ∑ i, u i * D.rep A i j = u j}` is a genuine `Subgroup SL(2,ℤ)` (inverses
  are free: `D.rep` is a `MonoidHom` out of a *group*), and `Γ_θ ≤ stab u` reduces by
  `Subgroup.closure_le` to **two** checks, `uᵀρ(S) = uᵀ` and `uᵀρ(T²) = uᵀ`.  The `T²` check is
  a computation on conformal weights, because `ModularData.rep_T` is pinned to
  `diag(e^{2πi(hᵢ−c/24)})`: if the `hᵢ` on `supp u` agree mod `½` but not mod `1` then
  `uᵀρ(T) = −uᵀ` and `uᵀρ(T²) = uᵀ`.  That is literally `tPhase_half_of_odd` /
  `tSqPhase_half` below, expressed inside machinery that already exists.  Mathematically this is
  the statement that a `½ℤ`-graded `V` is a `ℤ/2` simple-current extension
  `V = V_{(ℤ)} ⊕ V_{(ℤ+½)}` of the `ℤ`-graded `V_{(ℤ)}`, with `χ_V = ch₀ + ch_γ`.
  ⚠ **Caveat, and it is the main limitation of this route:** this gives `Γ_θ`-modularity of *one*
  function, not of the full space of `V`-module characters.  For the latter one needs the
  `ℤ/2`-orbifold dictionary `Irr(V) → Rep(V_{(ℤ)})` — `C₂`-cofiniteness and rationality of the
  even subalgebra (Miyamoto CMP 2015; Carnahan–Miyamoto; McRae) plus the simple-current
  induction correspondence.  **None of that is in Mathlib or in this library.**  It would enter as
  a *named, visible* hypothesis.
* **T5 — a half-integral slash: proved (`thetaHalfAutFactorExists`).  Not needed for characters.**
  The character statement is weight `0` (`v = 𝟙`), so it needs no `HalfAutFactor`; see
  `CharacterModularOn` below.  Half-integral factors are needed only for one-point functions of
  `v` of half-integral *square-bracket* weight.  The construction
  (`Modularity/ThetaHalfAutFactor.lean`) takes `sq A τ := (cτ+d)^{1/2}` on
  the principal branch — the honest content is then **τ-independence of `mult`**, which follows from
  continuity plus connectedness of `ℍ` (note `cτ+d` never meets the branch cut when `c ≠ 0`,
  since `Im(cτ+d) = c·Im τ ≠ 0`).  ⚠ One cannot take the instance `sq A τ = θ(Aτ)/θ(τ)`
  suggested in `SlashSubgroup`'s docstring: that needs the full `Γ_θ` transformation law of the
  Jacobi theta constant, which Mathlib does *not* have — it has only `jacobiTheta_S_smul` and
  `jacobiTheta_T_sq_smul`, i.e. exactly the two generator relations, unpackaged.
* **T6 — the real theorem: super Zhu (not formalized).  It needs a super analogue of the
  whole `Modularity/` stack.**  In dependency order: a super square-bracket VOA (Zhu
  Thm 4.21 super version = Dong–Zhao 2005 Thm 3.2); the super Zhu algebra `A_g(V)` /
  De Sole–Kac `Zhu_g(V)` (the repo has `Modules/ZhuAlgebra.lean` bosonically only); the twisted
  `P_k(μ,λ,z,τ)`, `Q_k(μ,λ,τ)` with characteristics (the repo's `EisensteinAnalytic`/`zhuGC`
  has only the `(1,1)` case); the super space of one-point functions and its Fuchsian ODE; a
  super Gaberdiel–Neitzke Prop. 8; and, for van Ekeren-level generality, the **super Wedderburn
  theorem** (simple superalgebras are `M(m|n)` or the queer `Q_n`), replacing
  `Modularity/WedderburnAMod.lean` — this is where **odd traces** come from.

The natural order is **T4 → T6**, with T4's orbifold dictionary written as a visible
hypothesis.

## Specific blockers in the slash layer

1. **The analytic/block layer needs no work.**  `slashC`, `mobiusC`, `serreDerivC_slashC`,
   `slashC_zhuGC`, `blockSlash`, `isGradedBlock_blockSlash`, `IsSlashOf`, `slashC_zhuGC_mul`,
   `omega_serre_slash` are all stated and proved for a *single fixed* `(γ : SL(2,ℤ))`, using
   only `ad − bc = 1` and `Im(γz) > 0`.  Restriction to a subgroup is free; nothing needs
   restating.
2. **The one genuine full-group step** is `Modularity/TraceSpanningS.lean`:
   `submonoid_closure_S_T_eq_top` feeding `traceSpanning_of_S`.  It does *not* transport to
   `Γ_θ` verbatim, because `Γ̄_θ ≅ ℤ/2 ∗ ℤ` with free factors `⟨S⟩`, `⟨T²⟩`, so `T⁻²` is **not**
   a positive word in `S` and `T²` — unlike `T⁻¹ = (ST)⁵S` in the full group.  This is
   **already fixed**: `SlashSub.realisesLaw_inv_of_diag` +
   `SlashSub.thetaGroup_le_submonoidClosure` + `SlashSub.realisesLawOn_thetaGroup_of_generators`.
3. **THE REAL BLOCKER IS THE WEIGHT.**  `slashC (k : ℤ)` multiplies by `(cz+d)^{-k}` with an
   **integer** exponent, and `IsSlashOf` quantifies only over `v ∈ sqWeightSpace W (n : ℂ)`,
   `n : ℤ`.  On half-integer weights the existing relation is **silently vacuous**
   (`SlashSub.isSlashOf_of_eqOn_int`), and the canonical `blockSlash` silently applies weight
   `0` there (`SlashSub.sqWtOf_eq_zero_of_notInt`, `SlashSub.blockSlash_apply_of_notInt`).  So a
   `βγ` or `4 ∣ p` doublet character will be *accepted* by `IsSlashOf`/`blockSlash` while being
   *constrained by nothing*.  A half-integral slash (T5) is required before any statement about
   half-integral-weight one-point functions has content.
4. **`SlashSub.SuperRealisesLawOn` quantifies over `W.grading`, the ordinary `L₀` grading.**
   Zhu's law is in the **square-bracket** grading `L[0]`, and the repo builds `Lsq` /
   `sqWeightSpace` only for `VertexOperatorAlgebra`.  Harmless at `v = 𝟙` (`m = 0`), wrong in
   general.  Repaired here by making the square-bracket grading an explicit field of
   `SuperCharacterSystem`; porting `Lsq` to the super side remains a prerequisite of T6.
5. **`HalfAutFactor` imposes no holomorphy on `sq` and no root-of-unity condition on `mult`.**
   Fine for *stating* covariance; strictly weaker than a multiplier system.  A proved
   `IsGammaThetaModular` would therefore not by itself license the phrase "modular form".

## References

Höhn, *Selbstduale Vertexoperatorsuperalgebren und das Babymonster*, Bonner Math. Schriften 286
(1996), arXiv:0706.0236, Satz 1.4.6 and Korollar 1.4.7 (the original `Γ_θ` statement) ·
Dong–Zhao, *Modularity in orbifold theory for vertex operator superalgebras*, CMP 260 (2005)
227–256, arXiv:math/0411524, Thm 9.1(4) (`Γ_θ` for `½ℤ`-graded VOSAs; with `G = 1` this is
exactly "the characters of the irreducible modules span a `Γ_θ`-module") · Dong–Zhao,
*Modularity of trace functions … for `ℤ`-graded vertex operator superalgebras*,
arXiv:math/0601571 (`ℤ`-graded ⟹ full `SL₂(ℤ)` on supertraces — **not** `Γ_θ`) · van Ekeren,
*Modular invariance for twisted modules over a vertex operator superalgebra*, CMP 322 (2013)
333–371, arXiv:1111.0682, Thm 1.3 (rational weights, no spin–statistics assumed, odd traces for
queer `Q_n` components) · Zhu, JAMS 9 (1996) 237–302 · Dong–Li–Mason, CMP 214 (2000) 1–56.

## Status

Proved, no `sorry`, no `admit`, no `native_decide`, no new axioms.  `Conjecture_HalfWeight` and
`Conjecture_ZGradedSuper` are `def`s, and are the point of the file.
-/

namespace VOA.GammaThetaStmt

open scoped BigOperators MatrixGroups
open VOA VHat VHat.DLM3

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 The theta group: reconciling the two definitions, and properness

`Modularity/SlashSubgroup.lean` defines `thetaGroup := Subgroup.closure {S, T²}` and carries
`ThetaGroupProper` as an **unproved `def`**.  `Modularity/ThetaGroup.lean` defines `GammaTheta`
by the classical mod-`2` congruence and proves it equals the same closure, together with
`T ∉ ⟨S, T²⟩` and index `3`.  The two are joined here. -/

/-- `SlashSub.thetaGroup = ⟨S, T²⟩` is the classical theta group
`Γ_θ = {γ : γ ≡ I or γ ≡ S (mod 2)} = Γ(2) ∪ Γ(2)·S`. -/
theorem thetaGroup_eq : SlashSub.thetaGroup = ThetaGroup.GammaTheta :=
  ThetaGroup.GammaTheta_eq_genSTsq.symm

/-- **`SlashSub.ThetaGroupProper` is a theorem.**  This is what makes the whole programme
non-vacuous: if `T` were in `Γ_θ` then `Γ_θ`-modularity would just be `SL₂(ℤ)`-modularity. -/
theorem thetaGroupProper : SlashSub.ThetaGroupProper :=
  ThetaGroup.T_not_mem_genSTsq

/-- `T ∉ Γ_θ`, spelled out. -/
theorem T_notMem_thetaGroup : ModularGroup.T ∉ SlashSub.thetaGroup :=
  thetaGroupProper

/-- `Γ_θ` is a *proper* subgroup of `SL₂(ℤ)`. -/
theorem thetaGroup_ne_top : SlashSub.thetaGroup ≠ ⊤ := fun h =>
  T_notMem_thetaGroup (h ▸ Subgroup.mem_top _)

/-- `[SL₂(ℤ) : Γ_θ] = 3`. -/
theorem thetaGroup_index : SlashSub.thetaGroup.index = 3 :=
  ThetaGroup.genSTsq_index_eq_three

/-- `Γ(2) ≤ Γ_θ`: the theta group is a congruence subgroup of level `2`. -/
theorem gamma_two_le_thetaGroup : CongruenceSubgroup.Gamma 2 ≤ SlashSub.thetaGroup :=
  thetaGroup_eq ▸ ThetaGroup.Gamma_two_le

/-! ## §2 The mechanism: why `Γ_θ`, and why it is the WEIGHT and not the parity

A state of conformal weight `h` contributes `e^{2πi h}` to the `T`-translation `τ ↦ τ + 1` and
`e^{4πi h}` to `T² : τ ↦ τ + 2`.  Writing `h = m/2` with `m : ℤ` — the *doubled weight*, which
is the natural index throughout this file — the three lemmas below are the entire reason the
group drops from `SL₂(ℤ)` to `⟨S, T²⟩`.  `S` is untouched by the grading: it is the hard
analytic step, and it survives for `½ℤ`-graded algebras (Höhn; Dong–Zhao Thm 9.1). -/

/-- **The `T`-phase of a state of conformal weight `m/2` is `(−1)^m`.** -/
theorem tPhase_half (m : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / 2)) = (-1 : ℂ) ^ m := by
  have hrw : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / 2)
      = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
  rw [hrw, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- **`T` is broken by a strictly half-integer weight**: for odd `m` the phase is `−1`, so
`T` does not act by a scalar on a family containing both integer and half-integer weights, and
the span of characters is not `T`-stable. -/
theorem tPhase_half_of_odd {m : ℤ} (hm : ¬ (2 ∣ m)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / 2)) = -1 := by
  have hodd : Odd m := by
    rcases Int.even_or_odd m with he | ho
    · exact absurd he.two_dvd hm
    · exact ho
  rw [tPhase_half, hodd.neg_one_zpow]

/-- **`T²` always survives.**  For every `m : ℤ` — integer or half-integer weight alike —
the `T²`-phase `e^{4πi·(m/2)} = e^{2πi m}` is `1`.  Together with the `S`-law this gives exactly
`⟨S, T²⟩ = Γ_θ` and nothing more. -/
theorem tSqPhase_half (m : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * ((m : ℂ) / 2))) = 1 := by
  have hrw : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (2 * ((m : ℂ) / 2))
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [hrw, Complex.exp_int_mul_two_pi_mul_I]

/-- For an *integer* weight the `T`-phase is already `1`: nothing is broken, which is why the
bosonic theorem gets all of `SL₂(ℤ)`. -/
theorem tPhase_int (m : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 := by
  have hrw : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (m : ℂ)
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [hrw, Complex.exp_int_mul_two_pi_mul_I]

/-- The same statement at the level of the half-automorphy factor: on any subgroup containing
`T`, a half-integral slash factor at `T` is a square root of `autFactor T = 1`, hence `±1` — the
sign that a half-integer weight sees.  (`Γ_θ` of course does **not** contain `T`; this records
what would go wrong.) -/
theorem halfAutFactor_T_sq_eq_one {Γ : Subgroup SL(2, ℤ)} (J : SlashSub.HalfAutFactor Γ)
    (hT : ModularGroup.T ∈ Γ) (τ : UpperHalfPlane) :
    J.sq ModularGroup.T τ ^ (2 : ℤ) = 1 := by
  rw [J.sq_sq ModularGroup.T hT τ, autFactor_T]

/-! ## §3 Grading and parity predicates — the two mechanisms, kept apart -/

/-- `W` is **`ℤ`-graded**: every weight space at a non-integer weight vanishes. -/
def IsIntegerGraded (W : SuperVertexOperatorAlgebra 𝒱) : Prop :=
  ∀ k : ℂ, (∀ m : ℤ, (m : ℂ) ≠ k) → W.grading k = ⊥

/-- `W` is **`½ℤ`-graded**: every weight space at a non-half-integer weight vanishes.  This is
the hypothesis of Höhn's theorem and of Dong–Zhao Thm 9.1(4). -/
def IsHalfIntegerGraded (W : SuperVertexOperatorAlgebra 𝒱) : Prop :=
  ∀ k : ℂ, (∀ m : ℤ, ((m : ℂ) / 2) ≠ k) → W.grading k = ⊥

/-- `W` **has a strictly half-integer weight**: some odd doubled weight `m` carries a nonzero
weight space.  This, and not `IsGenuinelySuper`, is the hypothesis that forces `Γ_θ`. -/
def HasStrictHalfWeight (W : SuperVertexOperatorAlgebra 𝒱) : Prop :=
  ∃ m : ℤ, ¬ (2 ∣ m) ∧ W.grading ((m : ℂ) / 2) ≠ ⊥

/-- `W` is **purely even**: the odd part vanishes.  Note this is logically independent of the
grading conditions — `βγ` and the `4 ∣ p` doublet are purely even with half-integer weights, the
`bc` ghosts are odd with integer weights.  The repo's `SpinStatistics` is deliberately a
predicate, not a field, for exactly this reason. -/
def IsPurelyEven (W : SuperVertexOperatorAlgebra 𝒱) : Prop := W.parity 1 = ⊥

/-- `W` is **genuinely super**: the odd part is nonzero. -/
def IsGenuinelySuper (W : SuperVertexOperatorAlgebra 𝒱) : Prop := W.parity 1 ≠ ⊥

/-- A `ℤ`-graded algebra has no strictly half-integer weight — the two mechanisms cannot both
fire on the same algebra. -/
theorem not_hasStrictHalfWeight_of_isIntegerGraded {W : SuperVertexOperatorAlgebra 𝒱}
    (hW : IsIntegerGraded W) : ¬ HasStrictHalfWeight W := by
  rintro ⟨m, hodd, hne⟩
  refine hne (hW _ ?_)
  intro n hn
  refine hodd ⟨n, ?_⟩
  have h2 : (2 : ℂ) * (n : ℂ) = (m : ℂ) := by rw [hn]; ring
  have : (2 : ℤ) * n = m := by exact_mod_cast h2
  omega

/-- `ℤ`-graded ⟹ `½ℤ`-graded. -/
theorem isHalfIntegerGraded_of_isIntegerGraded {W : SuperVertexOperatorAlgebra 𝒱}
    (hW : IsIntegerGraded W) : IsHalfIntegerGraded W := by
  intro k hk
  refine hW k ?_
  intro m hm
  refine hk (2 * m) ?_
  rw [← hm]
  push_cast
  ring

/-- An ordinary VOA, read as a super VOA, is `ℤ`-graded. -/
theorem toSuper_isIntegerGraded (W : VertexOperatorAlgebra 𝒱) :
    IsIntegerGraded W.toSuper := by
  intro k hk
  exact W.toPreVertexAlgebra.gradingC_of_not_int (fun ⟨m, hm⟩ => hk m hm)

/-- An ordinary VOA, read as a super VOA, is purely even. -/
theorem toSuper_isPurelyEven (W : VertexOperatorAlgebra 𝒱) :
    IsPurelyEven W.toSuper := by
  change (ParityGrading.even 𝒱).parity 1 = ⊥
  exact ParityGrading.even_parity_of_ne (by decide)

/-- Hence no bosonic VOA can be an instance of the `Γ_θ` hypothesis class. -/
theorem toSuper_not_hasStrictHalfWeight (W : VertexOperatorAlgebra 𝒱) :
    ¬ HasStrictHalfWeight W.toSuper :=
  not_hasStrictHalfWeight_of_isIntegerGraded (toSuper_isIntegerGraded W)

/-! ## §4 `C₂`-cofiniteness for a super vertex operator algebra

The repo's `C2Cofinite` is stated for `VertexOperatorAlgebra` only.  The super version is the
same span, taken with the super modes; on `W.toSuper` the two agree definitionally. -/

/-- `O₂(V) = span{u₍₋₂₎v}` for a super vertex operator algebra (Zhu's `C₂`). -/
def superO₂ (W : SuperVertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = W.toSuperVertexAlgebra.smul u (-2) v}

/-- **`C₂`-cofiniteness for a super VOA**: `V / O₂(V)` is finite-dimensional.  This is the
hypothesis of Höhn's theorem, of Dong–Zhao Thm 9.1(4), and of van Ekeren Thm 1.3.
⚠ `βγ` does **not** satisfy it — its modularity is of the quasi-lisse/logarithmic kind and is
*not* covered by any statement in this file. -/
def SuperC2Cofinite (W : SuperVertexOperatorAlgebra 𝒱) : Prop :=
  FiniteDimensional ℂ (𝒱 ⧸ superO₂ W)

/-- On a bosonic algebra the super `O₂` is the ordinary one. -/
theorem superO₂_toSuper (W : VertexOperatorAlgebra 𝒱) : superO₂ W.toSuper = O₂ W := rfl

/-- On a bosonic algebra the two `C₂`-cofiniteness notions agree. -/
theorem superC2Cofinite_toSuper_iff (W : VertexOperatorAlgebra 𝒱) :
    SuperC2Cofinite W.toSuper ↔ C2Cofinite W := Iff.rfl

/-! ## §5 The data a `Γ_θ` statement needs

`SuperCharacterSystem` carries two things the repo cannot yet produce on the super side:

* the **square-bracket** (`L[0]`, "Zhu") weight grading `sqWt`.  Zhu's transformation law is
  stated in `L[0]`, not `L₀`, and the repo builds `Lsq`/`sqWeightSpace` only for
  `VertexOperatorAlgebra`.  Carrying it as data is the honest move, and it repairs the stated
  defect of `SlashSub.SuperRealisesLawOn` (blocker 4 above).
* the family `chi` of **one-point functions** of a finite family of modules.  The repo has
  `Modules/SuperWeakModule.lean` but no graded super modules, hence no super characters; so the
  family is abstracted.  ⚠ Every module-theoretic hypothesis of the real theorem — that the
  family is a complete irredundant set of irreducibles, `g`-rationality, `h`-stability — is
  therefore **not** expressible here and must be added by name when the super module theory
  arrives.  See `Conjecture_HalfWeight`. -/

/-- The data of a family of one-point functions over a `SuperVertexOperatorAlgebra`, together
with the square-bracket weight grading they are graded by. -/
structure SuperCharacterSystem (W : SuperVertexOperatorAlgebra 𝒱) (ι : Type v) [Fintype ι] where
  /-- The **square-bracket** (`L[0]`) weight grading.  Carried as data: see the section
  docstring. -/
  sqWt : ℂ → Submodule ℂ 𝒱
  /-- The square-bracket weights are half-integral. -/
  sqWt_halfInt : ∀ k : ℂ, (∀ m : ℤ, ((m : ℂ) / 2) ≠ k) → sqWt k = ⊥
  /-- The vacuum has square-bracket weight `0` (`L[0]𝟙 = 0`).  This is what makes the
  weight-zero *character* statement a special case. -/
  vacuum_mem_sqWt : W.vacuum ∈ sqWt 0
  /-- The one-point functions `χ_i(v; τ) = 𝒵_{M_i}(v; τ)`. -/
  chi : ι → 𝒱 → UpperHalfPlane → ℂ
  /-- Each is linear in `v`; only vanishing at `0` is needed below. -/
  chi_zero : ∀ (i : ι) (τ : UpperHalfPlane), chi i 0 τ = 0

namespace SuperCharacterSystem

variable {W : SuperVertexOperatorAlgebra 𝒱} {ι : Type v} [Fintype ι]

/-- The **character** of the `i`-th module: the one-point function at the vacuum.  This is a
weight-`0` object, so its transformation law carries **no** automorphy factor at all. -/
def character (S : SuperCharacterSystem W ι) (i : ι) (τ : UpperHalfPlane) : ℂ :=
  S.chi i W.vacuum τ

end SuperCharacterSystem

/-! ## §6 The transformation laws -/

section Laws

variable {W : SuperVertexOperatorAlgebra 𝒱} {ι : Type v} [Fintype ι]

/-- **The half-integral transformation law on a subgroup `Γ`.**

For `A ∈ Γ`, every doubled weight `m : ℤ` and every `v` of square-bracket weight `m/2`,
`χ_i(v; Aτ) = (cτ+d)^{m/2} · Σ_j ρ(A)_{ij} χ_j(v; τ)`,
the fractional power being `J.sq A τ ^ m`.  `m : ℤ` — rather than `n : ℕ` as in
`ZhuModularityAnalytic` — is exactly where half-integer weights enter. -/
def ModularLawOn (S : SuperCharacterSystem W ι) (Γ : Subgroup SL(2, ℤ))
    (J : SlashSub.HalfAutFactor Γ) (ρ : SL(2, ℤ) → ι → ι → ℂ) : Prop :=
  ∀ A ∈ Γ, ∀ (m : ℤ) (v : 𝒱), v ∈ S.sqWt ((m : ℂ) / 2) → ∀ (i : ι) (τ : UpperHalfPlane),
    S.chi i v (A • τ) = J.sq A τ ^ m * ∑ j, ρ A i j * S.chi j v τ

/-- **`Γ_θ`-modularity of a family of super / half-integer-weight one-point functions.**
The target of the programme.  Deliberately a `def`: no proof is claimed for any object with a
genuinely half-integer weight. -/
def IsGammaThetaModular (S : SuperCharacterSystem W ι)
    (J : SlashSub.HalfAutFactor SlashSub.thetaGroup) (ρ : SL(2, ℤ) → ι → ι → ℂ) : Prop :=
  ModularLawOn S SlashSub.thetaGroup J ρ

/-- The law restricts to a smaller subgroup, provided the two half-automorphy factors agree
there. -/
theorem ModularLawOn.mono {S : SuperCharacterSystem W ι} {Γ Γ' : Subgroup SL(2, ℤ)}
    (hle : Γ ≤ Γ') {J : SlashSub.HalfAutFactor Γ'} {J' : SlashSub.HalfAutFactor Γ}
    (hJ : ∀ A ∈ Γ, ∀ τ : UpperHalfPlane, J'.sq A τ = J.sq A τ)
    {ρ : SL(2, ℤ) → ι → ι → ℂ} (hS : ModularLawOn S Γ' J ρ) : ModularLawOn S Γ J' ρ := by
  intro A hA m v hv i τ
  rw [hJ A hA τ]
  exact hS A (hle hA) m v hv i τ

/-- **The integral-weight law on a subgroup** — the shape of `ZhuModularityAnalytic`, with
`∀ A : SL(2,ℤ)` weakened to `∀ A ∈ Γ`.  This, and *not* `ModularLawOn`, is the correct vehicle
for a `ℤ`-graded VOSA: there the weights are integers, the ordinary `(cτ+d)ⁿ` suffices, and the
group is the **full** `SL₂(ℤ)` on supertraces (Dong–Zhao 2006). -/
def IntegerWeightModularLawOn (S : SuperCharacterSystem W ι) (Γ : Subgroup SL(2, ℤ))
    (ρ : SL(2, ℤ) → ι → ι → ℂ) : Prop :=
  ∀ A ∈ Γ, ∀ (n : ℕ) (v : 𝒱), v ∈ S.sqWt (n : ℂ) → ∀ (i : ι) (τ : UpperHalfPlane),
    S.chi i v (A • τ) = autFactor A τ ^ n * ∑ j, ρ A i j * S.chi j v τ

theorem IntegerWeightModularLawOn.mono {S : SuperCharacterSystem W ι}
    {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ ≤ Γ') {ρ : SL(2, ℤ) → ι → ι → ℂ}
    (hS : IntegerWeightModularLawOn S Γ' ρ) : IntegerWeightModularLawOn S Γ ρ :=
  fun A hA => hS A (hle hA)

/-- **The weight-zero (character) law on a subgroup.**

`χ_i(Aτ) = Σ_j ρ(A)_{ij} χ_j(τ)`, with **no** automorphy factor.  This is the cheapest honest
form of the target statement — Höhn's Korollar 1.4.7, or Dong–Zhao Thm 9.1(4) with `G = 1` at
`v = 𝟙` — and, crucially, it is fully expressible with the machinery the repo has today: it
needs no half-integral slash (T5) whatsoever. -/
def CharacterModularOn (Γ : Subgroup SL(2, ℤ)) (χ : ι → UpperHalfPlane → ℂ)
    (ρ : SL(2, ℤ) → ι → ι → ℂ) : Prop :=
  ∀ A ∈ Γ, ∀ (i : ι) (τ : UpperHalfPlane), χ i (A • τ) = ∑ j, ρ A i j * χ j τ

theorem CharacterModularOn.mono {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ ≤ Γ')
    {χ : ι → UpperHalfPlane → ℂ} {ρ : SL(2, ℤ) → ι → ι → ℂ}
    (hχ : CharacterModularOn Γ' χ ρ) : CharacterModularOn Γ χ ρ :=
  fun A hA => hχ A (hle hA)

/-- The character law is the doubled-weight-`0` slice of `ModularLawOn`. -/
theorem characterModularOn_of_modularLawOn {S : SuperCharacterSystem W ι}
    {Γ : Subgroup SL(2, ℤ)} {J : SlashSub.HalfAutFactor Γ} {ρ : SL(2, ℤ) → ι → ι → ℂ}
    (hS : ModularLawOn S Γ J ρ) : CharacterModularOn Γ S.character ρ := by
  intro A hA i τ
  have hv : W.vacuum ∈ S.sqWt (((0 : ℤ) : ℂ) / 2) := by
    simpa using S.vacuum_mem_sqWt
  have := hS A hA 0 W.vacuum hv i τ
  simpa [SuperCharacterSystem.character] using this

/-- **The bridge to `SlashSub.SuperRealisesLawOn`, and the repair of its defect.**  That
predicate quantifies over `W.grading` — the ordinary `L₀` grading — whereas Zhu's law lives in
the square-bracket grading.  The two statements coincide exactly when `sqWt = W.grading`. -/
theorem modularLawOn_iff_superRealisesLawOn (S : SuperCharacterSystem W ι)
    (hS : S.sqWt = W.grading) (Γ : Subgroup SL(2, ℤ)) (J : SlashSub.HalfAutFactor Γ)
    (ρ : SL(2, ℤ) → ι → ι → ℂ) :
    ModularLawOn S Γ J ρ ↔ SlashSub.SuperRealisesLawOn W Γ J S.chi ρ := by
  simp only [ModularLawOn, SlashSub.SuperRealisesLawOn, hS]

/-- **Linear independence of the one-point functions** — the super / half-integral analogue of
`TraceIndependent`.  Of the module-theoretic content of "`ι` indexes a complete *irredundant*
family of irreducibles", this is the part that **is** expressible with the machinery available
today, and it is the part that makes the modular representation unique. -/
def CharacterIndependent (S : SuperCharacterSystem W ι) : Prop :=
  ∀ c : ι → ℂ, (∀ (m : ℤ) (v : 𝒱), v ∈ S.sqWt ((m : ℂ) / 2) → ∀ τ : UpperHalfPlane,
    ∑ j, c j * S.chi j v τ = 0) → c = 0

/-- **The modular representation is unique.**  Two matrices realising the half-integral law
at the same `A ∈ Γ` agree, provided the one-point functions are independent.  This is the exact
analogue of the repo's `rho_unique` (`Modularity/BlockSpanning.lean`), and the only extra input
it needs in the half-integral setting is `J.sq_ne_zero`: a half-automorphy factor never
vanishes, so `J.sq A τ ^ m` can be cancelled for every `m : ℤ`, negative `m` included.

Consequence worth stating explicitly: because `ρ` is pinned by the law, the `Γ_θ` statements of
§7 are statements about a *canonical* object, not about a choice. -/
theorem rho_unique_of_characterIndependent {S : SuperCharacterSystem W ι}
    {Γ : Subgroup SL(2, ℤ)} {J : SlashSub.HalfAutFactor Γ} (hind : CharacterIndependent S)
    {ρ ρ' : SL(2, ℤ) → ι → ι → ℂ} (hρ : ModularLawOn S Γ J ρ) (hρ' : ModularLawOn S Γ J ρ')
    {A : SL(2, ℤ)} (hA : A ∈ Γ) : ρ A = ρ' A := by
  funext i
  have hc := hind (fun j => ρ A i j - ρ' A i j) ?_
  · funext j
    have hj := congrFun hc j
    simp only [Pi.zero_apply] at hj
    exact sub_eq_zero.mp hj
  · intro m v hv τ
    have h1 := hρ A hA m v hv i τ
    have h2 := hρ' A hA m v hv i τ
    have hne : J.sq A τ ^ m ≠ 0 := zpow_ne_zero _ (J.sq_ne_zero A hA τ)
    have hsum : J.sq A τ ^ m * (∑ j, ρ A i j * S.chi j v τ)
        = J.sq A τ ^ m * (∑ j, ρ' A i j * S.chi j v τ) := by rw [← h1, ← h2]
    have heq := mul_left_cancel₀ hne hsum
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at heq
    rw [← heq]
    exact Finset.sum_congr rfl (fun j _ => by ring)

end Laws

/-! ## §7 The conjectures — stated separately for the two mechanisms

Everything below is a `def`.  Each hypothesis is named and visible; in particular the
module-theoretic hypotheses that the repo cannot yet express appear as explicit `Prop`
arguments rather than being smuggled into the character family. -/

section Conjectures

variable {W : SuperVertexOperatorAlgebra 𝒱} {ι : Type v} [Fintype ι]

/-- `Γ_θ`-modularity holds for `S`: there exist a half-automorphy factor and a representation
realising the law. -/
def GammaThetaModularityHolds (S : SuperCharacterSystem W ι) : Prop :=
  ∃ (J : SlashSub.HalfAutFactor SlashSub.thetaGroup) (ρ : SL(2, ℤ) → ι → ι → ℂ),
    IsGammaThetaModular S J ρ

/-- `Γ_θ`-modularity of the **characters** alone.  Weaker than `GammaThetaModularityHolds`
(it is its weight-`0` slice, `characterModularOn_of_modularLawOn`) and — the point — fully
expressible today. -/
def GammaThetaCharacterModularityHolds (S : SuperCharacterSystem W ι) : Prop :=
  ∃ ρ : SL(2, ℤ) → ι → ι → ℂ, CharacterModularOn SlashSub.thetaGroup S.character ρ

/-- Full `SL₂(ℤ)`-modularity in the integral-weight law — the conclusion appropriate to a
`ℤ`-graded VOSA with **super**traces. -/
def SL2ZSuperModularityHolds (S : SuperCharacterSystem W ι) : Prop :=
  ∃ ρ : SL(2, ℤ) → ι → ι → ℂ, IntegerWeightModularLawOn S ⊤ ρ

/-- `Γ₀(2)`-modularity in the integral-weight law — the conclusion appropriate to a `ℤ`-graded
VOSA with **plain** traces.  ⚠ `Γ₀(2)` is `SL₂(ℤ)`-conjugate to `Γ_θ` but is **not** equal to
it; the three even spin structures form one `SL₂(ℤ)`-orbit of size `3`, with stabilisers
`Γ_θ` (plain NS trace), `Γ⁰(2)` (NS supertrace) and `Γ₀(2)` (plain Ramond trace). -/
def Gamma0TwoPlainTraceModularityHolds (S : SuperCharacterSystem W ι) : Prop :=
  ∃ ρ : SL(2, ℤ) → ι → ι → ℂ,
    IntegerWeightModularLawOn S (CongruenceSubgroup.Gamma0 2) ρ

/-- The module-theoretic hypotheses of the real theorem that this repo **cannot yet express**,
carried as an explicit named placeholder so that no statement below can smuggle them in.

Concretely this must eventually assert: `ι` indexes a complete, irredundant set of
representatives of the irreducible **admissible / positive-energy** `W`-modules; `W` is rational
(`g`-rational for every `g` in the relevant group, in the orbifold version); each `chi i` is the
genuine graded one-point function of the `i`-th module, taken with the correct trace (plain
trace on the NS sector for the `Γ_θ` statement, supertrace for the `SL₂(ℤ)` statement, and — in
van Ekeren's generality — the **odd trace** on Type-II queer components of `Zhu_g(W)`).

⚠ For the `ℤ/2`-extension route T4 it must in addition assert the orbifold dictionary
`Irr(W) → Rep(W_{(ℤ)})`: `C₂`-cofiniteness and rationality of the even subalgebra together with
the simple-current induction correspondence.  That is genuinely hard research mathematics and is
**not** available anywhere in Mathlib or in this repo. -/
def CompleteRationalFamily (_S : SuperCharacterSystem W ι) : Prop → Prop := fun P => P

/-- **CONJECTURE A — the half-integer-weight form.**

Höhn 1996, Satz 1.4.6 and Korollar 1.4.7; Dong–Zhao 2005 (CMP 260, arXiv:math/0411524),
Thm 9.1(4) with `G = 1`; van Ekeren 2013 (CMP 322, arXiv:1111.0682), Thm 1.3.

*If* `W` is a `C₂`-cofinite, `½ℤ`-graded super vertex operator algebra and `S` is the system of
one-point functions of a complete family of its irreducible modules, *then* those one-point
functions are modular for the theta group `Γ_θ = ⟨S, T²⟩`.

Two things to note.  **First**, the driving hypothesis is `IsHalfIntegerGraded` together with
`HasStrictHalfWeight` — *not* `IsGenuinelySuper`.  Dong–Zhao say it in as many words: in this
approach "the `σ` does not play any role".  A purely even algebra with half-integer weights
(the `4 ∣ p` doublet `A(p)`) is squarely inside this conjecture; a genuinely super algebra with
integer weights is not (see Conjecture B).  **Second**, `HasStrictHalfWeight` is what makes the
conclusion *sharp*: without it the algebra is `ℤ`-graded and the stronger `SL₂(ℤ)` conclusion
already holds, so `Γ_θ` would be a strictly weaker statement about a strictly larger class. -/
def Conjecture_HalfWeight (S : SuperCharacterSystem W ι) (hFam : Prop) : Prop :=
  SuperC2Cofinite W → IsHalfIntegerGraded W → HasStrictHalfWeight W →
    CharacterIndependent S → CompleteRationalFamily S hFam → GammaThetaModularityHolds S

/-- The character-level form of Conjecture A — Höhn's Korollar 1.4.7 verbatim: the projection to
the span of the characters `χ_{M_i}` induces a representation of the inhomogeneous theta group
`Γ̄_θ = Γ_θ/{±1}`.  This form needs no half-integral slash and is the recommended first
target (task T4). -/
def Conjecture_HalfWeight_Characters (S : SuperCharacterSystem W ι) (hFam : Prop) : Prop :=
  SuperC2Cofinite W → IsHalfIntegerGraded W → HasStrictHalfWeight W →
    CharacterIndependent S → CompleteRationalFamily S hFam →
      GammaThetaCharacterModularityHolds S

/-- **CONJECTURE B — the `ℤ`-graded super form.  NOT `Γ_θ`.**

Dong–Zhao 2006/07 (arXiv:math/0601571).  For a **`ℤ`-graded** vertex operator *superalgebra* the
space of `hσ`-traces (supertraces) on `g`-twisted sectors is invariant under the **full**
`SL₂(ℤ)`.  There is no `Γ_θ` here at all: the parity alone does not break `T`.

`Ssuper` is the supertrace system, `Splain` the plain-trace system.  The plain traces are only
`Γ₀(2)`-modular — worked example: symplectic fermions (`c = −2`, two odd fields of weight `1`,
`ℤ`-graded) have `str q^{L₀+1/12} = η(τ)²`, modular of weight `1` for all of `SL₂(ℤ)`, while
`tr q^{L₀+1/12} = (η(2τ)/η(τ))²`, whose stabiliser is `Γ₀(2)`.

⚠ Stating a `Γ_θ` theorem for this class would be a category error, and this is exactly the
class `p ≡ 2 (mod 4)` of the doublet family falls into. -/
def Conjecture_ZGradedSuper (Ssuper Splain : SuperCharacterSystem W ι) (hFam : Prop) : Prop :=
  SuperC2Cofinite W → IsIntegerGraded W → IsGenuinelySuper W →
    CharacterIndependent Ssuper → CompleteRationalFamily Ssuper hFam →
      SL2ZSuperModularityHolds Ssuper ∧ Gamma0TwoPlainTraceModularityHolds Splain

end Conjectures

/-! ## §8 A half-automorphy factor exists — on `⟨T²⟩ ≤ Γ_θ`

`SlashSub.HalfAutFactor` is only useful if it is satisfiable.  On the translation subgroup
`⟨T²⟩` the automorphy factor is identically `1`, so the constant square root works and the
multiplier is trivial.  This is a satisfiability check for the structure, in the same spirit as
`VertexOperatorAlgebra.toSuper_spinStatistics`.  The instance on all of `Γ_θ` (item T5 above) is
built in `Modularity/ThetaHalfAutFactor.lean` (`thetaHalfAutFactorExists`), not here. -/

/-- `T^n` has `c = 0`, `d = 1`, hence automorphy factor `1`, for every `n : ℤ`. -/
theorem autFactor_T_zpow (n : ℤ) (τ : UpperHalfPlane) :
    autFactor (ModularGroup.T ^ n) τ = 1 := by
  simp [autFactor, ModularGroup.coe_T_zpow]

theorem T_sq_zpow_eq (n : ℤ) :
    (ModularGroup.T ^ (2 : ℕ)) ^ n = ModularGroup.T ^ ((2 : ℤ) * n) := by
  rw [← zpow_natCast ModularGroup.T 2, ← zpow_mul]
  norm_num

/-- **A genuine `HalfAutFactor` on `⟨T²⟩`.**  Constant square root, trivial multiplier. -/
def translationHalfAutFactor :
    SlashSub.HalfAutFactor (Subgroup.zpowers (ModularGroup.T ^ (2 : ℕ))) where
  sq _ _ := 1
  sq_sq := by
    rintro A hA τ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hA
    rw [one_zpow, T_sq_zpow_eq, autFactor_T_zpow]
  sq_ne_zero := fun _ _ _ => one_ne_zero
  mult _ _ := 1
  cocycle := by intros; norm_num
  sq_one := fun _ => rfl

/-- `⟨T²⟩ ≤ Γ_θ`. -/
theorem zpowers_T_sq_le_thetaGroup :
    Subgroup.zpowers (ModularGroup.T ^ (2 : ℕ)) ≤ SlashSub.thetaGroup :=
  Subgroup.zpowers_le.mpr SlashSub.T_sq_mem_thetaGroup

/-- Existence of a half-automorphy factor on all of `Γ_θ` (item T5 above).  **Proved** as
`thetaHalfAutFactorExists` (`Modularity/ThetaHalfAutFactor.lean`, principal square root).  Take
`sq A τ := (cτ+d)^{1/2}` on the principal branch — `sq_sq`, `sq_ne_zero`, `sq_one` are then
immediate; the content is `τ`-independence of the multiplier, which follows from continuity plus
connectedness of `ℍ` (and the branch cut is never met when `c ≠ 0`, since
`Im(cτ+d) = c·Im τ ≠ 0`). -/
def ThetaHalfAutFactorExists : Prop :=
  Nonempty (SlashSub.HalfAutFactor SlashSub.thetaGroup)

/-! ## §9 The consistency check: the bosonic case, by restriction

This is the *trivial direction*, and it is the deliverable that a statement of this kind must
come with: a bosonic (purely even, `ℤ`-graded) VOA satisfying the already-proved `SL₂(ℤ)` Zhu
theorem must satisfy the `Γ_θ` statement written above.  If it did not, the statement would be
malformed.

⚠ It buys nothing mathematically — for a `VertexOperatorAlgebra` the `ℤ`-grading is baked in,
`T` is available (`SlashSub.realisesLaw_T`), and `Γ_θ`-modularity is a corollary of
`SL₂(ℤ)`-modularity; `SlashSub.realisesLawOn_thetaGroup_of_S` records exactly this.  Its value
is as a type-check on §5–§6. -/

section Bosonic

variable {W : VertexOperatorAlgebra 𝒱} {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The repo's `sqWeightSpace_eq_bot_of_neg`, generalized.**  A square-bracket weight space
at a weight that is not a natural number vanishes.  (The repo proves this only for negative
integers; the proof is the same, using `sqWeightSpace_nat_spans_top` and
`sqWeightSpace_iSupIndep`.)  This is what makes the odd-doubled-weight branch of
`modularLawOn_thetaGroup_of_zhuModularityAnalytic` go through. -/
theorem sqWeightSpace_eq_bot_of_not_natCast (W : VertexOperatorAlgebra 𝒱) {k : ℂ}
    (hk : ∀ m : ℕ, (m : ℂ) ≠ k) : sqWeightSpace W k = ⊥ := by
  have hind := sqWeightSpace_iSupIndep W k
  have htop : (⊤ : Submodule ℂ 𝒱) ≤ ⨆ j : {j : ℂ // j ≠ k}, sqWeightSpace W (j : ℂ) := by
    rw [← sqWeightSpace_nat_spans_top W]
    refine iSup_le (fun m ↦ ?_)
    exact le_iSup_of_le (⟨(m : ℂ), hk m⟩ : {j : ℂ // j ≠ k}) le_rfl
  have hsupp : (⨆ j : {j : ℂ // j ≠ k}, sqWeightSpace W (j : ℂ)) = ⊤ := eq_top_iff.mpr htop
  rw [iSup_subtype] at hsupp
  rw [hsupp] at hind
  exact disjoint_top.mp hind

/-- A square-bracket weight space at a strictly half-integer weight vanishes. -/
theorem sqWeightSpace_eq_bot_of_half (W : VertexOperatorAlgebra 𝒱) {k : ℂ}
    (hk : ∀ m : ℤ, ((m : ℂ) / 2) ≠ k) : sqWeightSpace W k = ⊥ := by
  refine sqWeightSpace_eq_bot_of_not_natCast W (fun n hn => hk (2 * n) ?_)
  rw [← hn]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The trace functions vanish at `v = 0`. -/
theorem traceFun_zero (Mfam : ι → IrrModule W) (hw : ι → ℂ) (i : ι) (τ : UpperHalfPlane) :
    traceFun Mfam hw i 0 τ = 0 := by
  simp [traceFun, qEvalAt]

/-- **The `SuperCharacterSystem` of a bosonic modular datum.**  `sqWt` is the genuine
square-bracket grading `sqWeightSpace W`, and `chi` the genuine analytic one-point functions
`traceFun`. -/
noncomputable def ofModularData (D : ModularData W ι) :
    SuperCharacterSystem W.toSuper ι where
  sqWt := sqWeightSpace W
  sqWt_halfInt := fun _ hk => sqWeightSpace_eq_bot_of_half W hk
  vacuum_mem_sqWt := by
    have := vacuum_mem_sqWeightSpace_zero W
    simpa using this
  chi := traceFun D.Mfam D.h
  chi_zero := fun i τ => traceFun_zero D.Mfam D.h i τ

/-- **THE CONSISTENCY CHECK.**

A bosonic VOA whose one-point functions satisfy Zhu's analytic modularity satisfies the
half-integral `Γ_θ` law of §6 — for **every** half-automorphy factor `J` on `Γ_θ`.

The proof is exactly the two mechanisms of §2, read backwards.  On even doubled weight `m = 2n`
the half-integral factor collapses to the integral one, `J.sq A τ ^ (2n) = (cτ+d)ⁿ`
(`SlashSub.HalfAutFactor.zpow_even`), and Zhu's law applies verbatim.  On odd `m` — and on even
`m < 0` — the square-bracket weight space is `⊥`, so `v = 0` and both sides vanish: a bosonic
algebra simply has no states there.  That is precisely `toSuper_not_hasStrictHalfWeight`. -/
theorem modularLawOn_thetaGroup_of_zhuModularityAnalytic (D : ModularData W ι)
    (hD : ZhuModularityAnalytic D) (J : SlashSub.HalfAutFactor SlashSub.thetaGroup) :
    IsGammaThetaModular (ofModularData D) J (fun A i j => D.rep A i j) := by
  intro A hA m v hv i τ
  by_cases hex : ∃ n : ℕ, (n : ℂ) = (m : ℂ) / 2
  · obtain ⟨n, hn⟩ := hex
    have h2 : (2 : ℂ) * (n : ℂ) = (m : ℂ) := by rw [hn]; ring
    have hm : (2 : ℤ) * (n : ℤ) = m := by exact_mod_cast h2
    have hv' : v ∈ sqWeightSpace W ((n : ℕ) : ℂ) := by
      show v ∈ sqWeightSpace W ((n : ℂ))
      rw [hn]; exact hv
    have hlaw := hD A n v hv' i τ
    change traceFun D.Mfam D.h i v (A • τ)
      = J.sq A τ ^ m * ∑ j, D.rep A i j * traceFun D.Mfam D.h j v τ
    rw [hlaw, ← hm, J.zpow_even hA τ (n : ℤ), zpow_natCast]
  · push Not at hex
    have hbot : sqWeightSpace W ((m : ℂ) / 2) = ⊥ :=
      sqWeightSpace_eq_bot_of_not_natCast W hex
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule ℂ 𝒱) := hbot ▸ hv
      simpa using this
    subst hv0
    change traceFun D.Mfam D.h i 0 (A • τ)
      = J.sq A τ ^ m * ∑ j, D.rep A i j * traceFun D.Mfam D.h j 0 τ
    rw [traceFun_zero]
    simp [traceFun_zero]

/-- The same, packaged as the existential `GammaThetaModularityHolds`, given a half-automorphy
factor `ThetaHalfAutFactorExists` (which is proved: `thetaHalfAutFactorExists`). -/
theorem gammaThetaModularityHolds_of_zhuModularityAnalytic (D : ModularData W ι)
    (hD : ZhuModularityAnalytic D) (hJ : ThetaHalfAutFactorExists) :
    GammaThetaModularityHolds (ofModularData D) := by
  obtain ⟨J⟩ := hJ
  exact ⟨J, _, modularLawOn_thetaGroup_of_zhuModularityAnalytic D hD J⟩

/-- **The character form of the consistency check, unconditional.**  No half-automorphy
factor is involved, so nothing is assumed: the characters of a bosonic VOA satisfying Zhu's
theorem are `Γ_θ`-modular (indeed `SL₂(ℤ)`-modular). -/
theorem characterModularOn_top_of_zhuModularityAnalytic (D : ModularData W ι)
    (hD : ZhuModularityAnalytic D) :
    CharacterModularOn ⊤ (ofModularData D).character (fun A i j => D.rep A i j) := by
  intro A _ i τ
  have hvac : W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := vacuum_mem_sqWeightSpace_zero W
  have hlaw := hD A 0 W.vacuum hvac i τ
  change traceFun D.Mfam D.h i W.vacuum (A • τ)
    = ∑ j, D.rep A i j * traceFun D.Mfam D.h j W.vacuum τ
  simpa using hlaw

theorem gammaThetaCharacterModularityHolds_of_zhuModularityAnalytic (D : ModularData W ι)
    (hD : ZhuModularityAnalytic D) :
    GammaThetaCharacterModularityHolds (ofModularData D) :=
  ⟨_, (characterModularOn_top_of_zhuModularityAnalytic D hD).mono le_top⟩

/-- The integral-weight law on all of `SL₂(ℤ)` is exactly `ZhuModularityAnalytic`. -/
theorem integerWeightModularLawOn_top_of_zhuModularityAnalytic (D : ModularData W ι)
    (hD : ZhuModularityAnalytic D) :
    IntegerWeightModularLawOn (ofModularData D) ⊤ (fun A i j => D.rep A i j) :=
  fun A _ n v hv i τ => hD A n v hv i τ

end Bosonic

/-! ## §10 The consistency check, chained off `C₂`-cofiniteness

`zhuModularity_pinned_of_C2Cofinite` is the library's main modularity theorem: a `C₂`-cofinite,
rational
bosonic VOA has an `SL₂(ℤ)` modular datum, pinned to the given module family.  Composing it with
§9 gives the bosonic shadow of the target statement — *the characters of a `C₂`-cofinite vertex
operator algebra are modular for `Γ_θ`* — with `Γ_θ` here being the honest, proper, index-3
subgroup of §1 rather than a synonym for `SL₂(ℤ)`. -/

section C2

variable {W : VertexOperatorAlgebra 𝒱} {ι : Type u} [Fintype ι] [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **The characters of a `C₂`-cofinite, rational VOA are `Γ_θ`-modular.**  Bosonic, so this
is a restriction of the full theorem; it is the type-check that §5–§7 are stated correctly.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem characterModularOn_thetaGroup_of_C2Cofinite [Finite (Φ W)]
    (Mfam : ι → IrrModule W) (hw : ι → ℂ)
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hw i))
    (hsep : ∀ j k : ι, j ≠ k → hw j = hw k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ ρ : SL(2, ℤ) → ι → ι → ℂ,
      CharacterModularOn SlashSub.thetaGroup
        (fun i τ => traceFun Mfam hw i W.vacuum τ) ρ := by
  obtain ⟨D, hM, hh, hD⟩ :=
    zhuModularity_pinned_of_C2Cofinite Mfam hw hC2 hss Pr hcard hcw hsep
  refine ⟨fun A i j => D.rep A i j, ?_⟩
  intro A _ i τ
  have hvac : W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := vacuum_mem_sqWeightSpace_zero W
  have hlaw := hD A 0 W.vacuum hvac i τ
  rw [hM, hh] at hlaw
  simpa using hlaw

end C2

end VOA.GammaThetaStmt
