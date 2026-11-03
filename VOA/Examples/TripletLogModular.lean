/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSpanning
import VOA.Examples.TripletW2Log
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Rationality forbids a `log q`: the modular route to the irrationality of the triplet `W(2)`

The physics argument this file formalizes, in the project lead's words:

> *Strongly rational VOAs have a finite number of simples, which are all ordinary, so no logs can
> appear in the characters, and Zhu tells us that the `S`-transform of the vacuum character is a
> linear combination of the characters of the other simples.*

Two independent halves are built here, both `sorry`-free.

* **§1–§2 — the module half.**  A vertex operator algebra whose module category contains a
  grading-restricted *generalized* module with `L₀ⁿⁱˡ ≠ 0` is not rational.  Combined with the
  logarithmic `W(2)`-module already constructed in `Examples/TripletW2Log.lean`, this gives
  `¬ AdmissiblyRational W(2)` from named hypotheses.
* **§4–§7 — the character half.**  A `τ`-linear ("`log q`") term cannot occur in any finite
  `ℂ`-combination of `T`-eigenfunctions on `ℍ`, and Zhu's law puts `S·χ` into exactly such a
  combination.  Hence a logarithmic `S`-transform of the vacuum character contradicts Zhu, and
  therefore rationality.
* **§3** is the vacuum character of `W(2)` itself, as a formal `q`-series built from the
  repository's own grading of `W(2)` rather than from any product formula.

**Where "all the simples are ordinary" enters the character half.**  It is not an extra
hypothesis there: `Modularity.ZhuTheorem.ModularData` carries `Mfam : ι → IrrModule W`, a family
of **ordinary** (`OrdVModule`) modules, so each character is a `qEvalAt` — a `q^h` times a power
series — *by construction*, hence a `T`-eigenfunction (`charOf_isTEigen`).  Steps 1–2 of the
lead's chain are therefore what makes the right-hand side of Zhu's law log-free, and they are
built into the shape of `ZhuVacuumModularity`.

## Main results

* `AllModulesOrdinary`, `RationalImpliesOrdinary` — the "rational ⟹ ordinary" step, stated as an
  explicit **named hypothesis** (it is a theorem of the literature, not a definitional
  consequence; see the *Named hypotheses* section below).
* `not_admissiblyRational_of_L0nil_ne_zero` — a genuine logarithmic module refutes rationality.
* `not_admissiblyRational_tripletW2_of_logModule` — the `W(2)` instance of the previous item, run
  off `SympFerm.tripletW2Log_L0nil_ne_zero`.
* `w2VacChar`, `w2VacChar_shifted`, `w2VacChar_grade_one`, `w2VacChar_support` — the vacuum
  character of `W(2)` as a formal `q`-series, its exponent support `1/12 + ℤ` (i.e. the
  `q^{-c/24} = q^{1/12}` normalization at `c = -2`), and the coefficients the repository actually
  proves.
* `IsTEigen`, `logFreeSpan`, `HasLogTerm` — the design decision that makes "has no `log q`"
  precise: see *The `log q` predicate* below.
* `linTerm_notMem_logFreeSpan` — **the rigidity lemma.**  If `B` is a nonzero
  `T`-eigenfunction with nonzero eigenvalue then `τ ↦ τ·B(τ)` is not in the span of
  `T`-eigenfunctions.  This is the formal content of "ordinary modules have no `log q`", and the
  repository had nothing like it.
* `charOf_mem_logFreeSpan`, `charOf_smul_mem_logFreeSpan` — every character of a
  `ModularData` family is a `T`-eigenfunction, and Zhu's law places each modular transform of a
  character in `logFreeSpan`.
* `not_zhuModularityAnalytic_of_hasLogTerm`, `not_admissiblyRational_of_hasLogTerm_vacChar`,
  `not_admissiblyRational_tripletW2_of_logS` — the contradiction, and the `W(2)` statement.
* ⚠ `hasLogTerm_coe`, `logFreeSpan_ne_top` — **non-vacuity guards**: `HasLogTerm` is inhabited and
  `logFreeSpan` is a proper subspace, so §4 is not a statement about an empty class.
* `tripletW2_vacuum_ne_zero`, `w2VacChar_low`, `vacChar_tripletW2` — the vacuum of `W(2)` is
  nonzero, the two low character coefficients are `1, 0`, and the formal series of §3 is the one
  the analytic statement of §7 is about.

## The `log q` predicate — the design decision, stated explicitly

The statement requires a notion of "the character has a `log q` term".  Three candidates were
considered and two were rejected:

1. *"The formal `q`-series has a `log` coefficient."*  **Impossible to express**, and that is the
   point: `Modules.Character.FormalQSeries` is a coefficient function `ℂ → ℂ`, and
   `Modularity.ConvergenceBridge.qEvalAt χ h τ = q^h · Σ_{n≥0} χ(h+n) qⁿ` is *by construction*
   `q^h` times a power series.  A `log q` cannot be written in that shape at all.
2. *"`tr_M L₀ⁿⁱˡ ≠ 0` on some graded piece."*  **False as stated, and a trap**: `L₀ⁿⁱˡ` is
   nilpotent, so every trace `tr (L₀ⁿⁱˡ)^k` vanishes.  This is exactly why the logarithmic
   literature needs *pseudo*-traces (`Modularity.PseudoTrace`), and it is why the module half
   (§2) is kept separate from the character half here rather than being routed through a trace.
3. **The choice made here.**  A `q`-series `q^{h}·Σ aₙqⁿ` is, for free and with no summability
   hypothesis whatsoever, an eigenfunction of `τ ↦ τ+1` with eigenvalue `e^{2πih}`
   (`isTEigen_qEvalAt`).  So define

   * `logFreeSpan` — the `ℂ`-span inside `ℍ → ℂ` of all `T`-eigenfunctions.  Every character of
     an ordinary module lies in it, and so does every finite linear combination of characters,
     which is what Zhu's law produces.
   * `HasLogTerm f` — `f = A + τ·B` with `A ∈ logFreeSpan`, `B` a `T`-eigenfunction with nonzero
     eigenvalue, and `B ≠ 0`.  Writing `τ = log q / 2πi`, `τ·B` *is* the `log q` term.

   `notMem_logFreeSpan_of_hasLogTerm` then says: a function with a `log q` term is not a linear
   combination of ordinary characters.  This is the precise sense in which "ordinary ⟹ no logs".

⚠ Note that `A` is only required to lie in `logFreeSpan`, **not** to be a single eigenfunction.
That is not laziness: for `c = -2` the constant term of `χ_0(-1/τ)` is
`¼(χ_{-1/8} - χ_{3/8})(τ)`, whose two summands have `T`-eigenvalues `e^{-iπ/12}` and
`e^{11iπ/12} = -e^{-iπ/12}` — *different*.  A definition demanding a single eigenvalue for `A`
would not be satisfiable by the actual `W(2)` data, and the resulting theorem would be vacuous.

## ⚠ Named hypotheses — what is assumed, and the citation for each

Nothing below is `sorry`-ed, `admit`-ted, or axiomatized.  Four facts of the literature are
carried as explicit named `Prop`s, each an argument of the theorem that uses it.

1. `RationalImpliesOrdinary W` — *rational ⟹ every grading-restricted generalized module is
   `L₀`-semisimple*.  **A theorem, not a definitional consequence.**  `AdmissiblyRational`
   (`Modules/AdmissibleModule.lean`, Zhu / Dong–Li–Mason) is complete reducibility of the
   *admissible* modules; McRae's Def. 2.4 rationality is complete reducibility of the *generalized*
   modules of `Modules.LogVModule`.  That the two agree — and in particular that a rational VOA has
   no generalized module with a Jordan block — is Huang–Lepowsky–Zhang / McRae.
   *Reference:* R. McRae, *On rationality for `C₂`-cofinite vertex operator algebras*, Def. 2.4
   and §2; Huang–Lepowsky–Zhang, arXiv:1012.4193.
   ⚠ A transcription of Gannon Def. 5.3.2 is the wrong antecedent for
   this citation — Gannon's clause (1) quantifies only over **ordinary** modules.  See the `def`'s
   own docstring.
2. The four inputs of `SympFerm.tripletW2Log_L0nil_ne_zero` (`hAnm`, `hA`, `hgate`, `hnd`) —
   documented in full in `Examples/TripletW2Log.lean`; `hnd : OmegaJordanAt tripletW2 h` is the
   crux there (`[ω] − h ∉ A(𝒱)([ω] − h)²`).  Passed straight through; nothing is added here.
3. `ZhuVacuumModularity W` — *rational (admissible sense) ⟹ there is a finite modular datum
   satisfying Zhu's
   analytic law whose `i`-th character is the vacuum character*.  This is Zhu's Theorem 5.3.8 in
   the shape the repository already states it (`Modularity.BlockSpanning.ZhuModularityAnalytic`,
   `Modularity.ZhuTheorem.ModularData`); the reason it is carried rather than derived is that
   `Modularity.GNProp8Closure.zhuModularity_pinned_of_C2Cofinite` additionally needs
   `C₂`-cofiniteness of `W(2)`, finiteness of `Φ(W(2))`, and an explicit family of irreducible
   `W(2)`-modules, none of which the repository has.
   *Reference:* Y. Zhu, *Modular invariance of characters of vertex operator algebras*, J. Amer.
   Math. Soc. **9** (1996) 237–302, Thm. 5.3.2–5.3.3; Gannon §5.3.3, Thm. 5.3.8.
4. `HasLogTerm (fun τ => vacChar tripletW2 (S • τ))` — **the one analytic input.**  The `c = -2`
   computation
   `χ_0(-1/τ) = ¼[χ_{-1/8}(τ) - χ_{3/8}(τ)] + (-iτ/2)[χ_0(τ) - χ_1(τ)]`,
   i.e. `A = ¼(χ_{-1/8} - χ_{3/8})`, `B = (-i/2)(χ_0 - χ_1)`, `ν = e^{iπ/6}` (both `χ_0` and
   `χ_1` have `T`-eigenvalue `e^{2πi/12}` since `h - c/24 = 1/12` and `13/12`).  In `η`-quotients
   `χ_0 = ½[η(2τ)²/η(τ)² + η(τ)²]`, `χ_1 = ½[η(2τ)²/η(τ)² - η(τ)²]`, so
   `B = (-i/2)η(τ)² ≠ 0` — the whole `τ`-term is the *weight-one* piece `η(τ)²` of the character.
   *Reference:* Fuchs–Hwang–Semikhatov–Tipunin, arXiv:hep-th/0306274, Prop. 3.4 (the explicit
   `-2iτ` term and the automorphy factor `j_p(γ,τ)` introduced to absorb it); Flohr–Gaberdiel,
   *Logarithmic torus amplitudes*, arXiv:hep-th/0509075, eqs. (22)–(25).
   ⚠ **Not proved here.**  Proving it needs the closed form
   `char W(2) = q^{1/12}·½[∏(1+qⁿ)² + ∏(1-qⁿ)²]` as an identity between the repository's
   `gradedDim (adjointModule tripletW2)` and Mathlib's `ModularForm.eta`, which is an
   infinite-product/word-basis problem: `Examples/SymplecticFermion*.lean` provides no basis, no
   `LinearIndependent`, and no `finrank` value for any `gradingSF n`.

## Relation to the companion algebraic route

`Examples/TripletIrrational.lean` (deliberately not imported here) attacks
the same conclusion through non-semisimplicity of the Zhu algebra `A(W(2))`.  To avoid a rival
vocabulary — and an import-time name clash — **this file introduces no rationality predicate at
all**: it uses `AdmissiblyRational` (`Modules/AdmissibleModule.lean`) directly, which is the same
predicate that file's `¬`-theorems target.  Everything new here lives in the fresh namespace
`VOA.LogModular`.  The two routes share only their conclusion, exactly as intended:
theirs isolates a Zhu-algebra fact, ours isolates a modular-transform fact.

## Status

`sorry`-free, `admit`-free, `native_decide`-free, `unsafe`-free.  No new axiom; the theorem
`VOA.pbw` is **not** used (nothing here touches
`BottomProjection`).
Not proved here: the four named hypotheses above are carried, not discharged; each is an explicit argument of
the theorem that consumes it, and each is a statement of the cited literature.

## References
* Gannon, *Moonshine beyond the Monster*, §5.3.1–§5.3.3 (Def. 5.3.2, Lem. 5.3.3, Thm. 5.3.8).
* Y. Zhu, J. Amer. Math. Soc. **9** (1996) 237–302.
* R. McRae, *On rationality for `C₂`-cofinite vertex operator algebras*, Def. 2.4.
* Fuchs–Hwang–Semikhatov–Tipunin, arXiv:hep-th/0306274, §3–§4.
* Flohr–Gaberdiel, arXiv:hep-th/0509075, §2.
-/

namespace VOA.LogModular

open scoped BigOperators MatrixGroups
open VOA

universe u v

/-! ## §1  Ordinariness of the module category, and the rationality bridge

The repository already has both endpoints:
`AdmissiblyRational` (`Modules/AdmissibleModule.lean`, Zhu / Dong–Li–Mason) on the rationality
side, and `Modules.LogVModule.IsL0Semisimple` / `L0nil` (McRae Def. 2.4) on the generalized-module
side.  Only the bridge between them is new, and it is carried as a named hypothesis. -/

section Ordinary

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Every grading-restricted generalized module is ordinary.**

`LogVModule` is McRae Def. 2.4 (Huang–Lepowsky–Zhang) — a weak module graded by *generalized*
`L₀`-eigenspaces — and `IsL0Semisimple` says the generalized eigenspaces are honest eigenspaces,
i.e. that the module is an `OrdVModule` in disguise (`LogVModule.toOrd`).  So this predicate is
literally "the module category contains no logarithmic object". -/
def AllModulesOrdinary (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : LogVModule W M), N.IsL0Semisimple

/-- ⚠ **The named hypothesis "rational ⟹ ordinary".**

This is a **theorem of the literature, not a definitional consequence**, and it is deliberately
*not* folded into any definition: `AdmissiblyRational` is a statement about the *admissible*
module category, so on its own it says nothing about `LogVModule`s.  Building the conclusion into a
rationality predicate would make `not_admissiblyRational_of_L0nil_ne_zero` a tautology.

*Reference:* McRae, *On rationality for `C₂`-cofinite VOAs*, Def. 2.4 and §2; Huang–Lepowsky–Zhang
arXiv:1012.4193.  For a rational vertex operator algebra every grading-restricted generalized
module is a direct sum of irreducible ordinary modules, hence `L₀` acts semisimply.

⚠⚠ **The antecedent is `AdmissiblyRational`, by licence.**  Attaching McRae's / HLZ's theorem
to a transcription of Gannon Def. 5.3.2 would not be licensed: McRae
and HLZ prove their statement for *rational* VOAs in the standard sense, "the category of
grading-restricted generalized modules is semisimple", which the repository formalizes as
`AdmissiblyRational` (`Modules/AdmissibleModule.lean`).  Gannon's clause (1) asks complete
reducibility only of **ordinary** modules and so is strictly weaker
(`Modules/RationalityLattice.lean` §8.2); a hypothesis with a weaker antecedent is a *stronger*
assumption, and that one would be unlicensed.

⚠ Consequently the faithful `GannonRational` version of this hypothesis is **deliberately not
stated**: no cited theorem supports it, and every downstream `¬ …` theorem in this file is
therefore about `AdmissiblyRational`, not about `GannonRational`.  The two conclusions are
incomparable; neither is claimed to imply the other. -/
def RationalImpliesOrdinary (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AdmissiblyRational W → AllModulesOrdinary W

/-- The free direction, for the record: an ordinary module is `L₀`-semisimple as a logarithmic
module.  (`OrdVModule.toLog_isL0Semisimple`, restated so that the two directions sit together.) -/
theorem isL0Semisimple_toLog {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M]
    [Module ℂ M] (N : OrdVModule W M) : N.toLog.IsL0Semisimple :=
  N.toLog_isL0Semisimple

/-- **A genuine logarithmic module refutes ordinariness.**  Unconditional. -/
theorem not_allModulesOrdinary_of_L0nil_ne_zero {W : VertexOperatorAlgebra 𝒱} {M : Type u}
    [AddCommGroup M] [Module ℂ M] (N : LogVModule W M) (hN : N.L0nil ≠ 0) :
    ¬ AllModulesOrdinary W := fun hall =>
  hN ((LogVModule.isL0Semisimple_iff_L0nil_eq_zero N).mp (hall N))

/-- **A genuine logarithmic module refutes rationality**, given the named bridge.

This is the module-level form of steps 1–2 of the lead's chain: *rational ⟹ all simples ordinary*,
contrapositive.  No character, no modular transform, no analysis. -/
theorem not_admissiblyRational_of_L0nil_ne_zero {W : VertexOperatorAlgebra 𝒱}
    (hro : RationalImpliesOrdinary W) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (hN : N.L0nil ≠ 0) : ¬ AdmissiblyRational W := fun hwr =>
  not_allModulesOrdinary_of_L0nil_ne_zero N hN (hro hwr)

/-- The same statement phrased through the explicit rank-two Jordan pair `L₀ x = h·x + y`,
`y ≠ 0`, which is the shape `LogVModule` consumers produce. -/
theorem not_admissiblyRational_of_jordan_pair {W : VertexOperatorAlgebra 𝒱}
    (hro : RationalImpliesOrdinary W) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) {h : ℂ} {x y : M} (hx : x ∈ N.weight h) (hy : y ≠ 0)
    (hjor : N.L0op x = h • x + y) : ¬ AdmissiblyRational W := by
  refine not_admissiblyRational_of_L0nil_ne_zero hro N (fun hnil => hy ?_)
  have hss : N.IsL0Semisimple := (LogVModule.isL0Semisimple_iff_L0nil_eq_zero N).mpr hnil
  have := hss h x hx
  rw [hjor] at this
  exact add_eq_left.mp this

end Ordinary

/-! ## §2  The triplet `W(2)`: a logarithmic module refutes rationality

`Examples/TripletW2Log.lean` builds `SympFerm.tripletW2Log`, a `LogVModule` over `W(2)` with a
rank-two `L₀` Jordan block, from four named inputs.  Feeding it into §1 gives the first of the two
independent irrationality statements of this file. -/

section TripletModuleRoute

open SympFerm

/-- **`W(2)` is not rational — the module route.**

All five hypotheses are explicit and none is discharged here:
`hro` is the McRae bridge of §1, and `hAnm`, `hA`, `hgate`, `hnd` are exactly the four inputs of
`SympFerm.tripletW2Log_L0nil_ne_zero`, documented in `Examples/TripletW2Log.lean` (`hnd`, the
non-semisimplicity of `[ω]` at `h` in the Zhu algebra, is the crux there).

Note this route uses **no** modular data, no character, and no analysis; it is completely
independent of §4–§7 below. -/
theorem not_admissiblyRational_tripletW2_of_logModule
    (hro : RationalImpliesOrdinary tripletW2) (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2)) (hgate : DJAnnEqAn tripletW2 0)
    (hnd : OmegaJordanAt tripletW2 h) :
    ¬ AdmissiblyRational tripletW2 :=
  not_admissiblyRational_of_L0nil_ne_zero hro (tripletW2Log h hAnm hA)
    (tripletW2Log_L0nil_ne_zero h hAnm hA hgate hnd)

end TripletModuleRoute

/-! ## §3  The vacuum character of `W(2)` as a formal `q`-series

The repository's character is a *coefficient function* `FormalQSeries = ℂ → ℂ`, the coefficient of
`q^e`, with the Casimir shift `q^{-c/24}` already built into the indexing
(`Modules.Character.gradedDim`).  At `c = -2` this puts the exponents on `1/12 + ℤ`, i.e.
`χ_{W(2)}(τ) = q^{1/12}·Σ_{n≥0} (dim W(2)_n) qⁿ`, which is the `q^{-c/24} = q^{1/12}` prefactor of
the physics normalization.

⚠ **What is and is not proved.**  The coefficients are *defined* through the repository's own
grading machinery — `adjWeight`, `tripletW2.grading` — and are **not** asserted from the product
formula.  Consequently only the coefficients the repository actually establishes appear as
theorems: the exponent support, `dim W(2)_1 = 0` (from `tripletW2_grading_one`), and
`dim W(2)_0 = 1` (from `vacuum_grade`, given a nonzero vacuum).  The remaining audit values
`dim W(2)_n = 1, 4, 5, 8, 10` for `n = 2,…,6` — equivalently
`½[∏(1+qⁿ)² + ∏(1-qⁿ)²] = 1 + q² + 4q³ + 5q⁴ + 8q⁵ + 10q⁶ + …` — are **not** proved anywhere in
the repository (there is no basis, no `LinearIndependent`, and no `finrank` value for any
`gradingSF n`), so they are not stated here. -/

section Character

open SympFerm

/-- **The vacuum character of `W(2)`** as a formal `q`-series: the graded dimension of the adjoint
module, with the `q^{-c/24}` shift carried in the exponent index. -/
noncomputable def w2VacChar : FormalQSeries := gradedDim (adjointModule tripletW2)

/-- Unwinding the `c = -2` Casimir shift: the coefficient of `q^e` is `dim W(2)_{e - 1/12}`. -/
theorem w2VacChar_apply (e : ℂ) :
    w2VacChar e = (Module.finrank ℂ (adjWeight tripletW2 (e - 1 / 12)) : ℂ) := by
  have hshift : e + tripletW2.centralCharge / 24 = e - 1 / 12 := by
    rw [tripletW2_centralCharge]; ring
  change ((Module.finrank ℂ (adjWeight tripletW2 (e + tripletW2.centralCharge / 24)) : ℂ)) = _
  rw [hshift]

/-- **The exponent support is `1/12 + ℤ`**: `χ_{W(2)}(τ) = q^{1/12}·(power series in q)`.
This is the formal statement that the character carries the `q^{-c/24} = q^{1/12}` prefactor at
`c = -2` and nothing else — no half-integral or irrational exponents occur. -/
theorem w2VacChar_support {e : ℂ} (he : ∀ m : ℤ, (m : ℂ) ≠ e - 1 / 12) : w2VacChar e = 0 := by
  rw [w2VacChar_apply, adjWeight_eq_bot _ he]
  simp

/-- **The coefficient of `q^{1/12+m}` is `dim W(2)_m`**, computed by the repository's own
`ℤ`-grading of `W(2)` — not by any product formula. -/
theorem w2VacChar_shifted (m : ℤ) :
    w2VacChar ((1 / 12 : ℂ) + (m : ℂ)) = (Module.finrank ℂ (tripletW2.grading m) : ℂ) := by
  rw [w2VacChar_apply, show ((1 / 12 : ℂ) + (m : ℂ)) - 1 / 12 = (m : ℂ) by ring, adjWeight_cast]

/-- **The `n = 1` coefficient vanishes**: `W(2)` has no conformal weight-one states
(`tripletW2_grading_one`), the first nontrivial entry of the audit sequence `1, 0, 1, 4, …`. -/
theorem w2VacChar_grade_one : w2VacChar ((1 / 12 : ℂ) + 1) = 0 := by
  have h := w2VacChar_shifted 1
  rw [Int.cast_one] at h
  rw [h, tripletW2_grading_one]
  simp

/-- **The `n = 0` coefficient is `1`**: grade zero is `ℂ|0⟩` (`vacuum_grade`), the leading entry of
the audit sequence.  The hypothesis `hvac` is the (unavoidable) nondegeneracy input — the axioms
of `VertexOperatorAlgebra` do not exclude the zero vertex operator algebra. -/
theorem w2VacChar_grade_zero (hvac : tripletW2.vacuum ≠ 0) : w2VacChar (1 / 12 : ℂ) = 1 := by
  have h := w2VacChar_shifted 0
  rw [Int.cast_zero, add_zero] at h
  rw [h, tripletW2.vacuum_grade, finrank_span_singleton hvac]
  norm_num

/-- **The vacuum of `W(2)` is nonzero.**  `FockSF = CliffordAlgebra QSF` over `ℂ` is nontrivial
(`2` is invertible in `ℂ`), and `tripletW2.vacuum` is `1 ∈ FockSF`. -/
theorem tripletW2_vacuum_ne_zero : tripletW2.vacuum ≠ 0 := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  haveI : Nontrivial FockSF := inferInstance
  intro hz
  have h2 : ((tripletW2.vacuum : CliffordAlgebra.evenOdd QSF 0) : FockSF) = 0 := by rw [hz]; rfl
  exact one_ne_zero (α := FockSF) h2

/-- **The two coefficients the repository proves**: `χ_{W(2)} = q^{1/12}(1 + 0·q + …)`, i.e.
the leading `1, 0` of the audit sequence `1, 0, 1, 4, 5, 8, 10, …`. -/
theorem w2VacChar_low : w2VacChar (1 / 12 : ℂ) = 1 ∧ w2VacChar ((1 / 12 : ℂ) + 1) = 0 :=
  ⟨w2VacChar_grade_zero tripletW2_vacuum_ne_zero, w2VacChar_grade_one⟩

end Character

/-! ## §4  "No `log q`" — the rigidity of `T`-eigenfunctions

The engine of the whole character half, and the piece the repository was missing.  A `q`-series
`q^h·Σ aₙqⁿ` is an eigenfunction of the shift `τ ↦ τ+1`; a `log q` term is *not*, and cannot be
repaired by adding eigenfunctions, because `τ·B` sits in a genuine size-two Jordan block of the
shift operator while a span of eigenvectors is semisimple.

The proof is the annihilating-polynomial form of that sentence.  If `x` lies in the span of
`T`-eigenfunctions with eigenvalues in a finite set `E`, then `∏_{μ∈E}(T − μ)` kills `x`.  For
`x = τ·B` with `T B = ν·B` one has `(T − ν)(τ·B) = ν·B`, so `∏_{μ∈E∖{ν}}(T − μ)` applied to the
result gives `ν·(∏_{μ∈E∖{ν}}(ν − μ))·B`, and every factor there is nonzero.  Hence `B = 0`.
Deleting `ν` from `E` before taking the product is what makes the argument work with **no**
case distinction on whether `ν` is itself an eigenvalue, and with no derivative of the
annihilating polynomial. -/

section Rigidity

open Polynomial

/-- The **modular `T`-shift** `τ ↦ τ + 1`, as a `ℂ`-linear endomorphism of `ℍ → ℂ`. -/
noncomputable def Tsh : Module.End ℂ (UpperHalfPlane → ℂ) where
  toFun f := fun τ => f ((1 : ℝ) +ᵥ τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem Tsh_apply (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    Tsh f τ = f ((1 : ℝ) +ᵥ τ) := rfl

/-- `f` is a **`T`-eigenfunction** with eigenvalue `μ`: `f(τ+1) = μ·f(τ)`.  Every `q`-expansion
`q^h·Σ aₙqⁿ` is one, with `μ = e^{2πih}` (`isTEigen_qEvalAt`). -/
def IsTEigen (μ : ℂ) (f : UpperHalfPlane → ℂ) : Prop := Tsh f = μ • f

theorem isTEigen_iff (μ : ℂ) (f : UpperHalfPlane → ℂ) :
    IsTEigen μ f ↔ ∀ τ : UpperHalfPlane, f ((1 : ℝ) +ᵥ τ) = μ * f τ :=
  ⟨fun h τ => congrFun h τ, fun h => funext h⟩

/-- **The log-free functions**: the `ℂ`-span inside `ℍ → ℂ` of all `T`-eigenfunctions.  This
is where Zhu's law lands every modular transform of a character. -/
noncomputable def logFreeSpan : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {f : UpperHalfPlane → ℂ | ∃ μ : ℂ, IsTEigen μ f}

theorem mem_logFreeSpan_of_isTEigen {μ : ℂ} {f : UpperHalfPlane → ℂ} (hf : IsTEigen μ f) :
    f ∈ logFreeSpan := Submodule.subset_span ⟨μ, hf⟩

/-- A polynomial in an operator acts on an eigenvector by the polynomial's value at the
eigenvalue. -/
theorem aeval_apply_of_eigen {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    {x : M} {ν : ℂ} (hx : T x = ν • x) (P : ℂ[X]) :
    (Polynomial.aeval T P) x = P.eval ν • x := by
  have hpow : ∀ k : ℕ, (T ^ k) x = ν ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, hx, map_smul, ih, smul_smul]
        congr 1
        ring
  refine Polynomial.induction_on' P ?_ ?_
  · intro p q hp hq
    rw [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  · intro n a
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, hpow, Polynomial.eval_monomial,
      Module.algebraMap_end_apply, smul_smul]

/-- Divisibility transfers annihilation: if `P(T)x = 0` and `P ∣ Q` then `Q(T)x = 0`. -/
theorem aeval_eq_zero_of_dvd {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    {P Q : ℂ[X]} (hdvd : P ∣ Q) {x : M} (hx : (Polynomial.aeval T P) x = 0) :
    (Polynomial.aeval T Q) x = 0 := by
  obtain ⟨S, rfl⟩ := hdvd
  rw [show P * S = S * P from mul_comm P S, map_mul, Module.End.mul_apply, hx, map_zero]

/-- The monic separable polynomial whose root set is `E`. -/
noncomputable def eigenPoly (E : Finset ℂ) : ℂ[X] := ∏ μ ∈ E, (Polynomial.X - Polynomial.C μ)

theorem eigenPoly_eval (E : Finset ℂ) (z : ℂ) :
    (eigenPoly E).eval z = ∏ μ ∈ E, (z - μ) := by
  rw [eigenPoly, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun μ _ => by simp

theorem eigenPoly_eval_ne_zero {E : Finset ℂ} {z : ℂ} (hz : z ∉ E) :
    (eigenPoly E).eval z ≠ 0 := by
  rw [eigenPoly_eval]
  exact Finset.prod_ne_zero_iff.mpr fun μ hμ =>
    sub_ne_zero.mpr fun h => hz (by rw [h]; exact hμ)

/-- **Every log-free function is annihilated by some separable polynomial in the `T`-shift.**
The finite root set is the set of eigenvalues occurring in a representing combination. -/
theorem exists_annihilating_finset {f : UpperHalfPlane → ℂ} (hf : f ∈ logFreeSpan) :
    ∃ E : Finset ℂ, (Polynomial.aeval Tsh (eigenPoly E)) f = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro g ⟨μ, hμ⟩
    refine ⟨{μ}, ?_⟩
    have hg : Tsh g = μ • g := hμ
    rw [eigenPoly, Finset.prod_singleton, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      LinearMap.sub_apply, Module.algebraMap_end_apply, hg, sub_self]
  · exact ⟨∅, by rw [eigenPoly, Finset.prod_empty, map_one]; simp⟩
  · rintro x y _ _ ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ ∪ E₂, ?_⟩
    have hd₁ : eigenPoly E₁ ∣ eigenPoly (E₁ ∪ E₂) :=
      Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left
    have hd₂ : eigenPoly E₂ ∣ eigenPoly (E₁ ∪ E₂) :=
      Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right
    rw [map_add, aeval_eq_zero_of_dvd Tsh hd₁ h₁, aeval_eq_zero_of_dvd Tsh hd₂ h₂, add_zero]
  · rintro c x _ ⟨E, h⟩
    exact ⟨E, by rw [map_smul, h, smul_zero]⟩

/-- The `τ`-linear term `τ ↦ τ·B(τ)`.  Writing `τ = log q / 2πi`, this **is** `log q · B`. -/
def linTerm (B : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := fun τ => (τ : ℂ) * B τ

/-- **The Jordan block.**  On `span{B, τ·B}` with `B` a `ν`-eigenfunction the shift acts as
`[[ν, ν],[0, ν]]`: `T(τ·B) = ν·(τ·B) + ν·B`. -/
theorem Tsh_linTerm {ν : ℂ} {B : UpperHalfPlane → ℂ} (hB : IsTEigen ν B) :
    Tsh (linTerm B) = ν • linTerm B + ν • B := by
  have hBv : ∀ τ : UpperHalfPlane, B ((1 : ℝ) +ᵥ τ) = ν * B τ := (isTEigen_iff ν B).mp hB
  funext τ
  have hco : (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  simp only [Tsh_apply, linTerm, hco, hBv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The rigidity lemma — "ordinary modules have no `log q`".**

If `B` is a nonzero `T`-eigenfunction with nonzero eigenvalue, then `τ ↦ τ·B(τ)` is **not** a
finite `ℂ`-combination of `T`-eigenfunctions.  Equivalently: a `log q` term cannot be written as a
linear combination of characters of ordinary modules. -/
theorem linTerm_notMem_logFreeSpan {ν : ℂ} {B : UpperHalfPlane → ℂ} (hν : ν ≠ 0)
    (hB : IsTEigen ν B) (hB0 : B ≠ 0) : linTerm B ∉ logFreeSpan := by
  intro hmem
  obtain ⟨E, hE⟩ := exists_annihilating_finset hmem
  have hB' : Tsh B = ν • B := hB
  set Xν : ℂ[X] := Polynomial.X - Polynomial.C ν with hXν
  set Q : ℂ[X] := eigenPoly (E.erase ν) with hQ
  -- `∏_{μ ∈ E}(X − μ)` divides `(X − ν)·Q` with `Q = ∏_{μ ∈ E∖{ν}}(X − μ)`, in **both** cases:
  -- if `ν ∈ E` the two sides are equal, and if not then `Q` is already the whole product.
  have hdvd : eigenPoly E ∣ Xν * Q := by
    by_cases hνE : ν ∈ E
    · rw [hXν, hQ, eigenPoly, eigenPoly,
        Finset.mul_prod_erase E (fun μ : ℂ => Polynomial.X - Polynomial.C μ) hνE]
    · rw [hQ, Finset.erase_eq_of_notMem hνE]
      exact dvd_mul_left _ _
  have hzero : (Polynomial.aeval Tsh (Xν * Q)) (linTerm B) = 0 :=
    aeval_eq_zero_of_dvd Tsh hdvd hE
  rw [show Xν * Q = Q * Xν from mul_comm _ _, map_mul, Module.End.mul_apply] at hzero
  have hstep : (Polynomial.aeval Tsh Xν) (linTerm B) = ν • B := by
    rw [hXν, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, Tsh_linTerm hB]
    abel
  rw [hstep, map_smul, aeval_apply_of_eigen Tsh hB', smul_smul] at hzero
  have hc : ν * Q.eval ν ≠ 0 :=
    mul_ne_zero hν (hQ ▸ eigenPoly_eval_ne_zero (Finset.notMem_erase ν E))
  have hinv := congrArg (fun g : UpperHalfPlane → ℂ => (ν * Q.eval ν)⁻¹ • g) hzero
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] at hinv
  exact hB0 hinv

/-- `f` **has a `log q` term**: `f = A + τ·B` with `A` log-free, and `B` a nonzero
`T`-eigenfunction with nonzero eigenvalue.

⚠ `A` is only required to be *in the span* of eigenfunctions, not to be a single eigenfunction —
see the module docstring: for `c = -2` the constant part of `χ_0(-1/τ)` is a combination of two
eigenfunctions with *different* `T`-eigenvalues, so the stricter definition would be unusable. -/
def HasLogTerm (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ (A B : UpperHalfPlane → ℂ) (ν : ℂ),
    A ∈ logFreeSpan ∧ ν ≠ 0 ∧ IsTEigen ν B ∧ B ≠ 0 ∧ f = A + linTerm B

/-- **A function with a `log q` term is not log-free.**  This is step 4 of the lead's chain. -/
theorem notMem_logFreeSpan_of_hasLogTerm {f : UpperHalfPlane → ℂ} (hf : HasLogTerm f) :
    f ∉ logFreeSpan := by
  obtain ⟨A, B, ν, hA, hν, hB, hB0, hdec⟩ := hf
  intro hmem
  refine linTerm_notMem_logFreeSpan hν hB hB0 ?_
  have hsub : linTerm B = f - A := by rw [hdec]; abel
  rw [hsub]
  exact Submodule.sub_mem _ hmem hA

/-! ### Non-vacuity of §4

Fourteen prior audits in this repository found vacuous results, so the two predicates of §4 are
checked to be inhabited/proper before anything is built on them. -/

/-- ⚠ **`HasLogTerm` is inhabited.**  The identity `τ ↦ τ` has a log term: `A = 0`, `B = 1`,
`ν = 1`.  So `linTerm_notMem_logFreeSpan` and `notMem_logFreeSpan_of_hasLogTerm` are not
statements about an empty class. -/
theorem hasLogTerm_coe : HasLogTerm (fun τ : UpperHalfPlane => (τ : ℂ)) := by
  refine ⟨0, 1, 1, Submodule.zero_mem _, one_ne_zero, ?_, ?_, ?_⟩
  · rw [isTEigen_iff]; intro τ; simp
  · intro hcon
    have := congrFun hcon ⟨Complex.I, by simp⟩
    simp at this
  · funext τ; simp [linTerm]

/-- ⚠ **`logFreeSpan` is a proper subspace**: the rigidity lemma has content. -/
theorem logFreeSpan_ne_top : logFreeSpan ≠ ⊤ := fun h =>
  notMem_logFreeSpan_of_hasLogTerm hasLogTerm_coe (h ▸ Submodule.mem_top)

end Rigidity

/-! ## §5  Characters are `T`-eigenfunctions, and Zhu's law is log-free

This is where the repository's `FormalQSeries → ℍ` bridge does the work.  `qEvalAt χ h` is
*by construction* `q^h · Σ_{n≥0} χ(h+n) qⁿ`, and such a function is a `T`-eigenfunction with
eigenvalue `e^{2πih}` **unconditionally** — no summability, no growth bound, because the identity
is termwise and `q = e^{2πiτ}` is `1`-periodic.  That is the formal content of
"ordinary ⟹ the character has no `log q`". -/

section ZhuCharacters

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **A `q`-expansion is a `T`-eigenfunction**, with no hypothesis whatsoever. -/
theorem isTEigen_qEvalAt (χ : FormalQSeries) (hh : ℂ) :
    IsTEigen (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * hh)) (qEvalAt χ hh) := by
  rw [isTEigen_iff]
  intro τ
  have hco : (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  have hq : qParam ((1 : ℝ) +ᵥ τ) = qParam τ := qParam_translate hco
  simp only [qEvalAt, hq, hco]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) + 1) * hh
      = 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * hh + 2 * (Real.pi : ℂ) * Complex.I * hh from by
    ring, Complex.exp_add]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-- The **character** of the `i`-th module of a Zhu modular datum: the one-point function at the
vacuum, `χ_{M_i}(τ) = tr_{M_i} q^{L₀ - c/24}`. -/
noncomputable def charOf (D : ModularData W ι) (i : ι) : UpperHalfPlane → ℂ :=
  fun τ => traceFun D.Mfam D.h i W.vacuum τ

/-- The character is the `q`-expansion of the graded dimension along `h_i - c/24`. -/
theorem charOf_eq_qEvalAt (D : ModularData W ι) (i : ι) :
    charOf D i = qEvalAt (gradedDim (D.Mfam i).isMod) (D.h i - W.centralCharge / 24) := by
  have hv : torusOnePoint (D.Mfam i).isMod W.vacuum = gradedDim (D.Mfam i).isMod :=
    torusOnePoint_vacuum _
  funext τ
  have hdef : charOf D i τ
      = qEvalAt (torusOnePoint (D.Mfam i).isMod W.vacuum) (D.h i - W.centralCharge / 24) τ := rfl
  rw [hdef, hv]

/-- **Every character of a modular datum is a `T`-eigenfunction**, with the eigenvalue
`e^{2πi(h_i - c/24)}` that `ModularData.rep_T` pins down. -/
theorem charOf_isTEigen (D : ModularData W ι) (i : ι) :
    IsTEigen (modularTEntry W (D.h i)) (charOf D i) := by
  rw [charOf_eq_qEvalAt]
  exact isTEigen_qEvalAt _ _

theorem charOf_mem_logFreeSpan (D : ModularData W ι) (i : ι) : charOf D i ∈ logFreeSpan :=
  mem_logFreeSpan_of_isTEigen (charOf_isTEigen D i)

/-- **Zhu's law puts every modular transform of a character into `logFreeSpan`.**

This is steps 3 of the lead's chain, and it is exactly the repository's
`ZhuModularityAnalytic` specialized at `v = 𝟙` (square-bracket weight `0`, so the automorphy
factor is `j(A,τ)^0 = 1`): `χ_i(Aτ) = Σ_j ρ(A)_{ij} χ_j(τ)`, a finite combination of
`T`-eigenfunctions. -/
theorem charOf_smul_mem_logFreeSpan {D : ModularData W ι} (hD : ZhuModularityAnalytic D)
    (A : SL(2, ℤ)) (i : ι) : (fun τ => charOf D i (A • τ)) ∈ logFreeSpan := by
  have hfun : (fun τ => charOf D i (A • τ)) = ∑ j : ι, D.rep A i j • charOf D j := by
    funext τ
    have hlaw := hD A 0 W.vacuum (vacuum_mem_sqWeightSpace_zero W) i τ
    simp only [pow_zero, one_mul] at hlaw
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hlaw
  rw [hfun]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (charOf_mem_logFreeSpan D j)

/-- **The contradiction.**  If some modular transform of some character of a modular datum
has a `log q` term, Zhu's analytic modularity fails for that datum. -/
theorem not_zhuModularityAnalytic_of_hasLogTerm (D : ModularData W ι) (A : SL(2, ℤ)) (i : ι)
    (hlog : HasLogTerm (fun τ => charOf D i (A • τ))) : ¬ ZhuModularityAnalytic D := fun hD =>
  notMem_logFreeSpan_of_hasLogTerm hlog (charOf_smul_mem_logFreeSpan hD A i)

end ZhuCharacters

/-! ## §6  Rationality forbids a logarithmic `S`-transform of the vacuum character -/

section VacuumRoute

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The **vacuum character** as a function on `ℍ`: the adjoint module has conformal weight `0`, so
the exponent is `-c/24`. -/
noncomputable def vacChar (W : VertexOperatorAlgebra 𝒱) : UpperHalfPlane → ℂ :=
  qEvalAt (gradedDim (adjointModule W)) (0 - W.centralCharge / 24)

/-- ⚠ **Named hypothesis: Zhu's theorem, in the shape this argument consumes.**

*Rational ⟹ there is a finite family of irreducible modules with a modular datum satisfying
Zhu's analytic law, one of whose characters is the vacuum character.*  This is Zhu's Thm. 5.3.2–3
(Gannon Thm. 5.3.8).  It is carried rather than derived because the repository's route to it,
`Modularity.GNProp8Closure.zhuModularity_pinned_of_C2Cofinite`, additionally needs
`C₂`-cofiniteness of `𝒱`, finiteness of `Φ(𝒱)`, and an explicit irreducible family — for `W(2)`
none of these exists in the library (there are no `W(2)`-modules at all).

Indexing by `Fin n` is no loss: a finite family can always be so indexed.

⚠ **`C2Cofinite` is a hypothesis of Zhu's theorem and is carried explicitly.** Zhu's modular
invariance (Thm. 5.3.2) assumes his *condition C*, which is `C₂`-cofiniteness, **in addition to**
rationality. Taking `AdmissiblyRational W` alone as the
antecedent would assert Zhu's conclusion on a strictly weaker hypothesis than Zhu proves it
from — an unlicensed hypothesis. Including `C2Cofinite W` weakens `ZhuVacuumModularity` to something
the literature actually supports; the cost is that every consumer must supply `C₂`, which for
`W(2)` is the same Abe citation the Zhu-algebra route already carries. -/
def ZhuVacuumModularity (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AdmissiblyRational W → C2Cofinite W → ∃ (n : ℕ) (D : ModularData W (Fin n)) (i : Fin n),
    ZhuModularityAnalytic D ∧ charOf D i = vacChar W

/-- **The character route to irrationality.**

*If the `S`-transform of the vacuum character has a `log q` term, `𝒱` is not rational* — given
Zhu's theorem in the form `ZhuVacuumModularity`.  This is the lead's chain, complete: rational ⟹
(Zhu) `S·χ_vac` is a finite combination of ordinary characters ⟹ (§4–§5) `S·χ_vac` is log-free ⟹
contradiction with the hypothesis. -/
theorem not_admissiblyRational_of_hasLogTerm_vacChar (W : VertexOperatorAlgebra 𝒱)
    (hzhu : ZhuVacuumModularity W) (hC2 : C2Cofinite W)
    (hlog : HasLogTerm (fun τ => vacChar W (ModularGroup.S • τ))) :
    ¬ AdmissiblyRational W := by
  intro hwr
  obtain ⟨n, D, i, hD, hchar⟩ := hzhu hwr hC2
  refine not_zhuModularityAnalytic_of_hasLogTerm D ModularGroup.S i ?_ hD
  simpa only [hchar] using hlog

end VacuumRoute

/-! ## §7  The triplet `W(2)`: the character route -/

section TripletCharacterRoute

open SympFerm

/-- The `W(2)` vacuum character as a function on `ℍ` is the `q`-expansion of the formal series of
§3 along `q^{1/12}` — the `c = -2` Casimir normalization. -/
theorem vacChar_tripletW2 : vacChar tripletW2 = qEvalAt w2VacChar (1 / 12 : ℂ) := by
  have hc : (0 : ℂ) - tripletW2.centralCharge / 24 = 1 / 12 := by
    rw [tripletW2_centralCharge]; ring
  have hv : vacChar tripletW2
      = qEvalAt w2VacChar ((0 : ℂ) - tripletW2.centralCharge / 24) := rfl
  rw [hv, hc]

/-- **`W(2)` is not rational — the character route.**

Two named hypotheses, both statements of the literature and both explicit arguments:

* `hzhu` — Zhu's modularity theorem (see `ZhuVacuumModularity`);
* `hC2` — `C₂`-cofiniteness of `W(2)`, a genuine hypothesis of Zhu's theorem (Abe, Math. Z. 255
  (2007) 755–792, Thm 3.9), not an artefact of this formalisation;
* `hlog` — **the one analytic input**, that the `S`-transform of `χ_{W(2)}` carries a `log q`:
  `χ_0(-1/τ) = ¼[χ_{-1/8}(τ) - χ_{3/8}(τ)] + (-iτ/2)[χ_0(τ) - χ_1(τ)]`,
  so `A = ¼(χ_{-1/8} - χ_{3/8}) ∈ logFreeSpan`, `ν = e^{2πi/12}`, and
  `B = (-i/2)(χ_0 - χ_1) = (-i/2)·η(τ)² ≠ 0`, a `ν`-eigenfunction since `χ_0`, `χ_1` have
  exponents `1/12` and `13/12`.
  *Reference:* Fuchs–Hwang–Semikhatov–Tipunin, arXiv:hep-th/0306274, Prop. 3.4;
  Flohr–Gaberdiel, arXiv:hep-th/0509075, eqs. (22)–(25).
  ⚠ Not proved here: it needs `χ_{W(2)} = q^{1/12}·½[∏(1+qⁿ)² + ∏(1-qⁿ)²]` as an identity between
  `w2VacChar` and Mathlib's `ModularForm.eta`, and the repository supplies no basis of `FockSF`.

This statement is **logically independent** of `not_admissiblyRational_tripletW2_of_logModule`
(§2):
that one uses no modular data and no analysis, this one uses no Zhu-algebra input. -/
theorem not_admissiblyRational_tripletW2_of_logS
    (hzhu : ZhuVacuumModularity tripletW2) (hC2 : C2Cofinite tripletW2)
    (hlog : HasLogTerm (fun τ => vacChar tripletW2 (ModularGroup.S • τ))) :
    ¬ AdmissiblyRational tripletW2 :=
  not_admissiblyRational_of_hasLogTerm_vacChar _ hzhu hC2 hlog

end TripletCharacterRoute

end VOA.LogModular
