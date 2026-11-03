/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.AdmissibleModule
import VOA.Modules.Character
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rationality and holomorphicity  (Gannon §5.3.1, Def 5.3.2, Lemma 5.3.3)

The finiteness conditions that single out the "nice" VOAs — those whose representation
theory resembles that of a finite group.

* **Simple VOA.** `𝒱` is **simple** if it is irreducible as a module over itself
  (`IsSimple W := IsIrreducible (adjointModule W)`, Def 6.2.3).
* **Module isomorphism** `≃ₘ` (a genuine `Setoid`) and the iso-class set **`Φ(𝒱)`** of
  irreducible `𝒱`-modules.
* **`GannonRational`** (Def 5.3.2): every *ordinary* module is completely reducible, `Φ(𝒱)`
  is finite, and every irreducible *admissible* module is ordinary.
* **Holomorphic**: `GannonRational` with a *unique* irreducible module (necessarily `𝒱`).
* **Lemma 5.3.3.** For rational `𝒱` and irreducible `M` there is a conformal weight
  `h = h(M)` with `M_h ≠ 0`, `M_α ≠ 0 ⟹ α - h ∈ ℕ`, `M_h` generating `M`, and the
  **character periodicity** `χ_M(τ+1) = e^{2πi(h-c/24)} χ_M(τ)`. The periodicity is proved
  here (`char_T_transform`) for any module *with* a conformal weight (`HasConformalWeight`).
  The *existence* of a **rational** conformal weight `h(M) ∈ ℚ` is a modularity consequence
  (Anderson–Moore / Zhu) treated in `Modularity.ZhuTheorem`; recorded here as
  `conformalWeight_rational_gate` (not proved in this file).

## ⚠⚠ Why this file does not define `WeaklyRational`

Gannon calls his Def. 5.3.2 "weakly rational", but this file deliberately does not use that name,
and it transcribes the third clause over admissible modules, for three separate reasons.

1. **The name inverted its own meaning.**  "Weakly rational" reads as *rational with respect to
   weak modules* — every weak module completely reducible — which is `Regular`
   (`Modules/RationalityLattice.lean`), the **strongest** notion in the lattice below.  Gannon's
   "weakly" is instead a comparative against *his own* stronger Def. 6.2.3 "rational"; it says
   nothing about any module category.  The predicate in fact quantifies mostly over `OrdVModule`,
   the **narrowest** category, so the natural reading was exactly inverted.
2. **The third field was a mis-transcription of its own cited source.**  Gannon's Def. 5.3.1
   (CUP 2006, p. 330) defines a *weak `V`-module* to be `ℕ`-**graded** — verbatim, "an `ℕ`-graded
   vector space `M = ⊕_{n∈ℕ} M_[n]` … such that for any `u ∈ V_k` the mode `u_(n)` is a linear map
   from `M_[ℓ]` into `M_[k+ℓ−n−1]`" — which is verbatim Dong–Li–Mason **admissibility**.  So
   Gannon's clause (3) is DLM Thm. 8.1(c), needing no `C₂`-cofiniteness and no Abe–Buhl–Dong.
   A field quantifying over the *ungraded* `WeakModule` (`Modules/WeakModule.lean`), which carries
   no grading at all, would mis-transcribe the book.
3. **The third field's conclusion must be tied to its subject.**  A conclusion
   `Nonempty (OrdVModule W M)` says merely that the carrier *type* supports *some* ordinary
   structure, with nothing requiring that structure's `toWeakModule` to be the given module.
   Gannon asserts that the given pair `(M, Y_M)` **is** a `V`-module.

`GannonRational` below respects (2) and (3).  A field that is simultaneously *wider* than Gannon's
(ungraded quantifier) and *weaker* than Gannon's (detached conclusion) gives a predicate that is
**not comparable in either direction** with `GannonRational`.

## The rationality lattice

Each predicate is named for the module category it quantifies over.  Recall
`ordinary ⊆ admissible ⊆ weak` (`OrdVModule ⊆ AdmissibleModule ⊆ WeakModule`).

```
  Regular  ══[PROVED-HERE]══>  AdmissiblyRational  ══[PROVED-HERE + CITED]══>  GannonRational
```

* **`Regular`** (`Modules/RationalityLattice.lean`) — *every **weak** module is completely
  reducible*, and every irreducible weak module is ordinary.  Dong–Li–Mason,
  *Regularity of rational vertex operator algebras*, arXiv q-alg/9508018v1, Def. 3.1.  ⚠ This is
  the honest referent of the phrase "weakly rational", and it is the **strongest** notion here,
  not the weakest.
* **`AdmissiblyRational`** (`Modules/AdmissibleModule.lean`) — *every **admissible** module is
  completely reducible*.  The library's transcription of the standard Zhu / Dong–Li–Mason notion
  ("rational" in the modern literature).  ⚠ Complements are taken among *weak* submodules; whether
  this agrees with DLM's graded reading is not settled (`Modules/AdmissibleRationality.lean`,
  § *⚠ One deliberate convention*).
* **`GannonRational`** (here) — Gannon Def. 5.3.2, three clauses over three different categories:
  (1) ordinary, (2) `Φ(𝒱)` finite, (3) admissible.

### Implications, each tagged **PROVED-HERE** or **CITED**

* `Regular ⟹ AdmissiblyRational` — **PROVED-HERE**, `Regular.admissiblyRational`
  (Dong–Li–Mason, Remark 3.2).
* `Regular ⟹ GannonRational` clause (1) — **PROVED-HERE**,
  `Regular.ordinaryCompletelyReducible`.
* `Regular ⟹ GannonRational` clause (3) — **PROVED-HERE**,
  `Regular.gannonAdmissibleIsOrdinary`.  ⚠ This one-liner is why `gannonRational_of_regular`
  needs no borrowed Dong–Li–Mason citation.
* `AdmissiblyRational ⟹ GannonRational` clause (1) — **PROVED-HERE**,
  `OrdVModule.isCompletelyReducible_of_admissiblyRational`, via the proved
  `ordinary ⟹ admissible` (`OrdVModule.hasAdmissibleRefinement`).
* `AdmissiblyRational ⟹ GannonRational` clause (2) — **CITED** here: DLM Thm. 8.1(b), carried as
  `DLMFinitelyManyIrredAdmissible`.  The transfer `Φ(𝒱) ↪ Φadm(𝒱)` is PROVED-HERE
  (`finite_Φ_of_finite_Φadm`).  **Proved downstream for `C₂`-cofinite `𝒱`**:
  `LiteratureInputs.dlmFinitelyManyIrredAdmissible_of_c2Cofinite`
  (`Classification/COne/LiteratureInputsProved.lean`); the non-`C₂` case is open.
* `AdmissiblyRational ⟹ GannonRational` clause (3) — **CITED** here: DLM Thm. 8.1(c), carried as
  `DLMSimpleAdmissibleOrdinary`.  **Proved downstream for `C₂`-cofinite `𝒱`**:
  `AdmissibleOrdinary.dlmSimpleAdmissibleOrdinary_of_c2Cofinite`; the non-`C₂` case is open.
  For `StronglyRational 𝒱` both DLM inputs are discharged in
  `StronglyRational.gannonRational'`.
* `C₂`-cofinite `+ AdmissiblyRational ⟹ Regular` — Abe–Buhl–Dong Thm. 4.5, carried as
  `ABDRegularOfC2AndRational` and *derived* here from its two component citations.  **Proved
  for every `𝒱`**: `LiteratureInputs.abdRegularOfC2AndRational_holds` (both components are
  theorems: `ABDWeakAdmissible.abdWeakIsAdmissible`,
  `LiteratureInputs.abdIrreducibleWeakIsOrdinary_holds`).
* `Regular ⟹ C₂`-cofinite — **CITED, unproved**: H. Li Thm. 3.8, carried as
  `LiC2CofiniteOfRegular`.  The only one of the seven named literature predicates with no proof
  in the library.
* `GannonRational ⟹ AdmissiblyRational` — **NOT AVAILABLE**.  Clause (1) is only about
  ordinary modules; Gannon's own Def. 6.2.3 adds the admissible clause separately, remarking
  that it "is a little stronger than the usual complete reducibility requirement".

### ⚠ The `C₂` / Abe–Buhl–Dong caveat, and where it went

Under the **old, mis-transcribed** field (3) the only route to it was Abe–Buhl–Dong Cor. 5.8
("every irreducible **weak** module of a `C₂`-cofinite VOA is ordinary"), whose hypothesis is
`C₂`-cofiniteness and whose proof rests on Buhl's spanning theorem.  So the old predicate could not
be reached from rationality without paying `C₂`-cofiniteness.

With clause (3) restated over **admissible** modules, that price **disappears**: clause (3) is
exactly DLM Thm. 8.1(c), which assumes rationality alone.  See
`gannonRational_of_admissiblyRational` (`Modules/RationalityLattice.lean`), which takes no
`C2Cofinite` hypothesis.  `C₂`-cofiniteness re-enters only for the genuinely stronger `Regular`,
via Abe–Buhl–Dong Thm. 4.5.

## Dependencies
* `VOA.Modules.AdmissibleModule` (for clause (3)), `VOA.Modules.Character`;
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Status
`sorry`-free, with no project axioms, for the predicates and the character
periodicity: `IsSimple`, module iso `≃ₘ` (a genuine `Setoid`), `Φ`, `GannonRational`,
`Holomorphic`, `HasConformalWeight`, and **`char_T_transform`** (5.3.3's `q`-periodicity)
are all axiom-clean. The rationality of the conformal weight `h(M) ∈ ℚ` is **not proved here**;
it is the modular link to `Modularity.ZhuTheorem`, documented in place.

## References
* Gannon, *Moonshine beyond the Monster*, CUP 2006, §5.3.1, Def. 5.3.1, Def. 5.3.2, Lem. 5.3.3,
  Def. 6.2.3; Zhu [574] = J. Amer. Math. Soc. **9** (1996) 237–302; Dong–Li–Mason,
  *Twisted representations of vertex operator algebras*, Math. Ann. **310** (1998) 571–600,
  Thm. 8.1; Anderson–Moore.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Simple VOAs -/

set_option linter.style.longLine false in
/-- `𝒱` is **simple** (Gannon Def. 6.2.3) if it is irreducible as a module over itself.

⚠⚠ **DEPRECATED — this is a duplicate.**  `IsSimple` was defined twice in this repository:

* `VOA.VertexOperatorAlgebra.IsSimple` (`Core/BilinearForm.lean:208`) — `⊤ ≠ ⊥`, and every
  VOA ideal is `⊥` or `⊤`;
* this one — `OrdVModule.IsIrreducible (adjointModule W)`.

The two are **equivalent**, proved as `isSimple_iff_isSimple` /
`isSimple_iff_adjointModule_isIrreducible` in `Modules/StronglyRational.lean`: a
`WeakModule.Submodule'` of the adjoint module is definitionally an ideal (the adjoint action is
`W.smul` by `rfl`), and `Nontrivial 𝒱 ↔ (⊤ : Submodule ℂ 𝒱) ≠ ⊥`.

This one is the deprecated copy because it had **zero** consumers, while every downstream file
(`Core/InvariantFormFHL2`, `Core/InvariantFormRadical`, `Core/SimpleImage`, `Examples/…`) uses the
`Core/BilinearForm.lean` predicate — which is also the one the literature means: McRae
(arXiv:2108.01898v3, §2.2) argues simplicity through "any proper ideal `I ⊊ V`".  Use
`W.IsSimple`. -/
@[deprecated "Duplicate of `VOA.VertexOperatorAlgebra.IsSimple` (Core/BilinearForm.lean); the two are equivalent by `isSimple_iff_isSimple` (Modules/StronglyRational.lean). Use `W.IsSimple`." (since := "2026-08-23")]
def IsSimple (W : VertexOperatorAlgebra 𝒱) : Prop :=
  OrdVModule.IsIrreducible (adjointModule W)

/-! ## Module isomorphisms and `Φ(𝒱)` -/

/-- A **bundled irreducible `𝒱`-module** (carrier in `Type u`). -/
structure IrrModule (W : VertexOperatorAlgebra 𝒱) where
  /-- The underlying carrier type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The graded `𝒱`-module structure. -/
  isMod : OrdVModule W carrier
  /-- Irreducibility. -/
  irreducible : OrdVModule.IsIrreducible isMod

attribute [instance] IrrModule.addCommGroup IrrModule.module

/-- An **isomorphism of `𝒱`-modules**: a `ℂ`-linear equivalence intertwining every mode. -/
structure ModuleEquiv (W : VertexOperatorAlgebra 𝒱) {M N : Type u} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup N] [Module ℂ N] (A : OrdVModule W M) (B : OrdVModule W N) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : M ≃ₗ[ℂ] N
  /-- Intertwining of the actions: `e(u₍ₙ₎ x) = u₍ₙ₎ e(x)`. -/
  map_act : ∀ (u : 𝒱) (n : ℤ) (x : M),
    toLinearEquiv (A.toWeakModule.act u n x) = B.toWeakModule.act u n (toLinearEquiv x)

@[inherit_doc] scoped notation:25 A " ≃ₘ[" W "] " B => ModuleEquiv W A B

namespace ModuleEquiv

/-- The identity isomorphism. -/
def refl {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) : ModuleEquiv W A A where
  toLinearEquiv := LinearEquiv.refl ℂ M
  map_act _ _ _ := rfl

/-- The inverse isomorphism. -/
def symm {W : VertexOperatorAlgebra 𝒱} {M N : Type u} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {A : OrdVModule W M} {B : OrdVModule W N}
    (e : ModuleEquiv W A B) : ModuleEquiv W B A where
  toLinearEquiv := e.toLinearEquiv.symm
  map_act u n y := by
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, e.map_act, LinearEquiv.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {W : VertexOperatorAlgebra 𝒱} {M N P : Type u} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [AddCommGroup P] [Module ℂ P]
    {A : OrdVModule W M} {B : OrdVModule W N} {C : OrdVModule W P}
    (e : ModuleEquiv W A B) (f : ModuleEquiv W B C) : ModuleEquiv W A C where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_act u n x := by simp only [LinearEquiv.trans_apply, e.map_act, f.map_act]

end ModuleEquiv

/-- Isomorphism of bundled irreducible modules. -/
def IrrModule.Iso (W : VertexOperatorAlgebra 𝒱) (A B : IrrModule W) : Prop :=
  Nonempty (ModuleEquiv W A.isMod B.isMod)

/-- Module isomorphism is an equivalence relation on bundled irreducibles. -/
def IrrModule.setoid (W : VertexOperatorAlgebra 𝒱) : Setoid (IrrModule W) where
  r := IrrModule.Iso W
  iseqv :=
    { refl := fun A => ⟨ModuleEquiv.refl A.isMod⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- **`Φ(𝒱)`** — the set of isomorphism classes of irreducible `𝒱`-modules (Gannon §5.3.1).
For a `GannonRational` VOA this is finite (that is clause (2)) and indexes Zhu's algebra. -/
def Φ (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) := Quotient (IrrModule.setoid W)

/-! ## Gannon's rationality, and holomorphicity -/

/-- **Gannon Def. 5.3.2, clause (3)**: every irreducible **admissible** module carries an ordinary
structure **on the same underlying weak module**.

Two things are load-bearing about this statement, and both go wrong in the ungraded misreading
of clause (3) (a field `weakIsModule` over `WeakModule`).

* **The quantifier is over `AdmissibleModule`, not `WeakModule`.**  Gannon Def. 5.3.1 (CUP 2006,
  p. 330) defines "weak `V`-module" to *be* the `ℕ`-graded notion with the mode shift
  `u₍ₙ₎ : M_[ℓ] → M_[k+ℓ−n−1]`, i.e. Dong–Li–Mason admissibility.  So this clause is exactly
  **Dong–Li–Mason, Thm. 8.1(c)** (*Twisted representations of vertex operator algebras*,
  arXiv:q-alg/9509005v1 = Math. Ann. **310** (1998) 571–600), at `g = 1`: "every simple admissible
  `g`-twisted `V`-module is an ordinary `g`-twisted `V`-module", whose only hypothesis is
  `g`-rationality — **no** `C₂`-cofiniteness, **no** Abe–Buhl–Dong, **no** Buhl spanning set.
* **The conclusion names the given module.**  `∃ O, O.toWeakModule = N.toWeakModule` says the
  *given* pair `(M, Y_M)` is ordinary.  The misreading concludes only
  `Nonempty (OrdVModule W M)`, which says nothing beyond "the carrier type admits some ordinary
  structure, possibly with a different action".

⚠ **A subtlety of the citation, recorded rather than assumed.**  DLM's "simple admissible" means
*graded*-simple — verbatim, "`0` and `M` are the only **graded** submodules".  `IsIrreducible` here
forbids **all weak** submodules, a strictly stronger condition on `M`, so the class quantified over
here is a *subclass* of DLM's and this `Prop` is **implied by** DLM Thm. 8.1(c) rather than
implying it.  That is the safe direction; the bridge in the other direction is a short argument DLM
do not state at Thm. 8.1, and it is not assumed anywhere. -/
def GannonAdmissibleIsOrdinary (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M),
    N.IsIrreducible → ∃ O : OrdVModule W M, O.toWeakModule = N.toWeakModule

/-- **`GannonRational`** — Gannon, *Moonshine beyond the Monster*, CUP 2006, **Definition 5.3.2**
(p. 331), faithfully transcribed.  Verbatim: *"A VOA `V` is called weakly rational if every
`V`-module is completely reducible, `V` has only a finite number of irreducible modules, and every
irreducible weak `V`-module is a `V`-module."*

⚠ **On the name.**  Gannon calls this "**weakly** rational", and that adverb is a comparative
against **his own** stronger Def. 6.2.3 ("rational" = this, plus complete reducibility of
`ℕ`-graded weak modules, plus `C₂`-cofiniteness, plus simplicity and self-contragredience).  It is
**not** a reference to weak modules, and it does **not** mean this is the weakest condition in
sight: *every* weak module being completely reducible is `Regular`
(`Modules/RationalityLattice.lean`), the **strongest** notion in this repository's lattice.  Because
the name `WeaklyRational` invites exactly the inverted reading — and an ungraded transcription of
the third field would make that misreading half-true — the predicate is named for its author here,
and no `WeaklyRational` alias exists.

**Which module category each field quantifies over** (this is the whole point of the renaming):

1. `completelyReducible` — **ordinary** modules (`OrdVModule`, Gannon Def. 5.3.1c: `ℂ`-graded by
   honest `L₀`-eigenspaces, finite-dimensional pieces, `Re α` bounded below).  The **narrowest**
   category.  Strictly weaker than the Zhu/DLM clause, which asks the same of admissible modules.
2. `finitelyManyIrred` — a cardinality statement about `Φ(𝒱)`, the iso classes of irreducible
   **ordinary** modules.  Quantifies over no module at all.
3. `admissibleIsOrdinary` — **admissible** modules (`AdmissibleModule`, Gannon Def. 5.3.1 "weak"
   = DLM `ℕ`-gradable).  The **middle** category.  This is `GannonAdmissibleIsOrdinary`; see its
   docstring for the two defects of the ungraded misreading.

No field quantifies over the ungraded `WeakModule`. -/
structure GannonRational (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- (1) Every **ordinary** `𝒱`-module is completely reducible. -/
  completelyReducible : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
    OrdVModule.IsCompletelyReducible N
  /-- (2) Only finitely many irreducible **ordinary** modules: `Φ(𝒱)` is finite. -/
  finitelyManyIrred : Finite (Φ W)
  /-- (3) Every irreducible **admissible** module is ordinary, on the same weak module. -/
  admissibleIsOrdinary : GannonAdmissibleIsOrdinary W

/-- **Holomorphic** (Gannon §5.3.1): `GannonRational` with a *unique* irreducible module
(necessarily `𝒱` itself). One of the keys to Monstrous Moonshine.

⚠ **Which notion.**  Its first conjunct is Gannon's actual Def. 5.3.2, not the ungraded
misreading of it, and the two are not comparable.  The only consumer is the `holomorphic` field of
`Modularity.MoonshineCorollary.MoonshineHypotheses`, a structure with no consumers anywhere, so no
proof depends on which notion is named. -/
def Holomorphic (W : VertexOperatorAlgebra 𝒱) : Prop :=
  GannonRational W ∧ Nat.card (Φ W) = 1

/-! ## Lemma 5.3.3 — conformal weight and character periodicity -/

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `M` **has conformal weight `h`** (Gannon Lem. 5.3.3): the lowest-weight space `M_h` is
nonzero and every nonzero weight lies in `h + ℕ`. -/
def HasConformalWeight (N : OrdVModule W M) (h : ℂ) : Prop :=
  N.weight h ≠ ⊥ ∧ ∀ α : ℂ, N.weight α ≠ ⊥ → ∃ n : ℕ, α = h + n

/-- The `τ ↦ τ+1` (modular `T`) action on a formal `q`-series: `q^e ↦ e^{2πie} q^e`. -/
noncomputable def qShift (χ : FormalQSeries) : FormalQSeries :=
  fun e => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * e) * χ e

/-- **Character periodicity (Gannon Lemma 5.3.3):** for a module of conformal weight `h`,
`χ_M(τ+1) = e^{2πi(h - c/24)} χ_M(τ)`. (Convention: `gradedDim` carries the `q^{-c/24}`
Casimir shift, so the phase is `h - c/24`.) The integer spacing of the weights
(`α - h ∈ ℕ`) makes every coefficient pick up the *same* phase. -/
theorem char_T_transform (N : OrdVModule W M) (h : ℂ) (hcw : HasConformalWeight N h) :
    qShift (gradedDim N)
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)))
          • gradedDim N := by
  funext e
  simp only [qShift, gradedDim, Pi.smul_apply, smul_eq_mul]
  by_cases hz : N.weight (e + W.centralCharge / 24) = ⊥
  · rw [hz]; simp
  · obtain ⟨n, hn⟩ := hcw.2 _ hz
    have he : e = (h - W.centralCharge / 24) + (n : ℂ) := by linear_combination hn
    rw [he, show (2 * (Real.pi : ℂ) * Complex.I * ((h - W.centralCharge / 24) + (n : ℂ)))
          = (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24))
            + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- **Lemma 5.3.3, the achievable core** (Gannon): if a module `N` *has* a conformal weight `h`,
its character satisfies the `T`-periodicity `χ_M(τ+1) = e^{2πi(h-c/24)} χ_M(τ)`.

No rationality or irreducibility is needed: the statement is `char_T_transform`. Earlier versions
carried two unused hypotheses (`GannonRational W` and `OrdVModule.IsIrreducible N`) so the
statement would read as Gannon's Lemma 5.3.3; they were removed (register entry 50). The
remaining content of Lemma 5.3.3 — that an irreducible module of a rational VOA *has* a rational
conformal weight — is `conformalWeight_rational_gate` below and is not proved. -/
theorem conformalWeight_char_periodicity (N : OrdVModule W M)
    {h : ℂ} (hcw : HasConformalWeight N h) :
    qShift (gradedDim N)
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)))
          • gradedDim N :=
  char_T_transform N h hcw

/-!
### `conformalWeight_rational_gate` — the modular link (not proved here)

The remaining content of Lemma 5.3.3 — that an irreducible module of a `GannonRational` VOA *admits*
a conformal weight which is moreover **rational**, `h(M) ∈ ℚ` — is the Anderson–Moore /
Zhu rationality of conformal weights. It is a *consequence of modular invariance* (the
eigenvalues of the modular `T`-matrix are roots of unity), and so genuinely belongs to
`Modularity.ZhuTheorem`. It is documented here in place rather than proved or faked; from
`Modularity.ZhuTheorem` it discharges as

  `∃ h : ℚ, HasConformalWeight N (h : ℂ)`   (for irreducible `N` over a `GannonRational` `𝒱`),

and then `char_T_transform` gives `χ_M(τ+1) = e^{2πi(h-c/24)} χ_M(τ)` with `h ∈ ℚ`.
-/

end VOA
