/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.AdmissibleModule
import VOA.Modules.Rationality
import VOA.Modules.ZeroModeMult
import VOA.Modules.ZhuRingInstance
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Rationality in the **admissible** category — Zhu / Dong–Li–Mason

The **standard** rationality predicate `AdmissiblyRational`, and the admissible module category it
quantifies over, live one file upstream in `Modules/AdmissibleModule.lean` — a leaf importing
only `Modules/WeakModule.lean`, so that `Modules/Rationality.lean` can state Gannon Def. 5.3.2's
clause (3) over the category Gannon's own Def. 5.3.1 uses.  **This** file carries everything about
that predicate which needs Zhu's algebra or the comparison with the ordinary category.

## The standard definition

* Zhu, *Modular invariance of characters of vertex operator algebras*, J. Amer. Math. Soc. **9**
  (1996) 237–302, §1.4 / §2 — the "`ℕ`-gradable" (= admissible) modules.
* Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
  67–96, Def. 2.2 (admissible module) and §2 (rationality).
* Dong–Li–Mason, *Twisted representations of vertex operator algebras*, Math. Ann. **310** (1998)
  571–600 — the theorem that "every admissible module is completely reducible" already forces
  finitely many irreducibles, each of them ordinary.  That is why the modern definition is the
  single clause below and *not* a three-field structure.

An **admissible** (`ℕ`-gradable weak) module is a weak module `M` with a decomposition
`M = ⨁_{n ∈ ℕ} M(n)` such that `a₍ₚ₎ M(k) ⊆ M(k + wt a − p − 1)` for homogeneous `a ∈ 𝒱_{wt a}`.
No `L₀`-eigenvalue condition, no finite-dimensionality of the pieces: that is exactly what
separates `AdmissibleModule` from the repository's `OrdVModule` (Gannon 5.3.1c), and it is the
whole point — ordinary modules are a **proper subcategory** of admissible ones.

`AdmissiblyRational 𝒱` is then the single clause **"every admissible `𝒱`-module is completely
reducible"**.

## Why not Gannon's predicate

Gannon Def. 5.3.2 — `GannonRational` (`Modules/Rationality.lean`) — is a three-clause package
over three different module categories:

1. `completelyReducible` — every **ordinary** module is completely reducible.  *Weaker* than the
   DLM clause, because ordinary ⊊ admissible.
2. `finitelyManyIrred` — `Φ(𝒱)` finite.  A *theorem* about rational VOAs (DLM, Math. Ann. **310**,
   Thm. 8.1(b)), not part of the modern definition.
3. `admissibleIsOrdinary` — every irreducible **admissible** module is ordinary.  Another theorem
   about rational VOAs (DLM Thm. 8.1(c)).

So `AdmissiblyRational ⟹ GannonRational` holds given those two DLM citations, and with **no**
`C₂`-cofiniteness (`gannonRational_of_admissiblyRational`,
`Modules/RationalityLattice.lean`); the converse does **not** hold, because clause (1) speaks only
about ordinary modules.  Gannon himself records the gap: his Def. 6.2.3 adds
"*every `ℕ`-graded weak module is completely reducible*" — that is `AdmissiblyRational` — on top of
Def. 5.3.2, remarking that it "is a little stronger than the usual complete reducibility
requirement".

⚠ **Remark on a misreading, kept because it explains the shape of this file.**  If Gannon
Def. 5.3.2's clause (3) is read over the *ungraded* `WeakModule`, concluding a detached
`Nonempty (OrdVModule W M)`, it becomes a regularity-flavoured statement out of reach of
rationality — reachable only through Abe–Buhl–Dong Cor. 5.8 (*Rationality, regularity, and
`C₂`-cofiniteness*, Trans. AMS **356** (2004) 3391–3402) and its `C₂`-cofiniteness hypothesis — and
the resulting predicate is incomparable with `AdmissiblyRational`.  `GannonRational` uses Gannon's
own module category for clause (3), so it carries no `C₂` hypothesis.

## ⚠ One deliberate convention, stated so it is not smuggled

`IsCompletelyReducible` below asks that every **weak submodule** (`WeakModule.Submodule'`: a
`ℂ`-subspace closed under every mode) of an admissible module be complemented by a weak
submodule.  This matches the repository's existing `OrdVModule.IsCompletelyReducible`
(`Modules/WeakModule.lean`), so the library speaks one language.

The *category-internal* reading of DLM would instead quantify only over **level-graded**
submodules `P = ⨆_k (P ⊓ M(k))` and demand a level-graded **complement**.

⚠ **Relation between the two readings: not settled.**  Neither implication is proved in Lean.
Earlier revisions of this docstring asserted first that the readings are incomparable and then that
the weak reading *implies* the graded one ("replace the complement by its graded part"); the latter
sketch is not a valid argument as written (the graded part of a weak complement need not be a
complement), so neither claim should be relied on.  What is known on paper (textbook ch. L12):
DLM-rationality implies `AdmissiblyRational`, using DLM Thm 8.1 (every admissible module is a direct
sum of simple ordinary modules, so every weak submodule is complemented).  The converse — the
direction needed to apply DLM's theorems to a hypothesis `AdmissiblyRational W` — is unchecked.
Consequences:

* **Using it as a hypothesis** (e.g. `ZhuAdmissibleSemisimple`) is licensed by the literature only
  if `AdmissiblyRational` implies DLM-rationality, which is open here.
* **`¬ AdmissiblyRational W`** is a statement about the library's notion.  By the paper direction
  above it does imply "`W` is not DLM-rational".

The two readings ask different questions already over `trivialVOA`, with
`M = ℂe₀ ⊕ ℂe₁`, `M(0) = ℂe₀`, `M(1) = ℂe₁`:

* the diagonal line `ℂ(e₀+e₁)` is a weak submodule that is **not** level-graded, so the graded
  reading never asks for a complement of it;
* that same line is a weak complement of the level-graded `ℂe₀` which is itself **not** level
  graded, so a witness for this file's reading need not be a witness for the graded one.

Consequence to keep in view when reading the irrationality corollaries: `¬ AdmissiblyRational 𝒱`
as proved downstream is **not** literally `¬ (𝒱 is DLM-rational in the category-internal
reading)`; it is the same statement with the submodule notion fixed to the repository's.  The gap
is exactly one definitional choice, it is stated here rather than papered over, and it is much
narrower than the mismatch of the ungraded misreading of Gannon's clause (3) (wrong module
category plus a detached conclusion, hence an unformalized Abe–Buhl–Dong clause) that this file
routes around.

The graded variant is deliberately **not defined here** — a second vocabulary for
"rational" is the disease, not the cure.  If a later file does need it, the shape is
`structure GradedSubmodule (N) extends WeakModule.Submodule' N.toWeakModule where
  graded : toSubmodule'.carrier = ⨆ k : ℤ, toSubmodule'.carrier ⊓ N.lev k`,
with `IsCompletelyReducible` quantified over it and the complement also graded; the positive
witness for `trivialVOA` would then need the graded-complement construction (choose a complement
of `P ⊓ M(k)` inside each `M(k)`; their supremum is a graded complement, by the modular law and
`iSupIndep` of the level family).

## Main declarations

(`AdmissibleModule` and `AdmissiblyRational` themselves are in `Modules/AdmissibleModule.lean`.)

* `ZhuAdmissibleSemisimple` — the semisimplicity theorem carried as a **named hypothesis**
  (Dong–Li–Mason, J. Algebra **206** (1998), Thm. 4.10(a); equivalently Math. Ann. **310** (1998),
  Thm. 8.1(a) at `g = 1`; ⚠ *not* Zhu JAMS **9** Thm. 2.2.3 —
  see the declaration's own licence note); not proved in this file and never folded into a
  definition.  It is a theorem for every VOA, downstream:
  `VOA.Huang.ZhuSemisimple.zhuAdmissibleSemisimple_of_Pr`, with the bottom projection supplied by
  `voaPBWBottomProjection` (`LiteratureInputs.zhuAdmissibleSemisimple_holds`,
  `Classification/COne/LiteratureInputsProved.lean`).
* `OrdVModule.HasAdmissibleRefinement` and
  `OrdVModule.isCompletelyReducible_of_hasAdmissibleRefinement` — the free half of the comparison
  with Gannon's clause (1).
* `OrdVModule.hasAdmissibleRefinement_of_isLowestWeight` — the refinement exists for every
  ordinary module with a lowest weight (Gannon's `HasConformalWeight` clause), so the previous
  item is not vacuous.
* `admissiblyRational_of_span_vacuum` — a positive witness generator: any VOA with `𝒱 = ℂ𝟙` is
  admissibly rational.  Instantiated at `trivialVOA` in
  `Examples/TrivialAdmissiblyRational.lean`.

## Status
`sorry`-free, with no project axioms.  Every declaration below is `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Zhu's semisimplicity theorem, as a named hypothesis**: if `𝒱` is rational in the admissible
sense then Zhu's algebra `A(𝒱)` is semisimple.

**Dong–Li–Mason**, *Twisted representations of vertex operator algebras and associative algebras*
/ J. Algebra **206** (1998) 67–96, **Theorem 4.10(a)** — this is the correct license and should be
cited first (equivalently DLM, Math. Ann. **310** (1998), Thm. 8.1(a) at `g = 1`).  Proved for
every VOA: `LiteratureInputs.zhuAdmissibleSemisimple_holds` (see the status note below).

⚠ **Do not cite Zhu JAMS 9 (1996) Thm. 2.2.3 as the license.**  Zhu's own Definition 1.2.4 of
"rational" carries **two extra finiteness clauses** that `AdmissiblyRational` deliberately drops,
so Zhu's theorem is stated about a *different, stronger* predicate and does not directly apply.
DLM's single-clause notion is the one `AdmissiblyRational` targets.  Zhu JAMS 9 (1996) 237–302,
Thm. 2.2.3 remains the historical source and may be cited as "see also".

⚠ **This is a theorem of the literature, not a definitional consequence, and it is *not* proved
here.**  `AdmissiblyRational` is a statement about a module category; `IsSemisimpleRing (A 𝒱)` is a
statement about an associative algebra, and getting from the first to the second is Zhu's argument
(complete reducibility of admissible modules transports across `M ↦ Ω(M) = M(0)`).  Folding it into
a *definition* would make every irrationality corollary below a tautology.

Status: proved downstream for every VOA, from the library's own `AdmissiblyRational`, as
`VOA.Huang.ZhuSemisimple.zhuAdmissibleSemisimple_of_Pr` (restated hypothesis-free as
`LiteratureInputs.zhuAdmissibleSemisimple_holds`,
`Classification/COne/LiteratureInputsProved.lean`).
So the licence caveat above does not apply to consumers that use the Lean theorem. -/
def ZhuAdmissibleSemisimple (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AdmissiblyRational W → letI := instRingA W; IsSemisimpleRing (A W)

/-! ## Comparison with Gannon's clause (1), honestly

Nothing below asserts an equivalence.  What *is* free is one half of the comparison with clause (1)
of `GannonRational`: if an ordinary module happens to admit an admissible (level) refinement of its
*same underlying weak module*, then `AdmissiblyRational` hands back exactly
`OrdVModule.IsCompletelyReducible` for it, because both notions of complete reducibility are
phrased over `WeakModule.Submodule'` of that one weak module.

⚠ The restriction to modules *admitting a refinement* is lifted downstream:
`OrdVModule.hasAdmissibleRefinement` (`Modules/RationalityLattice.lean` §1) proves that **every**
ordinary module admits one, via the level function `ℓ(α) = ⌊Re α − B⌋`, so
`OrdVModule.isCompletelyReducible_of_admissiblyRational` there is the unconditional form (see also
the note on the general coercion below).

⚠ There is **no** analogous free statement about *ungraded weak* modules.  Rationality in the
admissible sense does not imply that every irreducible **weak** module carries an ordinary grading;
that implication is regularity-flavoured and needs `regular ⟺ rational + C₂`-cofinite
(Abe–Buhl–Dong, Trans. AMS **356** (2004) 3391–3402), an unformalized citation.  ⚠ Note this is
*not* a gap in Gannon's clause (3): Gannon's "weak module" (his Def. 5.3.1) is the `ℕ`-graded
notion, i.e. `AdmissibleModule`, so his clause (3) is DLM Thm. 8.1(c) and needs no such bridge. -/

/-- An ordinary module **admits an admissible refinement** when its underlying weak module carries
an `ℕ`-grading obeying the DLM mode shift.  (Stated as data on `N.toWeakModule` rather than as a
bundled `AdmissibleModule`, so that the two `IsCompletelyReducible` predicates are *definitionally*
about the same weak module and no transport is needed.) -/
def OrdVModule.HasAdmissibleRefinement {W : VertexOperatorAlgebra 𝒱} {M : Type v}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) : Prop :=
  ∃ lev : ℤ → Submodule ℂ M,
    (∀ k : ℤ, k < 0 → lev k = ⊥) ∧ DirectSum.IsInternal lev ∧
      ∀ ⦃w p k : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ ⦃x : M⦄, x ∈ lev k →
        mode (N.YM a) p x ∈ lev (k + (w - p - 1))

/-- **The free half of the comparison.**  Complete reducibility over admissible modules restricts
to those ordinary modules that admit an admissible refinement. -/
theorem OrdVModule.isCompletelyReducible_of_hasAdmissibleRefinement
    {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (hAR : AdmissiblyRational W) (href : N.HasAdmissibleRefinement) :
    OrdVModule.IsCompletelyReducible N := by
  obtain ⟨lev, hneg, hint, hact⟩ := href
  exact hAR (AdmissibleModule.mk N.toWeakModule lev hneg hint hact)

/-- **The refinement exists for lowest-weight ordinary modules.**  If every nonzero weight space of
`N` sits at `h + ℕ` (`IsLowestWeight`, i.e. the second clause of Gannon's `HasConformalWeight`),
then `M(k) := M_{h+k}` is an admissible refinement: the `ℕ`-support is exactly the lowest-weight
condition, internality is inherited from the `ℂ`-grading along the injection `k ↦ h + k`, and the
mode shift is the module `L₀`-commutator `mode_mem_weight`.

This is what keeps `isCompletelyReducible_of_hasAdmissibleRefinement` from being vacuous: every
irreducible ordinary module of a VOA is of this shape. -/
theorem OrdVModule.hasAdmissibleRefinement_of_isLowestWeight
    {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {h : ℂ} (hlw : IsLowestWeight N h) :
    N.HasAdmissibleRefinement := by
  classical
  -- Below the lowest weight everything vanishes.
  have hbot : ∀ j : ℤ, j < 0 → N.weight (h + (j : ℂ)) = ⊥ := by
    intro j hj
    by_contra hne
    obtain ⟨n, hn⟩ := hlw _ hne
    have hjn : (j : ℂ) = (n : ℂ) := add_left_cancel hn
    have hjn' : j = (n : ℤ) := by exact_mod_cast hjn
    omega
  have hNi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp
    N.isInternal
  refine ⟨fun k => if 0 ≤ k then N.weight (h + (k : ℂ)) else ⊥, ?_, ?_, ?_⟩
  · intro k hk
    dsimp only
    exact if_neg (not_le.mpr hk)
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · have hinj : Function.Injective (fun k : ℤ => h + (k : ℂ)) := by
        intro a b hab
        have : (a : ℂ) = (b : ℂ) := add_left_cancel hab
        exact_mod_cast this
      refine (hNi.1.comp hinj).mono ?_
      intro k
      dsimp only [Function.comp_def]
      split_ifs with hk
      · exact le_rfl
      · exact bot_le
    · refine le_antisymm le_top ?_
      rw [← hNi.2]
      refine iSup_le (fun α => ?_)
      by_cases hα : N.weight α = ⊥
      · rw [hα]; exact bot_le
      · obtain ⟨n, rfl⟩ := hlw α hα
        refine le_iSup_of_le (n : ℤ) ?_
        rw [if_pos (Int.natCast_nonneg n)]
        have hcast : (((n : ℤ)) : ℂ) = (n : ℂ) := by push_cast; ring
        rw [hcast]
  · intro w p k a ha x hx
    dsimp only at hx ⊢
    by_cases hk : 0 ≤ k
    · rw [if_pos hk] at hx
      have hmem := mode_mem_weight N ha hx p
      have heq : (h + (k : ℂ)) + (w : ℂ) - (p : ℂ) - 1
          = h + (((k + (w - p - 1) : ℤ)) : ℂ) := by push_cast; ring
      rw [heq] at hmem
      by_cases hj : 0 ≤ k + (w - p - 1)
      · rw [if_pos hj]; exact hmem
      · rw [hbot _ (not_le.mp hj)] at hmem
        rw [if_neg hj]
        exact hmem
    · rw [if_neg hk, Submodule.mem_bot] at hx
      subst hx
      have hz : mode (N.YM a) p (0 : M) = 0 := map_zero _
      rw [hz]
      exact Submodule.zero_mem _

/-- Packaged: an admissibly rational VOA has all its **lowest-weight ordinary** modules completely
reducible.  (This is the part of `GannonRational.completelyReducible` that the standard notion
delivers *within this file*; the general ordinary module is handled unconditionally by
`OrdVModule.isCompletelyReducible_of_admissiblyRational` in `Modules/RationalityLattice.lean`.) -/
theorem AdmissiblyRational.ordinary_isCompletelyReducible_of_isLowestWeight
    {W : VertexOperatorAlgebra 𝒱} (hAR : AdmissiblyRational W) {M : Type u} [AddCommGroup M]
    [Module ℂ M] (N : OrdVModule W M) {h : ℂ} (hlw : IsLowestWeight N h) :
    OrdVModule.IsCompletelyReducible N :=
  N.isCompletelyReducible_of_hasAdmissibleRefinement hAR
    (N.hasAdmissibleRefinement_of_isLowestWeight hlw)

/-!
### The general `OrdVModule → AdmissibleModule` coercion (proved downstream)

`hasAdmissibleRefinement_of_isLowestWeight` covers exactly the ordinary modules whose weights lie
in a single coset `h + ℕ`.  The general `OrdVModule` is *not* of that shape: `boundedBelow` only
bounds `Re α`, and the weights may be spread over infinitely many cosets of `ℤ` in `ℂ`.

No route through the quotient `ℂ⧸ℤ`, a global choice of coset representatives or
`Int.least_of_bdd`-style minima is needed.  `OrdVModule.hasAdmissibleRefinement`
(`Modules/RationalityLattice.lean` §1) proves the general statement outright with a single floor
function.  With `B` the global lower bound from `boundedBelow`, put `ℓ(α) := ⌊Re α − B⌋ ∈ ℤ`; then
`ℓ(α) ≥ 0` on nonzero pieces, internality is regrouping an internal direct sum along an arbitrary
map (`RationalityLattice.fibreSup_isInternal`), and the mode shift is `Int.floor_add_intCast`
because the weight shift is by an *integer*.  Dong–Li–Mason, arXiv:q-alg/9509005v1, Lemma 3.4 at
`g = 1`.

The unconditional consequence is `OrdVModule.isCompletelyReducible_of_admissiblyRational`, in the
same file: `AdmissiblyRational` gives Gannon clause (1) for *every* ordinary module.  The
lowest-weight version below is kept because it is self-contained and needs no `⌊·⌋`. -/

/-! ## A positive witness generator: `𝒱 = ℂ𝟙` -/

/-- If `𝒱` is spanned by its vacuum then **every** `ℂ`-subspace of a weak module is a weak
submodule: the only modes are `𝟙₍ₙ₎ = δ_{n,−1}·id`, rescaled. -/
theorem WeakModule.act_mem_of_span_vacuum {W : VertexOperatorAlgebra 𝒱}
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤)
    {M : Type v} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (S : Submodule ℂ M)
    (u : 𝒱) (n : ℤ) {x : M} (hx : x ∈ S) : A.act u n x ∈ S := by
  have hu : u ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have hsm : A.act (c • W.vacuum) n x = c • A.act W.vacuum n x := by
    change mode (A.YM (c • W.vacuum)) n x = c • mode (A.YM W.vacuum) n x
    rw [map_smul, mode_smul]; rfl
  rw [hsm, A.act_vacuum]
  split_ifs
  · exact S.smul_mem c hx
  · simp

/-- **Positive witness generator.**  A VOA whose underlying space is `ℂ𝟙` is admissibly
rational: every subspace of every weak module is a weak submodule, and subspaces of a
`ℂ`-vector space always have complements.

This is what guards `AdmissiblyRational` against being accidentally over-strong (and hence
`¬ AdmissiblyRational` against being vacuously true of everything).  Instantiated at `trivialVOA`
in `Examples/TrivialAdmissiblyRational.lean`. -/
theorem admissiblyRational_of_span_vacuum (W : VertexOperatorAlgebra 𝒱)
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) : AdmissiblyRational W := by
  intro M _ _ N P
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl P.carrier
  exact ⟨⟨q, fun u n {_} hx =>
    WeakModule.act_mem_of_span_vacuum hspan N.toWeakModule q u n hx⟩, hq⟩

end VOA
