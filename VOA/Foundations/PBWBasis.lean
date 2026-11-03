/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Foundations.AffineLie
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# `PBWBasis` — Poincaré–Birkhoff–Witt for the affine vacuum module, as a **named hypothesis**

**Status.**  `PBWBasis` is **proved** for every `𝔤`, `κ`, ordered basis and level `k`
(critical included): `VOA.pbwBasis_holds` in `Foundations/PBWTheorem/VacuumBasis.lean`.  And
`VOA.pbw` (`Foundations.AffineLie`) is a **theorem**; the library has no project
axiom.  The discussion below explains why `PBWBasis` is stated as a hypothesis.

## Why this file exists

The PBW principle `VOA.pbw` (`Foundations.AffineLie`, `PBWPrinciple`; a theorem) has exactly two
fields — `affineVacuum` (the vacuum vector is nonzero) and
`inducedBottom`
(injectivity of `PBWInduction.bottom`).  **Neither gives linear independence of creation
monomials.**  That independence is what every "`A₂(V^k(𝔤)) ≅ Sym(𝔤)`"-type statement needs
(`Examples.AffineSl2Indep`, `Examples.AffineSl2Symbol`, `Examples.AffineSl2QuasiLisse`), and
this file gives it a name.

Design decision: PBW may be **assumed**, because nobody doubts
it is a true theorem and this project exists to formalize things that are more prone to human
error — **but it must be a named hypothesis, never a new axiom**, for three reasons:

1. `#print axioms` is this project's quality gate.  If PBW dependence were an axiom the audits
   could not distinguish "genuinely unconditional" from "conditional on PBW".
2. Every vacuity failure found in this repository was visible in a **signature**.  A hypothesis
   keeps the dependence visible; an axiom hides it.
3. A hypothesis is the *stronger* claim: "this is a true theorem we have not formalized", rather
   than "we are assuming this".

This matches the existing citation-hypothesis culture: `Modules.PoissonTrace.EtingofFinite`,
`ZhuAdmissibleSemisimple`, `AffineSl2Rigidity43.RegularImpliesTrivialGraded`,
`DLMSimpleAdmissibleOrdinary`.

⚠ **`VOA.pbw` is not extended.**  It is not threaded through this file; it has
about 671 use sites.  Nothing in this file touches it, and
nothing in this file is an axiom.

## Not in Mathlib

`Mathlib/Algebra/Lie/UniversalEnveloping.lean` provides only `UniversalEnvelopingAlgebra.lift`
and `ι`, and does not even prove `ι` injective.  There is no PBW theorem in Mathlib at the time
of writing, so it cannot be imported.  References for the classical statement: Dixmier,
*Enveloping Algebras*, 2.1.11; Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §17.3; Kac, *Infinite Dimensional Lie Algebras*, §1.4 (and §9.10 for the affine vacuum
module `𝒱(𝔤,k) = U(ĝ)⧸J(k)` being free of rank one over `U(t⁻¹𝔤[t⁻¹])`).

## The shape, and why it is this shape

```
def PBWBasis (κ) (hκ) (b : Module.Basis ι ℂ 𝔤) (k : ℂ) : Prop :=
  ∃ B : Module.Basis ((ι ×ₗ ℕ) →₀ ℕ) ℂ (AffineLie.vacuumSpace κ hκ k),
    ∀ μ, B μ = AffineLie.negWord κ hκ k (pbwWord b μ)
```

* **A bundled `Basis`, not a bare `LinearIndependent`.**  Every intended consumer needs a
  *coordinate functional defined on all of* `𝒱(𝔤,k)` — e.g. "project onto the pure `(-1)`-mode
  monomials", used to prove `Ψ(O₂) = 0`.  `LinearIndependent` alone gives functionals only on
  the span; extending them needs a complement whose values off the span are arbitrary, which is
  useless for a vanishing statement.
* **Bundling the basis is honest, not overreach.**  The *proved* spanning theorem
  `AffineLie.negSpan_eq_top` spans `𝒱(𝔤,k)` by **all** words `negWord L`, not by *ordered* ones.
  Upgrading it to ordered words is the straightening/reordering half of PBW and is itself
  unformalized here.  So the hypothesis is exactly PBW — no more, and no less.
* **The index `(ι ×ₗ ℕ) →₀ ℕ`** is the exponent function on colour × depth, ordered
  lexicographically.  Using the `Lex` synonym is what supplies the `LinearOrder` needed to sort
  the support into the fixed order; `ℕ` is the *depth*, matching this repository's convention
  that depth `n` means the mode `-n-1` (`AffineLie.negWord_cons`).
* **It is deliberately NOT phrased** as "the symbol map `Sym(𝔤) → A₂(V^k(𝔤))` is injective".
  That is a *conclusion* one would want to derive; assuming it would hollow out the derivation.

## Main declarations

* `pbwWord b μ` — the ordered creation word of an exponent function;
* `PBWBasis κ hκ b k` — the hypothesis;
* `PBWBasis.linearIndependent` — its usable content: the ordered creation monomials are
  linearly independent;
* `PBWBasis.vacuumVector_ne_zero` — it implies `AffineLie.PBW κ hκ k`, i.e. the first field of
  `VOA.pbw`.  **So `PBWBasis` is strictly stronger than `VOA.pbw.affineVacuum`,
  and in particular it is not vacuously true.**
* `pbwBasis_of_subsingleton` and `pbwBasis_iff_of_subsingleton` — the **positive control**:
  for the zero Lie algebra, `PBWBasis` holds *iff* the vacuum vector is nonzero.  This certifies
  that the `∃ Basis …` shape is **satisfiable** — it is not accidentally self-contradictory
  (e.g. through a mis-chosen index type) — while making no unproved claim, since the degenerate
  case is exactly where the statement has no content beyond non-degeneracy.

## Status

* This file proves nothing about non-degenerate `𝔤`; `PBWBasis` is a hypothesis here.
* It is **proved** in general by `VOA.pbwBasis_holds` (`Foundations/PBWTheorem/VacuumBasis.lean`).
* At `𝔰𝔩₂` it was first **proved** for every non-critical level `k + 2 ≠ 0`:
  `AffineSl2WakimotoLiLeading.affineSl2PBWBasis` (via Wakimoto triangularity,
  `pbwBasis_of_wakimotoOrderedCreationState_linearIndependent`).  It is consumed by, e.g.,
  `AffineSl2UniversalC2PBW.symbolAlg_injective_of_PBWBasis` (injectivity of the `C₂` symbol map
  `Sym(𝔰𝔩₂) → A₂(V^k(𝔰𝔩₂))`) and the `AffineSl2Joint*`/`AffineSl2Vacuum*` files.
* The universal affine VOA of a general simple `𝔤` exists (`AffineGeneral.universalAffineVOA`,
  `AffineGeneral/Simple.lean`); the general `A₂(V^k(𝔤)) ≅ Sym(𝔤)` is not stated in this file.

## Dependencies
* `Foundations.AffineLie` — `vacuumSpace`, `vacuumVector`, `vacuumRho`, `ofLoop`, `ofLoopₗ`,
  `negWord`, `negSpan`, `negSpan_eq_top`.
-/

namespace VOA

open AffineLie

universe u

/-! ## §1  The ordered creation word of an exponent function -/

/-- The **ordered creation word** of an exponent function `μ` on colour × depth: the support is
sorted in the fixed lexicographic order of `ι ×ₗ ℕ`, and each pair `(i, n)` contributes `μ (i,n)`
copies of the generator `(b i, n)` — i.e. of the mode `b i ⊗ t^{-n-1}`.

The convention matches `AffineLie.negWord`, whose index is `List (𝔤 × ℕ)` with depth `n : ℕ`
denoting the mode `-n-1`. -/
noncomputable def pbwWord {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι ℂ 𝔤) (μ : (ι ×ₗ ℕ) →₀ ℕ) : List (𝔤 × ℕ) :=
  (μ.support.sort (· ≤ ·)).flatMap fun p => List.replicate (μ p) (b (ofLex p).1, (ofLex p).2)

/-- The empty exponent function gives the empty word, so its monomial is the vacuum vector. -/
@[simp] theorem pbwWord_zero {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] {ι : Type*}
    [LinearOrder ι] (b : Module.Basis ι ℂ 𝔤) : pbwWord b (0 : (ι ×ₗ ℕ) →₀ ℕ) = [] := by
  simp [pbwWord]

/-- If the index type is empty then *every* exponent function gives the empty word. -/
theorem pbwWord_of_isEmpty {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] {ι : Type*}
    [LinearOrder ι] [IsEmpty (ι ×ₗ ℕ)] (b : Module.Basis ι ℂ 𝔤) (μ : (ι ×ₗ ℕ) →₀ ℕ) :
    pbwWord b μ = [] := by
  have hs : μ.support = ∅ := Finset.eq_empty_of_forall_notMem fun a _ => isEmptyElim a
  simp [pbwWord, hs]

/-! ## §2  The hypothesis -/

/-- **PBW for the affine vacuum module** (Poincaré–Birkhoff–Witt; Dixmier 2.1.11,
Humphreys §17.3, Kac §1.4 and §9.10).

The ordered creation monomials
`(x_{i₁} ⊗ t^{-n₁-1}) ⋯ (x_{i_r} ⊗ t^{-n_r-1})·|0⟩`
form a **basis** of `𝒱(𝔤,k) = U(ĝ)⧸J(k)`; equivalently, `𝒱(𝔤,k)` is free of rank one over
`U(t⁻¹𝔤[t⁻¹])`.

⚠ **NOT in Mathlib** (`Mathlib/Algebra/Lie/UniversalEnveloping.lean` supplies only `lift`/`ι`,
and does not even prove `ι` injective), and **carried here as a named hypothesis by design —
never as an axiom.**  It is proved for every `𝔤`, `b`, `k`:
`VOA.pbwBasis_holds` (`Foundations/PBWTheorem/VacuumBasis.lean`).

⚠ It is strictly stronger than the `affineVacuum` field of `VOA.pbw`
(`PBWBasis.vacuumVector_ne_zero`), and strictly stronger than the proved spanning theorem
`AffineLie.negSpan_eq_top`, which spans by *all* words rather than ordered ones. -/
def PBWBasis {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant)
    {ι : Type*} [LinearOrder ι] (b : Module.Basis ι ℂ 𝔤) (k : ℂ) : Prop :=
  ∃ B : Module.Basis ((ι ×ₗ ℕ) →₀ ℕ) ℂ (AffineLie.vacuumSpace κ hκ k),
    ∀ μ, B μ = AffineLie.negWord κ hκ k (pbwWord b μ)

namespace PBWBasis

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {κ : LinearMap.BilinForm ℂ 𝔤} {hκ : κ.IsInvariant}
  {ι : Type*} [LinearOrder ι] {b : Module.Basis ι ℂ 𝔤} {k : ℂ}

/-- **The usable content**: the ordered creation monomials are linearly independent. -/
theorem linearIndependent (h : PBWBasis κ hκ b k) :
    LinearIndependent ℂ fun μ : (ι ×ₗ ℕ) →₀ ℕ => AffineLie.negWord κ hκ k (pbwWord b μ) := by
  obtain ⟨B, hB⟩ := h
  have : (fun μ : (ι ×ₗ ℕ) →₀ ℕ => AffineLie.negWord κ hκ k (pbwWord b μ)) = ⇑B :=
    funext fun μ => (hB μ).symm
  rw [this]
  exact B.linearIndependent

/-- The ordered creation monomials also span, so `PBWBasis` refines `AffineLie.negSpan_eq_top`
from arbitrary words to ordered ones. -/
theorem span_eq_top (h : PBWBasis κ hκ b k) :
    Submodule.span ℂ
        (Set.range fun μ : (ι ×ₗ ℕ) →₀ ℕ => AffineLie.negWord κ hκ k (pbwWord b μ)) = ⊤ := by
  obtain ⟨B, hB⟩ := h
  have : (fun μ : (ι ×ₗ ℕ) →₀ ℕ => AffineLie.negWord κ hκ k (pbwWord b μ)) = ⇑B :=
    funext fun μ => (hB μ).symm
  rw [this]
  exact B.span_eq

/-- `PBWBasis` implies affine-vacuum nonvanishing — the first field of `VOA.pbw` (a theorem).  **So `PBWBasis` is not vacuously true.** -/
theorem vacuumVector_ne_zero (h : PBWBasis κ hκ b k) :
    AffineLie.vacuumVector κ hκ k ≠ 0 := by
  obtain ⟨B, hB⟩ := h
  have h0 : B 0 = AffineLie.vacuumVector κ hκ k := by
    rw [hB 0, pbwWord_zero, AffineLie.negWord_nil]
  rw [← h0]
  exact B.ne_zero 0

/-- Restatement of the previous lemma in the vocabulary of `Foundations.AffineLie`. -/
theorem toPBW (h : PBWBasis κ hκ b k) : _root_.VOA.PBW κ hκ k :=
  h.vacuumVector_ne_zero

end PBWBasis

/-! ## §3  The positive control: satisfiability of the `∃ Basis …` shape

A named hypothesis is only useful if it can be *true*.  The danger with an `∃ Basis I ℂ V`
statement is that a mis-chosen index type makes it contradictory (two distinct indices forced to
the same vector, say), which no amount of `#print axioms` would reveal.

The control below settles that: for the **zero** Lie algebra, where the affine vacuum module is
spanned by the vacuum vector alone, `PBWBasis` holds **exactly when** the vacuum vector is
nonzero.  Both directions are proved.  This is deliberately the degenerate case — it is the only
place where PBW is cheap, and claiming anything more would be claiming PBW itself. -/

section Control

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [Subsingleton 𝔤]
  (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant) (k : ℂ)

/-- `Fin 0 ×ₗ ℕ` is empty. -/
instance : IsEmpty (Fin 0 ×ₗ ℕ) := ⟨fun p => (ofLex p).1.elim0⟩

/-- Exponent functions on an empty colour × depth set are unique. -/
instance : Unique ((Fin 0 ×ₗ ℕ) →₀ ℕ) where
  default := 0
  uniq _ := Finsupp.ext fun a => isEmptyElim a

/-- For the zero Lie algebra every nonempty creation word gives `0`. -/
theorem negWord_eq_zero_of_subsingleton (L : List (𝔤 × ℕ)) (hL : L ≠ []) :
    AffineLie.negWord κ hκ k L = 0 := by
  match L, hL with
  | (x, n) :: L', _ =>
      have hx : x = 0 := Subsingleton.elim x 0
      rw [AffineLie.negWord_cons, hx,
        show AffineLie.ofLoop κ hκ (0 : 𝔤) (-(n : ℤ) - 1) = 0 from
          map_zero (AffineLie.ofLoopₗ κ hκ (-(n : ℤ) - 1)),
        map_zero, LinearMap.zero_apply]

/-- For the zero Lie algebra the affine vacuum module is spanned by the vacuum vector. -/
theorem span_vacuumVector_eq_top_of_subsingleton :
    Submodule.span ℂ {AffineLie.vacuumVector κ hκ k} = (⊤ : Submodule ℂ _) := by
  rw [eq_top_iff, ← AffineLie.negSpan_eq_top κ hκ k, AffineLie.negSpan, Submodule.span_le]
  rintro _ ⟨L, rfl⟩
  rcases eq_or_ne L [] with rfl | hL
  · rw [AffineLie.negWord_nil]
    exact Submodule.subset_span rfl
  · rw [negWord_eq_zero_of_subsingleton κ hκ k L hL]
    exact Submodule.zero_mem _

/-- **Positive control.**  For the zero Lie algebra, `PBWBasis` holds as soon as the affine
vacuum vector is nonzero.  So the `∃ Basis …` shape of `PBWBasis` is **satisfiable**: it is not
accidentally self-contradictory.

⚠ This claims nothing about PBW for a nonzero `𝔤`; it is a shape check. -/
theorem pbwBasis_of_subsingleton (hne : AffineLie.vacuumVector κ hκ k ≠ 0) :
    PBWBasis κ hκ (Module.Basis.empty 𝔤 : Module.Basis (Fin 0) ℂ 𝔤) k := by
  classical
  set v : ((Fin 0 ×ₗ ℕ) →₀ ℕ) → AffineLie.vacuumSpace κ hκ k :=
    fun _ => AffineLie.vacuumVector κ hκ k with hv
  have hli : LinearIndependent ℂ v := linearIndependent_unique_iff.mpr hne
  have hsp : (⊤ : Submodule ℂ (AffineLie.vacuumSpace κ hκ k)) ≤ Submodule.span ℂ (Set.range v) := by
    rw [hv, Set.range_const, span_vacuumVector_eq_top_of_subsingleton κ hκ k]
  refine ⟨Module.Basis.mk hli hsp, fun _ => ?_⟩
  rw [Module.Basis.mk_apply, hv, pbwWord_of_isEmpty, AffineLie.negWord_nil]

/-- The converse, for the zero Lie algebra: `PBWBasis` is *equivalent* to vacuum nonvanishing
there.  Together with `pbwBasis_of_subsingleton` this pins the degenerate case exactly, which is
the strongest control available without proving PBW. -/
theorem pbwBasis_iff_of_subsingleton :
    PBWBasis κ hκ (Module.Basis.empty 𝔤 : Module.Basis (Fin 0) ℂ 𝔤) k
      ↔ AffineLie.vacuumVector κ hκ k ≠ 0 :=
  ⟨fun h => h.vacuumVector_ne_zero, pbwBasis_of_subsingleton κ hκ k⟩

end Control

end VOA

section AxiomAudit
#print axioms VOA.pbwWord
#print axioms VOA.pbwWord_zero
#print axioms VOA.pbwWord_of_isEmpty
#print axioms VOA.PBWBasis
#print axioms VOA.PBWBasis.linearIndependent
#print axioms VOA.PBWBasis.span_eq_top
#print axioms VOA.PBWBasis.vacuumVector_ne_zero
#print axioms VOA.PBWBasis.toPBW
#print axioms VOA.negWord_eq_zero_of_subsingleton
#print axioms VOA.span_vacuumVector_eq_top_of_subsingleton
#print axioms VOA.pbwBasis_of_subsingleton
#print axioms VOA.pbwBasis_iff_of_subsingleton
end AxiomAudit
