/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.AdmissibleRationality
import VOA.Modules.C2Cofinite
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# The rationality lattice — `AdmissiblyRational`, `Regular`, `GannonRational`

Four notions of module, from widest to narrowest, and the four rationality predicates built on
them.  This file records **which implications between them are theorems of this repository, which
are theorems of the literature carried as named hypotheses, and which are neither**.

## The module categories, and where they live

* **weak** — `WeakModule` (`Modules/WeakModule.lean:84`): no grading at all, plus an explicit
  `truncation` axiom.
* **admissible** — `AdmissibleModule` (`Modules/AdmissibleModule.lean`): an `ℕ`-grading
  with the DLM mode shift `a₍ₚ₎ M(k) ⊆ M(k + wt a − p − 1)`.  No `L₀`-eigenvalue condition, no
  finite-dimensionality.
* **ordinary** — `OrdVModule` (`Modules/WeakModule.lean:159`): a `ℂ`-grading by honest
  `L₀`-eigenspaces, finite-dimensional pieces, `Re α` bounded below.

`ordinary ⊆ admissible ⊆ weak`.  The first inclusion is **proved here**, in full generality:
`OrdVModule.hasAdmissibleRefinement` (§1).

## The rationality predicates

* `AdmissiblyRational` (`Modules/AdmissibleModule.lean`) — every **admissible** module is
  completely reducible.  This is the standard Zhu / Dong–Li–Mason notion (`Rational_DLM`).
* `Regular` (§4) — every **weak** module is completely reducible, and every irreducible weak module
  is ordinary.  Dong–Li–Mason, Adv. Math. **132** (1997), Def. 3.1.  ⚠ This — not Gannon's
  predicate — is what the phrase "weakly rational" would naturally mean, and it is the
  **strongest** notion in the lattice, not the weakest.
* `GannonRational` (`Modules/Rationality.lean`) — Gannon Def. 5.3.2, faithfully transcribed.
  ⚠ It is not the misreading whose third field is transcribed over the *ungraded* `WeakModule`
  and concludes a detached `Nonempty (OrdVModule W M)`; §6 records what goes wrong under that
  misreading.  No predicate is named `WeaklyRational`.
* `Holomorphic` (`Modules/Rationality.lean`) — `GannonRational` with `#Φ(𝒱) = 1`.

## What is proved here (no hypotheses, no axioms beyond the Lean three)

* `OrdVModule.hasAdmissibleRefinement` — **every ordinary module is admissible**, via the level
  function `ℓ(α) = ⌊Re α − B⌋`.  (Dong–Li–Mason Lemma 3.4 at `g = 1`.)  No route through
  `ℂ⧸ℤ` and a global choice of coset representatives is needed (see the note on the general
  coercion in `Modules/AdmissibleRationality.lean`).
* `OrdVModule.isCompletelyReducible_of_admissiblyRational` — hence `AdmissiblyRational` gives
  Gannon's field (1) unconditionally.
* `ΦtoΦadm_injective`, `finite_Φ_of_finite_Φadm` — `Φ(𝒱) ↪ Φadm(𝒱)`, so DLM's finiteness of
  irreducible *admissible* modules yields Gannon's field (2).
* `Regular.admissiblyRational` — **regular ⟹ rational** (DLM Remark 3.2).
* `abdRegularOfC2AndRational_of_components` — the hard direction of Abe–Buhl–Dong Thm. 4.5,
  assembled from ABD Prop. 5.7 and ABD Cor. 5.8.
* `Regular.gannonAdmissibleIsOrdinary` — **regular ⟹ Gannon clause (3)**, in one line and with no
  borrowed citation.  This is why `gannonRational_of_regular` needs no
  `DLMSimpleAdmissibleOrdinary` hypothesis.
* `gannonRational_of_admissiblyRational` — **`Rational_DLM ⟹ GannonRational`**, from
  the two DLM theorems alone, with **no** `C₂`-cofiniteness and **no** Abe–Buhl–Dong.
  ⚠ A composite `[DLM] + [ABD] ⟹ (ungraded misreading)` would have to pay `C₂`-cofiniteness in
  field (3); that price is an artefact of the transcription error, not of Gannon's definition.

## What is CARRIED as a named hypothesis (§5), and which of these are theorems

One `def` per literature theorem, never folded into a definition and never an `axiom`:
`DLMSimpleAdmissibleOrdinary` (DLM Thm. 8.1(c)), `DLMFinitelyManyIrredAdmissible` (DLM Thm. 8.1(b)),
`ABDWeakIsAdmissible` (ABD Prop. 5.7, alt. Miyamoto Thm. 2.7), `ABDIrreducibleWeakIsOrdinary`
(ABD Cor. 5.8), `ABDRegularOfC2AndRational` (ABD Thm. 4.5, hard direction — but *derived* here),
`LiC2CofiniteOfRegular` (H. Li Thm. 3.8).  Zhu's semisimplicity theorem is already carried, as
`ZhuAdmissibleSemisimple` (`Modules/AdmissibleRationality.lean`); it is not redefined.

**Status update.**  The declarations of this file still take these predicates as hypotheses, but
most of them are proved downstream (summary: `Classification/COne/LiteratureInputsProved.lean`,
namespace `VOA.Classification.COne.LiteratureInputs`):

* for **every** VOA: `ABDWeakIsAdmissible` (`ABDWeakAdmissible.abdWeakIsAdmissible`),
  `ABDIrreducibleWeakIsOrdinary` (`abdIrreducibleWeakIsOrdinary_holds`),
  `ABDRegularOfC2AndRational` (`abdRegularOfC2AndRational_holds`) and `ZhuAdmissibleSemisimple`
  (`zhuAdmissibleSemisimple_holds`);
* for **`C₂`-cofinite** VOAs only: `DLMSimpleAdmissibleOrdinary`
  (`AdmissibleOrdinary.dlmSimpleAdmissibleOrdinary_of_c2Cofinite`) and
  `DLMFinitelyManyIrredAdmissible` (`dlmFinitelyManyIrredAdmissible_of_c2Cofinite`).

**Still unproved:** `LiC2CofiniteOfRegular`, and the non-`C₂` cases of the two DLM predicates.  So
`regular_iff_c2Cofinite_and_admissiblyRational`, which as stated carries both `hABD`
(dischargeable by `abdRegularOfC2AndRational_holds`) and `hLi`, remains conditional on
`LiC2CofiniteOfRegular`.

## ⚠ Gannon's clause (3) is admissible, not weak (§6, in full)

One might read Gannon Def. 5.3.2's third field as quantifying over **weak** modules, and therefore
as needing Abe–Buhl–Dong.  **That is false about Gannon.**  Gannon's
Def. 5.3.1 (p. 330) defines "weak `V`-module" to be `ℕ`-**graded** with the DLM mode shift, i.e.
what everyone else calls *admissible*.  Gannon's clause (3) is therefore DLM Thm. 8.1(c), free from
`C₂`-cofiniteness.  The weak-module reading would be correct only for a transcription of clause (3)
over the *ungraded* `WeakModule`; `Modules/Rationality.lean` transcribes it over admissible modules.

## Status

`sorry`-free, `admit`-free, `native_decide`-free, no project axioms, `pbw`-free.  Every declaration
is `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0  Regrouping an internal direct sum along an arbitrary relabelling -/

namespace RationalityLattice

section Collapse

variable {ι κ : Type*} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The `k`-th piece of the grading obtained from `t` by relabelling along `f` and summing
the fibre. -/
def fibreSup (t : ι → Submodule R M) (f : ι → κ) (k : κ) : Submodule R M :=
  ⨆ i ∈ f ⁻¹' {k}, t i

theorem fibreSup_def (t : ι → Submodule R M) (f : ι → κ) (k : κ) :
    fibreSup t f k = ⨆ i ∈ f ⁻¹' {k}, t i := rfl

theorem le_fibreSup (t : ι → Submodule R M) (f : ι → κ) (i : ι) :
    t i ≤ fibreSup t f (f i) :=
  le_biSup t (show i ∈ f ⁻¹' {f i} by simp)

theorem iSup_ne_fibreSup (t : ι → Submodule R M) (f : ι → κ) (k : κ) :
    (⨆ (k' : κ) (_ : k' ≠ k), fibreSup t f k') = ⨆ i ∈ (f ⁻¹' {k})ᶜ, t i := by
  apply le_antisymm
  · refine iSup_le fun k' => iSup_le fun hk' => ?_
    rw [fibreSup_def]
    refine iSup_le fun i => iSup_le fun hi => le_biSup t ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hi]
    exact hk'
  · refine iSup_le fun i => iSup_le fun hi => ?_
    have hik : f i ≠ k := by
      simpa only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using hi
    refine le_trans (le_fibreSup t f i) ?_
    refine le_trans (le_iSup (fun _ : f i ≠ k => fibreSup t f (f i)) hik) ?_
    exact le_iSup (fun k' => ⨆ (_ : k' ≠ k), fibreSup t f k') (f i)

/-- **Independence survives relabelling** — no finiteness hypothesis needed, because the
submodule lattice is compactly generated. -/
theorem fibreSup_iSupIndep {t : ι → Submodule R M} (ht : iSupIndep t) (f : ι → κ) :
    iSupIndep (fibreSup t f) := by
  rw [iSupIndep_def]
  intro k
  rw [fibreSup_def, iSup_ne_fibreSup t f k]
  exact ht.disjoint_biSup_biSup disjoint_compl_right

/-- **Spanning survives relabelling.** -/
theorem fibreSup_iSup (t : ι → Submodule R M) (f : ι → κ) :
    (⨆ k : κ, fibreSup t f k) = ⨆ i, t i := by
  apply le_antisymm
  · exact iSup_le fun k => iSup_le fun i => iSup_le fun _ => le_iSup t i
  · exact iSup_le fun i =>
      le_trans (le_fibreSup t f i) (le_iSup (fun k => fibreSup t f k) (f i))

/-- **Relabelling an internal direct sum along an arbitrary map keeps it internal.** -/
theorem fibreSup_isInternal [DecidableEq κ] {t : ι → Submodule R M}
    (h₁ : iSupIndep t) (h₂ : iSup t = ⊤) (f : ι → κ) :
    DirectSum.IsInternal (fibreSup t f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (fibreSup_iSupIndep h₁ f)
    (by rw [show iSup (fibreSup t f) = iSup t from fibreSup_iSup t f]; exact h₂)

end Collapse

end RationalityLattice

/-! ## §1  Every ordinary module is admissible — proved -/

open RationalityLattice in
/-- **Ordinary ⟹ admissible, in full generality and with no extra hypothesis.**

Dong–Li–Mason, *Twisted representations of vertex operator algebras*, arXiv:q-alg/9509005v1
(= Math. Ann. **310** (1998) 571–600), **Lemma 3.4** (rendered numbering): "There is a natural
identification of the category of `g`-twisted `V`-modules with a subcategory of the category of
admissible `g`-twisted `V`-modules."  At `g = 1` this is exactly the statement below.

The proof here is *not* the coset-by-coset argument sketched in
`Modules/AdmissibleRationality.lean` (which would need `ℂ⧸ℤ` and a global choice of coset
representatives).  With `B` the global lower bound supplied by `OrdVModule.boundedBelow`, the
level of the weight `α` is simply

  `ℓ(α) := ⌊Re α − B⌋ ∈ ℤ`,

and the three axioms are one line each:

* `ℓ(α) ≥ 0` whenever `M_α ≠ 0`, because `boundedBelow` gives `Re α ≥ B`;
* internality is `fibreSup_isInternal` — regrouping an internal direct sum along *any* map
  keeps it internal;
* the mode shift is `Int.floor_add_intCast`: `ℓ(α + w − p − 1) = ℓ(α) + (w − p − 1)`, since the
  weight shift `mode_mem_weight` is by an *integer*.

⚠ This uses the repository's `OrdVModule.boundedBelow`, which asks for **one global** real bound
`B ≤ Re α` on all nonzero pieces.  Abe–Buhl–Dong Def. 2.5 (published; = arXiv Def. 2.4) instead
bound each coset `λ + ℤ` separately with no bound uniform across cosets, so `OrdVModule` is a
*proper subclass* of ABD-ordinary and the floor construction is available here but would not be
available verbatim from ABD's definition.  Recorded so that no ABD statement is silently
strengthened by import. -/
theorem OrdVModule.hasAdmissibleRefinement {W : VertexOperatorAlgebra 𝒱} {M : Type u}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) : N.HasAdmissibleRefinement := by
  classical
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨fibreSup N.weight (fun α : ℂ => ⌊α.re - B⌋), ?_, ?_, ?_⟩
  · -- `ℕ`-support: a nonzero weight space forces `⌊Re α − B⌋ ≥ 0`.
    intro k hk
    refine le_antisymm (iSup_le fun α => iSup_le fun hα => ?_) bot_le
    by_cases hw : N.weight α = ⊥
    · rw [hw]
    · exfalso
      have hle : B ≤ α.re := hB α hw
      have h0 : (0 : ℤ) ≤ ⌊α.re - B⌋ := Int.le_floor.mpr (by push_cast; linarith)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hα
      omega
  · -- Internality: regroup the `ℂ`-grading along `α ↦ ⌊Re α − B⌋`.
    have hNi :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal
    exact fibreSup_isInternal hNi.1 hNi.2 _
  · -- Mode shift.
    intro w p k a ha x hx
    have key : fibreSup N.weight (fun α : ℂ => ⌊α.re - B⌋) k ≤
        Submodule.comap (mode (N.YM a) p)
          (fibreSup N.weight (fun α : ℂ => ⌊α.re - B⌋) (k + (w - p - 1))) := by
      refine iSup_le fun α => iSup_le fun hα => ?_
      rw [SetLike.le_def]
      intro y hy
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hα
      have hmem := mode_mem_weight N ha hy p
      have hfl : ⌊(α + (w : ℂ) - (p : ℂ) - 1).re - B⌋ = k + (w - p - 1) := by
        have hre : (α + (w : ℂ) - (p : ℂ) - 1).re - B
            = (α.re - B) + ((w - p - 1 : ℤ) : ℝ) := by
          push_cast
          simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
          ring
        rw [hre, Int.floor_add_intCast, hα]
      have : N.weight (α + (w : ℂ) - (p : ℂ) - 1)
          ≤ fibreSup N.weight (fun α : ℂ => ⌊α.re - B⌋) (k + (w - p - 1)) := by
        rw [← hfl]
        exact le_fibreSup N.weight (fun α : ℂ => ⌊α.re - B⌋) _
      exact this hmem
    exact key hx

/-! ## §2  Consequences: the ordinary category sits inside the admissible one -/

/-- The canonical admissible refinement of an ordinary module, carried on the **same** underlying
weak module (`toAdmissible_toWeakModule` is `rfl`).  Non-computable only because a level family is
chosen out of `OrdVModule.hasAdmissibleRefinement`. -/
noncomputable def OrdVModule.toAdmissible {W : VertexOperatorAlgebra 𝒱} {M : Type u}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) : AdmissibleModule W M where
  toWeakModule := N.toWeakModule
  lev := N.hasAdmissibleRefinement.choose
  lev_eq_bot_of_neg := N.hasAdmissibleRefinement.choose_spec.1
  isInternal := N.hasAdmissibleRefinement.choose_spec.2.1
  act_lev := N.hasAdmissibleRefinement.choose_spec.2.2

@[simp] theorem OrdVModule.toAdmissible_toWeakModule {W : VertexOperatorAlgebra 𝒱} {M : Type u}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) :
    N.toAdmissible.toWeakModule = N.toWeakModule := rfl

/-- **`AdmissiblyRational` gives Gannon's field (1) unconditionally.**  Every *ordinary* module
of an admissibly rational VOA is completely reducible — no lowest-weight hypothesis, no extra
citation.  This upgrades `AdmissiblyRational.ordinary_isCompletelyReducible_of_isLowestWeight`
(`Modules/AdmissibleRationality.lean`), which was restricted to modules concentrated on a single
coset `h + ℕ`. -/
theorem OrdVModule.isCompletelyReducible_of_admissiblyRational {W : VertexOperatorAlgebra 𝒱}
    {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)
    (hAR : AdmissiblyRational W) : OrdVModule.IsCompletelyReducible N :=
  N.isCompletelyReducible_of_hasAdmissibleRefinement hAR N.hasAdmissibleRefinement

/-! ## §3  Isomorphism of **weak** modules, and `Φadm(𝒱)`

`ModuleEquiv` (`Modules/Rationality.lean`) is *already* nothing but a weak-module intertwiner: its
only fields are a `ℂ`-linear equivalence and `map_act`, with no compatibility with the `ℂ`-grading.
The same notion at the level of bare weak modules is therefore the common denominator of the
ordinary, admissible and weak categories, and it is what makes the comparison of iso-class sets
below purely formal. -/

/-- An **isomorphism of weak `𝒱`-modules**: a `ℂ`-linear equivalence intertwining every mode. -/
structure WeakModuleEquiv (W : VertexOperatorAlgebra 𝒱) {M N : Type u} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup N] [Module ℂ N] (A : WeakModule W M) (B : WeakModule W N) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : M ≃ₗ[ℂ] N
  /-- Intertwining of the actions: `e(u₍ₙ₎ x) = u₍ₙ₎ e(x)`. -/
  map_act : ∀ (u : 𝒱) (n : ℤ) (x : M),
    toLinearEquiv (A.act u n x) = B.act u n (toLinearEquiv x)

namespace WeakModuleEquiv

variable {W : VertexOperatorAlgebra 𝒱}

/-- The identity isomorphism. -/
def refl {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) :
    WeakModuleEquiv W A A where
  toLinearEquiv := LinearEquiv.refl ℂ M
  map_act _ _ _ := rfl

/-- The inverse isomorphism. -/
def symm {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    {A : WeakModule W M} {B : WeakModule W N} (e : WeakModuleEquiv W A B) :
    WeakModuleEquiv W B A where
  toLinearEquiv := e.toLinearEquiv.symm
  map_act u n y := by
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, e.map_act, LinearEquiv.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {M N P : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] {A : WeakModule W M} {B : WeakModule W N} {C : WeakModule W P}
    (e : WeakModuleEquiv W A B) (f : WeakModuleEquiv W B C) : WeakModuleEquiv W A C where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_act u n x := by simp only [LinearEquiv.trans_apply, e.map_act, f.map_act]

end WeakModuleEquiv

/-- An ordinary-module isomorphism *is* a weak-module isomorphism — same two fields. -/
def ModuleEquiv.toWeak {W : VertexOperatorAlgebra 𝒱} {M N : Type u} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {A : OrdVModule W M} {B : OrdVModule W N}
    (e : ModuleEquiv W A B) : WeakModuleEquiv W A.toWeakModule B.toWeakModule :=
  ⟨e.toLinearEquiv, e.map_act⟩

/-- …and conversely: the repository's `ModuleEquiv` imposes **no** condition on the `ℂ`-grading, so
a weak-module isomorphism between the underlying weak modules of two ordinary modules already *is*
an isomorphism of ordinary modules.  (Recorded explicitly: this is the reason the comparison of
`Φ` with `Φadm` below is formal rather than mathematical.) -/
def WeakModuleEquiv.toOrd {W : VertexOperatorAlgebra 𝒱} {M N : Type u} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup N] [Module ℂ N] {A : OrdVModule W M} {B : OrdVModule W N}
    (e : WeakModuleEquiv W A.toWeakModule B.toWeakModule) : ModuleEquiv W A B :=
  ⟨e.toLinearEquiv, e.map_act⟩

/-- A **bundled irreducible admissible `𝒱`-module** (carrier in `Type u`), the admissible-category
analogue of `IrrModule`. -/
structure IrrAdmModule (W : VertexOperatorAlgebra 𝒱) where
  /-- The underlying carrier type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The admissible `𝒱`-module structure. -/
  isMod : AdmissibleModule W carrier
  /-- Irreducibility (no weak submodule other than `0` and `M`). -/
  irreducible : isMod.IsIrreducible

attribute [instance] IrrAdmModule.addCommGroup IrrAdmModule.module

/-- Isomorphism of bundled irreducible admissible modules: an isomorphism of the underlying
**weak** modules.  (Deliberately *not* grade-preserving — see the module docstring's discussion of
DLM's grade-preserving morphisms.) -/
def IrrAdmModule.Iso (W : VertexOperatorAlgebra 𝒱) (A B : IrrAdmModule W) : Prop :=
  Nonempty (WeakModuleEquiv W A.isMod.toWeakModule B.isMod.toWeakModule)

/-- Isomorphism of bundled irreducible admissible modules is an equivalence relation. -/
def IrrAdmModule.setoid (W : VertexOperatorAlgebra 𝒱) : Setoid (IrrAdmModule W) where
  r := IrrAdmModule.Iso W
  iseqv :=
    { refl := fun A => ⟨WeakModuleEquiv.refl A.isMod.toWeakModule⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- **`Φadm(𝒱)`** — the set of isomorphism classes of irreducible **admissible** `𝒱`-modules.
This, not `Φ(𝒱)`, is the set that Dong–Li–Mason's finiteness theorem is about. -/
def Φadm (W : VertexOperatorAlgebra 𝒱) : Type (u + 1) := Quotient (IrrAdmModule.setoid W)

/-- Every irreducible ordinary module is an irreducible admissible module, on the same weak
module. -/
noncomputable def IrrModule.toIrrAdmModule {W : VertexOperatorAlgebra 𝒱} (V : IrrModule W) :
    IrrAdmModule W where
  carrier := V.carrier
  isMod := V.isMod.toAdmissible
  irreducible := V.irreducible

/-- The induced map `Φ(𝒱) → Φadm(𝒱)`. -/
noncomputable def ΦtoΦadm (W : VertexOperatorAlgebra 𝒱) : Φ W → Φadm W :=
  Quotient.lift (fun V => (Quotient.mk (IrrAdmModule.setoid W) V.toIrrAdmModule : Φadm W))
    (fun _ _ h => Quotient.sound (h.map fun e => ⟨e.toLinearEquiv, e.map_act⟩))

/-- `Φ(𝒱) → Φadm(𝒱)` is **injective**: both iso-relations are "the underlying weak modules are
isomorphic", and the refinement `toAdmissible` does not change the underlying weak module. -/
theorem ΦtoΦadm_injective (W : VertexOperatorAlgebra 𝒱) : Function.Injective (ΦtoΦadm W) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun A B h => ?_)
  exact Quotient.sound ((Quotient.exact h).map fun e => ⟨e.toLinearEquiv, e.map_act⟩)

/-- **Finiteness transfer**: finitely many irreducible *admissible* modules forces finitely many
irreducible *ordinary* modules.  This is what turns Dong–Li–Mason Thm. 8.1(b) into Gannon's field
(2). -/
theorem finite_Φ_of_finite_Φadm (W : VertexOperatorAlgebra 𝒱) (h : Finite (Φadm W)) :
    Finite (Φ W) :=
  haveI := h
  Finite.of_injective _ (ΦtoΦadm_injective W)

/-! ## §4  `Regular` — Dong–Li–Mason's strongest notion

### §4.0  The missing bottom of the ladder: reducibility for **weak** modules

`Modules/WeakModule.lean` names `IsIrreducible` and `IsCompletelyReducible` for `OrdVModule`, and
`Modules/AdmissibleModule.lean` names them for `AdmissibleModule`, but the **widest** category —
the plain `WeakModule` those two are built on — had no name for either, even though both existing
definitions are stated *through* `WeakModule.Submodule'` and are therefore literally about the
underlying weak module.  The two `def`s below supply the missing names, and the four `Iff.rfl`
bridges after them record that `ordinary ⊆ admissible ⊆ weak` is, for these two predicates, not an
inclusion of *different* notions but one notion read at three places. -/

namespace WeakModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **Irreducible weak module**: nonzero, and `0` and `M` are its only weak submodules.

`OrdVModule.IsIrreducible` (`Modules/WeakModule.lean`) and `AdmissibleModule.IsIrreducible`
(`Modules/AdmissibleModule.lean`) are *literally* this predicate applied to the underlying weak
module — see `OrdVModule.isIrreducible_iff_toWeakModule` and
`AdmissibleModule.isIrreducible_iff_toWeakModule`, both `Iff.rfl`.  That is why every
category-crossing bridge in §7 is a one-liner rather than a transport.

⚠ **Why this is declared here rather than beside its two siblings in `Modules/WeakModule.lean`.**
Beside them is where it belongs, and moving it there later is a pure relocation — nothing in the
statement mentions anything from this file.  It is declared here only to keep the recompilation
cone small: several hundred files lie downstream of `Modules/WeakModule.lean`. -/
def IsIrreducible (A : WeakModule W M) : Prop :=
  Nontrivial M ∧ ∀ P : WeakModule.Submodule' A, P.carrier = ⊥ ∨ P.carrier = ⊤

/-- **Completely reducible weak module**: every weak submodule is complemented by a weak submodule.

The analogue of `OrdVModule.IsCompletelyReducible` (`Modules/WeakModule.lean`) and
`AdmissibleModule.IsCompletelyReducible` (`Modules/AdmissibleModule.lean`), on the **widest** of
the three categories.  `Regular` below is exactly *"every weak module satisfies this"* — and that,
not Gannon's Def. 5.3.2, is what the phrase "weakly rational" says if it is read at face value.

Same relocation caveat as `WeakModule.IsIrreducible`. -/
def IsCompletelyReducible (A : WeakModule W M) : Prop :=
  ∀ P : WeakModule.Submodule' A, ∃ Q : WeakModule.Submodule' A, IsCompl P.carrier Q.carrier

end WeakModule

section CategoryLadder

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- Irreducibility of an **ordinary** module *is* irreducibility of its underlying weak module —
the same proposition, not merely an equivalent one. -/
theorem OrdVModule.isIrreducible_iff_toWeakModule (N : OrdVModule W M) :
    OrdVModule.IsIrreducible N ↔ N.toWeakModule.IsIrreducible := Iff.rfl

/-- Complete reducibility of an **ordinary** module *is* complete reducibility of its underlying
weak module.  This `rfl` is what makes `Regular.ordinaryCompletelyReducible` a one-liner. -/
theorem OrdVModule.isCompletelyReducible_iff_toWeakModule (N : OrdVModule W M) :
    OrdVModule.IsCompletelyReducible N ↔ N.toWeakModule.IsCompletelyReducible := Iff.rfl

/-- Irreducibility of an **admissible** module *is* irreducibility of its underlying weak module.
This `rfl` is what makes `Regular.gannonAdmissibleIsOrdinary` — the `F4(i)` repair — a one-liner
instead of a borrowed Dong–Li–Mason citation. -/
theorem AdmissibleModule.isIrreducible_iff_toWeakModule (N : AdmissibleModule W M) :
    AdmissibleModule.IsIrreducible N ↔ N.toWeakModule.IsIrreducible := Iff.rfl

/-- Complete reducibility of an **admissible** module *is* complete reducibility of its underlying
weak module.  This `rfl` is what makes `Regular.admissiblyRational` a one-liner. -/
theorem AdmissibleModule.isCompletelyReducible_iff_toWeakModule (N : AdmissibleModule W M) :
    AdmissibleModule.IsCompletelyReducible N ↔ N.toWeakModule.IsCompletelyReducible := Iff.rfl

end CategoryLadder

/-! ### §4.1  `Regular` itself -/

/-- **Regular** — Dong–Li–Mason, *Regularity of rational vertex operator algebras*, arXiv
q-alg/9508018v1 (sole version), **Definition 3.1**, p. 5 (published as Adv. Math. **132** (1997)
148–166, whose numbering was not independently verified; note that Abe–Buhl–Dong and Dong–Yu both
misprint the volume as 312).  Verbatim: *"A vertex operator algebra `V` is said to be regular if
any weak `V`-module `M` is a direct sum of simple ordinary `V`-modules."*  Hypotheses: none beyond
`V` a VOA — no CFT type, no simplicity, no `C₂`-cofiniteness.

⚠ **Convention, stated rather than smuggled.**  "Direct sum of simple ordinary modules" is rendered
here by the repository's semisimplicity convention (`IsCompletelyReducible`: every weak submodule is
complemented by a weak submodule) *plus* the separate clause that the simple pieces are ordinary.
The two fields below are exactly those two halves:

1. `weakCompletelyReducible` — every **weak** module is completely reducible (this is where
   `Regular` outruns `AdmissiblyRational`, which quantifies only over admissible modules);
2. `irreducibleWeakIsOrdinary` — every **irreducible weak** module carries an ordinary structure
   **on the same weak module**.

Both fields are written out in full here rather than through the §4.0 names
`WeakModule.IsCompletelyReducible` / `WeakModule.IsIrreducible`, so that the structure keeps
exactly the shape every existing proof constructs and destructs.  The named readings are available
as `Regular.weakIsCompletelyReducible` and `Regular.weakIrreducibleIsOrdinary`, which are the two
fields verbatim — *"every weak module is completely reducible"*.

Field (2) is stated in the faithful `∃ N, N.toWeakModule = A` form, not the weaker
`Nonempty (OrdVModule W M)` of the ungraded misreading `weakIsModule`; see §6.

⚠ **This is the honest referent of the phrase "weakly rational"** — "rational with respect to weak
modules" — and it is the **strongest** notion in this file, not the weakest.  Gannon's "weakly
rational" (`GannonRational`, `Modules/Rationality.lean`) means something else entirely and is
strictly implied by this. -/
structure Regular (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- Every **weak** module is completely reducible. -/
  weakCompletelyReducible : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (P : WeakModule.Submodule' A), ∃ Q : WeakModule.Submodule' A, IsCompl P.carrier Q.carrier
  /-- Every irreducible **weak** module carries an ordinary structure on the same weak module. -/
  irreducibleWeakIsOrdinary : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
    (Nontrivial M ∧ ∀ P : WeakModule.Submodule' A, P.carrier = ⊥ ∨ P.carrier = ⊤) →
    ∃ N : OrdVModule W M, N.toWeakModule = A

namespace Regular

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Field (1) in the named vocabulary of §4.0**: *every **weak** `𝒱`-module is completely
reducible*.  This is `Regular.weakCompletelyReducible` verbatim, restated through
`WeakModule.IsCompletelyReducible` so that the defining property of `Regular` can be spelled with
the predicate it is named for.  Nothing is proved: the two are definitionally equal. -/
theorem weakIsCompletelyReducible (h : Regular W) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) : A.IsCompletelyReducible :=
  fun P => h.weakCompletelyReducible A P

/-- **Field (2) in the named vocabulary of §4.0**: every **irreducible weak** module carries an
ordinary structure *on that same weak module*.  Note the conclusion `N.toWeakModule = A`, which
names the given module — avoiding the detached-conclusion defect of the misreading
`weakIsModule` (§6), which `Regular.gannonAdmissibleIsOrdinary` also avoids. -/
theorem weakIrreducibleIsOrdinary (h : Regular W) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) (hA : A.IsIrreducible) : ∃ N : OrdVModule W M, N.toWeakModule = A :=
  h.irreducibleWeakIsOrdinary A hA

/-- **Regular ⟹ rational** — Dong–Li–Mason, arXiv q-alg/9508018v1, **Remark 3.2**, verbatim:
*"A regular vertex operator algebra `V` is necessarily rational.  Indeed if `M` is a weak
`V`-module then, being a direct sum of ordinary simple `V`-module, it is admissible (Remark 2.4
(i)) and, for the same reason, a direct sum of simple admissibles."*

In the repository's semisimplicity convention the argument collapses to one line: complete
reducibility is a property of the *underlying weak module*, and an admissible module has one. -/
theorem admissiblyRational (h : Regular W) : AdmissiblyRational W :=
  fun N P => h.weakCompletelyReducible N.toWeakModule P

/-- Regular ⟹ every **ordinary** module is completely reducible (Gannon field (1)), directly,
without going through `AdmissiblyRational`. -/
theorem ordinaryCompletelyReducible (h : Regular W) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) : OrdVModule.IsCompletelyReducible N :=
  fun P => h.weakCompletelyReducible N.toWeakModule P

/-- **Regular ⟹ Gannon Def. 5.3.2 clause (3)**, in its faithful reading — a one-liner, with
**no** `C₂`-cofiniteness and **no** borrowed Dong–Li–Mason citation.

It typechecks on the nose because `AdmissibleModule.IsIrreducible`
(`Modules/AdmissibleModule.lean`) is *definitionally* the antecedent of
`Regular.irreducibleWeakIsOrdinary`: both are
`Nontrivial M ∧ ∀ P : WeakModule.Submodule' …, P.carrier = ⊥ ∨ P.carrier = ⊤` on the same
underlying weak module.

⚠ A detached variant, `.choose`-ing the faithful `∃ N : OrdVModule W M, N.toWeakModule = A`
down to `Nonempty (OrdVModule W M)`, would only propagate the detached-conclusion defect of §6;
the statement below is strictly more informative. -/
theorem gannonAdmissibleIsOrdinary (h : Regular W) : GannonAdmissibleIsOrdinary W :=
  fun N hN => h.irreducibleWeakIsOrdinary N.toWeakModule hN

end Regular

/-! ## §5  The literature, carried as **named, cited hypotheses** — one `def` per theorem

Nothing in this section is proved *in this file*; for which predicates are theorems
elsewhere, see the status update in the module docstring and
`Classification/COne/LiteratureInputsProved.lean`.  Each `def` is a `Prop` whose docstring
carries the exact
citation of the theorem it transcribes, together with the hypotheses of that theorem that are
**not** formalized in this repository.  Anything that a definition would otherwise hide is written
out.

⚠ **CFT type is automatic here.**  `VOA.VertexOperatorAlgebra` builds Gannon's VOA4 into
the structure: `vacuum_grade : grading 0 = ℂ ∙ vacuum` and `positivity : ∀ n < 0, grading n = ⊥`
(`Core/VertexOperatorAlgebra.lean:124-127`).  That is *exactly* Abe–Buhl–Dong's standing hypothesis
"`V = ⊕_{n≥0} V_n` and `V_0 = ℂ𝟙`".  So the ABD statements below need only `C2Cofinite` as an
explicit hypothesis; their CFT-type assumption is discharged by the ambient structure and is *not*
being dropped.

⚠ **Why applying DLM to `AdmissiblyRational` is licensed.**  Dong–Li–Mason's `g`-rationality is
complete reducibility in the *graded* admissible category ("`0` and `M` are the only graded
submodules", their own words); the repository's `AdmissiblyRational` uses the weak-submodule
reading.  ⚠ It is tempting to claim that the weak-submodule reading **implies** the graded one,
so that every `def` below with antecedent `AdmissiblyRational W` would be a consequence of the
cited theorem.  That sketch fails (the graded part of a weak complement need not be a complement),
and `Modules/AdmissibleRationality.lean` (§ *⚠ One deliberate convention*) records the relation
between the two readings as **not settled**; only
"DLM-rational ⟹ `AdmissiblyRational`" is known on paper.  So the literature does not by itself
license the `AdmissiblyRational`-antecedent `def`s below.  For those that are Lean theorems
(see the module docstring) the question is moot: they are proved from the library's own
`AdmissiblyRational`. -/

/-- **Dong–Li–Mason Thm. 8.1(c)** — *Twisted representations of vertex operator algebras*,
arXiv:q-alg/9509005v1 (sole arXiv version) = Math. Ann. **310** (1998) 571–600, Theorem 8.1,
part (c), specialized to `g = 1`.  Verbatim: *"Every simple admissible `g`-twisted `V`-module is
an ordinary `g`-twisted `V`-module."*  Hypothesis: `V` is `g`-rational, i.e. every admissible
module is completely reducible.  No CFT type, no simplicity of `V`, no `C₂`-cofiniteness.

⚠ **Quantifier direction, checked.**  DLM's "simple admissible" means simple in the **graded**
category: verbatim, *"a simple object in this category is an admissible `g`-twisted `V`-module `M`
such that `0` and `M` are the only graded submodules"*.  The repository's
`AdmissibleModule.IsIrreducible` instead forbids **all weak** submodules, which is a *stronger*
condition on `M`; so the class of `M` quantified over here is a *subclass* of DLM's, and the `Prop`
below is therefore **implied by** DLM Thm. 8.1(c) rather than implying it.  Carrying the weaker
statement is the safe direction. -/
def DLMSimpleAdmissibleOrdinary (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AdmissiblyRational W →
    ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M),
      N.IsIrreducible → ∃ O : OrdVModule W M, O.toWeakModule = N.toWeakModule

/-- **Dong–Li–Mason Thm. 8.1(b)** — same source, part (b), at `g = 1`.  Verbatim: *"`V` has only
finitely many isomorphism classes of simple admissible `g`-twisted modules."*  Same hypotheses:
`g`-rationality alone.  Restated by the same authors as Theorem 3.2(b) of *Modular invariance of
trace functions in orbifold theory*, arXiv:q-alg/9703016v2 (= Comm. Math. Phys. **214** (2000)
1–56), attributed there solely to the Math. Ann. paper.

⚠ **Do NOT cite** *Regularity of rational vertex operator algebras*, Adv. Math. **132** (1997)
148–166 for (b) or (c).  That paper only **asserts** them, in its Remark 2.4(ii), and cites the
Math. Ann. paper for the proof.

⚠ **Quantifier direction, checked.**  DLM count graded-simple admissibles up to *grade-preserving*
iso; `Φadm` counts weak-simple admissibles up to *weak* iso.  Weak-simple ⟹ graded-simple (graded
submodules are weak submodules) and grade-preserving iso ⟹ weak iso, so `Φadm W` is a quotient of a
subset of DLM's iso-class set.  Finiteness therefore descends, and the `Prop` below is again
**implied by** DLM Thm. 8.1(b). -/
def DLMFinitelyManyIrredAdmissible (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AdmissiblyRational W → Finite (Φadm W)

/-- **Abe–Buhl–Dong Prop. 5.7** (published numbering) `=` **Prop. 5.6** of arXiv:math/0204021v1
— *Rationality, regularity, and `C₂`-cofiniteness*, Trans. Amer. Math. Soc. **356** (2004), no. 8,
3391–3402, p. 3400.  Verbatim (published): *"If `V` is a `C₂`-cofinite vertex operator algebra,
then any weak `V`-module is admissible."*  Hypotheses: `C₂`-cofiniteness plus the paper's standing
CFT-type assumption (automatic here, see the section note).  **No** rationality, **no** simplicity,
**no** finite generation.

Independently, and under the strictly weaker standing hypothesis `V = ⊕_{m≥0} V_m` with no
`dim V_0 = 1`: Miyamoto, *Modular invariance of vertex operator algebras satisfying
`C₂`-cofiniteness*, Duke Math. J. **122** (2004), no. 1, 51–91 (= arXiv:math/0209101v2),
**Theorem 2.7**, the implication (1) ⟹ (3).  ⚠ Miyamoto's conclusion is *stronger* than the `Prop`
below: his `W(n)` are additionally direct sums of **generalized** `L(0)`-eigenspaces, which the
repository's `AdmissibleModule` does not record.  The transcription below keeps only the
`ℕ`-gradability, so it is implied by both sources. -/
def ABDWeakIsAdmissible (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
    ∃ N : AdmissibleModule W M, N.toWeakModule = A

/-- **Abe–Buhl–Dong Cor. 5.8** (published) `=` **Cor. 5.7** of arXiv:math/0204021v1, same paper,
p. 3400.  Verbatim (published): *"If `V` is a `C₂`-cofinite vertex operator algebra, then any
irreducible weak `V`-module is an irreducible ordinary `V`-module."*  Hypotheses: `C₂`-cofiniteness
plus the standing CFT-type assumption (automatic here).  **No** rationality, **no** regularity,
**no** simplicity.

This — *not* ABD's main Theorem 4.5 — is the bridge from irreducible **weak** modules to ordinary
ones.  ABD's own proof is one line and rests on their Theorem 3.3, which is Buhl's PBW-type
spanning set for weak modules (G. Buhl, *A spanning set for VOA modules*, J. Algebra **254** (2002)
125–151); so the price of this bridge is `C₂`-cofiniteness *and* Buhl's spanning theorem, neither of
which is formalized here.

⚠ **One direction of strengthening, recorded.**  ABD's "ordinary" (their Def. 2.5, published) bounds
each coset `λ + ℤ` separately; `OrdVModule.boundedBelow` demands one global bound.  For an
*irreducible* module the two agree, because all nonzero weights lie in a single coset — proved in
this repository as `OrdVModule.weight_eq_coset_of_irreducible`
(`Modularity/LowestWeightExistence.lean`) — so the transcription is faithful on the class it
quantifies over. -/
def ABDIrreducibleWeakIsOrdinary (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
    (Nontrivial M ∧ ∀ P : WeakModule.Submodule' A, P.carrier = ⊥ ∨ P.carrier = ⊤) →
    ∃ N : OrdVModule W M, N.toWeakModule = A

/-- **Abe–Buhl–Dong Thm. 4.5**, the hard direction — same paper, p. 3397.  Verbatim: *"A vertex
operator algebra, `V`, of CFT type is regular if and only if `V` is `C₂`-cofinite and rational."*
Here "rational" is ABD Def. 2.6 (published) = `AdmissiblyRational`, and "regular" is ABD Def. 2.7
(published) = `Regular`.

This `def` is kept for the record only: it is **derived** below from the two component hypotheses
`ABDWeakIsAdmissible` and `ABDIrreducibleWeakIsOrdinary`
(`abdRegularOfC2AndRational_of_components`), which is how ABD themselves prove it. -/
def ABDRegularOfC2AndRational (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → AdmissiblyRational W → Regular W

/-- **H. Li, Thm. 3.8** — *Some finiteness properties of regular vertex operator algebras*,
J. Algebra **212** (1999) 495–514 (= arXiv:math/9807077v1, sole version; the theorem number is the
preprint's, reconstructed from the shared per-section counter and corroborated by Carnahan's
citations of Cor. 2.6 / Cor. 2.11 of the same paper).  Verbatim: *"Any vertex operator algebra of
class `A` satisfies the `C₂`-finiteness condition and it is finitely generated.  In particular, any
regular vertex operator algebra `V` satisfies the `C₂`-finiteness condition and it is finitely
generated."*  Hypotheses: `V` a VOA of class `A` (`L(0)` acts semisimply on every weak module); no
CFT type, no simplicity, no self-duality.  Regularity enters only through Li's remark that class
`A` contains all regular VOAs.

This is the **easy** direction of ABD Thm. 4.5, and the reference ABD cite as their `[16]`.

⚠ Class `A` is a condition on **all** weak modules, so this cannot be fired from Gannon field (3),
which speaks only of irreducible weak modules. -/
def LiC2CofiniteOfRegular (W : VertexOperatorAlgebra 𝒱) : Prop :=
  Regular W → C2Cofinite W

/-! ## §6  Gannon's Definition 5.3.2 as **Gannon** states it

⚠⚠ **A correction to the framing this file was commissioned under, and to a doc comment already in
the repository.**

Gannon, *Moonshine beyond the Monster*, CUP 2006, **Definition 5.3.1** (p. 330) defines a *weak
`V`-module* to be **`ℕ`-graded**: verbatim, *"a weak `V`-module `(M, Y_M)` is an `ℕ`-graded vector
space `M = ⊕_{n∈ℕ} M_[n]` … such that for any `u ∈ V_k`, the mode `u_(n)` is a linear map from
`M_[ℓ]` into `M_[k+ℓ−n−1]`"*.  That is **verbatim Dong–Li–Mason admissibility**, not the ungraded
weak module of Li/DLM.  Gannon's unqualified *`V`-module* (5.3.1c) is the **ordinary** notion.
Gannon never uses the word "admissible" for modules anywhere in Chapter 5.

Consequently Gannon **Definition 5.3.2** (p. 331) — verbatim: *"A VOA `V` is called weakly rational
if every `V`-module is completely reducible, `V` has only a finite number of irreducible modules,
and every irreducible weak `V`-module is a `V`-module."* — reads, in DLM vocabulary:

1. every **ordinary** module is completely reducible;
2. finitely many irreducible **ordinary** modules;
3. every irreducible **admissible** module is **ordinary**.

Clause (3) is therefore *exactly* Dong–Li–Mason Thm. 8.1(c).  It needs **no** Abe–Buhl–Dong bridge
and reintroduces **no** `C₂`-cofiniteness.  The claim that Gannon's clause (3) quantifies over
ungraded weak modules is **false about Gannon**.

What *is* true concerns a transcription of clause (3) over `WeakModule`
(`Modules/WeakModule.lean`), which carries **no grading at all** — the `ℕ`-grading and mode shift
of Gannon Def. 5.3.1 are dropped and an explicit `truncation` axiom substituted (Gannon needs no
truncation axiom: it follows from the `ℕ`-grading).  Such a field (call it `weakIsModule`) is
**strictly stronger** than Gannon's clause (3), and *that* is
where a regularity-flavoured, `C₂`-consuming statement enters.  The docstring attribution
"Gannon Def. 5.3.1, after [199]" at `Modules/WeakModule.lean:79-84` is inaccurate for the same
reason; the shape matching Gannon Def. 5.3.1 is `AdmissibleModule` (and
`ZGradedWeakModule`, `Modules/ZhuVermaAnArchDLM3Level.lean:97`).

There is a **second, independent** defect in such a field (3), pulling the other way if its
conclusion is `Nonempty (OrdVModule W M)`, which merely says the carrier type supports *some*
ordinary structure, with nothing requiring that structure's `toWeakModule` to be the given `A`.
Gannon asserts that the given pair `(M, Y_M)` **is** a `V`-module.  So such a `weakIsModule`
is simultaneously stronger than Gannon (wider quantifier) and weaker than Gannon (detached
conclusion), and is **not comparable** to Gannon's clause (3) in either direction.

**Neither defect is present in the library.**  `Modules/Rationality.lean` does not define
`WeaklyRational`; it defines `GannonAdmissibleIsOrdinary` (clause (3), over `AdmissibleModule`,
with the conclusion tied to the given module) and `GannonRational` (the three-clause package).
This section records what goes wrong under the misreading and why; the definitions live upstream, next to
`Φ(𝒱)` and `Holomorphic`, which is where Gannon's Def. 5.3.2 belongs. -/

/-! ## §7  The lattice, machine-checked -/

variable {W : VertexOperatorAlgebra 𝒱}

/-- Gannon's clause (3), in its faithful reading, is Dong–Li–Mason Thm. 8.1(c) applied — a
one-liner, with **no** `C₂`-cofiniteness and **no** Abe–Buhl–Dong. -/
theorem gannonAdmissibleIsOrdinary_of_dlm (hAR : AdmissiblyRational W)
    (hDLM : DLMSimpleAdmissibleOrdinary W) : GannonAdmissibleIsOrdinary W := hDLM hAR

/-- **`Rational_DLM ⟹ GannonRational`**, all three clauses, from the two
Dong–Li–Mason theorems alone.  No `C₂`-cofiniteness, no Abe–Buhl–Dong, no Buhl spanning set.

This statement fails only for the *mis*-transcription of clause (3) over ungraded weak modules
(§6), not for Gannon's actual definition. -/
theorem gannonRational_of_admissiblyRational (hAR : AdmissiblyRational W)
    (hFin : DLMFinitelyManyIrredAdmissible W) (hOrd : DLMSimpleAdmissibleOrdinary W) :
    GannonRational W where
  completelyReducible := fun N => N.isCompletelyReducible_of_admissiblyRational hAR
  finitelyManyIrred := finite_Φ_of_finite_Φadm W (hFin hAR)
  admissibleIsOrdinary := hOrd hAR

/-- **Abe–Buhl–Dong Cor. 5.8 is not primitive**: it factors through ABD Prop. 5.7 (every weak module
is admissible) followed by "irreducible admissible ⟹ ordinary".

⚠ The factorization shown here costs an extra `AdmissiblyRational` hypothesis, because the
"irreducible admissible ⟹ ordinary" step is imported as Dong–Li–Mason Thm. 8.1(c), which assumes
rationality.  ABD's own proof of Cor. 5.8 does **not** assume rationality: it uses their Theorem
3.3 = Buhl's spanning theorem instead.  So this is a *sufficient* route to the same conclusion, not
a reconstruction of ABD's proof. -/
theorem abdIrreducibleWeakIsOrdinary_of_components (hWA : ABDWeakIsAdmissible W)
    (hOrd : DLMSimpleAdmissibleOrdinary W) (hAR : AdmissiblyRational W) :
    ABDIrreducibleWeakIsOrdinary W := by
  intro hC2 M _ _ A hA
  obtain ⟨N, rfl⟩ := hWA hC2 A
  exact hOrd hAR N hA

/-- **The hard direction of Abe–Buhl–Dong Thm. 4.5, assembled from its two component lemmas.**
Given ABD Prop. 5.7 and ABD Cor. 5.8 as named hypotheses, `C₂`-cofiniteness plus rationality really
does yield regularity — and the derivation is machine-checked rather than asserted in prose.
CFT type is discharged by the ambient `VertexOperatorAlgebra` structure (VOA4). -/
theorem abdRegularOfC2AndRational_of_components (hWA : ABDWeakIsAdmissible W)
    (hIrr : ABDIrreducibleWeakIsOrdinary W) : ABDRegularOfC2AndRational W := by
  intro hC2 hAR
  constructor
  · intro M _ _ A P
    obtain ⟨N, rfl⟩ := hWA hC2 A
    exact hAR N P
  · intro M _ _ A hA
    exact hIrr hC2 A hA

/-- **Abe–Buhl–Dong Thm. 4.5 in full**, as a biconditional, from the hard direction plus H. Li's
theorem — the easy half `Regular ⟹ AdmissiblyRational` being *proved* here (DLM Remark 3.2), not
assumed. -/
theorem regular_iff_c2Cofinite_and_admissiblyRational (hABD : ABDRegularOfC2AndRational W)
    (hLi : LiC2CofiniteOfRegular W) :
    Regular W ↔ (C2Cofinite W ∧ AdmissiblyRational W) :=
  ⟨fun h => ⟨hLi h, h.admissiblyRational⟩, fun h => hABD h.1 h.2⟩

/-- **`Regular ⟹ GannonRational`**, needing only DLM Thm. 8.1(b) on top.

⚠ **This is the `F4(i)` repair.**  The previous version of this theorem also carried
`hOrd : DLMSimpleAdmissibleOrdinary W`, a cited-literature hypothesis, to discharge clause (3).
That was a borrowed citation for something regularity proves outright in one line
(`Regular.gannonAdmissibleIsOrdinary`), so the hypothesis is gone.  `hFin` genuinely stays: DLM
Thm. 8.1(b) is not derivable from `Regular` in this repository, since nothing here classifies the
irreducible admissible modules of an arbitrary regular VOA.

No `C₂`-cofiniteness hypothesis appears, and none is hidden: `C₂`-cofiniteness is a *consequence*
of regularity (H. Li Thm. 3.8, carried as `LiC2CofiniteOfRegular`), not an input here. -/
theorem gannonRational_of_regular (h : Regular W)
    (hFin : DLMFinitelyManyIrredAdmissible W) : GannonRational W where
  completelyReducible := fun N => h.ordinaryCompletelyReducible N
  finitelyManyIrred := finite_Φ_of_finite_Φadm W (hFin h.admissiblyRational)
  admissibleIsOrdinary := h.gannonAdmissibleIsOrdinary

/-- Regularity gives the ABD Cor. 5.8 conclusion for free, discarding the `C₂` hypothesis. -/
theorem Regular.abdIrreducibleWeakIsOrdinary (h : Regular W) :
    ABDIrreducibleWeakIsOrdinary W :=
  fun _ _ _ _ A hA => h.irreducibleWeakIsOrdinary A hA

/-!
## §8  What does **not** follow, and why — stated, not papered over

### 8.1  `AdmissiblyRational ⇏ "every irreducible **ungraded weak** module is ordinary"`

⚠ **This gap does not stand between `AdmissiblyRational` and `GannonRational`.**  It stands
between `AdmissiblyRational` and the misreading of Gannon's clause (3) over ungraded weak modules
(§6).  With clause (3) stated over admissible modules — which is what Gannon Def. 5.3.1 says —
`gannonRational_of_admissiblyRational` needs no `C2Cofinite` hypothesis at all.  A `C₂` price
arises only from that transcription error.  The gap below is real, but it is a gap about
`Regular`, not about Gannon's definition.

`AdmissiblyRational` quantifies over admissible modules; `ABDIrreducibleWeakIsOrdinary` quantifies
over **ungraded** weak modules.  No theorem in the literature derives the second from the first.
The only available bridge is Abe–Buhl–Dong Cor. 5.8 (`ABDIrreducibleWeakIsOrdinary`), whose
hypothesis is `C₂`-cofiniteness, so `abdRegularOfC2AndRational_of_components` takes `C2Cofinite W`
and cannot avoid it.  Miyamoto Thm. 2.7 replaces ABD Prop. 5.7 with an *equivalence*
(`C₂`-cofinite ⟺ every weak module is `ℕ`-graded with generalized-`L(0)`-eigenspace pieces), so on
that route the price is **exactly** `C₂`-cofiniteness.

⚠ "Does not follow" here means **"no theorem in the literature derives it"**, not "there is a
counterexample".  No counterexample can exist unless rationality fails to imply `C₂`-cofiniteness,
which is open: Abe–Buhl–Dong open their published paper with, verbatim, *"One of the most important
conjectures in the theory of vertex operator algebra is the equivalence of rationality and
`C₂`-cofiniteness."*  (The arXiv v1 reads *"is perhaps the equivalence"*; quote the published text.)

### 8.2  `GannonRational ⇏ AdmissiblyRational`

Gannon's clause (1) asks complete reducibility only of **ordinary** modules.  Gannon himself treats
the admissible statement as strictly more: his **Definition 6.2.3** (p. 375) defines a *rational*
VOA to be a weakly rational one obeying in addition *"(iii) every `ℕ`-graded weak module is
completely reducible"* — that is `AdmissiblyRational` — and remarks *"Condition (iii) is a little
stronger than the usual complete reducibility requirement."*  He adds `C₂`-cofiniteness separately,
as his clause (iv), together with simplicity and self-contragredience (i) and `M_0 = {0}` (ii).
So the direction proved in §7 (`AdmissiblyRational ⟹ GannonRational`) is the only one
available; the converse is not claimed anywhere and is not proved here.

### 8.3  The ungraded misreading is not comparable with `GannonRational`

This is why the library has no `WeaklyRational` alias: identifying the misreading with
`GannonRational` would silently swap one predicate for an incomparable one.  Two independent
defects, pulling opposite ways (see §6):
* **wider quantifier** — `weakIsModule` ranges over ungraded `WeakModule`s, Gannon's clause (3)
  over `ℕ`-graded ones, so that field is *stronger* than Gannon's;
* **detached conclusion** — `weakIsModule` concludes `Nonempty (OrdVModule W M)`, which does not
  require the produced ordinary structure to have the *given* `A` as its `toWeakModule`, so that
  field is also *weaker* than Gannon's.
Neither predicate implies the other.

### 8.4  `C2Cofinite ⇏ AdmissiblyRational`, `⇏ Regular`, `⇏ GannonRational`

Adamović–Milas, *On the triplet vertex algebra `W(p)`*, Adv. Math. **217** (2008) 2664–2699
(= arXiv:0707.1857v2).  For every integer `p ≥ 2` the triplet algebra `W(p)` of central charge
`c = 1 − 6(p−1)²/p` is simple (their Cor. 3.8), `C₂`-cofinite (their Thm. 2.1; also
Carqueville–Flohr, J. Phys. A **39** (2006) 951–966, by a different method), of CFT type, and has
exactly `2p` irreducible modules (their Thm. 3.12) — yet it is **not rational**: their Prop. 4.2
exhibits, for every `p ≥ 2`, non-split short exact sequences whose middle terms `V_{L+jα/2p}` are
indecomposable **ordinary** modules that are not completely reducible.  Since
`ordinary ⊆ admissible ⊆ weak`, that single family refutes rationality in **all** of the ordinary,
admissible and weak senses at once.

⚠ Consequently Gannon's remark on p. 336 — verbatim, *"It is conjectured that a VOA is weakly
rational if and only if it is `C₂`-cofinite, but although this would significantly simplify the
definition of weakly rational, it seems difficult to prove."* — must **not** be used in either
direction.  The `C₂`-cofinite ⟹ weakly rational half is known **false**.  Only the converse
(rational ⟹ `C₂`-cofinite) remains open.

### 8.5  `ABDIrreducibleWeakIsOrdinary ⇏ Regular`

`Regular.abdIrreducibleWeakIsOrdinary` (§7) is the easy direction and holds unconditionally.  The
converse fails on `W(p)` of §8.4: `W(p)` is `C₂`-cofinite and of CFT type, so ABD Cor. 5.8 gives it
`ABDIrreducibleWeakIsOrdinary`, yet Adamović–Milas Prop. 4.2 exhibits an ordinary — hence weak —
module that is not a direct sum of simple ordinary modules, which contradicts `Regular` directly
from the definition.  (Abe's `ℤ₂`-orbifold of the symplectic fermion vertex operator superalgebra,
Math. Z. **255** (2007) 755–792 = arXiv:math/0503472, gives the same counterexample at `p = 2`.)

### 8.6  Gannon field (3) is **not** enough to run the Dong–Li–Mason regularity criterion

DLM, arXiv q-alg/9508018v1, **Proposition 3.5** (quoted as Prop. 3.4 by Abe–Buhl–Dong), verbatim:
*"Let `V` be a rational vertex operator algebra such that any nonzero weak `V`-module contains a
simple ordinary `V`-submodule.  Then `V` is regular."*  Its hypothesis is about **every nonzero
weak module containing** a simple ordinary submodule — and the proof genuinely needs that
generality, since it is applied to the quotient `M/W`, an arbitrary weak module.  A statement about
*irreducible* weak modules, such as Gannon's clause (3) or `ABDIrreducibleWeakIsOrdinary`, does not
supply it: a weak module need not have any irreducible submodule at all.  So there is no route from
`AdmissiblyRational` plus field (3) to `Regular` through this proposition.

## §9  Literature theorems deliberately **not** encoded, with the precise obstruction

* **DLM Prop. 3.5** (the regularity criterion of §8.6).  Its hypothesis quantifies over *simple
  ordinary submodules* of a weak module.  The repository has no weak-module structure on a
  `WeakModule.Submodule'` — `Modules/ModuleRestrict.lean` restricts a module along a *subalgebra*
  of `𝒱`, which is a different operation — so the hypothesis cannot be stated without first
  building that restriction (`YM` restricted to the submodule, plus `vacuum_YM`, `truncation` and
  the finsum-valued `jacobi` transported along the inclusion).  Not attempted here.
* **McRae, Main Theorem 3 = Cor. 5.19**, *On rationality for `C₂`-cofinite vertex operator
  algebras*, Cambridge J. Math. **14** (2026), no. 1, 1–115 (= arXiv:2108.01898v3), verbatim:
  *"Let `V` be an `ℕ`-graded simple self-contragredient `C₂`-cofinite vertex operator algebra.  If
  the Zhu algebra `A(V)` is semisimple, then `V` is rational."*  Not encoded because *module-level*
  self-contragredience is not formalized here: `SelfContragredient`
  (`Modules/Contragredient.lean:116`) is only `Nonempty (M ≃ₗ[ℂ] RestrictedDual N)`, a graded-space
  isomorphism, strictly weaker than McRae's `V' ≅ V` **as a `V`-module** (the contragredient action
  itself is a separate construction there).  Encoding McRae with the weaker hypothesis would yield a `Prop`
  **stronger** than his theorem — the exact failure mode this file exists to prevent.
* **Dong–Yu, Thm. 4.5**, *`ℤ`-graded weak modules and regularity*, Comm. Math. Phys. **316** (2012),
  no. 1, 269–277 (= arXiv:1104.2369v1): *"For a vertex operator algebra `V`, if any `ℤ`-graded weak
  `V`-module is completely reducible, then `V` is regular."*  Two obstructions.  (i) The paper's
  standing hypothesis, verbatim from its §2, is *"Throughout this paper, we assume that `V` is a
  simple vertex operator algebra"*, and simplicity is used in the proof (it invokes irreducibility
  of the graded dual `V'`).  (ii) Its Def. 2.7 demands an honest internal direct sum
  `M = ⊕_{i∈ℤ} M(i)`, whereas the repository's `ZGradedWeakModule`
  (`Modules/ZhuVermaAnArchDLM3Level.lean:97`) asserts only *spanning* and explicitly declines to
  assert `DirectSum.IsInternal`.  The repository notion is strictly weaker, so Dong–Yu cannot be
  applied to it without first proving directness.  Not encoded.
* **Zhu's own Def. 1.2.4** of "rational" (JAMS **9** (1996) 237–302) is a **three**-clause package —
  finitely many irreducibles, finite-dimensional graded pieces, complete reducibility — not the
  single clause `AdmissiblyRational`.  The two coincide only by DLM Thm. 8.1(b),(c), i.e. by
  `DLMFinitelyManyIrredAdmissible` and `DLMSimpleAdmissibleOrdinary`.  Any citation of "Zhu,
  rational" therefore routes silently through DLM; cite DLM when the DLM definition is ambient.
  Zhu's semisimplicity theorem itself (Thm. 2.2.3, *"If `V` is rational, then `A(V)` is a
  semi-simple associative algebra"*) is already carried as `ZhuAdmissibleSemisimple`
  (`Modules/AdmissibleRationality.lean`) and is **not** redefined here.

## §10  Remarks on related statements in this repository

* The general `OrdVModule → AdmissibleModule` coercion does not need the quotient `ℂ⧸ℤ`, a global
  choice of coset representatives or `Int.least_of_bdd`-style minima: §1 shows a single floor
  function does it, `ℓ(α) = ⌊Re α − B⌋`.
* The ungraded misreading of Gannon's clause (3) is not comparable to `AdmissiblyRational` in
  either direction, but `GannonRational` is: `AdmissiblyRational ⟹ GannonRational` holds outright
  given the two DLM citations (`gannonRational_of_admissiblyRational`), and only the converse
  fails (§8.2).  Field by field: `AdmissiblyRational` **provably implies** clause (1) for *every*
  ordinary module (`Modules/AdmissibleRationality.lean` alone reaches the lowest-weight ones, via
  `AdmissiblyRational.ordinary_isCompletelyReducible_of_isLowestWeight`); given DLM Thm. 8.1(b) it
  implies clause (2); and given DLM Thm. 8.1(c) it implies clause (3).  **No** field is out of
  reach; under the ungraded misreading (§6) clause (3) would be, but not because of anything in
  Gannon.
* `Modules/WeakModule.lean:79-84` attributes the ungraded `WeakModule` to "Gannon Def. 5.3.1, after
  [199]".  Gannon's Def. 5.3.1 weak module is `ℕ`-graded; the ungraded notion is Li/DLM's.  See §6.
* `Modules.lean` describes Gannon Def. 5.3.1 as giving "weak, `ℕ`-graded, and `ℂ`-graded modules"
  — three notions.  Gannon defines **two**, and his "weak" already *is* the `ℕ`-graded one.
-/

end VOA
