/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVModQuot

/-!
# The **graded `OrdVModule` quotient** — the full `OrdVModule W (M ⧸ P)` instance

This is THE keystone unblocking `M̄(U)`, `L(U)`, and Game Two: assembling the *full* graded
`OrdVModule` structure on the quotient `M ⧸ P` of a graded `OrdVModule` `N` by a **graded**
(`L₀`-stable / homogeneous) invariant submodule `P`.

The companion file `ZhuVermaAnArchVModQuot.lean` already delivers:

* `WeakModule.quotient` / `quotient_action_mk` — the complete *weak* descent;
* `OrdVModule.quotientWeak`, `OrdVModule.quotientWeight α := map mkQ (N.weight α)`,
  `OrdVModule.quotient_L0_weight` — the descended `L₀`-eigenspace property (5.3.1c).

Here we close the remaining **graded** obligations of the `OrdVModule` structure
(`DirectSum.IsInternal` of the image grading, bounded-below, finite-dimensional pieces),
producing `OrdVModule.quotient (hgr : P graded) : OrdVModule W (M ⧸ P)` together with the
projection `OrdVModule.quotientMk` as a `OrdVModule` homomorphism.

## The graded hypothesis

A submodule `P` of a graded module is **graded** (homogeneous, `L₀`-stable) when it is the
internal sum of its homogeneous parts:
`P = ⨆_α (P ⊓ N.weight α)`. This is exactly the case for the defect/maximal-proper
submodules used to build `M̄(U)` and `L(U)`.

## Construction of the internal grading on `M ⧸ P`

Write `mkQ : M ↠ M ⧸ P`, `wα := N.weight α`, and `(M/P)_α := map mkQ wα` (the image
grading `quotientWeight`). We need `DirectSum.IsInternal (quotientWeight N P)`, i.e.
`iSupIndep (quotientWeight N P) ∧ iSup (quotientWeight N P) = ⊤`
(`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`).

* **Spanning descends** (`mkQ` surjective):
  `⨆_α map mkQ wα = map mkQ (⨆_α wα) = map mkQ ⊤ = range mkQ = ⊤`.

* **Independence descends** (`P` graded): for each `α`, with `B := ⨆_{β≠α} wβ`,
  `Disjoint (map mkQ wα) (map mkQ B)` reduces (via
  `map_inf_eq_map_inf_comap` + `comap_map_eq` + `ker_mkQ`) to `wα ⊓ (B ⊔ P) ≤ P`. With
  `P = ⨆_γ (P ⊓ wγ)` we have `B ⊔ P = B ⊔ (P ⊓ wα)` (the `γ≠α` parts of `P` sink into `B`),
  whence by the **modular law** `inf_sup_assoc_of_le` and `Disjoint wα B` (from `N.isInternal`),
  `wα ⊓ (B ⊔ (P ⊓ wα)) = (wα ⊓ B) ⊔ (P ⊓ wα) = P ⊓ wα ≤ P`.

* **Bounded below / finite-dimensional descend**: `map mkQ ⊥ = ⊥`, so a nonzero quotient
  piece comes from a nonzero `wα` (`N.boundedBelow` bound transfers); and `map mkQ wα` is a
  quotient image of the finite-dimensional `wα`, hence finite-dimensional.

No engine, no mode identities — pure submodule-image bookkeeping.

## Main results

* `OrdVModule.IsGradedSubmodule N P` — the graded hypothesis `P = ⨆_α (P ⊓ N.weight α)`.
* `OrdVModule.quotient N P hgr : OrdVModule W (M ⧸ P.carrier)` — the full graded quotient module.
* `OrdVModule.quotientMk N P hgr : N.Hom (quotient N P hgr)` — the projection as a `OrdVModule`
  homomorphism.

## Dependencies
* `VOA.Modules.ZhuVermaAnArchVModQuot`.

## References
* Gannon §5.3.1; Lepowsky–Li Ch. 4–5; DLM3.
-/

namespace VOA

open scoped BigOperators
open DirectSum

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

namespace OrdVModule

variable (N : OrdVModule W M) (P : WeakModule.Submodule' N.toWeakModule)

/-! ## The graded-submodule hypothesis -/

/-- `P` is a **graded** (homogeneous, `L₀`-stable) invariant submodule of the graded
`OrdVModule` `N`: it is the internal sum of its homogeneous parts
`P = ⨆_α (P ⊓ N.weight α)`. This is the relevant case for the defect/maximal-proper
submodules building `M̄(U) = M(U)/(defect)` and `L(U) = M(U)/J`. -/
def IsGradedSubmodule : Prop :=
  P.carrier = ⨆ α : ℂ, (P.carrier ⊓ N.weight α)

/-! ## Lattice lemmas for the image grading -/

/-- `map mkQ X = ⊥ ↔ X ≤ P` (the kernel of `mkQ` is `P`). -/
theorem map_mkQ_eq_bot_iff (X : Submodule ℂ M) :
    X.map P.carrier.mkQ = ⊥ ↔ X ≤ P.carrier := by
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]

/-- **Disjointness descends through `mkQ`.** If `A ⊓ (B ⊔ P) ≤ P` then the images
`map mkQ A` and `map mkQ B` are disjoint in `M ⧸ P`. (Reduction via
`map_inf_eq_map_inf_comap` + `comap_map_eq` + `ker_mkQ`.) -/
theorem disjoint_map_mkQ (A B : Submodule ℂ M) (h : A ⊓ (B ⊔ P.carrier) ≤ P.carrier) :
    Disjoint (A.map P.carrier.mkQ) (B.map P.carrier.mkQ) := by
  rw [disjoint_iff, Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_eq,
    Submodule.ker_mkQ, map_mkQ_eq_bot_iff]
  exact h

/-- **The modular core for independence descent.** With `B := ⨆_{β≠α} N.weight β` and
`P = ⨆_γ (P ⊓ N.weight γ)` graded, the homogeneous-overlap bound holds:
`N.weight α ⊓ (B ⊔ P) ≤ P`. Uses `N.isInternal` (disjointness of `N.weight α` from `B`)
and the modular law. -/
theorem weight_inf_le_of_graded (hgr : IsGradedSubmodule N P) (α : ℂ) :
    N.weight α ⊓ ((⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β) ⊔ P.carrier) ≤ P.carrier := by
  set w := N.weight with hw
  set B := ⨆ β : ℂ, ⨆ (_ : β ≠ α), w β with hB
  have hindep : iSupIndep N.weight :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal |>.1
  have hdis : Disjoint (w α) B := hindep α
  -- `B ⊔ P = B ⊔ (P ⊓ w α)`: the `γ≠α` homogeneous parts of `P` sink into `B`.
  have hsplit : B ⊔ P.carrier = B ⊔ (P.carrier ⊓ w α) := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      conv_lhs => rw [hgr]
      rw [iSup_le_iff]
      intro γ
      by_cases hγ : γ = α
      · subst hγ; exact le_sup_right
      · refine le_trans inf_le_right ?_
        refine le_trans ?_ le_sup_left
        rw [hB]; exact le_iSup_of_le γ (le_iSup_of_le hγ le_rfl)
    · exact sup_le_sup_left inf_le_left B
  rw [hsplit, ← inf_sup_assoc_of_le B (show P.carrier ⊓ w α ≤ w α from inf_le_right),
    disjoint_iff.mp hdis, bot_sup_eq]
  exact inf_le_left

/-! ## The internal grading on the quotient -/

/-- **Independence of the image grading descends** (for graded `P`). -/
theorem quotientWeight_iSupIndep (hgr : IsGradedSubmodule N P) :
    iSupIndep (quotientWeight N P) := by
  intro α
  -- `⨆_{β≠α} (M/P)_β = map mkQ (⨆_{β≠α} wβ)`.
  have hrw : (⨆ β : ℂ, ⨆ (_ : β ≠ α), quotientWeight N P β)
      = (⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β).map P.carrier.mkQ := by
    rw [Submodule.map_iSup]
    refine iSup_congr fun β => ?_
    rw [Submodule.map_iSup]; rfl
  rw [show quotientWeight N P α = (N.weight α).map P.carrier.mkQ from rfl, hrw]
  exact disjoint_map_mkQ N P (N.weight α) (⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β)
    (weight_inf_le_of_graded N P hgr α)

/-- **Spanning of the image grading descends** (`mkQ` surjective). -/
theorem quotientWeight_iSup_eq_top : (⨆ α : ℂ, quotientWeight N P α) = ⊤ := by
  have htop : iSup N.weight = ⊤ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal |>.2
  change (⨆ α : ℂ, (N.weight α).map P.carrier.mkQ) = ⊤
  rw [← Submodule.map_iSup, htop, Submodule.map_top, Submodule.range_mkQ]

/-- **The image grading is an internal direct-sum decomposition** of `M ⧸ P` (for graded
`P`): independence + spanning descend through `mkQ`. -/
theorem quotientWeight_isInternal (hgr : IsGradedSubmodule N P) :
    DirectSum.IsInternal (quotientWeight N P) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (quotientWeight N P)).mpr
    ⟨quotientWeight_iSupIndep N P hgr, quotientWeight_iSup_eq_top N P⟩

/-- Each quotient homogeneous piece is **finite-dimensional** (a quotient image of the
finite-dimensional `N.weight α`). -/
theorem quotientWeight_finiteDimensional (α : ℂ) :
    FiniteDimensional ℂ (quotientWeight N P α) := by
  haveI := N.finrank α
  change FiniteDimensional ℂ ((N.weight α).map P.carrier.mkQ)
  infer_instance

/-- The image grading is **bounded below**: a nonzero quotient piece comes from a nonzero
`N.weight α`, so `N.boundedBelow`'s bound transfers. -/
theorem quotientWeight_boundedBelow :
    ∃ B : ℝ, ∀ α : ℂ, quotientWeight N P α ≠ ⊥ → B ≤ α.re := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨B, fun α hα => hB α ?_⟩
  intro hbot
  apply hα
  change (N.weight α).map P.carrier.mkQ = ⊥
  rw [hbot, Submodule.map_bot]

/-! ## The full graded `OrdVModule` quotient -/

/-- **The full graded `OrdVModule` quotient** `M ⧸ P` for a graded (homogeneous, `L₀`-stable)
invariant submodule `P` (Gannon Def. 5.3.1a–c). The *weak* structure is `quotientWeak`; the
graded data is the image grading `quotientWeight` (internal by `quotientWeight_isInternal`,
finite-dimensional and bounded-below by `quotientWeight_finiteDimensional` /
`quotientWeight_boundedBelow`); the `L₀`-eigenspace property is `quotient_L0_weight`.

THE keystone unblocking `M̄(U)`, `L(U)`, and Game Two. -/
def quotient (hgr : IsGradedSubmodule N P) : OrdVModule W (M ⧸ P.carrier) where
  toWeakModule := quotientWeak N P
  weight := quotientWeight N P
  isInternal := quotientWeight_isInternal N P hgr
  L0_weight := fun α y hy => quotient_L0_weight N P α y hy
  finrank := quotientWeight_finiteDimensional N P
  boundedBelow := quotientWeight_boundedBelow N P

@[simp] theorem quotient_weight (hgr : IsGradedSubmodule N P) (α : ℂ) :
    (quotient N P hgr).weight α = (N.weight α).map P.carrier.mkQ := rfl

@[simp] theorem quotient_toWeakModule (hgr : IsGradedSubmodule N P) :
    (quotient N P hgr).toWeakModule = quotientWeak N P := rfl

/-- **The canonical projection `M ↠ M ⧸ P` as a homomorphism of graded `OrdVModule`s** (the
surjective intertwiner `mkQ`). This is the weak-module projection `quotientMk`, reused at the
graded level (the homomorphism datum is the underlying weak intertwiner). -/
def quotientMk (hgr : IsGradedSubmodule N P) :
    N.toWeakModule.Hom (quotient N P hgr).toWeakModule :=
  WeakModule.quotientMk N.toWeakModule P

@[simp] theorem quotientMk_apply (hgr : IsGradedSubmodule N P) (x : M) :
    (quotientMk N P hgr).toLinearMap x = Submodule.Quotient.mk x := rfl

/-- The graded projection is **surjective**. -/
theorem quotientMk_surjective (hgr : IsGradedSubmodule N P) :
    Function.Surjective (quotientMk N P hgr).toLinearMap :=
  P.carrier.mkQ_surjective

end OrdVModule

end VOA
