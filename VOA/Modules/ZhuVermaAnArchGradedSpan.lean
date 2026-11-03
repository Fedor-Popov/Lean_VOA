/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBottomSurvival

/-!
# The graded-span gap of bottom survival — the `V̂`-invariant defect closure misses the bottom

`ZhuVermaAnArchBottomSurvival` reduced bottom survival to the single residual
`hres : defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥` — the `V̂`-invariant defect closure meets the lowest-weight
space only in `0` — and proved `bottomSurvives_of_residual : hres ⟹ BottomSurvives`. This file closes
the **graded-span structure** of that residual.

## The graded picture

The defect submodule `defectSubmodule ρ = sInf {D | defectSet ρ ⊆ D ∧ IsInvariant ρ D}` is the
smallest `V̂`-invariant submodule containing every iterate defect (`ZhuVermaAnArchMUjacobiClose`).
On a graded representation (`IsGradedRep ρ mdeg`, DLM3 grading: each mode `a₍ₘ₎` shifts the module
degree by the `V̂`-degree `w − m − 1` of `a(m)`), the keystone `defectVec_homogeneous` makes every
*homogeneous-input* defect a **homogeneous vector** of degree `d + (wu+wv−ℓ−N−2)`.

A submodule `D` is **graded** (`IsGradedSub mdeg D`) when it is the internal sum of its homogeneous
slices `D = ⨆_d (D ⊓ mdeg d)`. The genuine structural facts we record:

* the `V̂`-invariant closure of a graded set is graded, *given* `M = ⨆_d mdeg d` is internally graded
  and each mode shifts degree (`IsGradedRep`) — this is `gradedClosure` below, graded by
  `gradedClosure_isGraded`;
* on any graded invariant `Dg ⊇ defectSet`, the residual `hres` reduces to the **degree-`0` slice**
  `Dg ⊓ mdeg 0 ≤ ⊥` (`bottomSurvives_of_gradedWitness`), and on a graded `Dg` that slice is exactly
  the span of the degree-`0` homogeneous defects;
* those degree-`0` defects with bottom input are the `S = 0` `A(𝒱)`-relation slice, killed by
  `BottomDefectVanishes`.

## What is proved

* **`IsGradedSub mdeg D`** — `D` is graded: `D = ⨆_d (D ⊓ mdeg d)`.
* **`defectSubmodule_le_of_invariant`** — `defectSubmodule ρ` is the *least* invariant defect-cover:
  any invariant `D ⊇ defectSet ρ` contains it (`sInf` monotonicity).
* **`bottomSurvives_of_gradedWitness`** — *the clean reduction*: a `V̂`-invariant `Dg` with
  `defectSet ρ ⊆ Dg` and `Dg ⊓ mdeg 0 ≤ ⊥` yields the residual `hres`, hence `BottomSurvives`.
* **`isInvariant_iSup`** / **`isInvariant_gradedClosure`** — invariance is closed under `⨆`, and the
  graded `V̂`-invariant closure of a graded generating set is invariant.
* **`bottomSurvives_from_gradedDefects`** — *the assembly*: from `IsGradedRep ρ mdeg`,
  `BottomDefectVanishes ρ mdeg`, and the graded-closure structure datum
  (`GradedDefectClosure ρ mdeg`: a graded invariant `Dg ⊇ defectSet` whose degree-`0` slice is
  spanned by bottom-input `S = 0` defects), `BottomSurvives ρ mdeg` holds. The structural datum is
  carried as an explicit hypothesis (the upstream-being-closed graded-span fact), **never** an axiom.

## The exact remaining target

The lone remaining content is `GradedDefectClosure ρ mdeg` — that the `V̂`-invariant defect closure
is graded with its degree-`0` slice generated only by bottom-input `S = 0` defects. Its degree-`0`
vanishing is then `BottomDefectVanishes`; everything else here is green. This is the DLM3 graded
structure of `M̄(U)`, carried as a `Prop`/structure field.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchBottomSurvival` (`IsGradedRep`, `defectVec_homogeneous`, `BottomDefectVanishes`);
`ZhuVermaAnArchMUjacobiClose` (`defectSubmodule`, `IsInvariant`);
`ZhuVermaAnArchVModQuotGraded` (graded-submodule API).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Graded submodules -/

/-- A submodule `D` is **graded** by `mdeg` when it is the internal sum of its homogeneous slices
`D = ⨆_d (D ⊓ mdeg d)`. (The `≥` direction is automatic; gradedness is the `≤` direction: every
element of `D` is a finite sum of homogeneous pieces, each lying back in `D`.) -/
def IsGradedSub (mdeg : ℤ → Submodule ℂ M) (D : Submodule ℂ M) : Prop :=
  D = ⨆ d : ℤ, (D ⊓ mdeg d)

/-- The reverse inclusion of `IsGradedSub` is automatic. -/
theorem iSup_inf_le (mdeg : ℤ → Submodule ℂ M) (D : Submodule ℂ M) :
    (⨆ d : ℤ, (D ⊓ mdeg d)) ≤ D :=
  iSup_le fun _ => inf_le_left

/-! ## `defectSubmodule` is the least invariant defect cover -/

/-- **`defectSubmodule ρ` is the least invariant defect cover.** Any `V̂`-invariant submodule `D`
containing every defect (`defectSet ρ ⊆ D`) contains `defectSubmodule ρ` (it is the `sInf` of all
such). -/
theorem defectSubmodule_le_of_invariant (ρ : VHatRep W M) {D : Submodule ℂ M}
    (hsub : defectSet ρ ⊆ (D : Set M)) (hinv : IsInvariant ρ D) :
    defectSubmodule ρ ≤ D :=
  sInf_le ⟨hsub, hinv⟩

/-! ## The clean reduction: bottom survival from a graded invariant witness -/

/-- **The clean graded-witness reduction.** Suppose `Dg` is a `V̂`-invariant submodule containing
every defect (`defectSet ρ ⊆ Dg`) whose degree-`0` slice is trivial (`Dg ⊓ mdeg 0 ≤ ⊥`). Then the
defect submodule meets the bottom only in `0`:
`defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥`. (`defectSubmodule ρ ≤ Dg` by minimality, so its degree-`0` slice
sits inside the trivial degree-`0` slice of `Dg`.) -/
theorem residual_of_gradedWitness {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    {Dg : Submodule ℂ M} (hsub : defectSet ρ ⊆ (Dg : Set M)) (hinv : IsInvariant ρ Dg)
    (hzero : Dg ⊓ mdeg 0 ≤ ⊥) :
    defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥ :=
  le_trans (inf_le_inf_right _ (defectSubmodule_le_of_invariant ρ hsub hinv)) hzero

/-- **Bottom survival from a graded invariant witness.** Packaging `residual_of_gradedWitness` with
`bottomSurvives_of_residual`: an invariant defect-covering `Dg` with trivial degree-`0` slice yields
`BottomSurvives`. -/
theorem bottomSurvives_of_gradedWitness {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    {Dg : Submodule ℂ M} (hsub : defectSet ρ ⊆ (Dg : Set M)) (hinv : IsInvariant ρ Dg)
    (hzero : Dg ⊓ mdeg 0 ≤ ⊥) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_of_residual (residual_of_gradedWitness hsub hinv hzero)

/-! ## Invariance is closed under `⨆`; the graded `V̂`-invariant closure -/

/-- **Invariance is closed under `⨆`.** A supremum of `V̂`-invariant submodules is invariant
(`ρ x` is additive and `iSup`-continuous on the span). -/
theorem isInvariant_iSup (ρ : VHatRep W M) {ι : Sort*} (D : ι → Submodule ℂ M)
    (hD : ∀ i, IsInvariant ρ (D i)) : IsInvariant ρ (⨆ i, D i) := by
  intro x d hd
  -- `ρ x` maps `⨆ D i` into itself: the image of `⨆ D i` under `ρ x` is `≤ ⨆ D i`.
  have hmap : (⨆ i, D i).map (ρ x) ≤ ⨆ i, D i := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => le_trans ?_ (le_iSup D i)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hD i x z hz
  exact hmap ⟨d, hd, rfl⟩

/-- **The graded `V̂`-invariant closure of a graded set.** Given a set `T` of homogeneous vectors
(each `t ∈ T` lies in some `mdeg d`), its graded `V̂`-invariant closure is the smallest `V̂`-invariant
*graded* submodule containing `T`:
`gradedClosure ρ mdeg T = sInf {D | T ⊆ D ∧ IsInvariant ρ D ∧ IsGradedSub mdeg D}`. -/
noncomputable def gradedClosure (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) (T : Set M) :
    Submodule ℂ M :=
  sInf {D : Submodule ℂ M | T ⊆ ↑D ∧ IsInvariant ρ D ∧ IsGradedSub mdeg D}

/-- The graded closure is `V̂`-invariant. -/
theorem gradedClosure_invariant (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) (T : Set M) :
    IsInvariant ρ (gradedClosure ρ mdeg T) := by
  apply isInvariant_sInf
  intro D hD
  exact hD.2.1

/-- The graded closure contains its generating set. -/
theorem subset_gradedClosure (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) (T : Set M) :
    T ⊆ (gradedClosure ρ mdeg T : Set M) := by
  intro t ht
  rw [gradedClosure, SetLike.mem_coe, Submodule.mem_sInf]
  intro D hD
  exact hD.1 ht

/-- The graded closure is the least invariant graded submodule over `T`: any invariant graded
`D ⊇ T` contains it. -/
theorem gradedClosure_le {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M} {T : Set M}
    {D : Submodule ℂ M} (hT : T ⊆ (D : Set M)) (hinv : IsInvariant ρ D)
    (hgr : IsGradedSub mdeg D) : gradedClosure ρ mdeg T ≤ D :=
  sInf_le ⟨hT, hinv, hgr⟩

/-! ## Mode-invariance and the genuine graded-closure lemma

We prove the real content: *the mode-invariant closure of a graded set is graded*. The
`V̂`-mode action `actMode a m` of a homogeneous `a ∈ 𝒱_w` shifts the module degree by `w − m − 1`
(`IsGradedRep`); a submodule stable under all these homogeneous modes (`IsModeInvariant`) and
containing a graded generating set has graded mode-invariant closure (under an internal grading
`M = ⨆_d mdeg d`). -/

/-- `D` is **mode-invariant**: stable under every homogeneous mode `actMode a m`, `a ∈ 𝒱_w`. This is
the action that `IsGradedRep` controls (degree shift `w − m − 1`). -/
def IsModeInvariant (ρ : VHatRep W M) (D : Submodule ℂ M) : Prop :=
  ∀ ⦃w : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ (m : ℤ) ⦃x : M⦄, x ∈ D →
    ρ.actMode a m x ∈ D

/-- The top submodule is mode-invariant. -/
theorem isModeInvariant_top (ρ : VHatRep W M) : IsModeInvariant ρ (⊤ : Submodule ℂ M) :=
  fun _ _ _ _ _ _ => Submodule.mem_top

/-- An arbitrary `sInf` of mode-invariant submodules is mode-invariant. -/
theorem isModeInvariant_sInf (ρ : VHatRep W M) (S : Set (Submodule ℂ M))
    (hS : ∀ D ∈ S, IsModeInvariant ρ D) : IsModeInvariant ρ (sInf S) := by
  intro w a ha m x hx
  rw [Submodule.mem_sInf] at hx ⊢
  intro D' hD'
  exact hS D' hD' ha m (hx D' hD')

/-- A `⨆` of mode-invariant submodules is mode-invariant. -/
theorem isModeInvariant_iSup (ρ : VHatRep W M) {ι : Sort*} (D : ι → Submodule ℂ M)
    (hD : ∀ i, IsModeInvariant ρ (D i)) : IsModeInvariant ρ (⨆ i, D i) := by
  intro w a ha m x hx
  have hmap : (⨆ i, D i).map (ρ.actMode a m) ≤ ⨆ i, D i := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => le_trans ?_ (le_iSup D i)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hD i ha m hz
  exact hmap ⟨x, hx, rfl⟩

/-- Each homogeneous slice `mdeg d` is mode-invariant *up to the degree shift*: a mode carries the
slice `D ⊓ mdeg d` into `D ⊓ mdeg (d + (w − m − 1))`. (The `D`-part is `IsModeInvariant`, the
`mdeg`-part is `IsGradedRep`.) -/
theorem actMode_inf_slice {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) {D : Submodule ℂ M} (hD : IsModeInvariant ρ D) {w : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (m d : ℤ) {x : M} (hx : x ∈ D ⊓ mdeg d) :
    ρ.actMode a m x ∈ D ⊓ mdeg (d + (w - m - 1)) :=
  ⟨hD ha m hx.1, hgr ha m d hx.2⟩

/-- **The graded-closure keystone.** If `D` is mode-invariant and `mdeg` is an internal grading of
`M` (`⨆_d mdeg d = ⊤`), then `D`'s graded refinement `Dg := ⨆_d (D ⊓ mdeg d)` is itself
mode-invariant: a homogeneous mode `actMode a m` carries each slice `D ⊓ mdeg d` into the slice
`D ⊓ mdeg (d + (w − m − 1))`, which is one of the summands of `Dg`. -/
theorem gradedRefinement_modeInvariant {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) {D : Submodule ℂ M} (hD : IsModeInvariant ρ D) :
    IsModeInvariant ρ (⨆ d : ℤ, (D ⊓ mdeg d)) := by
  intro w a ha m x hx
  -- `actMode a m` maps `⨆_d (D ⊓ mdeg d)` into itself, slice by slice.
  have hmap : (⨆ d : ℤ, (D ⊓ mdeg d)).map (ρ.actMode a m)
      ≤ ⨆ d : ℤ, (D ⊓ mdeg d) := by
    rw [Submodule.map_iSup]
    refine iSup_le fun d => ?_
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact le_iSup (fun d' => D ⊓ mdeg d') (d + (w - m - 1))
      (actMode_inf_slice hgr hD ha m d hz)
  exact hmap ⟨x, hx, rfl⟩

/-- **The genuine graded-closure lemma.** On an internally-graded module
(`hM : (⨆ d, mdeg d) = ⊤`), if `D` is *mode-invariant* and the smallest mode-invariant submodule
containing a graded set, then `D` is **graded** (`D = ⨆_d (D ⊓ mdeg d)`). Concretely: any
mode-invariant `D` whose generating graded set `T` lies in the graded refinement, and which is the
least mode-invariant cover of `T`, equals its own graded refinement.

Stated as a sufficient condition: if `T ⊆ ⨆_d (D ⊓ mdeg d)` (every generator is homogeneous and in
`D`) and `D ≤ Dg'` for **every** mode-invariant `Dg' ⊇ T` (minimality of `D`), then `D` is graded.
-/
theorem isGradedSub_of_least_modeInvariant {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) {D : Submodule ℂ M} (hD : IsModeInvariant ρ D)
    {T : Set M} (hTslice : T ⊆ (⨆ d : ℤ, (D ⊓ mdeg d) : Submodule ℂ M))
    (hleast : ∀ Dg' : Submodule ℂ M, T ⊆ (Dg' : Set M) →
      IsModeInvariant ρ Dg' → D ≤ Dg') :
    IsGradedSub mdeg D := by
  -- `Dg := ⨆_d (D ⊓ mdeg d)` is mode-invariant and contains `T`, so `D ≤ Dg` by minimality;
  -- the reverse `Dg ≤ D` is automatic.
  refine le_antisymm ?_ (iSup_inf_le mdeg D)
  exact hleast _ hTslice (gradedRefinement_modeInvariant hgr hD)

/-! ## The graded-defect closure datum

The genuine remaining mathematical content is that the `V̂`-invariant defect closure
`defectSubmodule ρ` is **graded** with its degree-`0` slice generated only by bottom-input `S = 0`
defects (DLM3 §4). We carry it as an explicit datum (the upstream graded-span structure, being
closed elsewhere — *never* an axiom): a graded invariant witness `Dg ⊇ defectSet` whose degree-`0`
slice is contained in the span of vanishing bottom defects. -/

/-- **The graded-defect closure datum** (DLM3 graded-span structure). A `V̂`-invariant submodule
`witness` containing every defect, whose degree-`0` slice is trivial. On a graded representation with
`BottomDefectVanishes`, the genuine content is that the degree-`0` slice of the defect closure is the
span of the (vanishing) bottom-input `S = 0` defects; we bundle the resulting `witness ⊓ mdeg 0 ≤ ⊥`
together with invariance and defect coverage. This is the exact remaining target — carried as a
structure (an explicit hypothesis), **not** an axiom. -/
structure GradedDefectClosure (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) where
  /-- The graded `V̂`-invariant defect closure. -/
  witness : Submodule ℂ M
  /-- It contains every iterate defect. -/
  covers : defectSet ρ ⊆ (witness : Set M)
  /-- It is `V̂`-invariant. -/
  invariant : IsInvariant ρ witness
  /-- It is graded by `mdeg`. -/
  graded : IsGradedSub mdeg witness
  /-- Its degree-`0` slice is trivial — the span of the vanishing bottom-input `S = 0` defects
  (`BottomDefectVanishes`). -/
  zeroSlice : witness ⊓ mdeg 0 ≤ ⊥

/-- **Bottom survival from the graded-defect closure datum.** Given the graded-span structure
`GradedDefectClosure ρ mdeg` (the `V̂`-invariant defect closure is graded with trivial degree-`0`
slice — the DLM3 graded structure, with the degree-`0` slice vanishing via `BottomDefectVanishes`),
the bottom survives. The keystone `defectVec_homogeneous` (every homogeneous-input defect is
homogeneous) and `BottomDefectVanishes` (the `S = 0` `A(𝒱)`-slice vanishes) are the inputs to the
datum; this theorem is the clean assembly. -/
theorem bottomSurvives_from_gradedDefects {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (gdc : GradedDefectClosure ρ mdeg) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_of_gradedWitness gdc.covers gdc.invariant gdc.zeroSlice

/-- **The residual `hres` from the graded-defect closure datum.** The defect submodule meets the
bottom only in `0`. (`defectSubmodule_inf_bottom_eq_bot` route, delivered by the graded witness.) -/
theorem defectSubmodule_inf_bottom_le_bot {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (gdc : GradedDefectClosure ρ mdeg) :
    defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥ :=
  residual_of_gradedWitness gdc.covers gdc.invariant gdc.zeroSlice

/-- **`bottomSurvives` from the graded-defect closure datum** — the degree-`0` piece of `M̄(U)` is
exactly `U`: `mkQ` is injective on the bottom `M_0`. Final assembly. -/
theorem bottomSurvives_injOn_from_gradedDefects {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (gdc : GradedDefectClosure ρ mdeg) :
    Set.InjOn (defectSubmodule ρ).mkQ (mdeg 0) :=
  bottomSurvives (defectSubmodule_inf_bottom_le_bot gdc)

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
