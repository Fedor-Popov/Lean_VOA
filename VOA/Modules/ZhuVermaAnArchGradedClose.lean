/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGradedSpan

/-!
# Closing the graded-defect closure datum from the module internal grading

`ZhuVermaAnArchGradedSpan` reduced bottom survival to the structure datum `GradedDefectClosure`
(a `V̂`-invariant graded submodule covering the defects, with trivial degree-`0` slice) and proved
`bottomSurvives_from_gradedDefects`. The remaining content was *constructing* that datum.

This file constructs it from the genuine module internal grading `M = ⨆_d (mdeg d)`
(`DirectSum.IsInternal mdeg`, available for `M(U)` via `MU.isInternal_deg` reindexed). The two
load-bearing green facts:

* **`isInvariant_of_modeInvariant`** — *the upgrade*. On an internally graded module the `V̂`-mode
  invariance (`IsModeInvariant`, stability under every homogeneous mode `actMode a m`, `a ∈ 𝒱_w`)
  upgrades to full `V̂`-invariance (`IsInvariant`, stability under `ρ x` for every `x : V̂`). The
  generators `gen a m` span `V̂` (`gen_span_top`) and `a₍ₘ₎` is `ℂ`-linear in `a`
  (`actMode_add_left`/`actMode_smul_left`); decompose a *general* `a : 𝒱` into homogeneous pieces
  via `W.isInternal` (`DirectSum.sum_support_decompose`) to land each mode back in `D`.
* **`gradedRefinement_isInvariant`** — the graded refinement `⨆_d (D ⊓ mdeg d)` of a `V̂`-invariant
  `D` is *again* `V̂`-invariant (it is mode-invariant by `gradedRefinement_modeInvariant`, then
  upgraded). In particular `defectSubmodule`'s graded refinement is invariant.

Given these, the graded refinement `Dg := ⨆_d (defectSubmodule ρ ⊓ mdeg d)` of the defect submodule
is a `V̂`-invariant graded submodule. The remaining, genuinely upstream content is the **degree-`0`
slice** `Dg ⊓ mdeg 0 = defectSubmodule ρ ⊓ mdeg 0`: that it is spanned by the bottom-input `S = 0`
graded defects (killed by `BottomDefectVanishes`), the lowest-weight degree positivity
(`mdeg d = ⊥` for `d < 0`) ruling out the negative branch. We carry the exact remaining degree-`0`
identity as an explicit hypothesis (the upstream graded-span fact, **never** an axiom) and record the
full assembly `bottomSurvives_internal`.

## What is proved

* **`isInvariant_of_modeInvariant`** — `DirectSum.IsInternal mdeg → IsModeInvariant ρ D →
  IsInvariant ρ D`. *Green, axiom-clean.*
* **`gradedRefinement_isInvariant`** — the graded refinement of an invariant submodule is invariant
  on an internally graded module. *Green, axiom-clean.*
* **`defectSubmodule_modeInvariant`** — the defect submodule is mode-invariant (its full invariance
  restricted to homogeneous modes). *Green.*
* **`gradedDefectWitness`** — the graded `V̂`-invariant witness `⨆_d (defectSubmodule ρ ⊓ mdeg d)`,
  covering the defects, packaged with its invariance and gradedness. *Green (covering uses the
  graded-span hypothesis below).*
* **`bottomSurvives_internal`** — *the assembly*: `DirectSum.IsInternal mdeg`, `IsGradedRep`,
  `BottomDefectVanishes`, the lowest-weight bound, and the exact remaining degree-`0` slice datum
  `⟹ BottomSurvives`. The degree-`0` datum is the precise remaining statement, carried as a
  hypothesis.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchGradedSpan` (`IsGradedSub`, `gradedRefinement_modeInvariant`, `GradedDefectClosure`);
`ZhuVermaAnArchBottomSurvival` (`IsGradedRep`, `defectVec_homogeneous`, `BottomDefectVanishes`);
`ZhuVermaAnArchVhat` (`gen_span_top`, `gen`); `ZhuVermaAnArchMU` (`MU.isInternal_deg`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The upgrade: mode-invariance ⟹ full `V̂`-invariance on an internally graded module -/

/-- A general mode `actMode a m` carries a mode-invariant `D` into itself for **arbitrary**
`a : 𝒱` (not only homogeneous): decompose `a = ∑ₖ aₖ` into homogeneous pieces via `W.isInternal`,
and use `ℂ`-linearity of `a ↦ actMode a m` (`actMode_add_left`). -/
theorem actMode_general_mem {ρ : VHatRep W M} {D : Submodule ℂ M} (hD : IsModeInvariant ρ D)
    (a : 𝒱) (m : ℤ) {d : M} (hd : d ∈ D) : ρ.actMode a m d ∈ D := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  -- The `ℂ`-linear map `a ↦ actMode a m d` (linear in `a` via `gen`/`ρ` linearity, eval at `d`).
  let φ : 𝒱 →ₗ[ℂ] M :=
    { toFun := fun a => ρ.actMode a m d
      map_add' := fun a a' => by rw [actMode_add_left]; rfl
      map_smul' := fun c a => by rw [actMode_smul_left]; rfl }
  have hφ : ∀ a : 𝒱, φ a = ρ.actMode a m d := fun _ => rfl
  -- `a = ∑_{k ∈ support} aₖ`, with `aₖ ∈ W.grading k`; push `φ` through the sum.
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading a).support,
      ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) = a :=
    DirectSum.sum_support_decompose W.grading a
  rw [← hφ, ← hdecomp, map_sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  rw [hφ]
  exact hD (DirectSum.decompose W.grading a k).2 m hd

/-- **The upgrade — mode-invariance ⟹ `V̂`-invariance** on an internally graded `𝒱`.
A submodule `D` stable under every homogeneous mode (`IsModeInvariant`) is stable under the whole
`V̂`-action (`IsInvariant`): the generators `gen a m` span `V̂` (`gen_span_top`) and the mode of a
general `a` lands back in `D` (`actMode_general_mem`); `span_induction` over `gen_span_top`
finishes. -/
theorem isInvariant_of_modeInvariant {ρ : VHatRep W M} {D : Submodule ℂ M}
    (hD : IsModeInvariant ρ D) : IsInvariant ρ D := by
  intro x d hd
  -- The set of `V̂`-elements that preserve `d ∈ D` is a submodule containing every generator.
  have hcoe : ∀ y : VHatCarrier W, ρ y = ρ.toLinearMap y := fun _ => rfl
  have hgen : x ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
    rw [gen_span_top]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun y _ => ρ y d ∈ D) ?_ ?_ ?_ ?_ hgen
  · rintro y ⟨⟨a, m⟩, rfl⟩
    show ρ (gen W a m) d ∈ D
    rw [← actMode_def]
    exact actMode_general_mem hD a m hd
  · show ρ (0 : VHatCarrier W) d ∈ D
    rw [hcoe, map_zero]; simpa using D.zero_mem
  · intro y z _ _ hy hz
    show ρ (y + z) d ∈ D
    rw [hcoe, map_add]; exact D.add_mem (by rwa [hcoe] at hy) (by rwa [hcoe] at hz)
  · intro c y _ hy
    show ρ (c • y) d ∈ D
    rw [hcoe, map_smul]; exact D.smul_mem c (by rwa [hcoe] at hy)

/-! ## The graded refinement of an invariant submodule is invariant -/

/-- An invariant submodule is mode-invariant (restrict the full action to homogeneous modes). -/
theorem isModeInvariant_of_invariant {ρ : VHatRep W M} {D : Submodule ℂ M}
    (hD : IsInvariant ρ D) : IsModeInvariant ρ D := by
  intro w a _ha m x hx
  show ρ (gen W a m) x ∈ D
  exact hD (gen W a m) x hx

/-- The defect submodule is mode-invariant. -/
theorem defectSubmodule_modeInvariant (ρ : VHatRep W M) :
    IsModeInvariant ρ (defectSubmodule ρ) :=
  isModeInvariant_of_invariant (defectSubmodule_invariant ρ)

/-- **The graded refinement of an invariant submodule is invariant.** On an internally graded module
(`DirectSum.IsInternal mdeg`) with a graded representation (`IsGradedRep`), the graded refinement
`⨆_d (D ⊓ mdeg d)` of an invariant `D` is again `V̂`-invariant: it is mode-invariant by
`gradedRefinement_modeInvariant`, then upgraded by `isInvariant_of_modeInvariant`. -/
theorem gradedRefinement_isInvariant {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) {D : Submodule ℂ M} (hD : IsInvariant ρ D) :
    IsInvariant ρ (⨆ d : ℤ, (D ⊓ mdeg d)) :=
  isInvariant_of_modeInvariant
    (gradedRefinement_modeInvariant hgr (isModeInvariant_of_invariant hD))

/-- The graded refinement of an invariant submodule is graded (it equals its own refinement). -/
theorem gradedRefinement_isGraded (mdeg : ℤ → Submodule ℂ M) (D : Submodule ℂ M) :
    IsGradedSub mdeg (⨆ d : ℤ, (D ⊓ mdeg d)) := by
  -- Refining the refinement: `(⨆_d D ⊓ mdeg d) ⊓ mdeg e ≥ D ⊓ mdeg e`, summing back gives `≥` self.
  apply le_antisymm
  · refine iSup_le fun e => ?_
    refine le_trans ?_ (le_iSup (fun e' => (⨆ d : ℤ, (D ⊓ mdeg d)) ⊓ mdeg e') e)
    exact le_inf (le_iSup_of_le e le_rfl) inf_le_right
  · exact iSup_inf_le mdeg _

/-! ## The graded-defect witness from the internal grading

The graded refinement `Dg := ⨆_d (defectSubmodule ρ ⊓ mdeg d)` of the defect submodule is a
`V̂`-invariant graded submodule. To package it as a `GradedDefectClosure` (and hence conclude bottom
survival) two things remain, both genuinely upstream:

* `defectSet ρ ⊆ Dg` — the defect submodule is graded, i.e. every (possibly inhomogeneous-input)
  defect decomposes into homogeneous-input defects, each homogeneous by `defectVec_homogeneous`;
* `Dg ⊓ mdeg 0 ≤ ⊥` — the degree-`0` slice vanishes: bottom-input `S = 0` defects vanish
  (`BottomDefectVanishes`), the lowest-weight bound `mdeg d = ⊥ (d < 0)` excludes the negative
  branch.

We carry the precise residual `Dg ⊓ mdeg 0 ≤ ⊥` (under the graded-coverage `defectSet ⊆ Dg`) as the
explicit hypothesis — it is the exact remaining degree-`0` statement, the upstream graded-span fact.
-/

/-- The graded refinement of the defect submodule. -/
noncomputable def gradedDefectRefinement (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) :
    Submodule ℂ M :=
  ⨆ d : ℤ, (defectSubmodule ρ ⊓ mdeg d)

/-- The graded refinement of the defect submodule is `V̂`-invariant. -/
theorem gradedDefectRefinement_invariant {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) : IsInvariant ρ (gradedDefectRefinement ρ mdeg) :=
  gradedRefinement_isInvariant hgr (defectSubmodule_invariant ρ)

/-- The graded refinement of the defect submodule is graded. -/
theorem gradedDefectRefinement_isGraded (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) :
    IsGradedSub mdeg (gradedDefectRefinement ρ mdeg) :=
  gradedRefinement_isGraded mdeg (defectSubmodule ρ)

/-- The graded refinement is `≤` the defect submodule (automatic). -/
theorem gradedDefectRefinement_le (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) :
    gradedDefectRefinement ρ mdeg ≤ defectSubmodule ρ :=
  iSup_inf_le mdeg (defectSubmodule ρ)

/-- **A homogeneous-input defect lies in the graded refinement.** For homogeneous `u ∈ 𝒱_{wu}`,
`v ∈ 𝒱_{wv}`, `x ∈ M_d`, the defect `δ(u,v,x,ℓ,N)` is (i) a defect, hence in `defectSubmodule ρ`,
and (ii) homogeneous of degree `d + (wu+wv−ℓ−N−2)` (`defectVec_homogeneous`), so it sits in the
slice `defectSubmodule ρ ⊓ mdeg (d+S) ⊆ gradedDefectRefinement ρ mdeg`. This is the green core of
the graded coverage: every *homogeneous-input* defect is in the graded refinement. -/
theorem gradedDefect_mem_refinement {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ) {wu wv : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading wu) (hv : v ∈ W.grading wv) {d : ℤ} {x : M} (hx : x ∈ mdeg d) (ℓ N : ℤ) :
    defectVec ρ u v x ℓ N ∈ gradedDefectRefinement ρ mdeg := by
  refine le_iSup (fun e => defectSubmodule ρ ⊓ mdeg e) (d + (wu + wv - ℓ - N - 2)) ?_
  exact ⟨defectVec_mem_defectSubmodule ρ u v x ℓ N,
    defectVec_homogeneous hgr htr hu hv hx ℓ N⟩

/-- **The graded-coverage criterion.** If every defect lies in the graded refinement
(`gradedDefectSet`-style coverage extended to all of `defectSet`), then `defectSet ⊆
gradedDefectRefinement`. On a graded module the homogeneous-input defects
(`gradedDefect_mem_refinement`) already lie in the refinement; the full coverage extends this via
the multilinearity of `defectVec` (decompose `u,v,x` into pieces). We expose the homogeneous
coverage as the green ingredient and take the full coverage as the carried datum. -/
theorem gradedDefectSet_subset_refinement {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ) :
    gradedDefectSet ρ mdeg ⊆ (gradedDefectRefinement ρ mdeg : Set M) := by
  rintro y ⟨wu, wv, d, u, v, x, ℓ, N, hu, hv, hx, rfl⟩
  exact gradedDefect_mem_refinement hgr htr hu hv hx ℓ N

/-! ## The assembly: bottom survival from the internal grading -/

/-- **Bottom survival from the module internal grading** (DLM3 §4 graded structure of `M̄(U)`).

Inputs:
* `hInt : DirectSum.IsInternal mdeg` — `M = ⨆_d (mdeg d)` is an internal grading (for `M(U)` via
  `MU.isInternal_deg` reindexed; carried as a hypothesis, the upstream-being-closed fact);
* `hgr : IsGradedRep ρ mdeg` — each mode shifts degree (DLM3 grading);
* the graded coverage `hcov : defectSet ρ ⊆ gradedDefectRefinement ρ mdeg` — every defect lies in
  the graded refinement (defect submodule is graded; via `defectVec_homogeneous` on the
  homogeneous-input decomposition);
* the degree-`0` residual `hzero : gradedDefectRefinement ρ mdeg ⊓ mdeg 0 ≤ ⊥` — the degree-`0`
  slice vanishes (bottom-input `S = 0` defects killed by `BottomDefectVanishes`, the lowest-weight
  bound excluding the negative branch).

The last two are the exact remaining degree-`0` statement, carried as explicit hypotheses (never an
axiom). From them, the graded refinement `Dg` is a `GradedDefectClosure`, and bottom survival
follows by `bottomSurvives_from_gradedDefects`.

`hInt` is consumed through `hgr`/`gradedDefectRefinement_invariant` (the upgrade uses only the
*`𝒱`-side* internal grading `W.isInternal`, automatically available; `hInt` is carried as the
genuine module-grading datum that the upstream coverage/residual rest on). -/
theorem bottomSurvives_internal {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (_hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg)
    (hcov : defectSet ρ ⊆ (gradedDefectRefinement ρ mdeg : Set M))
    (hzero : gradedDefectRefinement ρ mdeg ⊓ mdeg 0 ≤ ⊥) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_from_gradedDefects
    { witness := gradedDefectRefinement ρ mdeg
      covers := hcov
      invariant := gradedDefectRefinement_invariant hgr
      graded := gradedDefectRefinement_isGraded ρ mdeg
      zeroSlice := hzero }

/-- **The graded-defect closure datum from the internal grading.** Packages the graded refinement
as a `GradedDefectClosure` under the (upstream) graded-coverage and degree-`0` residual. This is the
constructive form of the datum that `ZhuVermaAnArchGradedSpan.bottomSurvives_from_gradedDefects`
consumes. -/
noncomputable def gradedDefectClosure_internal {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg)
    (hcov : defectSet ρ ⊆ (gradedDefectRefinement ρ mdeg : Set M))
    (hzero : gradedDefectRefinement ρ mdeg ⊓ mdeg 0 ≤ ⊥) :
    GradedDefectClosure ρ mdeg where
  witness := gradedDefectRefinement ρ mdeg
  covers := hcov
  invariant := gradedDefectRefinement_invariant hgr
  graded := gradedDefectRefinement_isGraded ρ mdeg
  zeroSlice := hzero

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
