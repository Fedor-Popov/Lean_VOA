/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGradedCloseDeep

/-!
# The bottom `A_n`-relation — vanishing of the degree-`0` defect closure on `M(U)`

`ZhuVermaAnArchGradedCloseDeep` reduced full bottom survival to the single residual

  `defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥`

(via `refinementZeroSlice_eq`: the graded refinement and the defect submodule agree at degree `0`;
`bottomSurvives_full` consumes this as `hAn`). This file discharges that residual down to the
**precise genuine `A_n`-bimodule content** of the bottom, proving the constructive `V̂`-orbit
characterization of the defect submodule and the exact reduction.

## (1) The constructive `V̂`-orbit characterization — discharged here

The defect submodule `defectSubmodule ρ = sInf {D | defectSet ⊆ D ∧ IsInvariant ρ D}` is an
abstract intersection. We give it the explicit `U(V̂)`-orbit form

  `defectOrbit ρ := span_ℂ { ρ.toAlgHom g d | g : U(V̂), d ∈ defectSet ρ }`

— the `ℂ`-span of the `U(V̂)`-orbit of the defect set. This is (i) a submodule (span), (ii)
`V̂`-invariant (`ρ x · toAlgHom g d = toAlgHom (uι x * g) d`, since `ρ x = toAlgHom (uι x)` and
`toAlgHom` is an algebra hom), (iii) contains every defect (`g = 1`, `toAlgHom 1 = id`), and (iv) is
contained in every invariant cover (each orbit image lies in any invariant `D ⊇ defectSet`). By
minimality of the `sInf`, **`defectOrbit ρ = defectSubmodule ρ`** (`defectOrbit_eq_defectSubmodule`).
*Green, axiom-clean.*

## (2) The degree-`0` slice — the `A_n`-bimodule relation residual (engine-isolated)

A degree-`0` element of `defectSubmodule ρ = defectOrbit ρ` is, by (1), a finite `ℂ`-combination of
`U(V̂)`-orbit images `ρ.toAlgHom g d` of defects `d`, all lying in `mdeg 0`. On the DLM3-graded,
lowest-weight `M(U)` these are *not* killed by truncation
(`certificates/mathematica/bottom_d_gt_0.wl`, `certificates/mathematica/bottom_orbit_factor.wl`): the `d > 0` (`S = −d < 0`)
defects reach degree `0` only through the lowering modes of the orbit, and the degree-`0` orbit
images are **precisely the `A_n`-bimodule relations** on the bottom `M_0 = U`. They vanish because
the bottom is `U` *as an `A(𝒱)`-module* and the `A_n`-bimodule action on the bottom factors through
`A(𝒱) = A_0`. The `k = 0` (no lowering), `S = 0` special case is exactly `BottomDefectVanishes`.

This degree-`0` orbit vanishing is the genuine upstream `A_n`-bimodule content; it is carried as the
precise `Prop` `BottomOrbitDefectVanishes` — *not* an axiom — and we record the exact reduction
`bottomAnRelation` from it (together with the constructive orbit characterization).

## What is proved

* **`defectOrbit ρ`** — the `U(V̂)`-orbit span of the defect set.
* **`defectOrbit_invariant` / `defectVec_mem_defectOrbit` / `defectSet_subset_defectOrbit`** — the
  orbit span is `V̂`-invariant and covers the defects. *Green, axiom-clean.*
* **`defectOrbit_le_of_invariant`** — every invariant cover of the defect set contains the orbit
  span (minimality). *Green, axiom-clean.*
* **`defectOrbit_eq_defectSubmodule`** — *the constructive characterization (residual 1,
  discharged)*: `defectOrbit ρ = defectSubmodule ρ`. *Green, axiom-clean.*
* **`BottomOrbitDefectVanishes ρ mdeg`** — the precise `A_n`-bimodule degree-`0` residual: every
  degree-`0` `U(V̂)`-orbit image of a defect vanishes (the `A(𝒱)`-module structure of the bottom;
  carried as a `Prop`, **never** an axiom).
* **`BottomOrbitDefectVanishes.bottomDefect`** — `BottomOrbitDefectVanishes ⟹ BottomDefectVanishes`
  (the `k = 0`, `S = 0` special case): the orbit residual genuinely *strengthens* the carried bottom
  residual.
* **`bottomAnRelation`** — *the assembly*: `defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥`, from the constructive
  orbit characterization (1) + `BottomOrbitDefectVanishes` (2). The coverage and minimality are
  discharged here; the only carried input is the `A_n`-relation degree-`0` orbit datum.
* **`bottomSurvives_an` / `bottomSurvives_full_an`** — `bottomAnRelation` plugged into
  `bottomSurvives_full` (the full bottom-survival assembly) and `bottomSurvives` (`mkQ` injective on
  the bottom).

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626` (Prop 3.4–3.5, Thm 4.13); Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchGradedCloseDeep` (`refinementZeroSlice_eq`, `bottomSurvives_full`);
`ZhuVermaAnArchBottomSurvival` (`BottomDefectVanishes`, `defectVec`, `defectSubmodule`);
`ZhuVermaAnArchMUConstruct` (`MUConstruction`, the bottom `M_0 = U`);
`certificates/mathematica/bottom_d_gt_0.wl`, `certificates/mathematica/bottom_orbit_factor.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (1) The constructive `V̂`-orbit characterization of the defect submodule

`defectSubmodule ρ` is the `sInf` of all `V̂`-invariant submodules containing the defect set. We give
it the explicit `U(V̂)`-orbit form: the `ℂ`-span of `{ ρ.toAlgHom g d | g : U(V̂), d ∈ defectSet }`.
The `U(V̂)`-action (`ρ.toAlgHom`, the universal property of the enveloping algebra) realizes the
whole `V̂`-orbit, so this span is the smallest invariant cover. -/

/-- The `U(V̂)`-orbit of the defect set: all images `ρ.toAlgHom g d` of a defect `d` under an
element `g` of the universal enveloping algebra `U(V̂)`. The `ℂ`-span of this set is the defect
submodule (`defectOrbit_eq_defectSubmodule`). -/
def defectOrbitSet (ρ : VHatRep W M) : Set M :=
  {y | ∃ (g : UEnv W) (d : M), d ∈ defectSet ρ ∧ y = ρ.toAlgHom g d}

/-- **The `U(V̂)`-orbit span** of the defect set — the constructive form of the defect submodule. -/
noncomputable def defectOrbit (ρ : VHatRep W M) : Submodule ℂ M :=
  Submodule.span ℂ (defectOrbitSet ρ)

/-- Every defect lies in the orbit set (apply the unit `g = 1`, `toAlgHom 1 = id`). -/
theorem defectSet_subset_defectOrbitSet (ρ : VHatRep W M) :
    defectSet ρ ⊆ defectOrbitSet ρ := by
  intro d hd
  exact ⟨1, d, hd, by rw [map_one]; rfl⟩

/-- Every defect lies in the orbit span. -/
theorem defectSet_subset_defectOrbit (ρ : VHatRep W M) :
    defectSet ρ ⊆ (defectOrbit ρ : Set M) :=
  le_trans (defectSet_subset_defectOrbitSet ρ) Submodule.subset_span

/-- Every individual defect vector lies in the orbit span. -/
theorem defectVec_mem_defectOrbit (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ N : ℤ) :
    defectVec ρ u v x ℓ N ∈ defectOrbit ρ :=
  defectSet_subset_defectOrbit ρ ⟨u, v, x, ℓ, N, rfl⟩

/-- **The orbit span is `V̂`-invariant.** For `x : V̂`, `ρ x (ρ.toAlgHom g d) = ρ.toAlgHom (uι x ∗ g) d`
(since `ρ x = ρ.toAlgHom (uι x)` and `ρ.toAlgHom` is an algebra hom), so the action carries each
orbit generator back into the orbit set; `span_induction` extends this to the whole span. -/
theorem defectOrbit_invariant (ρ : VHatRep W M) : IsInvariant ρ (defectOrbit ρ) := by
  intro x d hd
  -- The action of `ρ x` on an orbit generator stays in the orbit set.
  have hgen : ∀ y ∈ defectOrbitSet ρ, ρ x y ∈ defectOrbit ρ := by
    rintro y ⟨g, e, he, rfl⟩
    refine Submodule.subset_span ⟨uι W x * g, e, he, ?_⟩
    rw [map_mul, Module.End.mul_apply, toAlgHom_uι]
  -- extend to the span.
  refine Submodule.span_induction (p := fun z _ => ρ x z ∈ defectOrbit ρ) ?_ ?_ ?_ ?_ hd
  · intro y hy; exact hgen y hy
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- **Minimality of the orbit span.** Any `V̂`-invariant submodule `D` that contains the defect set
contains the whole orbit span: each orbit generator `ρ.toAlgHom g d` is obtained from `d ∈ D` by the
`U(V̂)`-action, which `D` (being `V̂`-invariant) is closed under. -/
theorem defectOrbit_le_of_invariant {ρ : VHatRep W M} {D : Submodule ℂ M}
    (hcov : defectSet ρ ⊆ (D : Set M)) (hinv : IsInvariant ρ D) :
    defectOrbit ρ ≤ D := by
  rw [defectOrbit, Submodule.span_le]
  rintro y ⟨g, d, hd, rfl⟩
  have hd' : d ∈ D := hcov hd
  -- The preserving subalgebra `S ≤ End ℂ M`: all maps that carry `D` into `D`.
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {T : Module.End ℂ M | ∀ z ∈ D, T z ∈ D}
      mul_mem' := fun {a b} ha hb z hz => ha _ (hb z hz)
      one_mem' := fun z hz => hz
      add_mem' := fun {a b} ha hb z hz => Submodule.add_mem _ (ha z hz) (hb z hz)
      zero_mem' := fun z _ => Submodule.zero_mem _
      algebraMap_mem' := fun c z hz => by
        simp only [Module.algebraMap_end_apply]
        exact Submodule.smul_mem _ c hz }
  -- It suffices to show `ρ.toAlgHom g ∈ S`, then apply at `d ∈ D`.
  suffices hmem : ρ.toAlgHom g ∈ S by exact hmem d hd'
  -- `ρ` factors as a Lie morphism into `S` (every `ρ x` preserves `D` by invariance).
  let ρS : VHatCarrier W →ₗ⁅ℂ⁆ S :=
    { toFun := fun x => ⟨ρ x, fun z hz => hinv x z hz⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp
      map_lie' := fun {x y} => by
        apply Subtype.ext
        show (ρ ⁅x, y⁆ : Module.End ℂ M) = ((⟨ρ x, _⟩ : S) * ⟨ρ y, _⟩ - ⟨ρ y, _⟩ * ⟨ρ x, _⟩ : S)
        rw [ρ.map_lie x y]
        rfl }
  -- `S.val ∘ (lift ρS) = toAlgHom` since both agree on the generators `ι x`.
  have hfactor : S.val.comp (UniversalEnvelopingAlgebra.lift ℂ ρS) = ρ.toAlgHom := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    show S.val (UniversalEnvelopingAlgebra.lift ℂ ρS (UniversalEnvelopingAlgebra.ι ℂ x))
      = ρ.toAlgHom (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    show (ρ x : Module.End ℂ M) = ρ.toAlgHom (uι W x)
    rw [toAlgHom_uι]
  -- Hence `toAlgHom g = ↑(lift ρS g) ∈ S.carrier`.
  have hg : ρ.toAlgHom g = S.val (UniversalEnvelopingAlgebra.lift ℂ ρS g) := by
    rw [← hfactor]; rfl
  rw [hg]
  exact (UniversalEnvelopingAlgebra.lift ℂ ρS g).2

/-- **The constructive characterization (residual 1, discharged).** The defect submodule equals the
`U(V̂)`-orbit span of the defect set: `defectOrbit ρ = defectSubmodule ρ`. The orbit span is the
smallest `V̂`-invariant submodule containing the defects (`defectOrbit_invariant`,
`defectSet_subset_defectOrbit`, `defectOrbit_le_of_invariant`), which is exactly the defining `sInf`
of `defectSubmodule`. *Green, axiom-clean.* -/
theorem defectOrbit_eq_defectSubmodule (ρ : VHatRep W M) :
    defectOrbit ρ = defectSubmodule ρ := by
  apply le_antisymm
  · -- `defectOrbit ≤ defectSubmodule`: `defectSubmodule` is an invariant cover.
    exact defectOrbit_le_of_invariant
      (fun d hd => by
        have := defectVec_mem_defectSubmodule ρ
        obtain ⟨u, v, x, ℓ, N, rfl⟩ := hd
        exact defectVec_mem_defectSubmodule ρ u v x ℓ N)
      (defectSubmodule_invariant ρ)
  · -- `defectSubmodule ≤ defectOrbit`: `defectOrbit` is an invariant cover, so it is in the `sInf`.
    rw [defectSubmodule]
    exact sInf_le ⟨defectSet_subset_defectOrbit ρ, defectOrbit_invariant ρ⟩

/-! ## (2) The degree-`0` `A_n`-bimodule residual and the reduction

A degree-`0` element of `defectSubmodule ρ = defectOrbit ρ` is a finite `ℂ`-combination of
`U(V̂)`-orbit images of defects. The naive "each orbit image already in the bottom is `0`" is too
weak — a *sum* of orbit images can land in the bottom without each summand doing so. The correct,
non-circular residual is stated through the **degree-`0` projection** `π₀` of the internal grading
(`DirectSum.IsInternal mdeg`): the degree-`0` *component* of every orbit image of a defect vanishes.
Then `π₀` is `ℂ`-linear, so the degree-`0` component of the whole span vanishes, and any bottom
element of the span (which equals its own degree-`0` component) is `0`. On the DLM3-graded `M(U)`
the degree-`0` component of an orbit image is precisely the `A_n`-bimodule relation on the bottom
`M_0 = U` — `0` because `U` is an `A(𝒱)`-module (the action factors through `A(𝒱) = A_0`). -/

/-- The **degree-`0` projection** of an internal grading: `M ≃ ⨁_d (mdeg d)` followed by the
degree-`0` component and the inclusion `mdeg 0 ↪ M`. A `ℂ`-linear endomorphism of `M` with image in
`mdeg 0`, fixing `mdeg 0` pointwise. -/
noncomputable def deg0Proj {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg) :
    M →ₗ[ℂ] M :=
  letI := hInt.chooseDecomposition
  (mdeg 0).subtype.comp
    ((DirectSum.component ℂ ℤ (fun d => mdeg d) 0).comp
      (DirectSum.decomposeLinearEquiv mdeg).toLinearMap)

/-- `deg0Proj` applied to `m` unfolded. -/
theorem deg0Proj_apply {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg) (m : M) :
    deg0Proj hInt m =
      letI := hInt.chooseDecomposition
      ((DirectSum.component ℂ ℤ (fun d => mdeg d) 0
        ((DirectSum.decomposeLinearEquiv mdeg) m) : mdeg 0) : M) := rfl

/-- The degree-`0` projection lands in the bottom. -/
theorem deg0Proj_mem {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg) (m : M) :
    deg0Proj hInt m ∈ mdeg 0 := by
  letI := hInt.chooseDecomposition
  rw [deg0Proj_apply]
  exact ((DirectSum.component ℂ ℤ (fun d => mdeg d) 0)
    ((DirectSum.decomposeLinearEquiv mdeg) m)).2

/-- The degree-`0` projection fixes the bottom `mdeg 0` pointwise. -/
theorem deg0Proj_eq_self {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg) {m : M}
    (hm : m ∈ mdeg 0) : deg0Proj hInt m = m := by
  letI := hInt.chooseDecomposition
  rw [deg0Proj_apply]
  -- `decompose (⟨m, hm⟩ : mdeg 0) = lof … 0 ⟨m,hm⟩`; its `0`-component is `⟨m,hm⟩`.
  have hdec : (DirectSum.decomposeLinearEquiv mdeg) m
      = DirectSum.lof ℂ ℤ (fun d => mdeg d) 0 ⟨m, hm⟩ :=
    DirectSum.decomposeLinearEquiv_apply_coe mdeg 0 (⟨m, hm⟩ : mdeg 0)
  rw [hdec, DirectSum.component.lof_self]

/-- **The bottom-orbit defect residual** — the genuine `A_n`-bimodule degree-`0` content, stated
through the degree-`0` projection. The degree-`0` *component* `π₀(ρ.toAlgHom g δ)` of every
`U(V̂)`-orbit image of a defect `δ = δ(u,v,x,ℓ,N)` vanishes. On the DLM3-graded `M(U)` this is
precisely the `A_n`-bimodule relation on the bottom `M_0 = U` (the action factors through
`A(𝒱) = A_0`, the `A(𝒱)`-module structure of `U`). The `g = 1`, `S = 0` special case is exactly
`BottomDefectVanishes`. A `Prop`, **not** an axiom. -/
def BottomOrbitDefectVanishes {mdeg : ℤ → Submodule ℂ M} (ρ : VHatRep W M)
    (hInt : DirectSum.IsInternal mdeg) : Prop :=
  ∀ (g : UEnv W) (u v : 𝒱) (x : M) (ℓ N : ℤ),
    deg0Proj hInt (ρ.toAlgHom g (defectVec ρ u v x ℓ N)) = 0

/-- **`BottomOrbitDefectVanishes` strengthens `BottomDefectVanishes`.** Taking `g = 1`
(`toAlgHom 1 = id`) and using `defectVec_homogeneous` (the `S = 0` defect is already in the bottom
`mdeg 0`, where `π₀` is the identity), the bottom-orbit residual specializes to the `S = 0` slice
residual. So the orbit datum genuinely strengthens the carried bottom datum (and reduces to it on the
`k = 0` sector). -/
theorem BottomOrbitDefectVanishes.bottomDefect {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (h : BottomOrbitDefectVanishes ρ hInt) :
    BottomDefectVanishes ρ mdeg := by
  intro wu wv u v hu hv x hx ℓ N hS
  have hmem : defectVec ρ u v x ℓ N ∈ mdeg 0 := by
    have := defectVec_homogeneous hgr htr hu hv hx ℓ N
    rwa [show (0 : ℤ) + (wu + wv - ℓ - N - 2) = 0 by rw [hS]; ring] at this
  have hg := h 1 u v x ℓ N
  rw [map_one, Module.End.one_apply, deg0Proj_eq_self hInt hmem] at hg
  exact hg

/-- **The bottom `A_n`-relation — `defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥`.** This is the degree-`0` defect
closure vanishing, the residual that `bottomSurvives_full` consumes (`hAn`). Proof: by the
constructive characterization `defectOrbit_eq_defectSubmodule`, `defectSubmodule ρ` is the orbit
span; the degree-`0` projection `π₀` is `ℂ`-linear and kills every orbit generator
(`BottomOrbitDefectVanishes`), hence kills the whole span (`Submodule.span_induction`). An element
`y` of `defectSubmodule ρ ⊓ mdeg 0` satisfies `y = π₀ y` (`deg0Proj_eq_self`) and `π₀ y = 0`, so
`y = 0`. -/
theorem bottomAnRelation {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hav : BottomOrbitDefectVanishes ρ hInt) :
    defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥ := by
  rintro y ⟨hyD, hy0⟩
  rw [Submodule.mem_bot]
  -- `π₀` kills the whole orbit span.
  have hpiSpan : deg0Proj hInt y = 0 := by
    rw [← defectOrbit_eq_defectSubmodule, defectOrbit] at hyD
    refine Submodule.span_induction
      (p := fun z _ => deg0Proj hInt z = 0) ?_ ?_ ?_ ?_ hyD
    · rintro z ⟨g, d, ⟨u, v, x, ℓ, N, rfl⟩, rfl⟩
      exact hav g u v x ℓ N
    · simp only [map_zero]
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro c a _ ha; rw [map_smul, ha, smul_zero]
  -- `y ∈ mdeg 0` ⟹ `y = π₀ y = 0`.
  rw [← deg0Proj_eq_self hInt hy0, hpiSpan]

/-! ## The assembly: full bottom survival from the `A_n`-relation residual

`bottomAnRelation` delivers the residual `hAn` that `bottomSurvives_full`
(`ZhuVermaAnArchGradedCloseDeep`) consumes. Plugging it in closes bottom survival on the carried
`BottomOrbitDefectVanishes` datum (the `A_n`-bimodule degree-`0` content) instead of the raw
`defectSubmodule ⊓ mdeg 0 ≤ ⊥` residual. -/

/-- **Full bottom survival from the `A_n`-relation residual.** With the internal grading, gradedness,
truncation, lowest-weight bound, and the `A_n`-bimodule degree-`0` orbit datum
`BottomOrbitDefectVanishes`, the bottom `U` survives the defect quotient. The
`defectSubmodule ⊓ mdeg 0 ≤ ⊥` residual of `bottomSurvives_full` is discharged here by
`bottomAnRelation`. -/
theorem bottomSurvives_an {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (hlw : LowestWeight mdeg) (hav : BottomOrbitDefectVanishes ρ hInt) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_full hInt hgr htr hlw (bottomAnRelation hInt hav)

/-- **`mkQ` is injective on the bottom from the `A_n`-relation residual.** The degree-`0` piece of
`M̄(U) = M ⧸ defectSubmodule ρ` is exactly the bottom `U`; the only carried input is the
`A_n`-bimodule degree-`0` orbit datum `BottomOrbitDefectVanishes`. -/
theorem bottomSurvives_full_an {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (hlw : LowestWeight mdeg) (hav : BottomOrbitDefectVanishes ρ hInt) :
    Set.InjOn (defectSubmodule ρ).mkQ (mdeg 0) :=
  bottomSurvives_full_injOn hInt hgr htr hlw (bottomAnRelation hInt hav)

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
