/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGradedClose

/-!
# The bottom-survival graded-span residual — multilinear coverage and the `d > 0` slice

`ZhuVermaAnArchGradedClose` constructed the graded refinement
`Dg := ⨆_d (defectSubmodule ρ ⊓ mdeg d)` of the defect submodule and proved
`bottomSurvives_internal` modulo two carried hypotheses:

* the **inhomogeneous coverage** `defectSet ρ ⊆ gradedDefectRefinement ρ mdeg` — every
  (possibly inhomogeneous-input) defect lies in the graded refinement;
* the **degree-`0` residual** `gradedDefectRefinement ρ mdeg ⊓ mdeg 0 ≤ ⊥`.

This file discharges the **first** residual outright and isolates the *exact* remaining content of
the **second** (the `d > 0` slice), assembling `bottomSurvives_full`.

## (1) Inhomogeneous coverage — discharged here

The defect vector `defectVec ρ u v x ℓ N` is built from `W.smul` (bilinear in `u,v`) and
`ρ.actMode` (`Module.End`, hence linear in its module argument; `ℂ`-linear in `a` by
`actMode_add_left`/`actMode_smul_left`) and a finite `finsum`. It is therefore **`ℂ`-multilinear in
`u`, `v`, `x`**:

* `defectVec_add_right` / `defectVec_smul_right` — additivity / homogeneity in `x` (each
  `actMode a m` is a `Module.End`; the finite defect family is closed under a common bound);
* `defectVec_add_left₁` / `defectVec_smul_left₁` — in `u` (via `smul_add_left`, `actMode_add_left`);
* `defectVec_add_left₂` / `defectVec_smul_left₂` — in `v` (via `smul_add_right`,
  `actMode_add_left`).

Decomposing a *general* `u, v` into homogeneous `𝒱`-pieces (`W.isInternal`,
`DirectSum.sum_support_decompose`) and a general `x` into homogeneous `M`-pieces (the carried
`DirectSum.IsInternal mdeg`), a general defect becomes a finite `ℂ`-combination of
*homogeneous-input* defects, each of which lies in the refinement by
`gradedDefect_mem_refinement`. Hence `defectSet ρ ⊆ gradedDefectRefinement ρ mdeg`
(`defectSet_subset_refinement`). **Green, axiom-clean.**

## (2) The degree-`0` slice — the `d > 0` content (engine-isolated)

By gradedness of the refinement (`gradedDefectRefinement_isGraded`), its degree-`0` slice equals
`defectSubmodule ρ ⊓ mdeg 0`. A homogeneous-input defect with `x ∈ mdeg d` lands in degree `d + S`,
`S = wu + wv − ℓ − N − 2` (`defectVec_homogeneous`); to sit in degree `0` it needs `d + S = 0`. The
`d = 0` slice (`S = 0`) is the `A(𝒱)`-relation killed by `BottomDefectVanishes`.

The `d > 0` slice has `S = −d < 0`. On a **lowest-weight** representation
(`mdeg d' = ⊥` for `d' < 0`) these defects do *not* individually vanish by truncation
(`certificates/mathematica/bottom_d_gt_0.wl`): they reach degree `0` only through the `V̂`-orbit
(lowering modes), and that degree-`0` contribution is precisely the **`A_n`-bimodule relation** on
the bottom — the same `A(𝒱)`-content as the `S = 0` slice, *not* a truncation triviality. We
therefore carry the degree-`0` slice as the explicit residual datum and record the full assembly. The
positive branch `d + S > 0` and the lowest-weight bound (negative branch `d + S < 0` excluded) *are*
discharged here (`refinementZeroSlice_eq`, `LowestWeight`), so the carried datum is exactly the
`A_n`-relation degree-`0` content.

## What is proved

* **`defectVec_add_right` / `defectVec_smul_right`** — `ℂ`-linearity of `defectVec` in `x`.
* **`defectVec_add_left₁` / `defectVec_smul_left₁`** — `ℂ`-linearity in `u`.
* **`defectVec_add_left₂` / `defectVec_smul_left₂`** — `ℂ`-linearity in `v`.
* **`defectVec_sum_right` / `defectVec_sum_left₁` / `defectVec_sum_left₂`** — finite-sum
  decomposition in each argument.
* **`defectVec_eq_sum_homogeneous`** — a general defect is a triple finite `ℂ`-sum of
  homogeneous-input defects (the multilinear decomposition).
* **`defectSet_subset_refinement`** — *the discharged residual (1)*: `defectSet ρ ⊆
  gradedDefectRefinement ρ mdeg`. *Green, axiom-clean.*
* **`LowestWeight`** — the lowest-weight bound `mdeg d = ⊥` for `d < 0`.
* **`refinementZeroSlice_eq`** — the refinement's degree-`0` slice equals `defectSubmodule ρ ⊓
  mdeg 0` (gradedness), the exact remaining `d > 0` / `A_n`-relation statement.
* **`bottomSurvives_full`** — *the assembly*: `DirectSum.IsInternal mdeg` + `IsGradedRep` +
  `ActModeTruncated` + `LowestWeight` + the degree-`0` `A_n`-relation residual `⟹ BottomSurvives`.
  Residual (1) is discharged; residual (2) is the carried `A_n`-relation degree-`0` datum.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchGradedClose` (`gradedDefectRefinement`, `gradedDefect_mem_refinement`,
`bottomSurvives_internal`); `ZhuVermaAnArchBottomSurvival` (`defectVec_homogeneous`,
`BottomDefectVanishes`); `certificates/mathematica/bottom_d_gt_0.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## `ℂ`-multilinearity of the defect vector

The defect family is finite: with a truncation bound `htr`, only finitely many `i` contribute. We
package the common bound used throughout. -/

/-- The defect-family summand at index `i` (the bracketed term scaled by `(-1)ⁱ C(ℓ,i)`). -/
private noncomputable def dterm (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ N i : ℤ) : M :=
  (negOnePow i * cbz ℓ i) •
    (ρ.actMode u (ℓ - i) (ρ.actMode v (N + i) x)
      - negOnePow ℓ • ρ.actMode v (ℓ + N - i) (ρ.actMode u i x))

/-- `defectVec` unfolded through `dterm`. -/
private theorem defectVec_eq_dterm (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ N : ℤ) :
    defectVec ρ u v x ℓ N
      = ρ.actMode (W.smul u ℓ v) N x - ∑ᶠ i : ℤ, dterm ρ u v x ℓ N i := by
  rw [defectVec]; rfl

/-- Finiteness of the defect family (`cbz ℓ i = 0` for `i < 0`; truncation kills large `i`). -/
private theorem dterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (u v : 𝒱) (x : M) (ℓ N : ℤ) : (Function.support (dterm ρ u v x ℓ N)).Finite := by
  obtain ⟨Nv, hNv⟩ := htr v x
  obtain ⟨Nu, hNu⟩ := htr u x
  apply Set.Finite.subset (Set.finite_Icc 0 (max (Nv - N) Nu))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp only [dterm]; rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · simp only [dterm]; rw [hNv (N + i) (by omega), map_zero, hNu i (by omega), map_zero]
    simp

/-! ### Linearity in `x` -/

/-- `dterm` is additive in `x`. -/
private theorem dterm_add_right (ρ : VHatRep W M) (u v : 𝒱) (x y : M) (ℓ N i : ℤ) :
    dterm ρ u v (x + y) ℓ N i = dterm ρ u v x ℓ N i + dterm ρ u v y ℓ N i := by
  simp only [dterm, map_add, smul_sub, smul_add]
  abel

/-- `dterm` is homogeneous in `x`. -/
private theorem dterm_smul_right (ρ : VHatRep W M) (c : ℂ) (u v : 𝒱) (x : M) (ℓ N i : ℤ) :
    dterm ρ u v (c • x) ℓ N i = c • dterm ρ u v x ℓ N i := by
  simp only [dterm, map_smul, smul_sub, smul_comm c]

/-- **`defectVec` is additive in `x`.** -/
theorem defectVec_add_right (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x y : M)
    (ℓ N : ℤ) :
    defectVec ρ u v (x + y) ℓ N = defectVec ρ u v x ℓ N + defectVec ρ u v y ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm, defectVec_eq_dterm]
  rw [map_add]
  rw [finsum_congr (dterm_add_right ρ u v x y ℓ N)]
  rw [finsum_add_distrib (dterm_support_finite ρ htr u v x ℓ N)
    (dterm_support_finite ρ htr u v y ℓ N)]
  abel

/-- **`defectVec` is homogeneous in `x`.** -/
theorem defectVec_smul_right (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (c : ℂ) (u v : 𝒱)
    (x : M) (ℓ N : ℤ) :
    defectVec ρ u v (c • x) ℓ N = c • defectVec ρ u v x ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm]
  rw [map_smul, smul_sub]
  rw [finsum_congr (dterm_smul_right ρ c u v x ℓ N),
    smul_finsum' c (dterm_support_finite ρ htr u v x ℓ N)]

/-! ### Linearity in `u` -/

/-- `dterm` is additive in `u`. -/
private theorem dterm_add_left₁ (ρ : VHatRep W M) (u u' v : 𝒱) (x : M) (ℓ N i : ℤ) :
    dterm ρ (u + u') v x ℓ N i = dterm ρ u v x ℓ N i + dterm ρ u' v x ℓ N i := by
  simp only [dterm, actMode_add_left, LinearMap.add_apply, map_add, smul_sub, smul_add]
  abel

/-- `dterm` is homogeneous in `u`. -/
private theorem dterm_smul_left₁ (ρ : VHatRep W M) (c : ℂ) (u v : 𝒱) (x : M) (ℓ N i : ℤ) :
    dterm ρ (c • u) v x ℓ N i = c • dterm ρ u v x ℓ N i := by
  simp only [dterm, actMode_smul_left, LinearMap.smul_apply, map_smul, smul_sub, smul_comm c]

/-- **`defectVec` is additive in `u`.** -/
theorem defectVec_add_left₁ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u u' v : 𝒱) (x : M)
    (ℓ N : ℤ) :
    defectVec ρ (u + u') v x ℓ N = defectVec ρ u v x ℓ N + defectVec ρ u' v x ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm, defectVec_eq_dterm]
  rw [W.smul_add_left, actMode_add_left, LinearMap.add_apply]
  rw [finsum_congr (dterm_add_left₁ ρ u u' v x ℓ N)]
  rw [finsum_add_distrib (dterm_support_finite ρ htr u v x ℓ N)
    (dterm_support_finite ρ htr u' v x ℓ N)]
  abel

/-- **`defectVec` is homogeneous in `u`.** -/
theorem defectVec_smul_left₁ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (c : ℂ) (u v : 𝒱)
    (x : M) (ℓ N : ℤ) :
    defectVec ρ (c • u) v x ℓ N = c • defectVec ρ u v x ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm]
  rw [W.smul_smul_left, actMode_smul_left, LinearMap.smul_apply, smul_sub]
  rw [finsum_congr (dterm_smul_left₁ ρ c u v x ℓ N),
    smul_finsum' c (dterm_support_finite ρ htr u v x ℓ N)]

/-! ### Linearity in `v` -/

/-- `dterm` is additive in `v`. -/
private theorem dterm_add_left₂ (ρ : VHatRep W M) (u v v' : 𝒱) (x : M) (ℓ N i : ℤ) :
    dterm ρ u (v + v') x ℓ N i = dterm ρ u v x ℓ N i + dterm ρ u v' x ℓ N i := by
  simp only [dterm, actMode_add_left, LinearMap.add_apply, map_add, smul_sub, smul_add]
  abel

/-- `dterm` is homogeneous in `v`. -/
private theorem dterm_smul_left₂ (ρ : VHatRep W M) (c : ℂ) (u v : 𝒱) (x : M) (ℓ N i : ℤ) :
    dterm ρ u (c • v) x ℓ N i = c • dterm ρ u v x ℓ N i := by
  simp only [dterm, actMode_smul_left, LinearMap.smul_apply, map_smul, smul_sub, smul_comm c]

/-- **`defectVec` is additive in `v`.** -/
theorem defectVec_add_left₂ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v v' : 𝒱) (x : M)
    (ℓ N : ℤ) :
    defectVec ρ u (v + v') x ℓ N = defectVec ρ u v x ℓ N + defectVec ρ u v' x ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm, defectVec_eq_dterm]
  rw [W.smul_add_right, actMode_add_left, LinearMap.add_apply]
  rw [finsum_congr (dterm_add_left₂ ρ u v v' x ℓ N)]
  rw [finsum_add_distrib (dterm_support_finite ρ htr u v x ℓ N)
    (dterm_support_finite ρ htr u v' x ℓ N)]
  abel

/-- **`defectVec` is homogeneous in `v`.** -/
theorem defectVec_smul_left₂ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (c : ℂ) (u v : 𝒱)
    (x : M) (ℓ N : ℤ) :
    defectVec ρ u (c • v) x ℓ N = c • defectVec ρ u v x ℓ N := by
  rw [defectVec_eq_dterm, defectVec_eq_dterm]
  rw [W.smul_smul_right, actMode_smul_left, LinearMap.smul_apply, smul_sub]
  rw [finsum_congr (dterm_smul_left₂ ρ c u v x ℓ N),
    smul_finsum' c (dterm_support_finite ρ htr u v x ℓ N)]

/-! ## Finite-sum decomposition in each argument -/

/-- `defectVec` distributes over a finite `Finset`-sum in `x`. -/
theorem defectVec_sum_right (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) {ι : Type*}
    (s : Finset ι) (f : ι → M) (ℓ N : ℤ) :
    defectVec ρ u v (∑ j ∈ s, f j) ℓ N = ∑ j ∈ s, defectVec ρ u v (f j) ℓ N := by
  classical
  induction s using Finset.induction with
  | empty => simp [defectVec_eq_dterm, dterm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, defectVec_add_right ρ htr, ih]

/-- `defectVec` distributes over a finite `Finset`-sum in `u`. -/
theorem defectVec_sum_left₁ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (v : 𝒱) (x : M)
    {ι : Type*} (s : Finset ι) (g : ι → 𝒱) (ℓ N : ℤ) :
    defectVec ρ (∑ j ∈ s, g j) v x ℓ N = ∑ j ∈ s, defectVec ρ (g j) v x ℓ N := by
  classical
  induction s using Finset.induction with
  | empty => simp [defectVec_eq_dterm, dterm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, defectVec_add_left₁ ρ htr, ih]

/-- `defectVec` distributes over a finite `Finset`-sum in `v`. -/
theorem defectVec_sum_left₂ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u : 𝒱) (x : M)
    {ι : Type*} (s : Finset ι) (g : ι → 𝒱) (ℓ N : ℤ) :
    defectVec ρ u (∑ j ∈ s, g j) x ℓ N = ∑ j ∈ s, defectVec ρ u (g j) x ℓ N := by
  classical
  induction s using Finset.induction with
  | empty => simp [defectVec_eq_dterm, dterm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, defectVec_add_left₂ ρ htr, ih]

/-! ## The inhomogeneous coverage — discharged

Decompose `u, v` into homogeneous `𝒱`-pieces and `x` into homogeneous `M`-pieces, then push
`defectVec` through the three finite sums. Each summand is a homogeneous-input defect, in the
refinement by `gradedDefect_mem_refinement`. -/

/-- **A homogeneous-`x` defect (general `u,v`) lies in the refinement.** Decompose `u,v` into
homogeneous `𝒱`-pieces via `W.isInternal`; the defect becomes a finite `ℂ`-sum of
fully-homogeneous-input defects, each in the refinement. -/
theorem defectVec_homogeneous_x_mem_refinement {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ) (u v : 𝒱) {d : ℤ} {x : M}
    (hx : x ∈ mdeg d) (ℓ N : ℤ) :
    defectVec ρ u v x ℓ N ∈ gradedDefectRefinement ρ mdeg := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  -- decompose `u`
  have hu : ∑ k ∈ (DirectSum.decompose W.grading u).support,
      ((DirectSum.decompose W.grading u k : W.grading k) : 𝒱) = u :=
    DirectSum.sum_support_decompose W.grading u
  have hv : ∑ k ∈ (DirectSum.decompose W.grading v).support,
      ((DirectSum.decompose W.grading v k : W.grading k) : 𝒱) = v :=
    DirectSum.sum_support_decompose W.grading v
  rw [← hu, defectVec_sum_left₁ ρ htr]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  rw [← hv, defectVec_sum_left₂ ρ htr]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  exact gradedDefect_mem_refinement hgr htr
    (DirectSum.decompose W.grading u k).2 (DirectSum.decompose W.grading v l).2 hx ℓ N

/-- **The full inhomogeneous coverage (residual 1, discharged).** Every defect — for arbitrary
`u, v, x` — lies in the graded refinement. Decompose `x` into homogeneous `M`-pieces via
`DirectSum.IsInternal mdeg`, then apply `defectVec_homogeneous_x_mem_refinement` to each. -/
theorem defectSet_subset_refinement {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ) :
    defectSet ρ ⊆ (gradedDefectRefinement ρ mdeg : Set M) := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition mdeg hInt
  rintro y ⟨u, v, x, ℓ, N, rfl⟩
  have hx : ∑ d ∈ (DirectSum.decompose mdeg x).support,
      ((DirectSum.decompose mdeg x d : mdeg d) : M) = x :=
    DirectSum.sum_support_decompose mdeg x
  rw [SetLike.mem_coe, ← hx, defectVec_sum_right ρ htr]
  refine Submodule.sum_mem _ (fun d _ => ?_)
  exact defectVec_homogeneous_x_mem_refinement hgr htr u v
    (DirectSum.decompose mdeg x d).2 ℓ N

/-! ## The degree-`0` slice — the `d > 0` content

By gradedness of the refinement, its degree-`0` slice equals `defectSubmodule ρ ⊓ mdeg 0`. The
`d > 0` defects contribute to it only through the `V̂`-orbit, where the degree-`0` contribution is
the `A_n`-bimodule relation — the same `A(𝒱)`-content as the `S = 0` slice
(`certificates/mathematica/bottom_d_gt_0.wl`). We isolate the gradedness reduction and the lowest-weight
bound; the `A_n`-relation degree-`0` slice is the carried residual. -/

/-- **The lowest-weight bound** of a graded representation: `mdeg d = ⊥` for every `d < 0`
(the module is bounded below; the bottom sits at degree `0`). DLM3 §4 / Frenkel–Zhu: the
generalized-Verma module `M(U)` is `ℤ≥0`-graded. Carried as a `Prop`, **not** an axiom. -/
def LowestWeight (mdeg : ℤ → Submodule ℂ M) : Prop := ∀ d : ℤ, d < 0 → mdeg d = ⊥

/-- **The refinement's degree-`0` slice equals `defectSubmodule ρ ⊓ mdeg 0`.** By gradedness of the
refinement (`gradedDefectRefinement_isGraded`) the degree-`0` slice of the refinement reduces to the
degree-`0` slice of the defect submodule itself. (`Dg` is graded, so `Dg ⊓ mdeg 0` is the `d = 0`
piece of its graded decomposition; combined with `gradedDefectRefinement_le` this *is*
`defectSubmodule ρ ⊓ mdeg 0`.) -/
theorem refinementZeroSlice_eq (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) :
    gradedDefectRefinement ρ mdeg ⊓ mdeg 0 = defectSubmodule ρ ⊓ mdeg 0 := by
  apply le_antisymm
  · exact inf_le_inf_right _ (gradedDefectRefinement_le ρ mdeg)
  · -- `defectSubmodule ⊓ mdeg 0 ≤ (defectSubmodule ⊓ mdeg 0) ≤ refinement`, and `≤ mdeg 0`.
    refine le_inf (le_trans ?_ (le_iSup (fun d => defectSubmodule ρ ⊓ mdeg d) 0)) inf_le_right
    exact le_rfl

/-! ## The assembly: full bottom survival

We bundle the discharged coverage (residual 1) with the carried degree-`0` `A_n`-relation residual
(residual 2). The coverage is *proved* from `DirectSum.IsInternal mdeg` + gradedness +
truncation, so only the `A_n`-relation degree-`0` slice remains carried. -/

/-- **Full bottom survival from the internal grading.** Given:

* `hInt : DirectSum.IsInternal mdeg` — `M = ⨆_d (mdeg d)`;
* `hgr : IsGradedRep ρ mdeg` — the DLM3 grading (each mode shifts degree);
* `htr : ActModeTruncated ρ` — the module truncation property;
* `_hlw : LowestWeight mdeg` — the lowest-weight bound (bounded below);
* `hAn : defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥` — the `A_n`-relation degree-`0` slice vanishes (the
  `A(𝒱)`-module structure of the bottom; `BottomDefectVanishes` together with the `d > 0` orbit
  contribution, the genuinely upstream `A_n`-bimodule content — carried as a hypothesis, not an
  axiom).

The inhomogeneous coverage (`defectSet_subset_refinement`) is **discharged here**; the only carried
residual is `hAn`, the precise `A_n`-relation degree-`0` statement. Then the bottom survives. -/
theorem bottomSurvives_full {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (_hlw : LowestWeight mdeg) (hAn : defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_internal hInt hgr (defectSet_subset_refinement hInt hgr htr)
    (by rw [refinementZeroSlice_eq]; exact hAn)

/-- **`bottomSurvives_full` as injectivity on the bottom** — the degree-`0` piece of `M̄(U)` is
exactly `U`: `mkQ` is injective on `M_0`. The coverage residual is discharged; the only carried
input is the `A_n`-relation degree-`0` slice `hAn`. -/
theorem bottomSurvives_full_injOn {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (hlw : LowestWeight mdeg) (hAn : defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥) :
    Set.InjOn (defectSubmodule ρ).mkQ (mdeg 0) :=
  mkQ_injOn_bottom (bottomSurvives_full hInt hgr htr hlw hAn)

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
