/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.BilinearForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Graded Riesz representation on a VOA  (Moonshine step M8c, `W̄` part 1)

For a VOA `𝒱 = ⊕ₖ 𝒱ₖ` (finite-dimensional pieces) and a bilinear form `B` on `𝒱` that is
nondegenerate on every `𝒱ₖ`, a linear functional `f : 𝒱 → ℂ` that is nonzero on only finitely
many `𝒱ₖ` is represented by a unique vector `riesz B f ∈ 𝒱`: `B (riesz B f) φ = f φ`.
This is how the adjoint `W̄` of the skew intertwiner is turned from a functional into a vector
(`Moonshine.WbarDef`).

* `gradForm B k` — `B` restricted to `𝒱ₖ × 𝒱ₖ`; `GradedNondeg B` — each is nondegenerate;
  `GradedOrth B` — distinct `𝒱ₖ` are orthogonal.
* `rk B k : Dual(𝒱ₖ) →ₗ 𝒱` — the inverse of `x ↦ B(x,·)` on `𝒱ₖ` (zero if degenerate).
* `riesz B f := ∑ᶠ k, rk B k (f|_{𝒱ₖ})`.
* `riesz_spec` — `B (riesz B f) φ = f φ` (finite graded support, `GradedOrth`, `GradedNondeg`).
* `riesz_add`, `riesz_smul`, `riesz_zero` — linearity on finitely supported functionals
  (no hypothesis on `B`).
* `riesz_mem` — if `f` lives on `𝒱ₖ` only, `riesz B f ∈ 𝒱ₖ` (no hypothesis on `B`).
* `eq_zero_of_form` / `eq_of_form` — separation: `B x = 0 → x = 0`.
* `gradedNondeg_of_radical` — from `leftRadical = ⊥` of an `InvariantForm`.

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (the hypotheses are displayed).
-/

namespace VOA.Moonshine.SkewAdjoint

open Module (Dual)
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `B` restricted to the weight space `𝒱ₖ`. -/
noncomputable def gradForm (W : VertexOperatorAlgebra 𝒱) (B : LinearMap.BilinForm ℂ 𝒱) (k : ℤ) :
    LinearMap.BilinForm ℂ (W.grading k) :=
  B.compl₁₂ (W.grading k).subtype (W.grading k).subtype

/-- `B` is nondegenerate on every weight space. -/
def GradedNondeg (W : VertexOperatorAlgebra 𝒱) (B : LinearMap.BilinForm ℂ 𝒱) : Prop :=
  ∀ k : ℤ, (gradForm W B k).Nondegenerate

/-- Distinct weight spaces are `B`-orthogonal. -/
def GradedOrth (W : VertexOperatorAlgebra 𝒱) (B : LinearMap.BilinForm ℂ 𝒱) : Prop :=
  ∀ m n : ℤ, m ≠ n → ∀ x ∈ W.grading m, ∀ y ∈ W.grading n, B x y = 0

open Classical in
/-- The inverse of `x ↦ B(x, ·)` on `𝒱ₖ`, composed with the inclusion (zero if `B|𝒱ₖ` is
degenerate). -/
noncomputable def rk (W : VertexOperatorAlgebra 𝒱) (B : LinearMap.BilinForm ℂ 𝒱) (k : ℤ) :
    Dual ℂ (W.grading k) →ₗ[ℂ] 𝒱 :=
  haveI := W.finrank k
  if h : (gradForm W B k).Nondegenerate then
    (W.grading k).subtype ∘ₗ ((gradForm W B k).toDual h).symm.toLinearMap
  else 0

theorem rk_mem (B : LinearMap.BilinForm ℂ 𝒱) (k : ℤ) (g : Dual ℂ (W.grading k)) :
    rk W B k g ∈ W.grading k := by
  classical
  unfold rk
  split_ifs with h
  · exact Submodule.coe_mem _
  · exact Submodule.zero_mem _

theorem form_rk {B : LinearMap.BilinForm ℂ 𝒱} (hnd : GradedNondeg W B) (k : ℤ)
    (g : Dual ℂ (W.grading k)) {y : 𝒱} (hy : y ∈ W.grading k) :
    B (rk W B k g) y = g ⟨y, hy⟩ := by
  classical
  haveI := W.finrank k
  unfold rk
  rw [dif_pos (hnd k)]
  have := LinearMap.BilinForm.apply_toDual_symm_apply (B := gradForm W B k) (hB := hnd k) g
    ⟨y, hy⟩
  exact this

/-- Restriction of a functional to `𝒱ₖ`. -/
noncomputable def restr (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (f : 𝒱 →ₗ[ℂ] ℂ) :
    Dual ℂ (W.grading k) :=
  f ∘ₗ (W.grading k).subtype

theorem restr_add (k : ℤ) (f g : 𝒱 →ₗ[ℂ] ℂ) : restr W k (f + g) = restr W k f + restr W k g :=
  LinearMap.add_comp _ _ _

theorem restr_smul (k : ℤ) (c : ℂ) (f : 𝒱 →ₗ[ℂ] ℂ) : restr W k (c • f) = c • restr W k f :=
  LinearMap.smul_comp _ _ _

/-- The graded support of a functional. -/
def gsupp (W : VertexOperatorAlgebra 𝒱) (f : 𝒱 →ₗ[ℂ] ℂ) : Set ℤ := {k | restr W k f ≠ 0}

/-- **The graded Riesz vector** of a functional. -/
noncomputable def riesz (W : VertexOperatorAlgebra 𝒱) (B : LinearMap.BilinForm ℂ 𝒱)
    (f : 𝒱 →ₗ[ℂ] ℂ) : 𝒱 :=
  ∑ᶠ k : ℤ, rk W B k (restr W k f)

theorem support_rk_subset (B : LinearMap.BilinForm ℂ 𝒱) (f : 𝒱 →ₗ[ℂ] ℂ) :
    (Function.support fun k => rk W B k (restr W k f)) ⊆ gsupp W f := by
  intro k hk h
  apply hk
  change rk W B k (restr W k f) = 0
  have h' : restr W k f = 0 := by simpa [gsupp] using h
  rw [h', map_zero]

theorem riesz_add (B : LinearMap.BilinForm ℂ 𝒱) {f g : 𝒱 →ₗ[ℂ] ℂ} (hf : (gsupp W f).Finite)
    (hg : (gsupp W g).Finite) : riesz W B (f + g) = riesz W B f + riesz W B g := by
  unfold riesz
  rw [← finsum_add_distrib (hf.subset (support_rk_subset B f))
    (hg.subset (support_rk_subset B g))]
  refine finsum_congr fun k => ?_
  rw [restr_add, map_add]

theorem riesz_smul (B : LinearMap.BilinForm ℂ 𝒱) (c : ℂ) {f : 𝒱 →ₗ[ℂ] ℂ}
    (hf : (gsupp W f).Finite) : riesz W B (c • f) = c • riesz W B f := by
  unfold riesz
  rw [smul_finsum' c (hf.subset (support_rk_subset B f))]
  refine finsum_congr fun k => ?_
  rw [restr_smul, map_smul]

theorem riesz_zero (B : LinearMap.BilinForm ℂ 𝒱) : riesz W B 0 = 0 := by
  unfold riesz
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  rw [show restr W k (0 : 𝒱 →ₗ[ℂ] ℂ) = 0 from LinearMap.zero_comp _, map_zero]

theorem gsupp_add (f g : 𝒱 →ₗ[ℂ] ℂ) : gsupp W (f + g) ⊆ gsupp W f ∪ gsupp W g := by
  intro k hk
  by_contra h
  simp only [Set.mem_union, not_or, gsupp, Set.mem_setOf_eq, not_not] at h
  apply hk
  rw [restr_add, h.1, h.2, add_zero]

theorem gsupp_smul (c : ℂ) (f : 𝒱 →ₗ[ℂ] ℂ) : gsupp W (c • f) ⊆ gsupp W f := by
  intro k hk h
  apply hk
  have h' : restr W k f = 0 := by simpa [gsupp] using h
  rw [restr_smul, h', smul_zero]

theorem gsupp_zero : gsupp W (0 : 𝒱 →ₗ[ℂ] ℂ) = ∅ := by
  ext k
  simp only [gsupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact LinearMap.zero_comp _

/-- If `f` vanishes on every `𝒱_{k'}`, `k' ≠ k`, then `riesz B f ∈ 𝒱ₖ`. -/
theorem riesz_eq_rk (B : LinearMap.BilinForm ℂ 𝒱) {f : 𝒱 →ₗ[ℂ] ℂ} {k : ℤ}
    (hf : ∀ k' : ℤ, k' ≠ k → restr W k' f = 0) : riesz W B f = rk W B k (restr W k f) := by
  unfold riesz
  refine finsum_eq_single _ k fun k' hk' => ?_
  rw [hf k' hk', map_zero]

theorem riesz_mem (B : LinearMap.BilinForm ℂ 𝒱) {f : 𝒱 →ₗ[ℂ] ℂ} {k : ℤ}
    (hf : ∀ k' : ℤ, k' ≠ k → restr W k' f = 0) : riesz W B f ∈ W.grading k := by
  rw [riesz_eq_rk B hf]; exact rk_mem B k _

/-- **The Riesz property**: `B (riesz B f) φ = f φ` for every `φ`. -/
theorem riesz_spec {B : LinearMap.BilinForm ℂ 𝒱} (hO : GradedOrth W B) (hnd : GradedNondeg W B)
    {f : 𝒱 →ₗ[ℂ] ℂ} (hf : (gsupp W f).Finite) (φ : 𝒱) : B (riesz W B f) φ = f φ := by
  have hφ : φ ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hφ using Submodule.iSup_induction' with
  | mem k y hy =>
    unfold riesz
    change B.flip y (∑ᶠ k : ℤ, rk W B k (restr W k f)) = f y
    rw [map_finsum (B.flip y) (hf.subset (support_rk_subset B f)), finsum_eq_single _ k]
    · change B (rk W B k (restr W k f)) y = f y
      rw [form_rk hnd k _ hy]; rfl
    · intro k' hk'
      change B (rk W B k' (restr W k' f)) y = 0
      exact hO k' k hk' _ (rk_mem B k' _) y hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

/-- **Separation**: a vector orthogonal to everything is zero. -/
theorem eq_zero_of_form {B : LinearMap.BilinForm ℂ 𝒱} (hO : GradedOrth W B)
    (hnd : GradedNondeg W B) {x : 𝒱} (hx : ∀ φ, B x φ = 0) : x = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcomp : ∀ k, (DirectSum.decompose W.grading x k : 𝒱) = 0 := by
    intro k
    have hk : ∀ y : W.grading k, gradForm W B k (DirectSum.decompose W.grading x k) y = 0 := by
      intro y
      have h := hx y
      rw [← DirectSum.sum_support_decompose W.grading x, map_sum, LinearMap.sum_apply] at h
      rw [Finset.sum_eq_single k] at h
      · exact h
      · intro k' _ hk'
        exact hO k' k hk' _ (DirectSum.decompose W.grading x k').2 _ y.2
      · intro hk
        rw [DFinsupp.notMem_support_iff.mp hk]
        simp
    have := (hnd k).1 _ hk
    rw [this]; rfl
  rw [← DirectSum.sum_support_decompose W.grading x]
  exact Finset.sum_eq_zero fun k _ => hcomp k

theorem eq_of_form {B : LinearMap.BilinForm ℂ 𝒱} (hO : GradedOrth W B) (hnd : GradedNondeg W B)
    {x y : 𝒱} (h : ∀ φ, B x φ = B y φ) : x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_form hO hnd fun φ => by rw [map_sub, LinearMap.sub_apply, h, sub_self]

/-! ## Instances from the library's invariant forms -/

theorem gradedOrth_of_invariantForm (B : InvariantForm W) : GradedOrth W B.form :=
  fun _ _ hmn _ hx _ hy => B.orthogonal_of_ne hmn hx hy

/-- Graded nondegeneracy from the vanishing of the left radical. -/
theorem gradedNondeg_of_radical (B : InvariantForm W) (hrad : InvariantForm.leftRadical B = ⊥) :
    GradedNondeg W B.form := by
  intro k
  haveI := W.finrank k
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
  have hx0 : (x : 𝒱) ∈ InvariantForm.leftRadical B := by
    rw [InvariantForm.mem_leftRadical]
    refine LinearMap.ext fun φ => ?_
    have hφ : φ ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    induction hφ using Submodule.iSup_induction' with
    | mem k' y hy =>
      by_cases hk : k = k'
      · subst hk; exact hx ⟨y, hy⟩
      · exact B.orthogonal_of_ne hk x.2 hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [LinearMap.zero_apply] at ha hb ⊢
      rw [map_add, ha, hb, add_zero]
  rw [hrad, Submodule.mem_bot] at hx0
  exact Subtype.ext hx0

end VOA.Moonshine.SkewAdjoint
