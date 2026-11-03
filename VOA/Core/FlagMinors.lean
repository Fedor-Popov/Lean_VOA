/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Flags refining an ordered basis, and **leading principal minors**

Pure linear algebra: no vertex algebras appear in this file, and it is written so that it could be
lifted out of this repository unchanged.

## What this is for

`Core.GradedUnitarity` phrases the graded-unitarity datum in terms of a flag `G₀ ≤ G₁ ≤ ⋯` and a
bilinear form.  Clause (iv) — nondegeneracy of the form on **every step** of the flag — looks
analytic.  It is not.  When the flag is the family of initial segments of an ordered basis, it is
exactly the condition that the **leading principal minors** of the Gram matrix are nonzero:

  `nondegenerate_flag_iff_minors`.

That converts a statement about subspaces into a statement about determinants of submatrices of a
matrix that `Core.GradedFormMatrix.canGram` already builds.

## ⚠ The ordering hypothesis is not decoration

`RefinesBasis` carries the identification of each step with an *initial segment* of a *fixed order*
on the basis.  Dropping it makes the corresponding pivot statement **false**, not merely unproved:
at `c = -22/5`, level `6`, in the order `(L₋₆|0⟩, L₋₄L₋₂|0⟩)` the textbook Gram pivots are
`(-77, +682/35)`; in the reversed order they are `(66/5, -341/3)`.  Same subspace, same form,
opposite signs.

## The positivity/pivot half lives in `Core.MinorPivots`

This file proves only the **nondegeneracy** half of the minor criterion.  The **positivity/pivot**
half — `(-1)^{ℓ(λ)+1} · D_k / D_{k-1} > 0` — is supplied downstream in `Core.MinorPivots`: the Jacobi
quotient identity `det_leadingPrincipal_eq_mul_det_schurOfLeading`, the converse Sylvester
criterion `posDef_of_det_leadingPrincipal_pos` (absent from Mathlib, which has only the easy
direction), and the layer lemmas `schurOfLeading_posDef_of_sign_ratios` /
`schurOfLeading_negDef_of_sign_ratios`.  (`Mathlib.Analysis.Matrix.LDL` needs `Matrix.PosDef` and
does not apply to the indefinite Gram matrices here.)

## Contents

* `initFam`, `initFlag`, `initBasis` — the initial segment of an ordered basis, its span, and that
  span's basis.
* `leadingPrincipal` — the leading `k × k` principal submatrix.
* `toMatrix_restrict_initFlag` — the Gram matrix of the restricted form **is** the leading
  principal submatrix.
* `nondegenerate_restrict_initFlag_iff` — nondegeneracy on a step ↔ its minor is nonzero.
* `RefinesBasis` — a flag presented as the initial segments of an ordered basis.
* `nondegenerate_flag_iff_minors` — **the reduction**: clause (iv) ↔ all leading principal
  minors nonzero.

## Status
`sorry`-free, no new axioms.  Everything below is a **theorem** about matrices and subspaces.
The pivot/positivity half is in `Core.MinorPivots` (see above).
-/

namespace VOA

namespace FlagMinors

open LinearMap (BilinForm)
open Module (finrank)

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E] {m : ℕ}

/-! ## §1  Initial segments of an ordered basis -/

/-- The first `k` vectors of an ordered basis. -/
noncomputable def initFam (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) : Fin k → E :=
  fun i => e (Fin.castLE hk i)

@[simp] theorem initFam_apply (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) (i : Fin k) :
    initFam e hk i = e (Fin.castLE hk i) := rfl

theorem initFam_linearIndependent (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) :
    LinearIndependent K (initFam e hk) :=
  e.linearIndependent.comp _ (Fin.castLE_injective hk)

/-- The `k`-th step of the flag attached to an ordered basis: the span of the first `k` vectors. -/
noncomputable def initFlag (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) : Submodule K E :=
  Submodule.span K (Set.range (initFam e hk))

theorem initFlag_mono (e : Module.Basis (Fin m) K E) {k l : ℕ} (hk : k ≤ m) (hl : l ≤ m)
    (h : k ≤ l) : initFlag e hk ≤ initFlag e hl := by
  rw [initFlag, initFlag, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨Fin.castLE h i, by simp [initFam]⟩

/-- The initial segment, as a basis of the step it spans. -/
noncomputable def initBasis (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) :
    Module.Basis (Fin k) K (initFlag e hk) :=
  Module.Basis.span (initFam_linearIndependent e hk)

@[simp] theorem coe_initBasis (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) (i : Fin k) :
    ((initBasis e hk i : initFlag e hk) : E) = e (Fin.castLE hk i) :=
  Module.Basis.coe_span_apply _ i

/-- Each step has the expected dimension. -/
theorem finrank_initFlag (e : Module.Basis (Fin m) K E) {k : ℕ} (hk : k ≤ m) :
    finrank K (initFlag e hk) = k := by
  simpa using finrank_span_eq_card (initFam_linearIndependent e hk)

/-! ## §2  Leading principal minors -/

/-- The **leading `k × k` principal submatrix**. -/
def leadingPrincipal (M : Matrix (Fin m) (Fin m) K) {k : ℕ} (hk : k ≤ m) :
    Matrix (Fin k) (Fin k) K :=
  M.submatrix (Fin.castLE hk) (Fin.castLE hk)

@[simp] theorem leadingPrincipal_apply (M : Matrix (Fin m) (Fin m) K) {k : ℕ} (hk : k ≤ m)
    (i j : Fin k) : leadingPrincipal M hk i j = M (Fin.castLE hk i) (Fin.castLE hk j) := rfl

/-- **The Gram matrix of the restricted form is the leading principal submatrix.**  This is the
identification that makes the criterion computable: no new matrix has to be built for a step of the
flag, one just cuts the corner out of the full Gram matrix. -/
theorem toMatrix_restrict_initFlag (β : BilinForm K E) (e : Module.Basis (Fin m) K E)
    {k : ℕ} (hk : k ≤ m) :
    LinearMap.BilinForm.toMatrix (initBasis e hk) (β.restrict (initFlag e hk))
      = leadingPrincipal (LinearMap.BilinForm.toMatrix e β) hk := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- **Nondegeneracy on a step of the flag ↔ its leading principal minor is nonzero.** -/
theorem nondegenerate_restrict_initFlag_iff (β : BilinForm K E) (e : Module.Basis (Fin m) K E)
    {k : ℕ} (hk : k ≤ m) :
    (β.restrict (initFlag e hk)).Nondegenerate
      ↔ (leadingPrincipal (LinearMap.BilinForm.toMatrix e β) hk).det ≠ 0 := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (initBasis e hk),
    toMatrix_restrict_initFlag]

/-! ## §3  Flags that refine an ordered basis -/

/-- A flag `F` **refines the ordered basis `e`**: every step is an initial segment.

⚠ This structure is where the ordering hypothesis lives, and it must be carried explicitly in
every statement below.  See the file docstring: without it the corresponding pivot statement is
false, not merely unproved. -/
structure RefinesBasis (F : ℕ → Submodule K E) (e : Module.Basis (Fin m) K E) where
  /-- The dimension of the `p`-th step. -/
  dim : ℕ → ℕ
  /-- Each step dimension is at most the dimension of the ambient space. -/
  dim_le : ∀ p, dim p ≤ m
  /-- Step `p` is spanned by the first `dim p` basis vectors, **in the given order**. -/
  eq : ∀ p, F p = initFlag e (dim_le p)

namespace RefinesBasis

variable {F : ℕ → Submodule K E} {e : Module.Basis (Fin m) K E}

theorem finrank_eq (h : RefinesBasis F e) (p : ℕ) : finrank K (F p) = h.dim p := by
  rw [h.eq p]; exact finrank_initFlag e (h.dim_le p)

end RefinesBasis

/-- **THE REDUCTION (clause (iv) half).**

For a flag refining an ordered basis, the form is nondegenerate on **every step** if and only if
**every leading principal minor** of its Gram matrix is nonzero.

This is a *reduction*, not a criterion that anything is asserted to satisfy: it says the
subspace-theoretic clause (iv) of the graded-unitarity datum and the determinantal condition are
the same statement.  Whether either holds for the Virasoro minimal models is open. -/
theorem nondegenerate_flag_iff_minors {F : ℕ → Submodule K E} {e : Module.Basis (Fin m) K E}
    (h : RefinesBasis F e) (β : BilinForm K E) :
    (∀ p, (β.restrict (F p)).Nondegenerate)
      ↔ ∀ p, (leadingPrincipal (LinearMap.BilinForm.toMatrix e β) (h.dim_le p)).det ≠ 0 := by
  constructor
  · intro H p
    rw [← nondegenerate_restrict_initFlag_iff, ← h.eq p]
    exact H p
  · intro H p
    rw [h.eq p, nondegenerate_restrict_initFlag_iff]
    exact H p

end FlagMinors

end VOA
