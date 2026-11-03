/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientTransport

/-!
# The contragredient module from `DualAdjResidual` alone (the bilinear extension)

`Modules.ContragredientTransport` reduced the *homogeneous slice* of the module contragredient
Jacobi to the `Y_M`-side nested-transpose residual `DualAdjResidual N`
(`contraJacobiPaired_homog_of_residual`). This file supplies the **bilinear extension to general
`u, v`**, axiom-free, so that **`DualAdjResidual N` implies the full contragredient module
structure outright**:

* **`pairedLHS` / `pairedRHS` / `pairedDiff`** — the paired contragredient-Jacobi LHS, RHS and
  difference as `ℂ`-functions of `(u, v)`; their biadditivity / bi-vanishing (the `finsum`
  bookkeeping off `contraBL_fin`/`contraBR_fin` + `mode (YMdual N ·)` additivity).
* **`pairedDiff_eq_zero_all`** — from the homogeneous residual, `pairedDiff` vanishes on **all**
  `u, v` (double `Submodule.iSup_induction`).
* **`contragredientJacobi_of_dualAdjResidual`** — `DualAdjResidual N → ContragredientJacobi N`
  (the residual is *exactly* the strength of the module Jacobi).
* **`contragredient_of_dualAdjResidual`** — the full graded contragredient `OrdVModule`
  `M* = ⨁_α (M_α)*` built from `DualAdjResidual N` **alone** (no separate `ContragredientJacobi`).

## Status
Axiom-clean. The contragredient module is a genuine `OrdVModule` modulo the precise hypothesis
`DualAdjResidual N` (the module mirror of the `𝒱`-level FHL, `Core.InvariantFormDiagonal.DiagonalFHL`)
— and that hypothesis is discharged unconditionally (axiom-clean): `DualAdjResidual N`
follows from `dualAdjResidual_of_mvec N (dualAdjResidualMvec_holds N)`
(`Modules/ContragredientClose.lean`). Hence the contragredient is **closed**: the fully-discharged
module is `ContragredientClose.contragredientModule N : OrdVModule W (RestrictedDual N)`.

## References
* Gannon §5.3.1, eqs. (5.3.1b), (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The paired contragredient-Jacobi **LHS** as a function of `(u, v)`. -/
noncomputable def pairedLHS (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v : 𝒱) : ℂ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
    (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
      - negOnePow ℓ • dualPairing N xα
          (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f)))

/-- The paired contragredient-Jacobi **RHS** as a function of `(u, v)`. -/
noncomputable def pairedRHS (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v : 𝒱) : ℂ :=
  ∑ᶠ i : ℤ, cbz m i •
    dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)

/-- The paired contragredient-Jacobi **difference** `LHS − RHS`. -/
noncomputable def pairedDiff (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v : 𝒱) : ℂ :=
  pairedLHS N f ℓ m n xα u v - pairedRHS N f ℓ m n xα u v

theorem mode_YMdual_add_state (N : OrdVModule W M) (u₁ u₂ : 𝒱) (k : ℤ) (f : RestrictedDual N) :
    mode (YMdual N (u₁ + u₂)) k f
      = mode (YMdual N u₁) k f + mode (YMdual N u₂) k f := by
  rw [map_add, mode_add, LinearMap.add_apply]

theorem mode_YMdual_smul_state (N : OrdVModule W M) (c : ℂ) (u : 𝒱) (k : ℤ) (f : RestrictedDual N) :
    mode (YMdual N (c • u)) k f = c • mode (YMdual N u) k f := by
  rw [map_smul, mode_smul, LinearMap.smul_apply]

theorem mode_YMdual_zero_state (N : OrdVModule W M) (k : ℤ) (f : RestrictedDual N) :
    mode (YMdual N (0 : 𝒱)) k f = 0 := mode_YMdual_zero N k f

/-- The scalar **LHS** summand is finitely supported in `i`. -/
theorem pairedLHS_summand_fin (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v : 𝒱) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
        - negOnePow ℓ • dualPairing N xα
            (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f)))).Finite := by
  refine (contraBL_fin N u v f ℓ m n).subset (fun i hi => ?_)
  rw [Function.mem_support] at hi ⊢
  intro hzero
  apply hi
  have hpush : (negOnePow i * cbz ℓ i) •
        (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
          - negOnePow ℓ • dualPairing N xα
              (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f)))
      = dualPairing N xα ((negOnePow i * cbz ℓ i) •
          (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f)
            - negOnePow ℓ • mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f))) := by
    rw [map_smul, map_sub, map_smul]
  rw [hpush, hzero, map_zero]

/-- The scalar **RHS** summand is finitely supported in `i`. -/
theorem pairedRHS_summand_fin (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v : 𝒱) :
    (Function.support fun i : ℤ => cbz m i •
      dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)).Finite := by
  refine (contraBR_fin N u v f ℓ m n).subset (fun i hi => ?_)
  rw [Function.mem_support] at hi ⊢
  intro hzero
  apply hi
  have : cbz m i •
      dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)
      = dualPairing N xα (cbz m i • mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f) := by
    rw [map_smul]
  rw [this, hzero, map_zero]

theorem pairedLHS_add_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u₁ u₂ v : 𝒱) :
    pairedLHS N f ℓ m n xα (u₁ + u₂) v
      = pairedLHS N f ℓ m n xα u₁ v + pairedLHS N f ℓ m n xα u₂ v := by
  unfold pairedLHS
  rw [← finsum_add_distrib (pairedLHS_summand_fin N f ℓ m n xα u₁ v)
        (pairedLHS_summand_fin N f ℓ m n xα u₂ v)]
  refine finsum_congr (fun i => ?_)
  rw [mode_YMdual_add_state, mode_YMdual_add_state]
  rw [map_add, map_add, map_add]
  module

theorem pairedLHS_add_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v₁ v₂ : 𝒱) :
    pairedLHS N f ℓ m n xα u (v₁ + v₂)
      = pairedLHS N f ℓ m n xα u v₁ + pairedLHS N f ℓ m n xα u v₂ := by
  unfold pairedLHS
  rw [← finsum_add_distrib (pairedLHS_summand_fin N f ℓ m n xα u v₁)
        (pairedLHS_summand_fin N f ℓ m n xα u v₂)]
  refine finsum_congr (fun i => ?_)
  rw [mode_YMdual_add_state, mode_YMdual_add_state]
  rw [map_add, map_add, map_add]
  module

theorem pairedRHS_add_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u₁ u₂ v : 𝒱) :
    pairedRHS N f ℓ m n xα (u₁ + u₂) v
      = pairedRHS N f ℓ m n xα u₁ v + pairedRHS N f ℓ m n xα u₂ v := by
  unfold pairedRHS
  rw [← finsum_add_distrib (pairedRHS_summand_fin N f ℓ m n xα u₁ v)
        (pairedRHS_summand_fin N f ℓ m n xα u₂ v)]
  refine finsum_congr (fun i => ?_)
  rw [W.smul_add_left, mode_YMdual_add_state, map_add, smul_add]

theorem pairedRHS_add_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v₁ v₂ : 𝒱) :
    pairedRHS N f ℓ m n xα u (v₁ + v₂)
      = pairedRHS N f ℓ m n xα u v₁ + pairedRHS N f ℓ m n xα u v₂ := by
  unfold pairedRHS
  rw [← finsum_add_distrib (pairedRHS_summand_fin N f ℓ m n xα u v₁)
        (pairedRHS_summand_fin N f ℓ m n xα u v₂)]
  refine finsum_congr (fun i => ?_)
  rw [W.smul_add_right, mode_YMdual_add_state, map_add, smul_add]

theorem pairedLHS_zero_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (v : 𝒱) : pairedLHS N f ℓ m n xα 0 v = 0 := by
  unfold pairedLHS
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rw [mode_YMdual_zero_state, map_zero, mode_YMdual_zero N (m + i) f, map_zero]
  simp

theorem pairedLHS_zero_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u : 𝒱) : pairedLHS N f ℓ m n xα u 0 = 0 := by
  unfold pairedLHS
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rw [mode_YMdual_zero N (n + i) f, map_zero, mode_YMdual_zero_state, map_zero]
  simp

theorem pairedRHS_zero_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (v : 𝒱) : pairedRHS N f ℓ m n xα 0 v = 0 := by
  unfold pairedRHS
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rw [W.smul_zero_left, mode_YMdual_zero N (m + n - i) f, map_zero, smul_zero]

theorem pairedRHS_zero_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u : 𝒱) : pairedRHS N f ℓ m n xα u 0 = 0 := by
  unfold pairedRHS
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rw [W.smul_zero_right, mode_YMdual_zero N (m + n - i) f, map_zero, smul_zero]

theorem pairedDiff_add_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u₁ u₂ v : 𝒱) :
    pairedDiff N f ℓ m n xα (u₁ + u₂) v
      = pairedDiff N f ℓ m n xα u₁ v + pairedDiff N f ℓ m n xα u₂ v := by
  unfold pairedDiff
  rw [pairedLHS_add_left, pairedRHS_add_left]; ring

theorem pairedDiff_add_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u v₁ v₂ : 𝒱) :
    pairedDiff N f ℓ m n xα u (v₁ + v₂)
      = pairedDiff N f ℓ m n xα u v₁ + pairedDiff N f ℓ m n xα u v₂ := by
  unfold pairedDiff
  rw [pairedLHS_add_right, pairedRHS_add_right]; ring

theorem pairedDiff_zero_left (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (v : 𝒱) : pairedDiff N f ℓ m n xα 0 v = 0 := by
  unfold pairedDiff
  rw [pairedLHS_zero_left, pairedRHS_zero_left, sub_zero]

theorem pairedDiff_zero_right (N : OrdVModule W M) (f : RestrictedDual N) (ℓ m n : ℤ) (xα : M)
    (u : 𝒱) : pairedDiff N f ℓ m n xα u 0 = 0 := by
  unfold pairedDiff
  rw [pairedLHS_zero_right, pairedRHS_zero_right, sub_zero]

/-- **Base case.** From `DualAdjResidual N`, `pairedDiff` vanishes on every *homogeneous* pair. -/
theorem pairedDiff_eq_zero_homog (N : OrdVModule W M) (hres : DualAdjResidual N)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α)
    {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu) {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv) :
    pairedDiff N f ℓ m n xα u v = 0 := by
  have h := contraJacobiPaired_homog_of_residual N hres hu hv f ℓ m n hxα
  unfold pairedDiff pairedLHS pairedRHS
  rw [sub_eq_zero]
  exact h

/-- **Bilinear extension, first slot.** -/
theorem pairedDiff_eq_zero_left_all (N : OrdVModule W M) (hres : DualAdjResidual N)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α)
    {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv) (u : 𝒱) :
    pairedDiff N f ℓ m n xα u v = 0 := by
  have hutop : u ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => pairedDiff N f ℓ m n xα u v = 0) hutop ?_ ?_ ?_
  · intro wtu x hx
    exact pairedDiff_eq_zero_homog N hres f ℓ m n hxα hx hv
  · exact pairedDiff_zero_left N f ℓ m n xα v
  · intro x y hx hy
    rw [pairedDiff_add_left, hx, hy, add_zero]

/-- **Bilinear extension, both slots.** -/
theorem pairedDiff_eq_zero_all (N : OrdVModule W M) (hres : DualAdjResidual N)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) (u v : 𝒱) :
    pairedDiff N f ℓ m n xα u v = 0 := by
  have hvtop : v ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => pairedDiff N f ℓ m n xα u v = 0) hvtop ?_ ?_ ?_
  · intro wtv y hy
    exact pairedDiff_eq_zero_left_all N hres f ℓ m n hxα hy u
  · exact pairedDiff_zero_right N f ℓ m n xα u
  · intro x y hx hy
    rw [pairedDiff_add_right, hx, hy, add_zero]

/-- **The full paired contragredient Jacobi from the residual** (the bilinear extension). -/
theorem contragredientJacobiPaired_of_dualAdjResidual (N : OrdVModule W M)
    (hres : DualAdjResidual N) : ContragredientJacobiPaired N := by
  intro u v f ℓ m n α xα hxα
  have h := pairedDiff_eq_zero_all N hres f ℓ m n hxα u v
  unfold pairedDiff pairedLHS pairedRHS at h
  rw [sub_eq_zero] at h
  exact h

/-- **`DualAdjResidual N → ContragredientJacobi N`**: the homogeneous `Y_M`-side residual is
*sufficient* for the full, unrestricted module contragredient Jacobi (5.3.1b for `Y_{M*}`). -/
theorem contragredientJacobi_of_dualAdjResidual (N : OrdVModule W M)
    (hres : DualAdjResidual N) : ContragredientJacobi N :=
  contragredientJacobi_of_paired N (contragredientJacobiPaired_of_dualAdjResidual N hres)

/-- **Payoff 1.** The contragredient **weak** module from `DualAdjResidual N` alone. -/
noncomputable def contragredientWeakModule_of_dualAdjResidual (N : OrdVModule W M)
    (hres : DualAdjResidual N) : WeakModule W (RestrictedDual N) :=
  contragredientWeakModule N (contragredientJacobi_of_dualAdjResidual N hres)

/-- **Payoff 2.** The full graded contragredient `OrdVModule` `M* = ⨁_α (M_α)*` from
`DualAdjResidual N` **alone**. -/
noncomputable def contragredient_of_dualAdjResidual (N : OrdVModule W M)
    (hres : DualAdjResidual N) : OrdVModule W (RestrictedDual N) :=
  contragredient N (contragredientJacobi_of_dualAdjResidual N hres)

/-- Sanity: the residual-built contragredient module has weight spaces `(M*)_α = (M_α)*`. -/
@[simp] theorem contragredient_of_dualAdjResidual_weight (N : OrdVModule W M)
    (hres : DualAdjResidual N) (α : ℂ) :
    (contragredient_of_dualAdjResidual N hres).weight α = RestrictedDual.weight N α := rfl

end VOA
