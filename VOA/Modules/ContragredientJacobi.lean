/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientAction
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean

/-!
# The contragredient `WeakModule` — assembled modulo the module Jacobi 5.3.1b

The contragredient field-mode engine of `Modules.ContragredientAction` is here bundled into a full
weak-module structure, **parametric in one explicit hypothesis** `ContragredientJacobi N` (the
module Jacobi 5.3.1b for `dualModeEndo`):

* **`YMdual`** — the bundled field `Y_{M*} : 𝒱 →ₗ[ℂ] (End (RestrictedDual N))⟦z^±⟧` (sum of
  `dualModeEndo` over the grade decomposition of `u`); `YMdual_vacuum` (5.3.1a) and
  **`YMdual_truncation`** (the field/lower-truncation, via `boundedBelow`).
* **`restrictedDual_ext_of_pairing`** — the separation lemma (a `RestrictedDual N` element is
  determined by its pairings against the weight spaces), and `contragredientJacobi_of_paired`
  reducing `ContragredientJacobi N` to a scalar, weight-tested predicate `ContragredientJacobiPaired`.
* **`contragredientWeakModule N (hJac : ContragredientJacobi N) : WeakModule W (RestrictedDual N)`** —
  the genuine weak module, the instant the Jacobi hypothesis is supplied.

## Status
Axiom-clean for the bundled field, vacuum normalization, truncation, the separation lemma, and
the Jacobi→Paired reduction.

`ContragredientJacobi N` itself is proved unconditionally, axiom-clean
(`Modules/ContragredientClose.lean`, `contragredientJacobi_holds`). It is the **module-level
full-invariance** `⟨Y_{M*}(u,z)f,x⟩ = ⟨f, Y_M(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)x⟩` (the FHL / `ι_z`
generating-function content), discharged not via the `𝒱`-level `IsFullyInvariant` route but via the
`Y_M`-side residual: `contragredientJacobi_of_dualAdjResidual N (dualAdjResidual_of_mvec N
(dualAdjResidualMvec_holds N))`. Consequently `contragredient N (contragredientJacobi_holds N)` and
`contragredientWeakModule` are unconditional. `ContragredientJacobi` was a *hypothesis*, never an axiom.

## References
* Gannon §5.3.1, eqs. (5.3.1b), (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (0) Prelude.

We re-declare `dualModeFamily`, `dualModeAt`, `dualModeAt_homogeneous`, `YMdual`,
`mode_YMdual`, `mode_YMdual_homogeneous`, `YMdual_vacuum`, the truncation chain, and the
pairing-separation bridge.  These are *exactly* the wf3 results; this file consumes them. -/

noncomputable def dualModeFamily (N : OrdVModule W M) (n : ℤ) (wt : ℤ) :
    (W.grading wt) →ₗ[ℂ] End ℂ (RestrictedDual N) where
  toFun uwt := dualModeEndo N wt (uwt : 𝒱) n
  map_add' a b := by
    simp only [Submodule.coe_add]
    exact dualModeEndo_add_u N wt (a : 𝒱) (b : 𝒱) n
  map_smul' c a := by
    simp only [SetLike.val_smul, RingHom.id_apply]
    exact dualModeEndo_smul_u N wt c (a : 𝒱) n

noncomputable def dualModeAt (N : OrdVModule W M) (n : ℤ) : 𝒱 →ₗ[ℂ] End ℂ (RestrictedDual N) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (dualModeFamily N n)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem dualModeAt_homogeneous (N : OrdVModule W M) (n : ℤ) {wt : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading wt) :
    dualModeAt N n u = dualModeEndo N wt u n := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : dualModeAt N n u = dualModeFamily N n wt ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (dualModeFamily N n)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (dualModeFamily N n) wt ⟨u, hu⟩
  rw [hcollapse]; rfl

noncomputable def YMdual (N : OrdVModule W M) : 𝒱 →ₗ[ℂ] (End ℂ (RestrictedDual N))⟦z^±⟧ where
  toFun u := fun p => dualModeAt N (-p - 1) u
  map_add' u₁ u₂ := by
    funext p
    show dualModeAt N (-p - 1) (u₁ + u₂) = _
    rw [map_add]; rfl
  map_smul' c u := by
    funext p
    show dualModeAt N (-p - 1) (c • u) = _
    rw [map_smul]; rfl

theorem mode_YMdual (N : OrdVModule W M) (u : 𝒱) (n : ℤ) :
    mode (YMdual N u) n = dualModeAt N n u := by
  show (YMdual N u) (-n - 1) = dualModeAt N n u
  show dualModeAt N (-(-n - 1) - 1) u = dualModeAt N n u
  congr 1; ring

theorem mode_YMdual_homogeneous (N : OrdVModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (n : ℤ) :
    mode (YMdual N u) n = dualModeEndo N wt u n := by
  rw [mode_YMdual, dualModeAt_homogeneous N n hu]

theorem YMdual_vacuum (N : OrdVModule W M) : YMdual N W.vacuum = 1 := by
  refine FormalDist.ext (fun p => ?_)
  show dualModeAt N (-p - 1) W.vacuum = (1 : (End ℂ (RestrictedDual N))⟦z^±⟧) p
  rw [dualModeAt_homogeneous N (-p - 1) W.vacuum_mem, FormalDist.one_apply]
  by_cases hp : p = 0
  · subst hp
    rw [show (-(0 : ℤ) - 1) = -1 by ring, dualModeEndo_vacuum_id, if_pos rfl,
      Module.End.one_eq_id]
  · rw [if_neg hp]
    have hn : (-p - 1 : ℤ) ≠ -1 := by omega
    rw [dualModeEndo_vacuum_zero N hn]

theorem dual_eq_zero_of_weight_bot (N : OrdVModule W M) {α : ℂ} (hα : N.weight α = ⊥)
    (g : Module.Dual ℂ (N.weight α)) : g = 0 := by
  haveI : Subsingleton (N.weight α) := by rw [hα]; infer_instance
  exact Subsingleton.elim _ _

theorem dualModeEndo_lof_eq_zero_of_large (N : OrdVModule W M) {wt : ℤ} {u : 𝒱}
    (n : ℤ) (γ : ℂ) (g : Module.Dual ℂ (N.weight γ))
    (hbot : N.weight (dualOutIdx wt n γ) = ⊥) :
    dualModeEndo N wt u n
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g) = 0 := by
  rw [dualModeEndo_lof]
  rw [dual_eq_zero_of_weight_bot N hbot (restrictToWeight N (dualOutIdx wt n γ)
    (dualCompMap N wt u n γ g))]
  exact map_zero _

theorem weight_dualOutIdx_bot_of_large (N : OrdVModule W M) {B : ℝ}
    (hB : ∀ α : ℂ, N.weight α ≠ ⊥ → B ≤ α.re) (wt : ℤ) (γ : ℂ) {n : ℤ}
    (hn : (γ.re + (wt : ℝ) - 1 - B) < (n : ℝ)) :
    N.weight (dualOutIdx wt n γ) = ⊥ := by
  by_contra hne
  have hle := hB _ hne
  have hre : (dualOutIdx wt n γ).re = γ.re + (wt : ℝ) - (n : ℝ) - 1 := by
    simp only [dualOutIdx, Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
  rw [hre] at hle
  linarith

theorem dualModeEndo_truncation_homogeneous (N : OrdVModule W M) {wt : ℤ} {u : 𝒱}
    (f : RestrictedDual N) :
    ∃ Nthr : ℤ, ∀ n : ℤ, Nthr ≤ n → dualModeEndo N wt u n f = 0 := by
  classical
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine DirectSum.induction_on (β := fun α => Module.Dual ℂ (N.weight α)) f ?_ ?_ ?_
  · exact ⟨0, fun n _ => map_zero _⟩
  · intro γ g
    obtain ⟨z, hz⟩ := exists_int_gt (γ.re + (wt : ℝ) - 1 - B)
    refine ⟨z, fun n hn => ?_⟩
    have hnre : (γ.re + (wt : ℝ) - 1 - B) < (n : ℝ) := by
      have h2 : (z : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hbot := weight_dualOutIdx_bot_of_large N hB wt γ hnre
    have := dualModeEndo_lof_eq_zero_of_large N (u := u) n γ g hbot
    rw [DirectSum.lof_eq_of ℂ ℂ (fun α => Module.Dual ℂ (N.weight α)) γ g] at this
    exact this
  · rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    have he : (dualModeEndo N wt u n) (x + y)
        = (dualModeEndo N wt u n) x + (dualModeEndo N wt u n) y := LinearMap.map_add _ _ _
    rw [he, hx n (le_trans (le_max_left _ _) hn),
      hy n (le_trans (le_max_right _ _) hn), add_zero]

theorem YMdual_truncation (N : OrdVModule W M) (u : 𝒱) (f : RestrictedDual N) :
    ∃ Nthr : ℤ, ∀ n : ℤ, Nthr ≤ n → mode (YMdual N u) n f = 0 := by
  classical
  suffices h : ∃ Nthr : ℤ, ∀ n : ℤ, Nthr ≤ n → dualModeAt N n u f = 0 by
    obtain ⟨Nthr, hN⟩ := h
    exact ⟨Nthr, fun n hn => by rw [mode_YMdual]; exact hN n hn⟩
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => ∃ Nthr : ℤ, ∀ n : ℤ, Nthr ≤ n → dualModeAt N n u f = 0)
    hutop ?_ ?_ ?_
  · intro wt x hx
    obtain ⟨Nthr, hN⟩ := dualModeEndo_truncation_homogeneous N (wt := wt) (u := x) f
    refine ⟨Nthr, fun n hn => ?_⟩
    rw [dualModeAt_homogeneous N n hx]
    exact hN n hn
  · exact ⟨0, fun n _ => by rw [map_zero]; rfl⟩
  · rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    have he : dualModeAt N n (x + y) f = dualModeAt N n x f + dualModeAt N n y f := by
      rw [map_add]; rfl
    rw [he, hx n (le_trans (le_max_left _ _) hn), hy n (le_trans (le_max_right _ _) hn),
      add_zero]

theorem dualPairing_lof_self (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α)
    (g : Module.Dual ℂ (N.weight α)) :
    dualPairing N x (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g)
      = g ⟨x, hx⟩ := by
  rw [dualPairing_lof]
  congr 1
  exact internalProjTo_coe N.isInternal α ⟨x, hx⟩

theorem internalProjTo_eq_zero_of_ne (N : OrdVModule W M) {α β : ℂ} {x : M}
    (hx : x ∈ N.weight α) (hβ : β ≠ α) : internalProjTo N.isInternal β x = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  apply Subtype.ext
  have hdec := DirectSum.decompose_of_mem_ne N.weight hx (Ne.symm hβ)
  show ((DirectSum.component ℂ ℂ (fun j => N.weight j) β)
      (DirectSum.decomposeLinearEquiv N.weight x) : N.weight β) = ((0 : N.weight β) : M)
  rw [show (DirectSum.decomposeLinearEquiv N.weight x)
      = DirectSum.decompose N.weight x from rfl, ← DirectSum.apply_eq_component, hdec]
  rfl

theorem dualPairing_component (N : OrdVModule W M) (f : RestrictedDual N) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) :
    dualPairing N x f
      = (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α f) ⟨x, hx⟩ := by
  classical
  refine DirectSum.induction_on (β := fun β => Module.Dual ℂ (N.weight β)) f ?_ ?_ ?_
  · rw [map_zero]; rfl
  · intro β g
    have hof : (DirectSum.of (fun β => Module.Dual ℂ (N.weight β)) β g)
        = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) β g := rfl
    rw [hof]
    by_cases hβ : β = α
    · subst hβ
      rw [dualPairing_lof_self N hx g, DirectSum.component.lof_self]
    · rw [dualPairing_lof, internalProjTo_eq_zero_of_ne N hx hβ, map_zero,
        DirectSum.component.of, dif_neg hβ]
      rfl
  · intro a b ha hb
    have hadd : dualPairing N x (a + b) = dualPairing N x a + dualPairing N x b :=
      LinearMap.map_add _ _ _
    have hadd2 : (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) (a + b)
        = (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) a
          + (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) b :=
      LinearMap.map_add _ _ _
    rw [hadd, ha, hb, hadd2, LinearMap.add_apply]

theorem restrictedDual_ext_of_pairing (N : OrdVModule W M) {f g : RestrictedDual N}
    (h : ∀ (α : ℂ) (x : M), x ∈ N.weight α → dualPairing N x f = dualPairing N x g) :
    f = g := by
  classical
  refine DirectSum.ext_component ℂ (fun α => ?_)
  refine LinearMap.ext (fun y => ?_)
  have hy : (y : M) ∈ N.weight α := y.2
  have hf := dualPairing_component N f hy
  have hg := dualPairing_component N g hy
  have hxy : (⟨(y : M), hy⟩ : N.weight α) = y := Subtype.ext rfl
  rw [hxy] at hf hg
  rw [← hf, ← hg, h α (y : M) hy]

def ContragredientJacobi (N : OrdVModule W M) : Prop :=
  ∀ (u v : 𝒱) (x : RestrictedDual N) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) x)
          - negOnePow ℓ • mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) x

/-! ## (I) `YMdual` linearity bookkeeping: `mode (YMdual 0) = 0`. -/

/-- `YMdual N 0 = 0` (linearity), hence its modes vanish. -/
theorem mode_YMdual_zero (N : OrdVModule W M) (n : ℤ) (x : RestrictedDual N) :
    mode (YMdual N 0) n x = 0 := by
  rw [map_zero]
  show (0 : (End ℂ (RestrictedDual N))⟦z^±⟧) (-n - 1) x = 0
  rfl

/-! ## (II) Support-finiteness of the three `ℤ`-finsums in `ContragredientJacobi`.

The contragredient analogues of `Borcherds.Puv_fin` / `Pvu_fin` / `BR_fin`.  Lower bound:
`cbz · i = 0` for `i < 0`.  Upper bound: `YMdual_truncation` (Puv/Pvu — the *inner* mode
truncates) resp. `W.smul_eventually_zero` (BR — the *state* `u₍ℓ₊ᵢ₎v` truncates). -/

/-- The **`Puv`-type** summand `(negOnePow i·cbz ℓ i)·u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎ x)` is finitely
supported in `i`. -/
theorem contraPuv_fin (N : OrdVModule W M) (u v : 𝒱) (x : RestrictedDual N) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := YMdual_truncation N v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), map_zero, smul_zero]

/-- The **`Pvu`-type** summand `(negOnePow i·cbz ℓ i)·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎ x)` is finitely
supported in `i`. -/
theorem contraPvu_fin (N : OrdVModule W M) (u v : 𝒱) (x : RestrictedDual N) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := YMdual_truncation N u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), map_zero, smul_zero]

/-- The **`BR`-type** summand `cbz m i·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x` is finitely supported in `i`. -/
theorem contraBR_fin (N : OrdVModule W M) (u v : 𝒱) (x : RestrictedDual N) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => cbz m i •
      mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) x).Finite := by
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [hNs (ℓ + i) (by omega), mode_YMdual_zero, smul_zero]

/-- Combined: the **full LHS** summand (the `Puv − (-1)^ℓ Pvu` bracket) is finitely
supported. -/
theorem contraBL_fin (N : OrdVModule W M) (u v : 𝒱) (x : RestrictedDual N) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) x)
        - negOnePow ℓ • mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) x))).Finite := by
  refine ((contraPuv_fin N u v x ℓ m n).union
    (contraPvu_fin N u v x ℓ m n)).subset (fun i hi => ?_)
  simp only [Function.mem_support, Set.mem_union, ne_eq] at hi ⊢
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hi
  rw [smul_sub, h1, smul_comm, h2, smul_zero, sub_zero]

/-! ## (III) Pushing `dualPairing N x` through the finsums.

`dualPairing N x : RestrictedDual N →ₗ[ℂ] ℂ`, so `map_finsum` (with the finiteness lemmas of
(II)) pushes it inside each `∑ᶠ`, and `map_smul`/`map_sub` distribute it over the summand.
This produces the *scalar* shape of both sides of the contragredient Jacobi. -/

/-- The pairing of the **LHS** finsum against `x`, distributed inside the sum. -/
theorem dualPairing_lhs (N : OrdVModule W M) (u v : 𝒱) (f : RestrictedDual N) (ℓ m n : ℤ)
    (xα : M) :
    dualPairing N xα
        (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f)
            - negOnePow ℓ • mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f)))
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
            - negOnePow ℓ • dualPairing N xα
                (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f))) := by
  rw [map_finsum (dualPairing N xα) (contraBL_fin N u v f ℓ m n)]
  refine finsum_congr (fun i => ?_)
  rw [map_smul, map_sub, map_smul]

/-- The pairing of the **RHS** finsum against `x`, distributed inside the sum. -/
theorem dualPairing_rhs (N : OrdVModule W M) (u v : 𝒱) (f : RestrictedDual N) (ℓ m n : ℤ)
    (xα : M) :
    dualPairing N xα
        (∑ᶠ i : ℤ, cbz m i • mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)
      = ∑ᶠ i : ℤ, cbz m i •
          dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f) := by
  rw [map_finsum (dualPairing N xα) (contraBR_fin N u v f ℓ m n)]
  refine finsum_congr (fun i => ?_)
  rw [map_smul]

/-! ## (IV) The reduction of `ContragredientJacobi` to a `Y_M`-side scalar identity.

By `restrictedDual_ext_of_pairing`, the Jacobi equation in `RestrictedDual N` holds iff it
holds after pairing against every weight vector `xα ∈ M_α`.  Combining (III), this is the
predicate `ContragredientJacobiPaired` below: a family of *scalar* identities, with the
contragredient modes already exposed only through `dualPairing N xα ∘ mode (YMdual …)`. -/

/-- The **paired** (scalar) form of the contragredient Jacobi: the same equation tested
against every weight vector `xα ∈ M_α`. -/
def ContragredientJacobiPaired (N : OrdVModule W M) : Prop :=
  ∀ (u v : 𝒱) (f : RestrictedDual N) (ℓ m n : ℤ) (α : ℂ) (xα : M), xα ∈ N.weight α →
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
          - negOnePow ℓ • dualPairing N xα
              (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f))))
      = ∑ᶠ i : ℤ, cbz m i •
          dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)

/-! ## (V) The single-generator transpose — pinning the `Y_M`-side obligation.

Pairing one contragredient mode (homogeneous `u ∈ 𝒱_wt`) against `xα ∈ M_α`, evaluated on a
single graded generator `lof γ g`, reproduces the genuine module-side functional
`dualCompMap` *exactly when* `α = dualOutIdx wt k γ`, and vanishes otherwise.  This makes the
mode-index coupling between input slot `γ` and output weight `α` explicit: the contragredient
field is the transpose of `Y_M(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)` only as a *formal series* (matching
`z`-coefficients), not as a single operator — which is precisely why extracting the module
Jacobi requires the generating-function full-invariance + FHL rearrangement, not the bare
per-mode data. -/

/-- Single-generator transpose, matched slot.  For `xα ∈ M_α` with `α = dualOutIdx wt k γ`,
the pairing of the contragredient mode against `lof γ g` is the module-side functional
`dualCompMap … g` evaluated at `xα`. -/
theorem dualPairing_mode_lof_matched (N : OrdVModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) (γ : ℂ) (g : Module.Dual ℂ (N.weight γ)) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) (hmatch : α = dualOutIdx wt k γ) :
    dualPairing N xα (mode (YMdual N u) k
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g))
      = dualCompMap N wt u k γ g xα := by
  rw [mode_YMdual_homogeneous N hu k]
  subst hmatch
  exact dualModeEndo_pairing_out N wt u k γ g hxα

/-- Single-generator transpose, mismatched slot.  For `xα ∈ M_α` with `α ≠ dualOutIdx wt k γ`,
the pairing vanishes (the contragredient mode lands in the `dualOutIdx`-slot, orthogonal to
`M_α`). -/
theorem dualPairing_mode_lof_mismatched (N : OrdVModule W M) {wt : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading wt) (k : ℤ) (γ : ℂ) (g : Module.Dual ℂ (N.weight γ)) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) (hmis : α ≠ dualOutIdx wt k γ) :
    dualPairing N xα (mode (YMdual N u) k
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g)) = 0 := by
  rw [mode_YMdual_homogeneous N hu k, dualModeEndo_lof, dualPairing_lof,
    internalProjTo_eq_zero_of_ne N hxα hmis.symm, map_zero]

/-- **The reduction.**  `ContragredientJacobiPaired N` (a family of scalar identities)
implies the full `ContragredientJacobi N` (an equation in `RestrictedDual N`).  This is the
genuine pairing-separation step: it removes the `RestrictedDual N` from the obligation,
leaving a `Y_M`-side scalar identity. -/
theorem contragredientJacobi_of_paired (N : OrdVModule W M)
    (h : ContragredientJacobiPaired N) : ContragredientJacobi N := by
  intro u v f ℓ m n
  refine restrictedDual_ext_of_pairing N (fun α xα hxα => ?_)
  rw [dualPairing_lhs N u v f ℓ m n xα, dualPairing_rhs N u v f ℓ m n xα]
  exact h u v f ℓ m n α xα hxα

/-- **The contragredient weak module** `WeakModule W (RestrictedDual N)` (Gannon 5.3.1), assembled
from the proved fields `YMdual` / `YMdual_vacuum` / `YMdual_truncation` and the module Jacobi
supplied as `hJac : ContragredientJacobi N`. The genuine bundling of `M* = ⨁_α (M_α)*` as a weak
`𝒱`-module; the only input it consumes is the precise `ContragredientJacobi` statement (the
module-level FHL/`ι_z` full-invariance — see the file header). -/
noncomputable def contragredientWeakModule (N : OrdVModule W M)
    (hJac : ContragredientJacobi N) : WeakModule W (RestrictedDual N) where
  YM := YMdual N
  vacuum_YM := YMdual_vacuum N
  truncation := YMdual_truncation N
  jacobi := hJac

/-- Sanity: the assembled `YM` field is exactly `YMdual N`. -/
theorem contragredientWeakModule_YM (N : OrdVModule W M) (h : ContragredientJacobi N) :
    (contragredientWeakModule N h).YM = YMdual N := rfl

/-! ## (VI) The contragredient as a full graded `OrdVModule`, parametric in `ContragredientJacobi`.

With the weak module in hand (consuming only `ContragredientJacobi`), the *graded* structure of
`M* = ⨁_α (M_α)*` is unconditional and proved here:

* `directSum_isInternal_range_lof` — the canonical summand-ranges of any `DirectSum` are an
  internal direct-sum decomposition (a generic Mathlib-flavoured lemma);
* `L_one_conformalVector` — `L₁ω = 0` (the conformal vector is quasi-primary), via `ω = L₋₂𝟙`,
  `[L₁,L₋₂]=3L₋₁`, `L₁𝟙 = L₋₁𝟙 = 0`;
* `restrictToWeight_dualCompMap_omega` — `L₀^{M*}` acts on `(M_α)*` by the scalar `α` (the
  `e^{zL₁}`-twist of `ω` collapses to its single `j = 0` term since `L₁ω = 0`, leaving the
  module `L₀ = ω₍₁₎`), so `(M*)_α = (M_α)*` realizes weight `α` (whence `χ_{M*} = χ_M`);
* **`contragredientOrdVModule`** — the assembled `OrdVModule W (RestrictedDual N)`, `noncomputable`,
  whose only hypothesis is the same `ContragredientJacobi N` as the weak module.

The only hypothesis is exactly `ContragredientJacobi` itself (the module-level FHL/`ι_z`
full-invariance — see the file header); everything *else* in the contragredient module structure
is proved axiom-free. -/

/-- **The canonical summand-ranges of a `DirectSum` are internal.** For any family `β`,
`(fun i => range (lof i))` is a `DirectSum.IsInternal` decomposition of `⨁ i, β i`. -/
theorem directSum_isInternal_range_lof {ι : Type*} [DecidableEq ι] {R : Type*} [Ring R]
    (β : ι → Type*) [∀ i, AddCommGroup (β i)] [∀ i, Module R (β i)] :
    DirectSum.IsInternal (fun i => LinearMap.range (DirectSum.lof R ι β i)) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · apply iSupIndep_of_dfinsupp_lsum_injective
    rw [injective_iff_map_eq_zero]
    intro g hg
    refine DFinsupp.ext (fun j => ?_)
    apply Subtype.ext
    rw [DFinsupp.zero_apply, Submodule.coe_zero]
    have hsum : (DFinsupp.lsum ℕ fun i =>
        (LinearMap.range (DirectSum.lof R ι β i)).subtype) g
        = ∑ i ∈ g.support, ((g i : DirectSum ι β)) := by
      rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]; rfl
    have h0 : DirectSum.component R ι β j (∑ i ∈ g.support, ((g i : DirectSum ι β))) = 0 := by
      rw [← hsum, hg, map_zero]
    rw [map_sum, Finset.sum_eq_single j] at h0
    · obtain ⟨c, hc⟩ := (g j).2
      have hcomp : DirectSum.component R ι β j (g j : DirectSum ι β) = c := by
        rw [← hc, DirectSum.component.lof_self]
      rw [hcomp] at h0
      rw [← hc, h0, map_zero]
    · intro i _ hij
      obtain ⟨c, hc⟩ := (g i).2
      rw [← hc, DirectSum.component.of, dif_neg hij]
    · intro hj
      rw [DFinsupp.notMem_support_iff.mp hj]; simp
  · rw [eq_top_iff]
    intro f _
    rw [← DirectSum.sum_support_of f]
    apply Submodule.sum_mem
    intro i _
    refine Submodule.mem_iSup_of_mem i ?_
    exact ⟨f i, (DirectSum.lof_eq_of R ι β i (f i))⟩

/-- **`L₁ω = 0`** — the conformal vector is quasi-primary. Via `ω = L₋₂𝟙`, the Virasoro relation
`[L₁,L₋₂]=3L₋₁` (central term absent since `1+(-2)≠0`), and `L₁𝟙 = L₋₁𝟙 = 0` (creation/regularity).
This is exactly the `u = ω` case underlying `InvariantForm.virasoro_adj`. -/
theorem L_one_conformalVector (W : VertexOperatorAlgebra 𝒱) :
    W.L 1 W.conformalVector = 0 := by
  have homega : W.L (-2) W.vacuum = W.conformalVector := by
    rw [VertexOperatorAlgebra.L_def]
    show mode (W.Y W.conformalVector) (-2 + 1) W.vacuum = W.conformalVector
    rw [show (-2 : ℤ) + 1 = -1 by ring]
    exact PreVertexAlgebra.smul_vacuum_neg_one W.toPreVertexAlgebra W.conformalVector
  have hbr : ⁅W.L 1, W.L (-2)⁆ = (3 : ℂ) • W.L (-1) := by
    have key := W.L_virasoro 1 (-2); norm_num at key; convert key using 2
  have hL1vac : W.L 1 W.vacuum = 0 := by
    rw [VertexOperatorAlgebra.L_def]
    show mode (W.Y W.conformalVector) (1 + 1) W.vacuum = 0
    rw [show (1 : ℤ) + 1 = 2 by ring]
    exact PreVertexAlgebra.smul_vacuum_nonneg W.toPreVertexAlgebra W.conformalVector (by norm_num)
  have hLm1vac : W.L (-1) W.vacuum = 0 := by
    rw [VertexOperatorAlgebra.L_def]
    show mode (W.Y W.conformalVector) (-1 + 1) W.vacuum = 0
    rw [show (-1 : ℤ) + 1 = 0 by ring]
    exact PreVertexAlgebra.smul_vacuum_nonneg W.toPreVertexAlgebra W.conformalVector (le_refl 0)
  rw [← homega]
  have hcomp : W.L 1 (W.L (-2) W.vacuum)
      = ⁅W.L 1, W.L (-2)⁆ W.vacuum + W.L (-2) (W.L 1 W.vacuum) := by
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
  rw [hcomp, hbr, hL1vac, map_zero, add_zero, LinearMap.smul_apply, hLm1vac, smul_zero]

/-- `(W.L 1)^(j+1) ω = 0` — every positive power of `L₁` annihilates `ω`. -/
theorem L_one_pow_succ_conformalVector (W : VertexOperatorAlgebra 𝒱) (j : ℕ) :
    ((W.L 1) ^ (j + 1)) W.conformalVector = 0 := by
  rw [pow_succ, Module.End.mul_apply, L_one_conformalVector, map_zero]

/-- **The contragredient `L₀` acts on `(M_α)*` by `α`.** The twisted module mode of `ω` at
`n = 1` restricts, on the output weight space, to `dualCompMap N 2 ω 1 α`; the `e^{zL₁}`-twist
collapses to its `j = 0` term (`L₁ω = 0`), leaving the genuine module `L₀ = ω₍₁₎` whose
eigenvalue on `M_α` is `α`. Hence `restrictToWeight α (dualCompMap N 2 ω 1 α g) = α • g`. -/
theorem restrictToWeight_dualCompMap_omega (N : OrdVModule W M) (α : ℂ)
    (g : Module.Dual ℂ (N.weight α)) :
    restrictToWeight N α (dualCompMap N 2 W.conformalVector 1 α g) = α • g := by
  refine LinearMap.ext (fun y => ?_)
  show dualCompMap N 2 W.conformalVector 1 α g ((N.weight α).subtype y) = α • g y
  rw [dualCompMap_apply, show (2 : ℤ).toNat + 1 = 3 from rfl,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hkill : ∀ j : ℕ,
      g (internalProjTo N.isInternal α
          (mode (N.YM ((W.L 1 ^ (j + 1)) W.conformalVector)) (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ))
            ((N.weight α).subtype y))) = 0 := by
    intro j
    rw [L_one_pow_succ_conformalVector, map_zero]
    show g (internalProjTo N.isInternal α (mode (0 : (Module.End ℂ M)⟦z^±⟧)
        (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ)) ((N.weight α).subtype y))) = 0
    rw [show mode (0 : (Module.End ℂ M)⟦z^±⟧) (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ)) = 0 from rfl]
    simp
  have h0term : g (internalProjTo N.isInternal α
      (mode (N.YM ((W.L 1 ^ (0:ℕ)) W.conformalVector)) (2 * 2 - 1 - 2 - ((0:ℕ) : ℤ))
        ((N.weight α).subtype y))) = α • g y := by
    rw [pow_zero, Module.End.one_apply, show (2 * 2 - 1 - 2 - ((0:ℕ):ℤ) : ℤ) = 1 from by norm_num]
    have hy : ((N.weight α).subtype y) ∈ N.weight α := y.2
    rw [N.L0_weight α _ hy, map_smul, map_smul, Submodule.subtype_apply,
      internalProjTo_coe N.isInternal α y]
  rw [show ((1:ℕ)) = 0 + 1 from rfl, show ((2:ℕ)) = 1 + 1 from rfl, hkill 0, hkill 1]
  simp only [smul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [h0term]; norm_num

/-- **The contragredient as a full graded `OrdVModule`** `M* = ⨁_α (M_α)*` (Gannon §5.3.1), parametric
in the module Jacobi `ContragredientJacobi N`. Upgrades `contragredientWeakModule` with the graded
structure: the internal grading is the canonical `⨁`-decomposition
(`directSum_isInternal_range_lof`), `L₀` acts on `(M_α)*` by `α`
(`restrictToWeight_dualCompMap_omega`, whence the weights of `M*` match
those of `M` — consistent with `contragredient_gradedDim`, `χ_{M*}=χ_M`), each weight space is
finite-dimensional (`dim (M_α)* = dim M_α`), and the bounded-below bound is inherited from `N`.
The only hypothesis it consumes is the same `ContragredientJacobi N` as the weak module. -/
noncomputable def contragredientOrdVModule (N : OrdVModule W M) (hJac : ContragredientJacobi N) :
    OrdVModule W (RestrictedDual N) where
  toWeakModule := contragredientWeakModule N hJac
  weight := RestrictedDual.weight N
  isInternal := directSum_isInternal_range_lof (fun β => Module.Dual ℂ (N.weight β))
  L0_weight := by
    intro α f hf
    obtain ⟨g, rfl⟩ := hf
    show mode (YMdual N W.conformalVector) 1
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g) = _
    rw [mode_YMdual_homogeneous N W.conformal_mem 1, dualModeEndo_lof,
      show dualOutIdx 2 1 α = α from by simp only [dualOutIdx]; ring,
      restrictToWeight_dualCompMap_omega N α g]
    exact map_smul _ α g
  finrank := by
    intro α
    haveI := N.finrank α
    show FiniteDimensional ℂ
      (↥(LinearMap.range (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α)))
    haveI : FiniteDimensional ℂ (Module.Dual ℂ (N.weight α)) := inferInstance
    infer_instance
  boundedBelow := by
    obtain ⟨B, hB⟩ := N.boundedBelow
    refine ⟨B, fun α hα => hB α (fun hNbot => hα ?_)⟩
    show LinearMap.range (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) = ⊥
    rw [LinearMap.range_eq_bot]
    refine LinearMap.ext (fun g => ?_)
    rw [dual_eq_zero_of_weight_bot N hNbot g]
    exact map_zero _

/-- Sanity: the graded contragredient's underlying weak module is `contragredientWeakModule`. -/
theorem contragredientOrdVModule_toWeakModule (N : OrdVModule W M) (hJac : ContragredientJacobi N) :
    (contragredientOrdVModule N hJac).toWeakModule = contragredientWeakModule N hJac := rfl

/-- **The contragredient module** `M* = ⨁_α (M_α)*` as a graded `𝒱`-module (Gannon §5.3.1,
eq. 5.1.11a) — the public name. The transpose action twisted by `e^{zL₁}(−z⁻²)^{L₀}`, assembled
from the proved `dualModeEndo` engine (`Modules.ContragredientAction`) with the full graded
structure of `contragredientOrdVModule`. The only hypothesis it consumes is the module Jacobi
`ContragredientJacobi N` (the module-level FHL/`ι_z` full-invariance — see the file header);
it is **not** an axiom. Definitionally `contragredientOrdVModule N hJac`. -/
noncomputable def contragredient (N : OrdVModule W M) (hJac : ContragredientJacobi N) :
    OrdVModule W (RestrictedDual N) := contragredientOrdVModule N hJac

/-- The contragredient's weight space is `(M*)_α = (M_α)*` (same graded data as the dual). -/
@[simp] theorem contragredient_weight (N : OrdVModule W M) (hJac : ContragredientJacobi N) (α : ℂ) :
    (contragredient N hJac).weight α = RestrictedDual.weight N α := rfl

end VOA
