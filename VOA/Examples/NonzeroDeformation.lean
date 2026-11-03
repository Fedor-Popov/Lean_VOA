/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationGraded
import VOA.Core.RigidityBridge
import VOA.Examples.LeeYangGram
import VOA.Examples.FreeBosonGeneralC

/-!
# First-order deformations with `Y₁ ≠ 0`: giving the deformation layer an inhabitant

## Why this file exists

Before it, `Deform.zeroDeformation` was the **only** `Deform.FirstOrderDeformation` the repository
could construct (`grep -rn 'Y1 :=' VOA/` returned one hit, `Y1 := 0`).  Every theorem
gated on a hypothesis about a deformation was therefore true but empty, and
`RigidBridge.shapForm₁_zeroDeformation` was the only computation of the deformed Shapovalov form.
This file constructs deformations that are not zero, and then says precisely — and, where the
news is bad, loudly — what they do and do not buy.

## What is built

Everything comes from one construction, the **coboundary cochain**
`δφ(u,z) = Y(φu,z) − φ∘Y(u,z) + Y(u,z)∘φ` of a linear `φ : 𝒱 →ₗ[ℂ] 𝒱`.

**The key structural observation** (`deltaCochain_mem_cocycles`).  All four first-order axioms
of `δφ` — truncation, `Y₁(𝟙,z) = 0`, creation and the order-`t` Jacobi identity — hold for
**every** `φ` with `φ𝟙 = 0`.  Grade-preservation of `φ` is never used.  `Core.DeformationGraded`
proves this only through `coboundaries_le_cocycles`, whose hypothesis `Deform.IsCoboundary`
*bundles* grade-preservation; the proofs there discard it (`obtain ⟨φ, -, -, hφ⟩`).  Re-proving
the Jacobi axiom without that hypothesis (`jacobiAx_deltaCochain`, a transcription of
`Deform.jacobiAx_of_isCoboundary`) is what makes §7 possible.

Two instances:

* `scalingDeformation W = δL₀`.  Since `L₀` is grade-preserving and kills the vacuum this is
  `IsTrivial`, but it is **not zero**: on homogeneous vectors `u¹₍ₙ₎v = (n+1)·u₍ₙ₎v`
  (`smul₁_scalingDeformation_homog`), the mode-diagonal deformation `Y₁ = −z∂_z Y`.  ⚠ It is the
  *only* mode-diagonal one: `u¹₍ₙ₎v = g(n)·u₍ₙ₎v` forces `g(a)+g(b)` to depend only on `a+b`
  (Jacobi) and `g(-1) = 0` (vacuum), hence `g(n) = α(n+1)`.
* `l1Deformation W = δL₁`.  `L₁` kills the vacuum but *lowers the weight by one*, so `δL₁`
  is a first-order deformation that is **not graded**, hence — by `isGraded_of_isTrivial` — **not
  trivial**.  Consequently `¬ Deform.IsRigid (virasoroVOA c)`.

## ⚠ The three honest caveats

1. **`scalingDeformation` is `IsTrivial`.**  It defeats the vacuity of "there is a nonzero `Y₁`"
   and of `shapForm₁` (`shapForm₁_scaling_leeYang_ne_zero` computes a nonzero value of the
   deformed Shapovalov form).  It does **not** give a rigidity theorem content.
2. **§8 of `Core.RigidityBridge` is without content**, for a proved reason, not a
   suspected one.  `shapForm₁_self_eq_zero_of_isTrivial`: for *every* trivial graded
   deformation the deformed self-pairing vanishes on the radical of `shapForm`.  So the operative
   hypothesis `hself : shapForm₁ D hD hvac k s s ≠ 0` is satisfiable only by a **non-trivial
   graded** deformation, and the repository has none: `l1Deformation` is non-trivial but ungraded,
   and `shapForm₁` cannot be applied to it at all (it requires `hD : D.IsGraded`).
3. **`¬ IsRigid` is a statement about the definitions, not about `V(c,0)`.**  It records an
   asymmetry: the cocycle condition ignores the grading while `IsCoboundary` insists on it, so
   `IsRigid` compares a large space of cocycles with a small space of coboundaries.  Recommended
   repair: make `IsGraded` a field of `FirstOrderDeformation`, or define rigidity as "every
   *graded* first-order deformation is trivial".  Until then `Deform.IsRigid` is false for
   essentially every VOA and `IsRigid`-shaped goals should not be pursued.

## ⚠ Two routes that do **not** work, with the reason

* **The background-charge family** `Examples/FreeBosonGeneralC.freeBosonVOA λ` (the first
  candidate).  It is a genuine one-parameter family of VOAs, but not of vertex *algebras*:
  its entire `toPreVertexAlgebra`, `Y` included, is transported verbatim from `heisenbergVOA 1` and
  is `λ`-independent (`freeBosonVOA_toPreVertexAlgebra`).  Only `conformalVector`, `centralCharge`
  and VOA1 move.  Since `FirstOrderDeformation` deforms `Y` and nothing else, `∂λ Y = 0`:
  the family contributes only the zero cochain.  Recorded as `freeBosonVOA_Y_indep_of_lam`.
* **The Virasoro family in `c`.**  Here `Y` really does depend on `c`, but the *carrier* does
  too — `virasoroVOA c : VertexOperatorAlgebra (VirUniv c)` with `VirUniv c = UVir ⧸ vacIdeal c`.
  The `c`-derivative of `Y` is not even type-correct without first trivialising the family of
  carriers, which the repository does not do.  Not formalised; stated here as the reason.

## Main results

* `deltaCochain`, `jacobiAx_deltaCochain`, `deltaCochain_mem_cocycles`, `deformOf` — a
  first-order deformation from any `φ` with `φ𝟙 = 0`.
* `isGraded_of_isTrivial`, `not_isTrivial_of_not_isGraded` — triviality forces gradedness.
* `smul₁_scalingDeformation_homog` — `u¹₍ₙ₎v = (n+1)·u₍ₙ₎v`.
* `scalingDeformation_Y1_ne_zero`, `exists_nonzero_deformation` — a nonzero `Y₁` on `V(c,0)`.
* `isTrivial_scalingDeformation`, `isGraded_scalingDeformation`.
* `shapForm₁_scaling` — `⟨a,b⟩¹ₖ = 2k·⟨a,b⟩ₖ`; `shapForm₁_scaling_leeYang_ne_zero`.
* `shapForm₁_self_eq_zero_of_isTrivial` — the §8 hypothesis is unsatisfiable for trivial `D`.
* `not_isGraded_l1Deformation`, `not_isTrivial_l1Deformation`, `not_isRigid_virasoroVOA`.
* ⚠ `freeBosonVOA_Y_indep_of_lam` — the background-charge route is a dead end.

## Status
Complete and `sorry`-free / `admit`-free / `native_decide`-free; no new axioms, and
`VOA.pbw` is not used (`L3vac_ne_zero`, the only external non-vanishing input, is
`pbw`-free).

## Dependencies
`Core.DeformationGraded` (`cocycles`, `ofCocycle`, `jacL`/`jacR` and their Leibniz identities),
`Core.RigidityBridge` (`shapForm`, `shapForm₁`), `Examples.LeeYangGram` (and through it
`Examples.LeeYangRigidity`, `Examples.LeeYangSingular`: `virasoroVOA_L_eq_Lop`, `L3vac_ne_zero`,
`Lop_one_L2vac`, `Lop_one_L4vac`, `leeYangGram_L4vac`), `Examples.FreeBosonGeneralC`.
-/

namespace VOA

namespace NonzeroDeform

open Module (End)
open Deform

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  Pointwise access to the module structure of `FormalDist` -/

/-- `FormalDist 𝒲` is an opaque synonym for `ℤ → 𝒲`, so `Pi.add_apply` does not fire on it;
this records that its addition is pointwise. -/
@[simp] theorem dist_add_apply {𝒲 : Type*} [AddCommGroup 𝒲] (f g : FormalDist 𝒲) (k : ℤ) :
    (f + g) k = f k + g k := rfl

/-- Subtraction on `FormalDist` is pointwise. -/
@[simp] theorem dist_sub_apply {𝒲 : Type*} [AddCommGroup 𝒲] (f g : FormalDist 𝒲) (k : ℤ) :
    (f - g) k = f k - g k := rfl

/-- Scalar multiplication on `FormalDist` is pointwise. -/
@[simp] theorem dist_smul_apply {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (c : ℂ)
    (f : FormalDist 𝒲) (k : ℤ) : (c • f) k = c • f k := rfl

/-! ## §2  The coboundary cochain `δφ` -/

/-- The **coboundary cochain** `δφ`, built from a linear map `φ : 𝒱 →ₗ[ℂ] 𝒱`:
`(δφ)(u,z) := Y(φu,z) − φ∘Y(u,z) + Y(u,z)∘φ`, coefficient by coefficient. -/
def deltaCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) : Deform.Cochain 𝒱 where
  toFun u := fun k => W.Y (φ u) k - φ * (W.Y u k) + (W.Y u k) * φ
  map_add' u₁ u₂ := by
    refine FormalDist.ext fun k => ?_
    change W.Y (φ (u₁ + u₂)) k - φ * (W.Y (u₁ + u₂) k) + (W.Y (u₁ + u₂) k) * φ
      = (fun k => W.Y (φ u₁) k - φ * (W.Y u₁ k) + (W.Y u₁ k) * φ) k
        + (fun k => W.Y (φ u₂) k - φ * (W.Y u₂ k) + (W.Y u₂ k) * φ) k
    simp only [map_add, dist_add_apply, mul_add, add_mul]
    abel
  map_smul' c u := by
    refine FormalDist.ext fun k => ?_
    change W.Y (φ (c • u)) k - φ * (W.Y (c • u) k) + (W.Y (c • u) k) * φ
      = c • (W.Y (φ u) k - φ * (W.Y u k) + (W.Y u k) * φ)
    simp only [map_smul, dist_smul_apply, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

/-- The modes of `δφ` are the coboundary formula `(φu)₍ₙ₎v − φ(u₍ₙ₎v) + u₍ₙ₎(φv)`. -/
theorem cmode_deltaCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) (u : 𝒱) (n : ℤ)
    (v : 𝒱) :
    Deform.cmode (deltaCochain W φ) u n v
      = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v) := rfl

/-- `cmode_deltaCochain` spelled with `mode`, the form the cocycle proofs consume. -/
theorem mode_deltaCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) (u : 𝒱) (n : ℤ)
    (v : 𝒱) :
    mode ((deltaCochain W φ) u) n v
      = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v) := rfl

/-! ### The cocycle conditions need **no hypothesis on `φ` beyond `φ𝟙 = 0`**

`Deform.coboundaries_le_cocycles` proves this only for `φ` that also preserve the grading, because
`Deform.IsCoboundary` *bundles* grade-preservation.  Inspecting the upstream proofs
(`jacobiAx_of_isCoboundary` destructs the hypothesis as `⟨φ, -, -, hφ⟩`; `coboundaries_le_cocycles`
uses only `hφ0` and `hφ`) shows the grading plays no role.  Re-proving it here without that
hypothesis is what makes §8 below — the *non-trivial* deformation — possible. -/

/-- The order-`t` Jacobi identity for `δφ`, for an **arbitrary** linear `φ`. -/
theorem jacobiAx_deltaCochain (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) :
    Deform.JacobiAx W (deltaCochain W φ) := by
  intro u v x ℓ m n
  have hφ := mode_deltaCochain W φ
  have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (Deform.cmode (deltaCochain W φ) u (ℓ + m - i) (W.smul v (n + i) x)
        + W.smul u (ℓ + m - i) (Deform.cmode (deltaCochain W φ) v (n + i) x)
        - negOnePow ℓ •
          (Deform.cmode (deltaCochain W φ) v (ℓ + n - i) (W.smul u (m + i) x)
            + W.smul v (ℓ + n - i) (Deform.cmode (deltaCochain W φ) u (m + i) x)))
      = Deform.jacL W (φ u) v x ℓ m n i + Deform.jacL W u (φ v) x ℓ m n i
          + Deform.jacL W u v (φ x) ℓ m n i - φ (Deform.jacL W u v x ℓ m n i) := by
    intro i
    rw [Deform.cmode_def, Deform.cmode_def, Deform.cmode_def, Deform.cmode_def, hφ, hφ, hφ, hφ]
    exact Deform.jacL_delta W φ u v x ℓ m n i
  have hR : ∀ i : ℤ, cbz m i •
      (W.smul (Deform.cmode (deltaCochain W φ) u (ℓ + i) v) (m + n - i) x
        + Deform.cmode (deltaCochain W φ) (W.smul u (ℓ + i) v) (m + n - i) x)
      = Deform.jacR W (φ u) v x ℓ m n i + Deform.jacR W u (φ v) x ℓ m n i
          + Deform.jacR W u v (φ x) ℓ m n i - φ (Deform.jacR W u v x ℓ m n i) := by
    intro i
    rw [Deform.cmode_def, Deform.cmode_def, hφ, hφ]
    exact Deform.jacR_delta W φ u v x ℓ m n i
  have hLfin₁ := Deform.jacL_support_finite W (φ u) v x ℓ m n
  have hLfin₂ := Deform.jacL_support_finite W u (φ v) x ℓ m n
  have hLfin₃ := Deform.jacL_support_finite W u v (φ x) ℓ m n
  have hLfin₄ := Deform.jacL_support_finite W u v x ℓ m n
  have hRfin₁ := Deform.jacR_support_finite W (φ u) v x ℓ m n
  have hRfin₂ := Deform.jacR_support_finite W u (φ v) x ℓ m n
  have hRfin₃ := Deform.jacR_support_finite W u v (φ x) ℓ m n
  have hRfin₄ := Deform.jacR_support_finite W u v x ℓ m n
  rw [finsum_congr hL, finsum_congr hR,
    finsum_sub_distrib
      (Deform.support_add_finite (Deform.support_add_finite hLfin₁ hLfin₂) hLfin₃)
      (Deform.support_map_finite φ hLfin₄),
    finsum_add_distrib (Deform.support_add_finite hLfin₁ hLfin₂) hLfin₃,
    finsum_add_distrib hLfin₁ hLfin₂,
    finsum_sub_distrib
      (Deform.support_add_finite (Deform.support_add_finite hRfin₁ hRfin₂) hRfin₃)
      (Deform.support_map_finite φ hRfin₄),
    finsum_add_distrib (Deform.support_add_finite hRfin₁ hRfin₂) hRfin₃,
    finsum_add_distrib hRfin₁ hRfin₂,
    ← map_finsum φ hLfin₄, ← map_finsum φ hRfin₄,
    Deform.jacobi_jacL_jacR W (φ u) v x ℓ m n, Deform.jacobi_jacL_jacR W u (φ v) x ℓ m n,
    Deform.jacobi_jacL_jacR W u v (φ x) ℓ m n, Deform.jacobi_jacL_jacR W u v x ℓ m n]

/-- `δφ` is a cocycle for **every** `φ` with `φ𝟙 = 0` — grade-preservation is not needed. -/
theorem deltaCochain_mem_cocycles (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) : deltaCochain W φ ∈ Deform.cocycles W := by
  refine ⟨?_, ?_, ?_, jacobiAx_deltaCochain W φ⟩
  · intro u v
    obtain ⟨N₁, hN₁⟩ := W.toPreVertexAlgebra.smul_eventually_zero (φ u) v
    obtain ⟨N₂, hN₂⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
    obtain ⟨N₃, hN₃⟩ := W.toPreVertexAlgebra.smul_eventually_zero u (φ v)
    refine ⟨max (max N₁ N₂) N₃, fun k hk => ?_⟩
    rw [cmode_deltaCochain, hN₁ k (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk),
      hN₂ k (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk),
      hN₃ k (le_trans (le_max_right _ _) hk), map_zero, sub_zero, add_zero]
  · refine FormalDist.ext fun k => LinearMap.ext fun w => ?_
    have h := mode_deltaCochain W φ W.vacuum (-k - 1) w
    rw [mode_apply, show -(-k - 1) - 1 = k from by ring, hφ0,
      PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_vacuum_left,
      PreVertexAlgebra.smul_vacuum_left] at h
    rw [h]
    split_ifs with hk
    · simp
    · simp
  · intro w k hk
    rw [cmode_deltaCochain, hφ0, PreVertexAlgebra.smul_zero_right, add_zero]
    rcases eq_or_lt_of_le hk with h | h
    · rw [← h, PreVertexAlgebra.smul_vacuum_neg_one, PreVertexAlgebra.smul_vacuum_neg_one, sub_self]
    · rw [W.toPreVertexAlgebra.smul_vacuum_nonneg (φ w) (by omega),
        W.toPreVertexAlgebra.smul_vacuum_nonneg w (by omega), map_zero, sub_self]

/-- **The first-order deformation attached to any `φ` with `φ𝟙 = 0`.** -/
def deformOf (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱} (hφ0 : φ W.vacuum = 0) :
    Deform.FirstOrderDeformation W :=
  Deform.ofCocycle (deltaCochain W φ) (deltaCochain_mem_cocycles W hφ0)

@[simp] theorem deformOf_Y1 (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) : (deformOf W hφ0).Y1 = deltaCochain W φ := rfl

@[simp] theorem smul₁_deformOf (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (deformOf W hφ0).smul₁ u n v
      = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v) := rfl

/-- `δφ` **is** a coboundary — provided `φ` also preserves the grading. -/
theorem isCoboundary_deltaCochain (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    Deform.IsCoboundary W (deltaCochain W φ) :=
  ⟨φ, hφ0, hφg, fun u n v => cmode_deltaCochain W φ u n v⟩

/-- If `φ` preserves the grading, `deformOf` is trivial — by construction. -/
theorem isTrivial_deformOf (W : VertexOperatorAlgebra 𝒱) {φ : 𝒱 →ₗ[ℂ] 𝒱}
    (hφ0 : φ W.vacuum = 0) (hφg : Deform.GradePreserving W φ) :
    (deformOf W hφ0).IsTrivial :=
  isCoboundary_deltaCochain W hφ0 hφg

/-! ### Triviality forces gradedness

The converse direction of the same observation, and the tool that proves non-triviality below:
`Deform.IsCoboundary` demands a **grade-preserving** `φ`, and each of the three terms of `δφ`
then lands in `𝒱_{k+ℓ-n-1}`.  So a deformation that fails `IsGraded` cannot be `IsTrivial`. -/

/-- **Every trivial deformation is graded.** -/
theorem isGraded_of_isTrivial {W : VertexOperatorAlgebra 𝒱}
    (D : Deform.FirstOrderDeformation W) (hD : D.IsTrivial) : D.IsGraded := by
  obtain ⟨φ, -, hφg, hφ⟩ := hD
  intro k ℓ u hu v hv n
  rw [Deform.FirstOrderDeformation.smul₁_def, hφ]
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (W.smul_mem_grading (hφg k u hu) hv n)
      (hφg _ _ (W.smul_mem_grading hu hv n)))
    (W.smul_mem_grading hu (hφg ℓ v hv) n)

/-- Contrapositive: an **ungraded** deformation is non-trivial. -/
theorem not_isTrivial_of_not_isGraded {W : VertexOperatorAlgebra 𝒱}
    (D : Deform.FirstOrderDeformation W) (hD : ¬ D.IsGraded) : ¬ D.IsTrivial :=
  fun h => hD (isGraded_of_isTrivial D h)

/-- Two different weights meet only in `0`: if `x ∈ 𝒱ⱼ ∩ 𝒱ₖ` with `j ≠ k` then `L₀x = jx = kx`,
so `(j−k)x = 0`.  (VOA2 alone; no appeal to `isInternal`.) -/
theorem eq_zero_of_mem_grading_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {j k : ℤ}
    (hjk : j ≠ k) {x : 𝒱} (hj : x ∈ W.grading j) (hk : x ∈ W.grading k) : x = 0 := by
  have h : ((j : ℂ)) • x = ((k : ℂ)) • x := by
    rw [← W.L_zero_grading x hj, ← W.L_zero_grading x hk]
  have hsub : ((j : ℂ) - (k : ℂ)) • x = 0 := by rw [sub_smul, h, sub_self]
  have hne : ((j : ℂ) - (k : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
  exact (smul_eq_zero.mp hsub).resolve_left hne

/-! ## §3  `L₀` is such a `φ` -/

/-- `L₀𝟙 = 0`: the vacuum has weight `0`. -/
theorem L_zero_vacuum (W : VertexOperatorAlgebra 𝒱) : W.L 0 W.vacuum = 0 := by
  rw [W.L_zero_grading W.vacuum W.vacuum_mem]
  simp

/-- `L₀` preserves the grading: on `𝒱ₖ` it is multiplication by `k`. -/
theorem gradePreserving_L_zero (W : VertexOperatorAlgebra 𝒱) :
    Deform.GradePreserving W (W.L 0) := by
  intro k u hu
  rw [W.L_zero_grading u hu]
  exact Submodule.smul_mem _ _ hu

/-! ## §4  The scaling deformation `D_scal = δL₀` -/

/-- **The scaling deformation** `δL₀`, i.e. `Y₁(u,z) = −z ∂_z Y(u,z)`. -/
def scalingDeformation (W : VertexOperatorAlgebra 𝒱) : Deform.FirstOrderDeformation W :=
  deformOf W (L_zero_vacuum W)

@[simp] theorem scalingDeformation_Y1 (W : VertexOperatorAlgebra 𝒱) :
    (scalingDeformation W).Y1 = deltaCochain W (W.L 0) := rfl

/-- The products of the scaling deformation, before using homogeneity. -/
theorem smul₁_scalingDeformation (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (scalingDeformation W).smul₁ u n v
      = W.smul (W.L 0 u) n v - W.L 0 (W.smul u n v) + W.smul u n (W.L 0 v) := rfl

/-- **The closed form.**  On homogeneous vectors the scaling deformation is
`u¹₍ₙ₎v = (n+1)·u₍ₙ₎v`: the weights `a`, `b` and `a+b-n-1` combine to `a − (a+b−n−1) + b = n+1`,
independently of `a` and `b`. -/
theorem smul₁_scalingDeformation_homog (W : VertexOperatorAlgebra 𝒱) {a b : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading b) (n : ℤ) :
    (scalingDeformation W).smul₁ u n v = ((n : ℂ) + 1) • W.smul u n v := by
  rw [smul₁_scalingDeformation, W.L_zero_grading u hu, W.L_zero_grading v hv,
    W.L_zero_grading (W.smul u n v) (W.smul_mem_grading hu hv n),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  push_cast
  module

/-- The scaling deformation satisfies the order-`t` grading axiom VA1. -/
theorem isGraded_scalingDeformation (W : VertexOperatorAlgebra 𝒱) :
    (scalingDeformation W).IsGraded := by
  intro k ℓ u hu v hv n
  rw [smul₁_scalingDeformation_homog W hu hv n]
  exact Submodule.smul_mem _ _ (W.smul_mem_grading hu hv n)

/-- ⚠ **The scaling deformation is `IsTrivial`** — it is `δL₀` by construction. -/
theorem isTrivial_scalingDeformation (W : VertexOperatorAlgebra 𝒱) :
    (scalingDeformation W).IsTrivial :=
  isTrivial_deformOf W (L_zero_vacuum W) (gradePreserving_L_zero W)

/-- The value that will be shown nonzero: `ω¹₍₋₂₎𝟙 = −L₋₃𝟙`. -/
theorem smul₁_scaling_conformal_vacuum (W : VertexOperatorAlgebra 𝒱) :
    (scalingDeformation W).smul₁ W.conformalVector (-2) W.vacuum = - W.L (-3) W.vacuum := by
  rw [smul₁_scalingDeformation_homog W W.conformal_mem W.vacuum_mem (-2)]
  have hL : W.smul W.conformalVector (-2) W.vacuum = W.L (-3) W.vacuum := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show (-3 : ℤ) + 1 = -2 from by norm_num]
  rw [hL]
  norm_num

/-! ## §5  `Y₁ ≠ 0` on a concrete VOA: `Vir(c) = V(c,0)` -/

open VirModule LeeYang in
/-- `ω¹₍₋₂₎|0⟩ = −L₋₃|0⟩` on `V(c,0)`. -/
theorem smul₁_scaling_virasoro (c : ℂ) :
    (scalingDeformation (virasoroVOA c)).smul₁ ((virasoroVOA c).conformalVector) (-2)
        ((virasoroVOA c).vacuum) = - L3vac c := by
  rw [smul₁_scaling_conformal_vacuum]
  congr 1
  rw [virasoroVOA_L_eq_Lop]
  rfl

open VirModule LeeYang in
/-- `ω¹₍₋₂₎|0⟩ ≠ 0`, because `L₋₃|0⟩ ≠ 0` (`LeeYang.L3vac_ne_zero`, `pbw`-free). -/
theorem smul₁_scaling_virasoro_ne_zero (c : ℂ) :
    (scalingDeformation (virasoroVOA c)).smul₁ ((virasoroVOA c).conformalVector) (-2)
        ((virasoroVOA c).vacuum) ≠ 0 := by
  rw [smul₁_scaling_virasoro c, neg_ne_zero]
  exact L3vac_ne_zero c

open VirModule in
/-- **The main theorem.**  `Vir(c) = V(c,0)` carries a first-order deformation whose `Y₁` is
**not** the zero cochain, for every central charge `c`.  Compare `Deform.zeroDeformation`, the
trivial inhabitant of `Deform.FirstOrderDeformation`. -/
theorem scalingDeformation_Y1_ne_zero (c : ℂ) :
    (scalingDeformation (virasoroVOA c)).Y1 ≠ 0 := by
  intro h
  refine smul₁_scaling_virasoro_ne_zero c ?_
  rw [Deform.FirstOrderDeformation.smul₁_def, h]
  simp

open VirModule in
/-- The existence statement in the form the audit asked for: a first-order deformation of a
concrete VOA with nonzero `Y₁`, which is moreover graded. -/
theorem exists_nonzero_deformation (c : ℂ) :
    ∃ D : Deform.FirstOrderDeformation (virasoroVOA c), D.Y1 ≠ 0 ∧ D.IsGraded :=
  ⟨scalingDeformation (virasoroVOA c), scalingDeformation_Y1_ne_zero c,
    isGraded_scalingDeformation _⟩

/-! ## §6  ⚠ What this does **not** buy: the deformed Shapovalov form

For the coboundary `δL₀` the deformed form is a *scalar multiple* of the undeformed one,
`⟨a,b⟩¹ₖ = 2k·⟨a,b⟩ₖ`.  Two consequences, in opposite directions:

* the deformed form is **not identically zero** whenever the undeformed one isn't and `k ≠ 0`,
  so `shapForm₁` is not only ever the zero form (compare `shapForm₁_zeroDeformation`);
* but on the **radical** of `shapForm` — which is exactly where §8 of `Core.RigidityBridge`
  evaluates it — it vanishes identically.  So the operative hypothesis
  `hself : shapForm₁ D hD hvac k s s ≠ 0` is **unsatisfiable** for this `D`, and §8 acquires no
  content from it.  See `shapForm₁_scaling_self_eq_zero_of_mem_radBil`. -/

open RigidBridge in
/-- The deformed Shapovalov vector of `δL₀` is `2k` times the undeformed one. -/
theorem shapVec₁_scaling (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (a b : W.grading k) :
    shapVec₁ (scalingDeformation W) (isGraded_scalingDeformation W) k a b
      = (2 * (k : ℂ)) • shapVec W k a b := by
  refine Subtype.ext ?_
  rw [shapVec₁_coe, Submodule.coe_smul, shapVec_coe,
    smul₁_scalingDeformation_homog W a.2 b.2 (2 * k - 1)]
  congr 1
  push_cast
  ring

open RigidBridge in
/-- **`⟨a,b⟩¹ₖ = 2k·⟨a,b⟩ₖ`** for the scaling deformation. -/
theorem shapForm₁_scaling (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) (k : ℤ)
    (a b : W.grading k) :
    shapForm₁ (scalingDeformation W) (isGraded_scalingDeformation W) hvac k a b
      = (2 * (k : ℂ)) * shapForm W hvac k a b := by
  rw [shapForm₁_apply, shapForm_apply, shapVec₁_scaling, map_smul, smul_eq_mul]

open RigidBridge in
/-- ⚠⚠ **The vacuity result for §8.**  On a radical vector of the undeformed form the deformed
self-pairing of `δL₀` vanishes, so `not_liftable_of_self_pairing_ne_zero` (and every theorem
downstream of it) still cannot be applied with this deformation.  This is not an accident of the
construction: a coboundary is a change of variables, and a change of variables cannot obstruct
anything. -/
theorem shapForm₁_scaling_self_eq_zero_of_mem_radBil (W : VertexOperatorAlgebra 𝒱)
    (hvac : W.vacuum ≠ 0) {k : ℤ} {s : W.grading k}
    (hs : s ∈ DefForm.radBil (shapForm W hvac k)) :
    shapForm₁ (scalingDeformation W) (isGraded_scalingDeformation W) hvac k s s = 0 := by
  rw [shapForm₁_scaling, DefForm.apply_of_mem_radBil hs, mul_zero]

open RigidBridge in
/-- **The general vacuity result for §8.**  For *any* trivial graded deformation — not only
`δL₀` — the deformed self-pairing vanishes on the radical of the undeformed form.

The three terms of `δφ(s,2k−1,s)` are `⟨φs,s⟩ₖ·𝟙`, `φ(⟨s,s⟩ₖ·𝟙)` and `⟨s,φs⟩ₖ·𝟙`; the second and
third vanish because `s` is radical, and the first because `shapForm` is symmetric
(`shapForm_symm`) so `⟨φs,s⟩ₖ = ⟨s,φs⟩ₖ = 0` — here `φs ∈ 𝒱ₖ` uses precisely the
grade-preservation that `IsCoboundary` demands.

⚠ So `hself : shapForm₁ D hD hvac k s s ≠ 0` is satisfiable **only** by a non-trivial `D`.  The
repository does not (yet) possess a non-trivial *graded* one: `l1Deformation` of §7 is
non-trivial but not graded, and `shapForm₁` cannot even be applied to it. -/
theorem shapForm₁_self_eq_zero_of_isTrivial (W : VertexOperatorAlgebra 𝒱)
    (hvac : W.vacuum ≠ 0) (D : Deform.FirstOrderDeformation W) (hD : D.IsGraded)
    (hT : D.IsTrivial) {k : ℤ} {s : W.grading k}
    (hs : s ∈ DefForm.radBil (shapForm W hvac k)) :
    shapForm₁ D hD hvac k s s = 0 := by
  obtain ⟨φ, -, hφg, hφ⟩ := hT
  set t : W.grading k := ⟨φ (s : 𝒱), hφg k (s : 𝒱) s.2⟩ with ht
  have hss : W.smul (s : 𝒱) (2 * k - 1) (s : 𝒱) = 0 :=
    (shapForm_eq_zero_iff hvac s s).mp (DefForm.apply_of_mem_radBil hs s)
  have hst : W.smul (s : 𝒱) (2 * k - 1) (φ (s : 𝒱)) = 0 :=
    (shapForm_eq_zero_iff hvac s t).mp (DefForm.apply_of_mem_radBil hs t)
  have hts : W.smul (φ (s : 𝒱)) (2 * k - 1) (s : 𝒱) = 0 := by
    refine (shapForm_eq_zero_iff hvac t s).mp ?_
    rw [shapForm_symm hvac k t s]
    exact DefForm.apply_of_mem_radBil hs t
  rw [shapForm₁_apply]
  refine (vacCoeff_eq_zero_iff hvac _).mpr ?_
  rw [shapVec₁_coe, Deform.FirstOrderDeformation.smul₁_def, hφ, hss, hts, hst, map_zero]
  abel

open RigidBridge VirModule LeeYang in
/-- …but the deformed form is genuinely nonzero: at Lee–Yang level `4`,
`⟨L₋₄|0⟩, L₋₄|0⟩⟩¹₄ = 8·(−462) = −3696`.  So `shapForm₁` is not always the zero form — the
statement `shapForm₁_zeroDeformation` really was a statement about the zero deformation only. -/
theorem shapForm₁_scaling_leeYang_L4vac :
    shapForm₁ (scalingDeformation (virasoroVOA leeYangC))
        (isGraded_scalingDeformation _) leeYang_vacuum_ne_zero 4
        (L4vec4 leeYangC) (L4vec4 leeYangC) = -3696 := by
  rw [shapForm₁_scaling, leeYangGram_L4vac]
  norm_num

open RigidBridge VirModule LeeYang in
/-- The deformed level-4 Shapovalov form of `V(-22/5,0)` is not the zero form. -/
theorem shapForm₁_scaling_leeYang_ne_zero :
    shapForm₁ (scalingDeformation (virasoroVOA leeYangC))
      (isGraded_scalingDeformation _) leeYang_vacuum_ne_zero 4 ≠ 0 := by
  intro h
  have hg := shapForm₁_scaling_leeYang_L4vac
  rw [h] at hg
  simp only [LinearMap.zero_apply] at hg
  norm_num at hg

/-! ## §7  A **non-trivial** deformation, and `¬ IsRigid`

`Deform.IsCoboundary` requires the field redefinition `φ` to be **grade-preserving**, but
`Deform.FirstOrderDeformation` does **not** require the deformation to be graded (that is the
separate predicate `IsGraded`; see convention 2 in the `Core.Deformation` docstring).  The two
sides of the complex are therefore not taken in the same category, and the mismatch is visible:
`δφ` is a cocycle for *every* `φ` killing the vacuum (§2), while only the grade-preserving ones
produce coboundaries.

`φ = L₁` lowers the weight by one and kills the vacuum, so `δL₁` is a first-order deformation
that is **not graded**, hence **not trivial**, hence `Vir(c)` is **not** `Deform.IsRigid`.

⚠ **Read this correctly.**  It is a true theorem about the repository's definitions, and it does
defeat the vacuity of `IsRigid`/`IsTrivial` (both have a witness on each side).  It is *not*
evidence that `V(c,0)` has interesting deformations in the usual sense: `δL₁` is `δ` of something,
just of something that moves the grading.  The mathematically standard statement — every
*graded* first-order deformation is trivial — is untouched by this, and the honest reading is that
`Deform.IsRigid` as currently stated quantifies over a strictly larger class of cocycles than the
class of coboundaries it allows to kill them.  See `not_isRigid_virasoroVOA`. -/

/-- `L₁𝟙 = 0`: VA3 with `n = 2 ≥ 0`. -/
theorem L_one_vacuum (W : VertexOperatorAlgebra 𝒱) : W.L 1 W.vacuum = 0 :=
  W.toPreVertexAlgebra.smul_vacuum_nonneg W.conformalVector (by norm_num : (0 : ℤ) ≤ 1 + 1)

/-- **The `L₁` deformation** `δL₁`. -/
def l1Deformation (W : VertexOperatorAlgebra 𝒱) : Deform.FirstOrderDeformation W :=
  deformOf W (L_one_vacuum W)

@[simp] theorem l1Deformation_Y1 (W : VertexOperatorAlgebra 𝒱) :
    (l1Deformation W).Y1 = deltaCochain W (W.L 1) := rfl

theorem smul₁_l1Deformation (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (l1Deformation W).smul₁ u n v
      = W.smul (W.L 1 u) n v - W.L 1 (W.smul u n v) + W.smul u n (W.L 1 v) := rfl

open VirModule LeeYang in
/-- `ω¹₍₋₃₎|0⟩ = −5·L₋₃|0⟩` for `δL₁` on `V(c,0)`: `L₁ω = 0` and `L₁L₋₄|0⟩ = 5L₋₃|0⟩`. -/
theorem smul₁_l1_virasoro (c : ℂ) :
    (l1Deformation (virasoroVOA c)).smul₁ ((virasoroVOA c).conformalVector) (-3)
        ((virasoroVOA c).vacuum) = -((5 : ℂ) • L3vac c) := by
  have hom : ((virasoroVOA c).conformalVector) = L2vac c := rfl
  have hL1om : (virasoroVOA c).L 1 ((virasoroVOA c).conformalVector) = 0 := by
    rw [virasoroVOA_L_eq_Lop, hom]
    exact Lop_one_L2vac c
  have hsm : (virasoroVOA c).smul ((virasoroVOA c).conformalVector) (-3)
      ((virasoroVOA c).vacuum) = L4vac c := by
    rw [PreVertexAlgebra.smul_def, show (-3 : ℤ) = (-4 : ℤ) + 1 from by norm_num,
      ← VertexOperatorAlgebra.L_def, virasoroVOA_L_eq_Lop]
    rfl
  rw [smul₁_l1Deformation, hL1om, hsm, L_one_vacuum, PreVertexAlgebra.smul_zero_left,
    PreVertexAlgebra.smul_zero_right, virasoroVOA_L_eq_Lop, Lop_one_L4vac]
  abel

open VirModule LeeYang in
/-- `L₋₃|0⟩` has weight `3`: it is `ω₍₋₂₎|0⟩`, and `2 + 0 − (−2) − 1 = 3`. -/
theorem L3vac_mem_grading (c : ℂ) : L3vac c ∈ (virasoroVOA c).grading 3 := by
  have h := (virasoroVOA c).smul_mem_grading (virasoroVOA c).conformal_mem
    (virasoroVOA c).vacuum_mem (-2)
  rw [show (2 : ℤ) + 0 - (-2) - 1 = 3 from by norm_num] at h
  have hsm : (virasoroVOA c).smul ((virasoroVOA c).conformalVector) (-2)
      ((virasoroVOA c).vacuum) = L3vac c := by
    rw [PreVertexAlgebra.smul_def, show (-2 : ℤ) = (-3 : ℤ) + 1 from by norm_num,
      ← VertexOperatorAlgebra.L_def, virasoroVOA_L_eq_Lop]
    rfl
  rwa [hsm] at h

open VirModule LeeYang in
/-- **`δL₁` is not graded**: `ω¹₍₋₃₎|0⟩` has weight `3`, but VA1 at order `t` would put it in
weight `2 + 0 − (−3) − 1 = 4`. -/
theorem not_isGraded_l1Deformation (c : ℂ) : ¬ (l1Deformation (virasoroVOA c)).IsGraded := by
  intro hg
  have h4 := hg 2 0 _ (virasoroVOA c).conformal_mem _ (virasoroVOA c).vacuum_mem (-3)
  rw [show (2 : ℤ) + 0 - (-3) - 1 = 4 from by norm_num, smul₁_l1_virasoro] at h4
  have h4' : (5 : ℂ) • L3vac c ∈ (virasoroVOA c).grading 4 := by
    simpa using Submodule.neg_mem _ h4
  have h3 : (5 : ℂ) • L3vac c ∈ (virasoroVOA c).grading 3 :=
    Submodule.smul_mem _ _ (L3vac_mem_grading c)
  have hz := eq_zero_of_mem_grading_of_mem_grading (virasoroVOA c)
    (by norm_num : (3 : ℤ) ≠ 4) h3 h4'
  exact L3vac_ne_zero c ((smul_eq_zero.mp hz).resolve_left (by norm_num))

open VirModule in
/-- **A non-trivial first-order deformation of `V(c,0)`.** -/
theorem not_isTrivial_l1Deformation (c : ℂ) : ¬ (l1Deformation (virasoroVOA c)).IsTrivial :=
  not_isTrivial_of_not_isGraded _ (not_isGraded_l1Deformation c)

open VirModule in
/-- Its `Y₁` is nonzero too (a trivial consequence: the zero cochain is a coboundary). -/
theorem l1Deformation_Y1_ne_zero (c : ℂ) : (l1Deformation (virasoroVOA c)).Y1 ≠ 0 := by
  intro h
  refine not_isTrivial_l1Deformation c ?_
  change Deform.IsCoboundary (virasoroVOA c) ((l1Deformation (virasoroVOA c)).Y1)
  rw [h]
  exact Deform.isCoboundary_zero _

open VirModule in
/-- **`Vir(c)` is not `Deform.IsRigid`**, for every central charge `c`.

⚠ The caveat in the section docstring applies: what this exhibits is the asymmetry between the
cocycle condition (which does not see the grading) and `IsCoboundary` (which insists on it), not a
genuine deformation of the vertex-algebra structure of `V(c,0)`.  Recommended repair: either add
`IsGraded` as a field of `FirstOrderDeformation`, or define rigidity as "every **graded**
first-order deformation is trivial". -/
theorem not_isRigid_virasoroVOA (c : ℂ) : ¬ Deform.IsRigid (virasoroVOA c) :=
  fun h => not_isTrivial_l1Deformation c (h (l1Deformation (virasoroVOA c)))

/-! ## §8  ⚠ Why the background-charge family is **not** a route to a nonzero `Y₁`

Candidate (A) is `Examples/FreeBosonGeneralC.freeBosonVOA λ`, a one-parameter
family of VOAs.  It is a genuine family — the central charge `1 − 12λ²` is surjective onto `ℂ` —
but it is **not** a family of vertex-algebra structures: the whole `toPreVertexAlgebra`, `Y`
included, is transported verbatim from `heisenbergVOA 1` and does not depend on `λ`.  Only
`conformalVector`, `centralCharge` and the Virasoro axiom move.  Since `FirstOrderDeformation`
deforms `Y` and nothing else, `∂λ Y = 0` and the family contributes only the zero cochain. -/

/-- ⚠ **Route (A) is a dead end**: `Y` is literally `λ`-independent in the background-charge
family, so its `λ`-derivative — the candidate `Y₁` — is zero. -/
theorem freeBosonVOA_Y_indep_of_lam (lam mu : ℂ) :
    (FBgc.freeBosonVOA lam).Y = (FBgc.freeBosonVOA mu).Y := rfl

end NonzeroDeform

end VOA
