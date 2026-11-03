/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUBalFullPiece
import VOA.Modules.ZhuVermaAnArchBottomDefectClose
import VOA.Modules.ZhuRingInstance
import Mathlib.Algebra.DirectSum.Module

/-!
# The `A(𝒱)`-balanced generalized-Verma carrier on DJ's genuine ideal, and its bottom

`ZhuVermaAnArchMUBalFullPiece` built the balanced level-`n` pieces
`MUPieceBalFull W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U` over Dong–Jiang's FULL ideal `OnmFull`, together with
the descended mode operators `oBalFullU` (the balanced-bottom surgery).  This file assembles

  `MUBalFull W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`

with its `ℕ`-grading and the `𝒱`-modes `a_p`, and then identifies the **bottom**.

## Contents (axiom-clean, pbw-free)

* **`MUBalFull W U`**, `.incl`, `.proj`, `.deg`, `.isInternal_deg` — the balanced graded carrier.
* **`oBalLevelIncl` / `muBalFullMode` / `muBalFullYM`** — DJ's `u_p` and `Y_{M(U)}(u,z)` on the
  balanced carrier, with the lower truncation `muBalFullMode_truncation` (DJ Lemma 4.6(1)) and
  `muBalFullMode_vacuum` (DJ Lemma 4.6(2)).
* **STEP 3, the bottom.**  Under the explicitly named Gate hypothesis `hcol : OnmFull W 0 0 ≤ O W`
  (equivalently `OnmFull W 0 0 = O W`, `onmFull_zero_zero_eq_O_of_le` — the `OnmCollapses W 0`
  statement, NOT proved in this repo), the level-`0` action map `piece0ToUFull` is well defined, its
  kernel is exactly the balancing (`balancingFull_zero_eq_ker`), and hence
  `muPieceBalFull0EquivU : MUPieceBalFull W U 0 ≃ₗ[ℂ] U.carrier` — the genuine DJ bottom
  `M(U)(0) ≅ U`, unlike the ℂ-tensor bottom `A(𝒱) ⊗_ℂ U`, strictly larger when `dim A(𝒱) > 1`
  (`qInjOnBottom_false_of_balancing_ne_bot`).
* **`muBalFullBottomEquivA`** — the payoff: the bottom isomorphism is `A(𝒱)`-**linear**, for the
  genuine left Zhu-multiplication action `leftMulBalFull` on the balanced bottom and the `AMod`
  action on `U`.  The action facts `leftMulBalFull_mem_O` / `_vacuum` / `_mul` say precisely that
  `leftMulBalFull` is an `A(𝒱)`-module structure.

pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), §2, §4 (Lemma 4.1, Lemma 4.6, Thm 4.13);
Gannon §5.3.2, Thm 5.3.4.  Cross-ref `ZhuVermaAnArchMUBal` (the prime-ideal
template), `ZhuVermaAnArchMUBalancedBottomA` (the `n = 0` `A(𝒱)`-linear template).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## STEP 1 (continued) — the balanced graded carrier -/

/-- **The `A(𝒱)`-balanced Dong–Jiang induced-module carrier on the GENUINE ideal**
`MUBalFull W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`. -/
abbrev MUBalFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Type u :=
  ⨁ n : ℕ, MUPieceBalFull W U n

/-- The canonical inclusion of the balanced level-`n` piece into `MUBalFull W U`. -/
noncomputable def MUBalFull.incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPieceBalFull W U n →ₗ[ℂ] MUBalFull W U :=
  DirectSum.lof ℂ ℕ (MUPieceBalFull W U) n

/-- The canonical projection of `MUBalFull W U` onto the balanced level-`n` piece. -/
noncomputable def MUBalFull.proj (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUBalFull W U →ₗ[ℂ] MUPieceBalFull W U n :=
  DirectSum.component ℂ ℕ (MUPieceBalFull W U) n

/-- The level projections are idempotent on their own level. -/
@[simp] theorem MUBalFull.proj_incl_same (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (x : MUPieceBalFull W U n) : MUBalFull.proj W U n (MUBalFull.incl W U n x) = x :=
  DirectSum.component.lof_self ℂ n x

/-- The level projections annihilate the other levels. -/
theorem MUBalFull.proj_incl_ne (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n k : ℕ} (h : n ≠ k)
    (x : MUPieceBalFull W U k) : MUBalFull.proj W U n (MUBalFull.incl W U k x) = 0 := by
  rw [MUBalFull.proj, MUBalFull.incl, DirectSum.component.of]
  exact dif_neg (Ne.symm h)

/-- The balanced level-`n` graded subspace of `MUBalFull W U` (the range of `incl n`). -/
noncomputable def MUBalFull.deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MUBalFull W U) := LinearMap.range (MUBalFull.incl W U n)

/-- **The `ℕ`-grading of `MUBalFull W U` is a genuine internal direct-sum decomposition**
(`M(U) = ⊕ₙ M(U)(n)` on the `A(𝒱)`-balanced full-ideal carrier). -/
theorem MUBalFull.isInternal_deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    DirectSum.IsInternal (MUBalFull.deg W U) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hproj_sup : ∀ (n : ℕ) (z : MUBalFull W U),
      z ∈ (⨆ (j : ℕ) (_ : j ≠ n), MUBalFull.deg W U j) → MUBalFull.proj W U n z = 0 := by
    intro n z hz
    refine Submodule.iSup_induction _ (motive := fun w => MUBalFull.proj W U n w = 0) hz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro j z hjz
    refine Submodule.iSup_induction _ (motive := fun w => MUBalFull.proj W U n w = 0) hjz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro hjn w hw
    obtain ⟨v, rfl⟩ := hw
    exact MUBalFull.proj_incl_ne W U (Ne.symm hjn) v
  constructor
  · refine iSupIndep_def.mpr (fun n => ?_)
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨⟨y, rfl⟩, hxsup⟩
    rw [Submodule.mem_bot]
    have h0 : MUBalFull.proj W U n (MUBalFull.incl W U n y) = 0 := hproj_sup n _ hxsup
    rw [MUBalFull.proj_incl_same] at h0
    rw [h0, map_zero]
  · rw [eq_top_iff]
    intro x _
    refine DirectSum.induction_on x (Submodule.zero_mem _) ?_
      (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro n y
    exact Submodule.mem_iSup_of_mem n ⟨y, rfl⟩

/-! ## The `𝒱`-modes `a_p` on the balanced carrier -/

/-- **The level-`n` component of the balanced mode `a_p`** (`a` homogeneous of weight `k`), landing
in level `k − p − 1 + n` when that is `≥ 0` and `0` otherwise (Dong–Jiang's case split). -/
noncomputable def oBalLevelIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ)
    (a : 𝒱) : MUPieceBalFull W U n →ₗ[ℂ] MUBalFull W U :=
  if 0 ≤ muTargetLevel k p n then
    (MUBalFull.incl W U (muTargetLevel k p n).toNat).comp
      (oBalFullU W U (muTargetLevel k p n).toNat n a)
  else 0

/-- Below the DJ threshold the level component vanishes. -/
theorem oBalLevelIncl_of_neg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n : ℕ}
    (h : muTargetLevel k p n < 0) (a : 𝒱) : oBalLevelIncl W U k p n a = 0 := by
  simp only [oBalLevelIncl, if_neg (not_le.mpr h)]

/-- Above the DJ threshold the level component is the balanced mode into the target level. -/
theorem oBalLevelIncl_of_nonneg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n : ℕ}
    (h : 0 ≤ muTargetLevel k p n) (a : 𝒱) :
    oBalLevelIncl W U k p n a
      = (MUBalFull.incl W U (muTargetLevel k p n).toNat).comp
          (oBalFullU W U (muTargetLevel k p n).toNat n a) := by
  simp only [oBalLevelIncl, if_pos h]

/-- The level component with the target level named explicitly. -/
theorem oBalLevelIncl_eq_of_target (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n N : ℕ}
    (h : muTargetLevel k p n = (N : ℤ)) (a : 𝒱) :
    oBalLevelIncl W U k p n a = (MUBalFull.incl W U N).comp (oBalFullU W U N n a) := by
  have hA : (muTargetLevel k p n).toNat = N := by rw [h]; exact Int.toNat_natCast N
  have hnn : 0 ≤ muTargetLevel k p n := by rw [h]; positivity
  subst hA
  exact oBalLevelIncl_of_nonneg W U hnn a

/-- The level component is additive in the acting vector. -/
theorem oBalLevelIncl_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ)
    (a b : 𝒱) :
    oBalLevelIncl W U k p n (a + b) = oBalLevelIncl W U k p n a + oBalLevelIncl W U k p n b := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [oBalLevelIncl_of_nonneg W U h, oBalLevelIncl_of_nonneg W U h,
      oBalLevelIncl_of_nonneg W U h, oBalFullU_add_acting]
    exact LinearMap.comp_add _ _ _
  · rw [oBalLevelIncl_of_neg W U (not_le.mp h), oBalLevelIncl_of_neg W U (not_le.mp h),
      oBalLevelIncl_of_neg W U (not_le.mp h), add_zero]

/-- The level component is homogeneous in the acting vector. -/
theorem oBalLevelIncl_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ)
    (c : ℂ) (a : 𝒱) :
    oBalLevelIncl W U k p n (c • a) = c • oBalLevelIncl W U k p n a := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [oBalLevelIncl_of_nonneg W U h, oBalLevelIncl_of_nonneg W U h, oBalFullU_smul_acting]
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  · rw [oBalLevelIncl_of_neg W U (not_le.mp h), oBalLevelIncl_of_neg W U (not_le.mp h), smul_zero]

/-- **The balanced mode `a_p` for `a` homogeneous of weight `k`**, assembled from the level
components by the universal property of the direct sum. -/
noncomputable def muBalFullModeFamily (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] Module.End ℂ (MUBalFull W U) where
  toFun ak := DirectSum.toModule ℂ ℕ (MUBalFull W U) (fun n => oBalLevelIncl W U k p n (ak : 𝒱))
  map_add' a b := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, DirectSum.toModule_lof,
      Submodule.coe_add, oBalLevelIncl_add_acting]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.toModule_lof,
      SetLike.val_smul, oBalLevelIncl_smul_acting, RingHom.id_apply, LinearMap.smul_apply]

/-- **The balanced mode `a_p`** for arbitrary `a ∈ 𝒱`, extended over the grade decomposition. -/
noncomputable def muBalFullMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (a : 𝒱) :
    Module.End ℂ (MUBalFull W U) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (muBalFullModeFamily W U p)) (DirectSum.decompose W.grading a)

/-- On a homogeneous `a ∈ 𝒱_k` the balanced mode collapses to the single weight-`k` slice. -/
theorem muBalFullMode_homogeneous (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) {k : ℤ}
    {a : 𝒱} (ha : a ∈ W.grading k) :
    muBalFullMode W U p a = DirectSum.toModule ℂ ℕ (MUBalFull W U)
      (fun n => oBalLevelIncl W U k p n a) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : muBalFullMode W U p a = muBalFullModeFamily W U p k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (muBalFullModeFamily W U p)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (muBalFullModeFamily W U p) k ⟨a, ha⟩
  rw [hcollapse]; rfl

/-- The balanced mode is additive in the acting vector. -/
theorem muBalFullMode_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (a b : 𝒱) :
    muBalFullMode W U p (a + b) = muBalFullMode W U p a + muBalFullMode W U p b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (muBalFullModeFamily W U p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) a b

/-- The balanced mode is homogeneous in the acting vector. -/
theorem muBalFullMode_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (c : ℂ)
    (a : 𝒱) : muBalFullMode W U p (c • a) = c • muBalFullMode W U p a := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (muBalFullModeFamily W U p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c a

/-- The zero vector acts by zero. -/
@[simp] theorem muBalFullMode_zero_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) :
    muBalFullMode W U p (0 : 𝒱) = 0 := by
  have := muBalFullMode_smul_acting W U p (0 : ℂ) (0 : 𝒱)
  simpa using this

/-- Endomorphisms of `MUBalFull W U` agreeing on every level piece are equal. -/
theorem muBalFull_end_ext (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    {f g : Module.End ℂ (MUBalFull W U)}
    (h : ∀ (n : ℕ) (x : MUPieceBalFull W U n),
      f (MUBalFull.incl W U n x) = g (MUBalFull.incl W U n x)) : f = g :=
  DirectSum.linearMap_ext ℂ (fun n => LinearMap.ext (fun x => h n x))

/-- The balanced mode on a homogeneous level-`n` vector: DJ's defining formula. -/
theorem muBalFullMode_apply_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) {k : ℤ}
    {a : 𝒱} (ha : a ∈ W.grading k) (n : ℕ) (x : MUPieceBalFull W U n) :
    muBalFullMode W U p a (MUBalFull.incl W U n x) = oBalLevelIncl W U k p n a x := by
  rw [muBalFullMode_homogeneous W U p ha]
  exact DirectSum.toModule_lof ℂ n x

/-- The balanced mode annihilates the level-`n` piece once `p ≥ k + n`. -/
theorem muBalFullMode_incl_eq_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) {n : ℕ} (hp : k + (n : ℤ) ≤ p) (x : MUPieceBalFull W U n) :
    muBalFullMode W U p a (MUBalFull.incl W U n x) = 0 := by
  rw [muBalFullMode_apply_incl W U p ha n x]
  have hneg : muTargetLevel k p n < 0 := by
    simp only [muTargetLevel]; omega
  rw [oBalLevelIncl_of_neg W U hneg]
  rfl

/-- **DJ Lemma 4.6(1) on the balanced carrier** — lower truncation, so each `Y(u,z)` is a field. -/
theorem muBalFullMode_truncation (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (u : 𝒱)
    (x : MUBalFull W U) : ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muBalFullMode W U p u x = 0 := by
  refine reduce_homogeneous W (P := fun u => ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muBalFullMode W U p u x = 0)
    ?_ ?_ ?_ u
  · intro k a ha
    have key : ∀ y : MUBalFull W U, ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muBalFullMode W U p a y = 0 := by
      intro y
      refine DirectSum.induction_on y ⟨0, fun p _ => map_zero _⟩ ?_ ?_
      · intro n z
        exact ⟨k + (n : ℤ), fun p hp => muBalFullMode_incl_eq_zero W U ha hp z⟩
      · rintro y₁ y₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨max N₁ N₂, fun p hp => ?_⟩
        rw [map_add, h₁ p (le_trans (le_max_left _ _) hp), h₂ p (le_trans (le_max_right _ _) hp),
          add_zero]
    exact key x
  · exact ⟨0, fun p _ => by rw [muBalFullMode_zero_acting]; rfl⟩
  · rintro u₁ u₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun p hp => ?_⟩
    rw [muBalFullMode_add_acting, LinearMap.add_apply, h₁ p (le_trans (le_max_left _ _) hp),
      h₂ p (le_trans (le_max_right _ _) hp), add_zero]

/-- **DJ Lemma 4.6(2) on the balanced carrier** — `𝟙_p = δ_{p,−1}·id`. -/
theorem muBalFullMode_vacuum (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) :
    muBalFullMode W U p W.vacuum = if p = -1 then (1 : Module.End ℂ (MUBalFull W U)) else 0 := by
  rw [muBalFullMode_homogeneous W U p (vacuum_mem_grading_zero W)]
  refine DirectSum.linearMap_ext ℂ (fun n => ?_)
  refine LinearMap.ext (fun x => ?_)
  rw [LinearMap.comp_apply, DirectSum.toModule_lof]
  by_cases hp : p = -1
  · subst hp
    have hT : muTargetLevel 0 (-1) n = (n : ℤ) := by simp only [muTargetLevel]; ring
    rw [oBalLevelIncl_eq_of_target W U hT, if_pos rfl, LinearMap.comp_apply,
      oBalFullU_vacuum_diag W U n]
    rfl
  · rw [if_neg hp]
    by_cases hT : 0 ≤ muTargetLevel 0 p n
    · have hEq : muTargetLevel 0 p n = (((muTargetLevel 0 p n).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg hT).symm
      have hne : (muTargetLevel 0 p n).toNat ≠ n := by
        simp only [muTargetLevel] at hT ⊢
        omega
      rw [oBalLevelIncl_eq_of_target W U hEq, LinearMap.comp_apply,
        oBalFullU_vacuum_offdiag W U hne]
      simp
    · rw [oBalLevelIncl_of_neg W U (not_le.mp hT)]
      simp

/-- **`Y_{M(U)}(u,z) = ∑_p u_p z^{−p−1}` on the balanced carrier.** -/
noncomputable def muBalFullYM (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    𝒱 →ₗ[ℂ] (Module.End ℂ (MUBalFull W U))⟦z^±⟧ where
  toFun a := fun j => muBalFullMode W U (-j - 1) a
  map_add' a b := by
    funext j; exact muBalFullMode_add_acting W U (-j - 1) a b
  map_smul' c a := by
    funext j; exact muBalFullMode_smul_acting W U (-j - 1) c a

/-- The `p`-th mode of the balanced field is `a_p`. -/
@[simp] theorem mode_muBalFullYM (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (a : 𝒱) (p : ℤ) :
    mode (muBalFullYM W U a) p = muBalFullMode W U p a := by
  show muBalFullMode W U (-(-p - 1) - 1) a = muBalFullMode W U p a
  congr 1
  ring

/-! ## STEP 3 — the bottom `M(U)(0) ≅ U`

Everything below carries the **explicitly named Gate hypothesis** `hcol : OnmFull W 0 0 ≤ O W`.
It is NOT proved in this repo: it is the `n = 0` collapse `OnmCollapses W 0`
(`ZhuVermaAnArchHingeCollapse`, `ZhuVermaAnArchOnmCollapseZero`), where it is reduced — but not
discharged — to the two generator families for `O''_{0,0}` and `O'''_{0,0}`.  Nothing in STEPs 1–2
depends on it. -/

/-- The Gate hypothesis upgrades to an equality: `Onm W 0 0 = O W` always, and
`Onm W 0 0 ≤ OnmFull W 0 0`, so `OnmFull W 0 0 ≤ O W` forces `OnmFull W 0 0 = O W`. -/
theorem onmFull_zero_zero_eq_O_of_le (W : VertexOperatorAlgebra 𝒱)
    (hcol : OnmFull W 0 0 ≤ O W) : OnmFull W 0 0 = O W :=
  le_antisymm hcol (by rw [← Onm_zero_zero_eq_O]; exact Onm_le_OnmFull W 0 0)

/-- **The Gate hypothesis IS the repo predicate `OnmCollapses W 0`.**  So any discharge of
`OnmCollapses W 0` (e.g. via `onmCollapses_zero_of_gens`, `ZhuVermaAnArchOnmCollapseZero`)
immediately supplies `hcol` for every STEP-3 statement below. -/
theorem onmFull_zero_le_O_of_onmCollapses (W : VertexOperatorAlgebra 𝒱)
    (h : OnmCollapses W 0) : OnmFull W 0 0 ≤ O W := by
  rw [← Onm_zero_zero_eq_O]
  exact h

/-- The `A(𝒱)`-action of `U`, descended to `A_{0,0}(𝒱) = 𝒱 ⧸ OnmFull W 0 0` (needs the Gate). -/
noncomputable def rhoAnmFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : AnmFull W 0 0 →ₗ[ℂ] U.carrier →ₗ[ℂ] U.carrier :=
  Submodule.liftQ (OnmFull W 0 0) (U.ρ.comp (mk W))
    (fun x hx => by
      have h0 : mk W x = 0 := by
        rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, h0, map_zero])

/-- **The level-`0` action map on the full-ideal piece** `A_{0,0}(𝒱) ⊗_ℂ U → U`,
`[x]₀₀ ⊗ u ↦ ρ([x])·u`.  Well defined exactly because of the Gate `hcol`. -/
noncomputable def piece0ToUFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : MUPieceFull W U 0 →ₗ[ℂ] U.carrier :=
  TensorProduct.lift (rhoAnmFull W U hcol)

/-- The level-`0` action map on an elementary tensor. -/
@[simp] theorem piece0ToUFull_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (x : 𝒱) (u : U.carrier) :
    piece0ToUFull W U hcol (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u) = U.ρ (mk W x) u := rfl

/-- The level-`0` action map is surjective (`[𝟙] ⊗ u ↦ u`). -/
theorem piece0ToUFull_surjective (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : Function.Surjective (piece0ToUFull W U hcol) := by
  intro y
  refine ⟨mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] y, ?_⟩
  have h : U.ρ (mk W W.vacuum) = 1 := U.ρ_one
  rw [piece0ToUFull_tmul, h]
  rfl

/-- The balancing is contained in the kernel of the level-`0` action map (by `ρ_mul`). -/
theorem balancingFull_zero_le_ker (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) :
    balancingFull W U 0 ≤ LinearMap.ker (piece0ToUFull W U hcol) := by
  rw [balancingFull, Submodule.span_le]
  rintro z ⟨x, a, u, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, piece0ToUFull_tmul, anmRight_zero_zero,
    U.ρ_mul, Module.End.mul_apply, sub_self]

/-- Every vector agrees, modulo the balancing, with `[𝟙] ⊗ (its image under the action map)`. -/
theorem sub_bottom_mem_balancingFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (z : MUPieceFull W U 0) :
    z - mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToUFull W U hcol z ∈ balancingFull W U 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t u =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (OnmFull W 0 0) t
      show mkAnmFull W 0 0 x ⊗ₜ[ℂ] u
            - mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ]
                piece0ToUFull W U hcol (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
          ∈ balancingFull W U 0
      rw [piece0ToUFull_tmul]
      have hgen := balancingFull_gen_mem W U 0 W.vacuum x u
      rw [anmRight_zero_zero, zhuMul_vacuum_left] at hgen
      exact hgen
  | add z1 z2 h1 h2 =>
      have hsplit :
          (z1 + z2) - mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToUFull W U hcol (z1 + z2)
            = (z1 - mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToUFull W U hcol z1)
              + (z2 - mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToUFull W U hcol z2) := by
        rw [map_add, TensorProduct.tmul_add]; abel
      rw [hsplit]
      exact Submodule.add_mem _ h1 h2

/-- **The balancing at level `0` IS the kernel of the action map.** -/
theorem balancingFull_zero_eq_ker (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) :
    balancingFull W U 0 = LinearMap.ker (piece0ToUFull W U hcol) := by
  refine le_antisymm (balancingFull_zero_le_ker W U hcol) ?_
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have h := sub_bottom_mem_balancingFull W U hcol z
  rwa [hz, TensorProduct.tmul_zero, sub_zero] at h

/-- **`M(U)(0) ≅ U`** on DJ's genuine ideal: the `A(𝒱)`-balanced bottom recovers `U`.  This is the
balanced-bottom payoff — the ℂ-tensor bottom `A(𝒱) ⊗_ℂ U` is strictly larger when `dim A(𝒱) > 1`. -/
noncomputable def muPieceBalFull0EquivU (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : MUPieceBalFull W U 0 ≃ₗ[ℂ] U.carrier :=
  (Submodule.quotEquivOfEq _ _ (balancingFull_zero_eq_ker W U hcol)).trans
    (LinearMap.quotKerEquivOfSurjective (piece0ToUFull W U hcol)
      (piece0ToUFull_surjective W U hcol))

/-- The bottom isomorphism on a class is the action map. -/
@[simp] theorem muPieceBalFull0EquivU_mk (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (z : MUPieceFull W U 0) :
    muPieceBalFull0EquivU W U hcol (mkPieceBalFull W U 0 z) = piece0ToUFull W U hcol z := by
  rw [muPieceBalFull0EquivU, LinearEquiv.trans_apply,
    show mkPieceBalFull W U 0 z = Submodule.Quotient.mk z from rfl, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ z

/-! ### The left `A(𝒱)`-action on the balanced bottom -/

/-- Left Zhu multiplication descended to `A_{0,0}(𝒱)` (needs the Gate: `O(𝒱)` is a right ideal). -/
noncomputable def leftAnmFull0 (W : VertexOperatorAlgebra 𝒱) (hcol : OnmFull W 0 0 ≤ O W)
    (b : 𝒱) : AnmFull W 0 0 →ₗ[ℂ] AnmFull W 0 0 :=
  Submodule.liftQ (OnmFull W 0 0) ((OnmFull W 0 0).mkQ.comp (zhuMulₗ W b))
    (fun x hx => by
      have hmem : zhuMul W b x ∈ OnmFull W 0 0 := by
        rw [onmFull_zero_zero_eq_O_of_le W hcol]
        exact (zhuRingData_holds W).right_ideal b (hcol hx)
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hmem)

/-- Left multiplication on a class. -/
@[simp] theorem leftAnmFull0_mk (W : VertexOperatorAlgebra 𝒱) (hcol : OnmFull W 0 0 ≤ O W)
    (b x : 𝒱) :
    leftAnmFull0 W hcol b (mkAnmFull W 0 0 x) = mkAnmFull W 0 0 (zhuMul W b x) := rfl

/-- Left multiplication by `b ∈ O(𝒱)` is zero (left-ideal property). -/
theorem leftAnmFull0_mem_O (W : VertexOperatorAlgebra 𝒱) (hcol : OnmFull W 0 0 ≤ O W) {b : 𝒱}
    (hb : b ∈ O W) : leftAnmFull0 W hcol b = 0 := by
  refine LinearMap.ext (fun y => ?_)
  obtain ⟨x, rfl⟩ := (OnmFull W 0 0).mkQ_surjective y
  show leftAnmFull0 W hcol b (mkAnmFull W 0 0 x) = 0
  rw [leftAnmFull0_mk, mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    onmFull_zero_zero_eq_O_of_le W hcol]
  exact (zhuRingData_holds W).left_ideal hb x

/-- The vacuum acts as the identity (`𝟙 * x = x`). -/
theorem leftAnmFull0_vacuum (W : VertexOperatorAlgebra 𝒱) (hcol : OnmFull W 0 0 ≤ O W) :
    leftAnmFull0 W hcol W.vacuum = LinearMap.id := by
  refine LinearMap.ext (fun y => ?_)
  obtain ⟨x, rfl⟩ := (OnmFull W 0 0).mkQ_surjective y
  show leftAnmFull0 W hcol W.vacuum (mkAnmFull W 0 0 x) = mkAnmFull W 0 0 x
  rw [leftAnmFull0_mk, zhuMul_vacuum_left]

/-- Left multiplication on the ℂ-tensor bottom piece: act on the `A_{0,0}(𝒱)` factor. -/
noncomputable def leftMulPiece0 (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) : MUPieceFull W U 0 →ₗ[ℂ] MUPieceFull W U 0 :=
  TensorProduct.map (leftAnmFull0 W hcol b) LinearMap.id

/-- Left multiplication on an elementary tensor. -/
@[simp] theorem leftMulPiece0_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b x : 𝒱) (u : U.carrier) :
    leftMulPiece0 W U hcol b (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
      = mkAnmFull W 0 0 (zhuMul W b x) ⊗ₜ[ℂ] u := by
  simp only [leftMulPiece0, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, leftAnmFull0_mk]

/-- Left multiplication is additive in the acting vector. -/
theorem leftMulPiece0_add (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b c : 𝒱) :
    leftMulPiece0 W U hcol (b + c) = leftMulPiece0 W U hcol b + leftMulPiece0 W U hcol c := by
  refine TensorProduct.ext' (fun t u => ?_)
  obtain ⟨x, rfl⟩ := (OnmFull W 0 0).mkQ_surjective t
  show leftMulPiece0 W U hcol (b + c) (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
      = (leftMulPiece0 W U hcol b + leftMulPiece0 W U hcol c) (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
  rw [LinearMap.add_apply, leftMulPiece0_tmul, leftMulPiece0_tmul, leftMulPiece0_tmul,
    zhuMul_add_left, map_add, TensorProduct.add_tmul]

/-- Left multiplication is homogeneous in the acting vector. -/
theorem leftMulPiece0_smul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (r : ℂ) (b : 𝒱) :
    leftMulPiece0 W U hcol (r • b) = r • leftMulPiece0 W U hcol b := by
  refine TensorProduct.ext' (fun t u => ?_)
  obtain ⟨x, rfl⟩ := (OnmFull W 0 0).mkQ_surjective t
  show leftMulPiece0 W U hcol (r • b) (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
      = (r • leftMulPiece0 W U hcol b) (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)
  rw [LinearMap.smul_apply, leftMulPiece0_tmul, leftMulPiece0_tmul, zhuMul_smul_left, map_smul,
    TensorProduct.smul_tmul']

/-- The vacuum acts as the identity on the ℂ-tensor bottom piece. -/
theorem leftMulPiece0_vacuum (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : leftMulPiece0 W U hcol W.vacuum = LinearMap.id := by
  rw [leftMulPiece0, leftAnmFull0_vacuum, TensorProduct.map_id]

/-- **Left multiplication preserves the balancing** — associativity mod `O(𝒱)`. -/
theorem leftMulPiece0_le_comap (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) :
    balancingFull W U 0 ≤ Submodule.comap (leftMulPiece0 W U hcol b) (balancingFull W U 0) := by
  rw [balancingFull, Submodule.span_le]
  rintro z ⟨x, a, u, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, leftMulPiece0_tmul]
  have hgen := balancingFull_gen_mem W U 0 (zhuMul W b x) a u
  rw [anmRight_zero_zero] at hgen
  have heq : mkAnmFull W 0 0 (zhuMul W b (anmRight W 0 0 x a))
      = mkAnmFull W 0 0 (zhuMul W (zhuMul W b x) a) := by
    rw [anmRight_zero_zero, mkAnmFull, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, onmFull_zero_zero_eq_O_of_le W hcol]
    have h2 := Submodule.neg_mem _ ((zhuRingData_holds W).assoc b x a)
    rwa [neg_sub] at h2
  rw [heq]
  exact hgen

/-- **The left `A(𝒱)`-action on the balanced bottom** `A_{0,0}(𝒱) ⊗_{A(𝒱)} U`. -/
noncomputable def leftMulBalFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) :
    MUPieceBalFull W U 0 →ₗ[ℂ] MUPieceBalFull W U 0 :=
  Submodule.mapQ (balancingFull W U 0) (balancingFull W U 0) (leftMulPiece0 W U hcol b)
    (leftMulPiece0_le_comap W U hcol b)

/-- The balanced left action on a class. -/
@[simp] theorem leftMulBalFull_mk (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) (z : MUPieceFull W U 0) :
    leftMulBalFull W U hcol b (mkPieceBalFull W U 0 z)
      = mkPieceBalFull W U 0 (leftMulPiece0 W U hcol b z) := rfl

/-- The balanced left action is additive in the acting vector. -/
theorem leftMulBalFull_add (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b c : 𝒱) :
    leftMulBalFull W U hcol (b + c) = leftMulBalFull W U hcol b + leftMulBalFull W U hcol c := by
  refine mkPieceBalFull_ext W U 0 (fun z => ?_)
  rw [leftMulBalFull_mk, leftMulPiece0_add, LinearMap.add_apply, map_add, LinearMap.add_apply,
    leftMulBalFull_mk, leftMulBalFull_mk]

/-- The balanced left action is homogeneous in the acting vector. -/
theorem leftMulBalFull_smul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (r : ℂ) (b : 𝒱) :
    leftMulBalFull W U hcol (r • b) = r • leftMulBalFull W U hcol b := by
  refine mkPieceBalFull_ext W U 0 (fun z => ?_)
  rw [leftMulBalFull_mk, leftMulPiece0_smul, LinearMap.smul_apply, map_smul,
    LinearMap.smul_apply, leftMulBalFull_mk]

/-- **The balanced left action factors through `A(𝒱)`**: `b ∈ O(𝒱)` acts by zero. -/
theorem leftMulBalFull_mem_O (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) {b : 𝒱} (hb : b ∈ O W) :
    leftMulBalFull W U hcol b = 0 := by
  have h0 : leftMulPiece0 W U hcol b = 0 := by
    rw [leftMulPiece0, leftAnmFull0_mem_O W hcol hb, TensorProduct.map_zero_left]
  refine mkPieceBalFull_ext W U 0 (fun z => ?_)
  rw [leftMulBalFull_mk, h0]
  simp

/-- **The vacuum acts as the identity** on the balanced bottom. -/
theorem leftMulBalFull_vacuum (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : leftMulBalFull W U hcol W.vacuum = LinearMap.id := by
  refine mkPieceBalFull_ext W U 0 (fun z => ?_)
  rw [leftMulBalFull_mk, leftMulPiece0_vacuum]
  rfl

/-- **The balanced left action is multiplicative** (Zhu associativity mod `O(𝒱)`). -/
theorem leftMulBalFull_mul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b c : 𝒱) :
    leftMulBalFull W U hcol (zhuMul W b c)
      = (leftMulBalFull W U hcol b).comp (leftMulBalFull W U hcol c) := by
  refine mkPieceBalFull_ext W U 0 (fun z => ?_)
  rw [leftMulBalFull_mk, LinearMap.comp_apply, leftMulBalFull_mk, leftMulBalFull_mk]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t u =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (OnmFull W 0 0) t
      show mkPieceBalFull W U 0
            (leftMulPiece0 W U hcol (zhuMul W b c) (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u))
          = mkPieceBalFull W U 0 (leftMulPiece0 W U hcol b
              (leftMulPiece0 W U hcol c (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u)))
      rw [leftMulPiece0_tmul, leftMulPiece0_tmul, leftMulPiece0_tmul]
      have hA : mkAnmFull W 0 0 (zhuMul W (zhuMul W b c) x)
          = mkAnmFull W 0 0 (zhuMul W b (zhuMul W c x)) := by
        rw [mkAnmFull, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          onmFull_zero_zero_eq_O_of_le W hcol]
        exact (zhuRingData_holds W).assoc b c x
      rw [hA]
  | add z1 z2 h1 h2 => simp only [map_add, h1, h2]

/-- **The bottom isomorphism is `A(𝒱)`-equivariant** (representative form): it intertwines the
left Zhu-multiplication action on `A_{0,0}(𝒱) ⊗_{A(𝒱)} U` with the `AMod` action on `U`. -/
theorem piece0ToUFull_leftMulPiece0 (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) (z : MUPieceFull W U 0) :
    piece0ToUFull W U hcol (leftMulPiece0 W U hcol b z)
      = U.ρ (mk W b) (piece0ToUFull W U hcol z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t u =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (OnmFull W 0 0) t
      show piece0ToUFull W U hcol (leftMulPiece0 W U hcol b (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u))
          = U.ρ (mk W b) (piece0ToUFull W U hcol (mkAnmFull W 0 0 x ⊗ₜ[ℂ] u))
      rw [leftMulPiece0_tmul, piece0ToUFull_tmul, piece0ToUFull_tmul, U.ρ_mul]
      rfl
  | add z1 z2 h1 h2 => simp only [map_add, h1, h2]

/-- **`M(U)(0) ≅ U` is `A(𝒱)`-equivariant.**  The bottom isomorphism intertwines the balanced left
action with `U`'s own `A(𝒱)`-action. -/
theorem muPieceBalFull0EquivU_leftMul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) (z : MUPieceBalFull W U 0) :
    muPieceBalFull0EquivU W U hcol (leftMulBalFull W U hcol b z)
      = U.ρ (mk W b) (muPieceBalFull0EquivU W U hcol z) := by
  obtain ⟨y, rfl⟩ := mkPieceBalFull_surjective W U 0 z
  rw [leftMulBalFull_mk, muPieceBalFull0EquivU_mk, muPieceBalFull0EquivU_mk,
    piece0ToUFull_leftMulPiece0]

/-! ### Packaging: the bottom isomorphism as an `A(𝒱)`-linear equivalence -/

/-- Every bundled `AMod` is a genuine `A(𝒱)`-module: `ρ` is a ring homomorphism
`A(𝒱) →+* End ℂ U` (multiplicativity on all of `A(𝒱)` follows from `ρ_mul` on representables plus
surjectivity of `mk`). -/
noncomputable def amodRingHom (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    letI := instRingA W
    A W →+* Module.End ℂ U.carrier :=
  letI := instRingA W
  { toFun := fun p => U.ρ p
    map_one' := U.ρ_one
    map_mul' := fun p q => by
      obtain ⟨b, rfl⟩ := mk_surjective W p
      obtain ⟨c, rfl⟩ := mk_surjective W q
      have hmul : mk W b * mk W c = mk W (zhuMul W b c) := Amul_mk (zhuRingData_holds W) b c
      rw [hmul]
      exact U.ρ_mul b c
    map_zero' := map_zero U.ρ
    map_add' := fun p q => map_add U.ρ p q }

/-- **The `A(𝒱)`-module structure on a bundled `AMod`.** -/
@[reducible] noncomputable def amodModule (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    letI := instRingA W
    Module (A W) U.carrier :=
  letI := instRingA W
  Module.compHom U.carrier (amodRingHom W U)

/-- The balanced left action, packaged `ℂ`-linearly in the acting vector. -/
noncomputable def leftMulBalHom (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : 𝒱 →ₗ[ℂ] Module.End ℂ (MUPieceBalFull W U 0) where
  toFun := leftMulBalFull W U hcol
  map_add' := leftMulBalFull_add W U hcol
  map_smul' := fun r b => leftMulBalFull_smul W U hcol r b

/-- The balanced left action descended to `A(𝒱)` (it kills `O(𝒱)`). -/
noncomputable def leftMulBalA (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) : A W →ₗ[ℂ] Module.End ℂ (MUPieceBalFull W U 0) :=
  Submodule.liftQ (O W) (leftMulBalHom W U hcol)
    (fun b hb => by
      rw [LinearMap.mem_ker]
      exact leftMulBalFull_mem_O W U hcol hb)

/-- The descended balanced left action on a class. -/
@[simp] theorem leftMulBalA_mk (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) (b : 𝒱) :
    leftMulBalA W U hcol (mk W b) = leftMulBalFull W U hcol b := rfl

/-- **The balanced bottom carries a genuine `A(𝒱)`-action**, as a ring homomorphism
`A(𝒱) →+* End ℂ (A_{0,0}(𝒱) ⊗_{A(𝒱)} U)` — unitality is `leftMulBalFull_vacuum`,
multiplicativity is `leftMulBalFull_mul` (Zhu associativity mod `O(𝒱)`). -/
noncomputable def leftMulBalRingHom (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) :
    letI := instRingA W
    A W →+* Module.End ℂ (MUPieceBalFull W U 0) :=
  letI := instRingA W
  { toFun := fun p => leftMulBalA W U hcol p
    map_one' := by
      show leftMulBalA W U hcol (mk W W.vacuum) = 1
      rw [leftMulBalA_mk, leftMulBalFull_vacuum]
      rfl
    map_mul' := fun p q => by
      obtain ⟨b, rfl⟩ := mk_surjective W p
      obtain ⟨c, rfl⟩ := mk_surjective W q
      have hmul : mk W b * mk W c = mk W (zhuMul W b c) := Amul_mk (zhuRingData_holds W) b c
      rw [hmul, leftMulBalA_mk, leftMulBalA_mk, leftMulBalA_mk, leftMulBalFull_mul]
      rfl
    map_zero' := map_zero _
    map_add' := fun p q => map_add _ p q }

/-- **The `A(𝒱)`-module structure on the balanced bottom** `A_{0,0}(𝒱) ⊗_{A(𝒱)} U`. -/
@[reducible] noncomputable def moduleBottomBalFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) :
    letI := instRingA W
    Module (A W) (MUPieceBalFull W U 0) :=
  letI := instRingA W
  Module.compHom (MUPieceBalFull W U 0) (leftMulBalRingHom W U hcol)

/-- **THE STEP-3 PAYOFF.**  `M(U)(0) ≃ₗ[A(𝒱)] U` — the balanced bottom of the Dong–Jiang induced
module on the GENUINE ideal is isomorphic to `U` **as an `A(𝒱)`-module**, not merely as a `ℂ`-space.
The `A(𝒱)`-action on the bottom is the genuine left Zhu multiplication (`leftMulBalRingHom`), and
the intertwining is `muPieceBalFull0EquivU_leftMul`.  Carries the Gate hypothesis `hcol`. -/
noncomputable def muBalFullBottomEquivA (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcol : OnmFull W 0 0 ≤ O W) :
    letI := instRingA W
    letI := amodModule W U
    letI := moduleBottomBalFull W U hcol
    MUPieceBalFull W U 0 ≃ₗ[A W] U.carrier :=
  letI := instRingA W
  letI := amodModule W U
  letI := moduleBottomBalFull W U hcol
  { toFun := muPieceBalFull0EquivU W U hcol
    map_add' := map_add _
    map_smul' := fun p z => by
      obtain ⟨b, rfl⟩ := mk_surjective W p
      exact muPieceBalFull0EquivU_leftMul W U hcol b z
    invFun := (muPieceBalFull0EquivU W U hcol).symm
    left_inv := (muPieceBalFull0EquivU W U hcol).left_inv
    right_inv := (muPieceBalFull0EquivU W U hcol).right_inv }

end VOA
