/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEIterate
import VOA.Modularity.BuhlSpanningProof
import VOA.Core.InvariantFormPStep
import VOA.Modules.Translation

/-!
# `C₂`-cofiniteness implies graded `C₁`-cofiniteness (the `C₁` input)

Huang's finiteness argument (CCM 7 (2005), Prop. 1.1) needs `dim W/C₁(W) < ∞` for the modules
`W₁, W₂, W₃` and for the contragredient `W₄'`.  The product/iterate theorems of
`Huang/HuangODEProduct.lean` and `Huang/HuangODEIterate.lean` consume it in the graded form
`C1Graded` (resp. `DualC1Graded`).  This file derives `C1Graded` from module `C₂`-cofiniteness:

* `C₂(M) ⊆ C₁(M)`: `a₍₋₂₎m = (L₋₁a)₍₋₁₎m` (`act_T_covariance`) with `L₋₁a ∈ V_{p+1}`, `p + 1 ≥ 1`;
* `C₁(M)` is spanned by homogeneous vectors, so the weight projections preserve it;
* the images of the weight spaces in the finite-dimensional `M/C₁(M)` are independent, hence only
  finitely many are nonzero: above some level every weight space lies in `C₁(M)`.

## Main results
* `c1Graded_of_moduleC2Cofinite` — `ModuleC2Cofinite A → ∃ B, C1Graded A h B`.
* `moduleC1Data_of_C2` — `ModuleC1Data W` from `C₂`-cofiniteness of the irreducible modules
  and the dual datum `ModuleDualC1Data W`.
* `huangODEInput_of_moduleC2Input` — **`HuangODEInput` from the library's
  `ModuleC2Input` (Abe–Buhl–Dong) and `ModuleDualC1Input` (contragredient `C₁`)**.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEC1

open VOA VOA.Huang.Convergence VOA.Huang.HuangODEProduct VOA.Huang.HuangODEIterate
  VOA.Huang.FusionC2

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The homogeneous generators `u₋₁w'` of `C₁(M)`. -/
def c1Gen (A : OrdVModule W M) (h : ℂ) : Set M :=
  {x | ∃ (d N : ℕ) (u : 𝒱) (w' : M), 1 ≤ d ∧ u ∈ W.grading (d : ℤ) ∧
    w' ∈ A.weight (h + N) ∧ x = mode (A.YM u) (-1) w'}

theorem c1Gen_homog (A : OrdVModule W M) (h : ℂ) :
    ∀ x ∈ c1Gen A h, ∃ β : ℂ, x ∈ A.weight β := by
  rintro x ⟨d, N, u, w', _, hu, hw', rfl⟩
  exact ⟨_, mode_mem_weight A hu hw' (-1)⟩

/-- `C₂(M) ⊆ C₁(M)`. -/
theorem c2M_le_span_c1Gen (A : OrdVModule W M) {h : ℂ} (hl : IsLowestWeight A h) :
    C2M A.toWeakModule ≤ Submodule.span ℂ (c1Gen A h) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨a, m, rfl⟩
  refine induction_grading (W := W)
    (motive := fun a => mode (A.YM a) (-2) m ∈ Submodule.span ℂ (c1Gen A h)) a
    (by simp) (fun x y hx hy => ?_) (fun p a ha => ?_)
  · simp only [map_add, mode_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  · have hm : m ∈ ⨆ α : ℂ, A.weight α := by
      rw [A.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction A.weight hm
      (motive := fun m => mode (A.YM a) (-2) m ∈ Submodule.span ℂ (c1Gen A h)) ?_ ?_ ?_
    · intro α y hy
      rcases lt_or_ge p 0 with hp | hp
      · rw [W.positivity p hp, Submodule.mem_bot] at ha
        rw [ha, map_zero, mode_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      by_cases hα : A.weight α = ⊥
      · rw [hα, Submodule.mem_bot] at hy
        rw [hy, map_zero]; exact Submodule.zero_mem _
      obtain ⟨N, rfl⟩ := hl α hα
      obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
      have hcov := act_T_covariance A.toWeakModule a (-1) y
      simp only [WeakModule.act_def, Int.cast_neg, Int.cast_one, neg_neg, one_smul,
        show (-1 : ℤ) - 1 = -2 by norm_num] at hcov
      rw [← hcov]
      refine Submodule.subset_span ⟨P + 1, N, W.L (-1) a, y, by omega, ?_, hy, rfl⟩
      have := VertexOperatorAlgebra.L_neg_one_raise W ha
      simpa using this
    · beta_reduce; rw [map_zero]; exact Submodule.zero_mem _
    · intro y z hy hz; beta_reduce at hy hz ⊢; rw [map_add]; exact Submodule.add_mem _ hy hz

/-- The weight projection to `h + N` maps `C₁(M)` into the span of the level-`N` generators. -/
theorem wProj_mem_levelSpan (A : OrdVModule W M) (h : ℂ) (N : ℕ) {x : M}
    (hx : x ∈ Submodule.span ℂ (c1Gen A h)) :
    VOA.wProj A (h + N) x ∈ Submodule.span ℂ
      {x | ∃ (d : ℕ) (u : 𝒱) (w' : M), 1 ≤ d ∧ d ≤ N ∧ u ∈ W.grading (d : ℤ) ∧
        w' ∈ A.weight (h + ((N - d : ℕ) : ℂ)) ∧ x = mode (A.YM u) (-1) w'} := by
  refine Submodule.span_induction (p := fun x _ => VOA.wProj A (h + N) x ∈ _) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨d, N', u, w', hd, hu, hw', rfl⟩
    have hmem := mode_mem_weight A hu hw' (-1)
    by_cases hN : N' + d = N
    · rw [VOA.wProj_of_mem A (by
        convert hmem using 2; rw [← hN]; push_cast; ring)]
      refine Submodule.subset_span ⟨d, u, w', hd, by omega, hu, ?_, rfl⟩
      convert hw' using 3
      rw [← hN]; push_cast [Nat.add_sub_cancel]; ring
    · rw [VOA.wProj_of_mem_ne A hmem (by
        intro he
        apply hN
        have h1 : ((N : ℤ) : ℂ) = ((N' + d : ℕ) : ℤ) := by push_cast; linear_combination he
        have h2 : (N : ℤ) = ((N' + d : ℕ) : ℤ) := by exact_mod_cast h1
        omega)]
      exact Submodule.zero_mem _
  · beta_reduce; rw [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; beta_reduce at hy hz ⊢; rw [map_add]; exact Submodule.add_mem _ hy hz
  · intro a y _ hy; beta_reduce at hy ⊢; rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- **`C₂`-cofinite ⟹ graded `C₁`-cofinite.** -/
theorem c1Graded_of_moduleC2Cofinite (A : OrdVModule W M) {h : ℂ} (hl : IsLowestWeight A h)
    (hC2 : ModuleC2Cofinite A.toWeakModule) : ∃ B, C1Graded A h B := by
  classical
  set C := Submodule.span ℂ (c1Gen A h) with hCdef
  haveI : FiniteDimensional ℂ (M ⧸ C2M A.toWeakModule) := hC2
  haveI : FiniteDimensional ℂ (M ⧸ C) :=
    Module.Finite.of_surjective (Submodule.factor (c2M_le_span_c1Gen A hl))
      (Submodule.factor_surjective _)
  set E : ℕ → Submodule ℂ (M ⧸ C) := fun N => (A.weight (h + N)).map C.mkQ with hE
  -- the weight projections preserve `C`
  have hpres : ∀ (α : ℂ) {x : M}, x ∈ C → VOA.wProj A α x ∈ C := fun α x hx =>
    VOA.wProj_mem_span A _ (c1Gen_homog A h) α hx
  have hind : iSupIndep E := by
    rw [iSupIndep_def]
    intro N
    rw [Submodule.disjoint_def]
    intro q hq hq'
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hq
    have hq'' : C.mkQ x ∈ (⨆ (N' : ℕ) (_ : N' ≠ N), A.weight (h + N')).map C.mkQ := by
      rw [Submodule.map_iSup]
      simpa only [Submodule.map_iSup, hE] using hq'
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hq''
    have hdiff : y - x ∈ C := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.mkQ_apply] at *
      simp only [Submodule.mkQ_apply] at hxy
      rw [Submodule.Quotient.mk_sub, hxy, sub_self]
    have hy0 : VOA.wProj A (h + N) y = 0 := by
      refine Submodule.iSup_induction _ hy (motive := fun y => VOA.wProj A (h + N) y = 0) ?_
        (map_zero _) (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [map_add, ha, hb, add_zero])
      intro N' z hz
      refine Submodule.iSup_induction _ hz (motive := fun z => VOA.wProj A (h + N) z = 0) ?_
        (map_zero _) (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [map_add, ha, hb, add_zero])
      intro hne z hz
      refine VOA.wProj_of_mem_ne A hz ?_
      intro he
      apply hne
      have : ((N : ℤ) : ℂ) = ((N' : ℤ) : ℂ) := by push_cast; linear_combination he
      exact_mod_cast this.symm
    have hxC : x ∈ C := by
      have h1 := hpres (h + N) hdiff
      rw [map_sub, hy0, zero_sub, VOA.wProj_of_mem A hx] at h1
      simpa using C.neg_mem h1
    simp only [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero C).mpr hxC
  letI := hind.fintypeNeBotOfFiniteDimensional
  set S : Finset ℕ := Finset.univ.image (fun i : { N // E N ≠ ⊥ } => (i : ℕ))
  refine ⟨S.sup id, fun N hN w hw => ?_⟩
  have hEN : E N = ⊥ := by
    by_contra hne
    have hmem : N ∈ S := Finset.mem_image.mpr ⟨⟨N, hne⟩, Finset.mem_univ _, rfl⟩
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have hwC : w ∈ C := by
    have : C.mkQ w ∈ E N := Submodule.mem_map_of_mem hw
    rw [hEN, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have := wProj_mem_levelSpan A h N hwC
  rwa [VOA.wProj_of_mem A hw] at this

/-- **The dual `C₁` datum** of the irreducible modules (TRUE for strongly rational `W`: the
contragredient of an irreducible module is irreducible, hence `C₂`-cofinite (ABD), and FHL (5.2.4)
puts its `C₁` into the shape of `DualC1Graded`; see `ModuleC1Data`). -/
def ModuleDualC1Data (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW → ∃ B, DualC1Graded P.isMod P.h B

/-- `ModuleC1Data` from module `C₂`-cofiniteness and the dual datum. -/
theorem moduleC1Data_of_C2 (hC2 : ∀ P : LWModule W, P.IsIrreducibleLW →
      ModuleC2Cofinite P.isMod.toWeakModule)
    (hD : ModuleDualC1Data W) : ModuleC1Data W :=
  fun P hP => ⟨c1Graded_of_moduleC2Cofinite P.isMod P.isLow (hC2 P hP), hD P hP⟩

/-- **The contragredient `C₁` input** (TRUE: ABD for `W'` + FHL (5.2.4) + CFT type). -/
def ModuleDualC1Input : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ModuleDualC1Data W

/-- **`HuangODEInput` from `ModuleC2Input` (Abe–Buhl–Dong, already a named input of the
library) and `ModuleDualC1Input`.** -/
theorem huangODEInput_of_moduleC2Input (h2 : ModuleC2Input.{u}) (hD : ModuleDualC1Input.{u}) :
    HuangODEInput.{u} :=
  huangODEInput_of_moduleC1Input fun 𝒱 _ _ W hV =>
    moduleC1Data_of_C2 (fun P hP => h2 𝒱 W hV P hP) (hD 𝒱 W hV)

end VOA.Huang.HuangODEC1
