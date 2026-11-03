/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEC1
import VOA.Modules.ContragredientClose

/-!
# The contragredient `C₁` datum from the library's contragredient module

Huang's fourth family `𝒟` uses `C₁`-cofiniteness of the contragredient `W₄'`; the product/iterate
theorems consume it as `DualC1Graded`: above some level, every functional on the weight space
`h + N` is a sum of restrictions of `g ∘ u₍ₘ₎` with `u ∈ V_d`, `d ≥ 1`, `m ≥ 2d − 1`.

The library has the contragredient module unconditionally
(`ContragredientClose.contragredientModule A : OrdVModule W (RestrictedDual A)`), with
`Y_{M'}(u, z)` the transpose of `Y_M(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)` (`dualModeEndo`, `dualCompMap`).
For `u ∈ V_d` its mode `u'₋₁` is `(−1)^d Σ_{j ≤ d} (1/j!) g ∘ proj ∘ (L₁ʲu)₍₂d−1−j₎`, and
`L₁ʲu ∈ V_{d−j}` with `2d − 1 − j = 2 wt(L₁ʲu) + j − 1` — exactly the shape of `DualC1Graded`
(the `j = d` term is a mode of `V₀ = ℂ𝟙` at index `d − 1 ≠ −1`, hence zero).

## Main results
* `isLowestWeight_contragredientModule` — the contragredient has the same lowest weight.
* `dualC1Graded_of_contragredient` — `C1Graded M' h B → DualC1Graded M h B`.
* `moduleDualC1Data_of_contragredientC2` and
  `huangODEInput_of_C2Inputs : ModuleC2Input → ContragredientC2Input → HuangODEInput`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEDual

open VOA VOA.Huang.Convergence VOA.Huang.HuangODEProduct VOA.Huang.HuangODEIterate
  VOA.Huang.HuangODEC1 VOA.Huang.FusionC2

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `component ∘ lof = id`, for any `DecidableEq` instance (the library's `lof` and ours may use
different ones). -/
theorem component_lof_self' (dec : DecidableEq ℂ) (F : ℂ → Type*) [∀ i, AddCommGroup (F i)]
    [∀ i, Module ℂ (F i)] (i : ℂ) (b : F i) :
    DirectSum.component ℂ ℂ F i (by letI := dec; exact DirectSum.lof ℂ ℂ F i b) = b := by
  letI := dec
  exact DirectSum.component.lof_self ℂ i b

/-- The contragredient has the same lowest weight. -/
theorem isLowestWeight_contragredientModule (A : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight A h) : IsLowestWeight (contragredientModule A) h := by
  intro α hα
  apply hl α
  intro hbot
  apply hα
  show LinearMap.range (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α) = ⊥
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext (fun g => ?_)
  rw [dual_eq_zero_of_weight_bot A hbot g]
  exact map_zero _

/-- One term of the contragredient `u₋₁`: `(g₀ ∘ proj_γ ∘ (L₁ʲu)₍₂d−1−j₎)|_{h+N}` lies in the span
required by `DualC1Graded`. -/
theorem term_mem (A : OrdVModule W M) (h : ℂ) {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) {u : 𝒱}
    (hu : u ∈ W.grading (d : ℤ)) (γ : ℂ) (g₀ : Module.Dual ℂ (A.weight γ)) {j : ℕ}
    (hj : j ≤ d) :
    restrictToWeight A (h + N) (LinearMap.lcomp ℂ ℂ (dualTargetOp A (d : ℤ) u (-1) γ j) g₀)
      ∈ Submodule.span ℂ {φ | ∃ (d m : ℕ) (u : 𝒱) (g : M →ₗ[ℂ] ℂ), 1 ≤ d ∧ 2 * d ≤ m + 1 ∧
          m + 1 - d ≤ N ∧ u ∈ W.grading (d : ℤ) ∧
          φ = (g ∘ₗ mode (A.YM u) (m : ℤ)).domRestrict (A.weight (h + N))} := by
  have hv := VertexOperatorAlgebra.L_one_pow_mem W hu j
  have hidx : 2 * (d : ℤ) - (-1) - 2 - (j : ℤ) = ((2 * d - 1 - j : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rcases lt_or_eq_of_le hj with hjd | rfl
  · -- a genuine term: `v = L₁ʲu ∈ V_{d−j}`, `d − j ≥ 1`
    refine Submodule.subset_span ⟨d - j, 2 * d - 1 - j, (W.L 1 ^ j) u,
      g₀ ∘ₗ internalProjTo A.isInternal γ, by omega, by omega, by omega, ?_, ?_⟩
    · have e : ((d : ℤ) - (j : ℤ)) = ((d - j : ℕ) : ℤ) := by rw [Nat.cast_sub (by omega)]
      rw [← e]; exact hv
    · ext x
      simp only [restrictToWeight, LinearMap.lcomp_apply, LinearMap.comp_apply,
        LinearMap.domRestrict_apply, Submodule.subtype_apply, dualTargetOp, modeLinear,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [hidx]
  · -- `j = d`: a mode of `V₀ = ℂ𝟙` at index `d − 1 ≠ −1` vanishes
    have h0 : (W.L 1 ^ j) u ∈ W.grading 0 := by simpa using hv
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at h0
    obtain ⟨c, hc⟩ := h0
    have hz : restrictToWeight A (h + N)
        (LinearMap.lcomp ℂ ℂ (dualTargetOp A (j : ℤ) u (-1) γ j) g₀) = 0 := by
      ext x
      simp only [restrictToWeight, LinearMap.lcomp_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, dualTargetOp, modeLinear, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.zero_apply]
      rw [← hc, map_smul, A.vacuum_YM, mode_smul, mode_one, if_neg (by omega)]
      simp
    rw [hz]
    exact Submodule.zero_mem _

/-- **The contragredient's `C₁` gives `DualC1Graded`.** -/
theorem dualC1Graded_of_contragredient (A : OrdVModule W M) {h : ℂ} {B : ℕ}
    (hC : C1Graded (contragredientModule A) h B) : DualC1Graded A h B := by
  intro N hN f
  set R : RestrictedDual A →ₗ[ℂ] Module.Dual ℂ (A.weight (h + N)) :=
    DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) (h + N) with hR
  have hφ : DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) (h + N)
      (f.domRestrict (A.weight (h + N))) ∈ (contragredientModule A).weight (h + N) :=
    ⟨_, rfl⟩
  have key : R (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) (h + N)
      (f.domRestrict (A.weight (h + N)))) = f.domRestrict (A.weight (h + N)) := by
    rw [hR]; exact component_lof_self' _ (fun β => Module.Dual ℂ (A.weight β)) _ _
  rw [← key]
  refine Submodule.span_induction (p := fun x _ => R x ∈ _) ?_ ?_ ?_ ?_ (hC N hN _ hφ)
  · rintro x ⟨d, u, g', hd, hdN, hu, hg', rfl⟩
    obtain ⟨g₀, rfl⟩ := hg'
    change R (mode (YMdual A u) (-1) _) ∈ _
    rw [mode_YMdual_homogeneous A hu (-1)]
    erw [dualModeEndo_lof]
    have hidx : dualOutIdx (d : ℤ) (-1) (h + ((N - d : ℕ) : ℂ)) = h + N := by
      simp only [dualOutIdx]; rw [Nat.cast_sub hdN]; push_cast; ring
    rw [hidx, hR]
    suffices H : restrictToWeight A (h + N) (dualCompMap A (d : ℤ) u (-1) (h + ((N - d : ℕ) : ℂ)) g₀)
        ∈ Submodule.span ℂ {φ | ∃ (d m : ℕ) (u : 𝒱) (g : M →ₗ[ℂ] ℂ), 1 ≤ d ∧ 2 * d ≤ m + 1 ∧
          m + 1 - d ≤ N ∧ u ∈ W.grading (d : ℤ) ∧
          φ = (g ∘ₗ mode (A.YM u) (m : ℤ)).domRestrict (A.weight (h + N))} by
      convert H using 1
      exact DirectSum.component.lof_self ℂ _ _
    simp only [dualCompMap, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply,
      map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    simp only [Finset.mem_range, Int.toNat_natCast] at hj
    exact term_mem A h hd hdN hu _ g₀ (by omega)
  · beta_reduce; rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **`C₂`-cofiniteness of the contragredients of the irreducible modules** (TRUE for strongly
rational `W`: the contragredient of an irreducible module is irreducible (FHL Prop. 5.3.2), and
irreducible weak modules are `C₂`-cofinite (Abe–Buhl–Dong 2004)). -/
def ContragredientC2Data (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW →
    ModuleC2Cofinite (contragredientModule P.isMod).toWeakModule

/-- The dual `C₁` datum from `C₂`-cofinite contragredients. -/
theorem moduleDualC1Data_of_contragredientC2 (hC : ContragredientC2Data W) :
    ModuleDualC1Data W := by
  intro P hP
  obtain ⟨B, hB⟩ := c1Graded_of_moduleC2Cofinite (contragredientModule P.isMod)
    (isLowestWeight_contragredientModule P.isMod P.isLow) (hC P hP)
  exact ⟨B, dualC1Graded_of_contragredient P.isMod hB⟩

/-- **The contragredient `C₂` input** (TRUE: FHL + Abe–Buhl–Dong). -/
def ContragredientC2Input : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ContragredientC2Data W

/-- **`HuangODEInput` from two `C₂`-cofiniteness inputs**: of the irreducible modules
(`ModuleC2Input`, existing) and of their contragredients (`ContragredientC2Input`). -/
theorem huangODEInput_of_C2Inputs (h2 : ModuleC2Input.{u}) (h2' : ContragredientC2Input.{u}) :
    HuangODEInput.{u} :=
  huangODEInput_of_moduleC2Input h2 fun 𝒱 _ _ W hV =>
    moduleDualC1Data_of_contragredientC2 (h2' 𝒱 W hV)

end VOA.Huang.HuangODEDual
