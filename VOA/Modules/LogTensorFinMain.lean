/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinInduction

/-!
# Finiteness of logarithmic fusion rules for `C₂`-cofinite VOAs (stage T1d)

`logFusionFiniteFact_of_c2Cofinite : C2Cofinite W → LogFusionFiniteFact W`.

For a `C₂`-cofinite VOA `V` (of CFT type, built into `VertexOperatorAlgebra`) and finitely
generated logarithmic (grading-restricted generalized) modules `N₁, N₂, N₃`, the space of
logarithmic intertwining operators of type `(N₃ / N₁ N₂)` (HLZ II Def. 3.10) is
finite-dimensional.  Compare Huang, arXiv:0712.4109, and Miyamoto; the route here is
dual-free and elementary.

## Proof
1. (`LogTensorFinSpan`) Outside finite sets `F₁`, `F₂` of weights, the graded pieces of `N₁`,
   `N₂` lie in `C₂` (Buhl spanning).
2. (`LogTensorFinArtin`) Some `C` is such that every weak submodule of `N₃` with all weights of
   real part `≥ C` is zero (finite length ⟹ Artinian).
3. (`LogTensorFinInduction`) If `𝒴` vanishes on `(N₁)_[α₁] × (N₂)_[α₂]` for `α₁ ∈ F₁`,
   `α₂ ∈ F₂` at every output weight `α₃` with `Re α₃ < C`, then it vanishes at every input
   pair with output `Re α₃ < C`.
4. (`eq_zero_of_base`) Then the image of `𝒴` (a weak submodule) has all weights `≥ C`, so it is
   zero by 2, and `𝒴 = 0`.
5. (`finiteDimensional_logIntertwining`) Only finitely many output weights `α₃` with
   `Re α₃ < C` occur (`exists_finset_weights_re_lt`), and on each weight triple the log degree is
   bounded (`log_degree_le`).  So `𝒴 ↦ (its restrictions to the finitely many triples
   `F₁ × F₂ × F₃` and log degrees `k < K`)` is an injective linear map into a finite-dimensional
   space.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {N₁ : LogVModule W M₁} {N₂ : LogVModule W M₂} {N₃ : LogVModule W M₃}

/-- **Determination by finite data.**  A logarithmic intertwining operator vanishing on the
low-weight base data vanishes identically. -/
theorem eq_zero_of_base {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y)
    {F₁ F₂ : Set ℂ} (hF₁ : ∀ α, α ∉ F₁ → N₁.weight α ≤ c2Part N₁ α)
    (hF₂ : ∀ α, α ∉ F₂ → N₂.weight α ≤ c2Part N₂ α) {C : ℝ}
    (hC : ∀ P : Submodule ℂ M₃, ModeStable N₃.toWeakModule P →
      (∀ y ∈ P, ∀ α : ℂ, α.re < C → proj N₃ α y = 0) → P = ⊥)
    (hbase : ∀ α₁ ∈ F₁, ∀ α₂ ∈ F₂, ∀ n : ℂ, (α₁ + α₂ - n - 1).re < C →
      Van N₁ N₂ Y α₁ α₂ n) :
    Y = 0 := by
  have hvan := van_below hY hF₁ hF₂ C hbase
  have himg : image Y = ⊥ := by
    refine hC _ hY.mode_mem_image (fun y hy α hα => ?_)
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, w₁, w₂, rfl⟩ := hy
      refine induction_on N₁ (C := fun w₁ => proj N₃ α (Y n k w₁ w₂) = 0) w₁ ?_ ?_ ?_
      · intro α₁ x₁ hx₁
        refine induction_on N₂ (C := fun w₂ => proj N₃ α (Y n k x₁ w₂) = 0) w₂ ?_ ?_ ?_
        · intro α₂ x₂ hx₂
          by_cases hre : (α₁ + α₂ - n - 1).re < C
          · simp only [hvan α₁ α₂ n hre k x₁ x₂ hx₁ hx₂, map_zero]
          · refine proj_of_mem_ne N₃ (hY.mem_weight hx₁ hx₂ n k) (fun he => hre ?_)
            rw [he]; exact hα
        · simp
        · intro a b ha hb
          simp only at ha hb ⊢
          rw [map_add, map_add, ha, hb, add_zero]
      · simp
      · intro a b ha hb
        simp only at ha hb ⊢
        rw [map_add, LinearMap.add_apply, map_add, ha, hb, add_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  funext n k
  ext w₁ w₂
  have h := mem_image Y n k w₁ w₂
  rw [himg, Submodule.mem_bot] at h
  simpa using h

/-- The output of `(·)_{α₁+α₂−α₃−1; k}` on `(N₁)_[α₁] × (N₂)_[α₂]` lies in `(N₃)_[α₃]`. -/
theorem mem_weight_eval {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y)
    {α₁ α₂ : ℂ} (α₃ : ℂ) (k : ℕ) {w₁ : M₁} {w₂ : M₂} (h₁ : w₁ ∈ N₁.weight α₁)
    (h₂ : w₂ ∈ N₂.weight α₂) : Y (α₁ + α₂ - α₃ - 1) k w₁ w₂ ∈ N₃.weight α₃ := by
  have h := hY.mem_weight h₁ h₂ (α₁ + α₂ - α₃ - 1) k
  rwa [show α₁ + α₂ - (α₁ + α₂ - α₃ - 1) - 1 = α₃ by ring] at h

/-- The restriction of a logarithmic intertwining operator to one weight triple and one log
degree, as a linear map in the operator. -/
noncomputable def evalMap (α₁ α₂ α₃ : ℂ) (k : ℕ) :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule →ₗ[ℂ]
      (N₁.weight α₁ →ₗ[ℂ] N₂.weight α₂ →ₗ[ℂ] N₃.weight α₃) where
  toFun Y := LinearMap.mk₂ ℂ
    (fun w₁ w₂ => ⟨Y.1 (α₁ + α₂ - α₃ - 1) k w₁ w₂, mem_weight_eval Y.2 α₃ k w₁.2 w₂.2⟩)
    (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
    (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
  map_add' Y Y' := by ext; simp
  map_smul' c Y := by ext; simp

/-- **Finite-dimensionality from finite data**: the three finiteness inputs (graded `C₂`
for the two sources, no high submodules and finitely many low weights for the target) give a
finite-dimensional space of logarithmic intertwining operators. -/
theorem finiteDimensional_of_data {F₁ F₂ F₃ : Finset ℂ}
    (hF₁ : ∀ α, α ∉ F₁ → N₁.weight α ≤ c2Part N₁ α)
    (hF₂ : ∀ α, α ∉ F₂ → N₂.weight α ≤ c2Part N₂ α) {C : ℝ}
    (hC : ∀ P : Submodule ℂ M₃, ModeStable N₃.toWeakModule P →
      (∀ y ∈ P, ∀ α : ℂ, α.re < C → proj N₃ α y = 0) → P = ⊥)
    (hF₃ : ∀ α, N₃.weight α ≠ ⊥ → α.re < C → α ∈ F₃) :
    FiniteDimensional ℂ
      (LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) := by
  classical
  haveI : ∀ α, FiniteDimensional ℂ (N₁.weight α) := N₁.finrank
  haveI : ∀ α, FiniteDimensional ℂ (N₂.weight α) := N₂.finrank
  haveI : ∀ α, FiniteDimensional ℂ (N₃.weight α) := N₃.finrank
  let T : Finset (ℂ × ℂ × ℂ) := F₁ ×ˢ F₂ ×ˢ F₃
  let K : T → ℕ := fun t => Module.finrank ℂ (N₁.weight t.1.1) +
    Module.finrank ℂ (N₂.weight t.1.2.1) + Module.finrank ℂ (N₃.weight t.1.2.2)
  let Φ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule →ₗ[ℂ]
      ((t : T) → (k : Fin (K t)) →
        (N₁.weight t.1.1 →ₗ[ℂ] N₂.weight t.1.2.1 →ₗ[ℂ] N₃.weight t.1.2.2)) :=
    LinearMap.pi (fun t => LinearMap.pi (fun k => evalMap t.1.1 t.1.2.1 t.1.2.2 k))
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).mpr (fun Y hY0 => ?_))
  apply Subtype.ext
  refine eq_zero_of_base Y.2 (F₁ := (F₁ : Set ℂ)) (F₂ := (F₂ : Set ℂ)) hF₁ hF₂ hC ?_
  intro α₁ hα₁ α₂ hα₂ n hre k w₁ w₂ h₁ h₂
  by_cases hbot : N₃.weight (α₁ + α₂ - n - 1) = ⊥
  · exact eq_zero_of_mem_bot N₃ hbot (Y.2.mem_weight h₁ h₂ n k)
  have hα₃ := hF₃ _ hbot hre
  have ht : (α₁, α₂, α₁ + α₂ - n - 1) ∈ T :=
    Finset.mem_product.mpr ⟨hα₁, Finset.mem_product.mpr ⟨hα₂, hα₃⟩⟩
  by_cases hk : k < K ⟨_, ht⟩
  · have h := congrArg (fun f => ((f ⟨_, ht⟩ ⟨k, hk⟩ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ :
      N₃.weight (α₁ + α₂ - n - 1)) : M₃)) hY0
    simp only [Φ, LinearMap.pi_apply, evalMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.mk₂_apply, Pi.zero_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h
    rwa [show α₁ + α₂ - (α₁ + α₂ - n - 1) - 1 = n by ring] at h
  · refine Y.2.log_degree_le h₁ h₂ ?_
    simp only [K, not_lt] at hk
    omega

/-- **Finiteness of logarithmic fusion rules** (target T1d): for a `C₂`-cofinite VOA, the
space of logarithmic intertwining operators among finitely generated logarithmic modules is
finite-dimensional. -/
theorem logFusionFiniteFact_of_c2Cofinite (hC2 : C2Cofinite W) : LogFusionFiniteFact W := by
  intro M₁ M₂ M₃ _ _ _ _ _ _ N₁ N₂ N₃ hfg₁ hfg₂ hfg₃
  obtain ⟨F₁, hF₁⟩ := exists_c2_cofinite_weights N₁ hC2 hfg₁
  obtain ⟨F₂, hF₂⟩ := exists_c2_cofinite_weights N₂ hC2 hfg₂
  obtain ⟨C, hC⟩ := exists_eq_bot_of_high N₃ hC2 hfg₃
  obtain ⟨F₃, hF₃⟩ := exists_finset_weights_re_lt N₃ hC2 hfg₃ C
  exact finiteDimensional_of_data hF₁ hF₂ hC hF₃

end VOA.LogTensor.LogFin
