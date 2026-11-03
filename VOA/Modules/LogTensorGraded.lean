/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorStructure
import VOA.Modules.LogVModule

/-!
# Logarithmic intertwining operators among grading-restricted generalized modules — T1

For grading-restricted generalized modules (`LogVModule`, equivalently a `C2Rigid.GWModule` whose
grading is by generalized `L₀`-eigenspaces, e.g. `C2Rigid.gwOfFiniteLength`):

* `mem_weight` — **weight shift**: `(W₁)_[α₁] × (W₂)_[α₂] → (W₃)_[α₁+α₂−n−1]` under `(·)_{n;k}`;
* `log_degree_le` — **uniform log-degree bound per weight triple**: `(w₁)_{n;k} w₂ = 0` for
  `w₁ ∈ (W₁)_[α₁]`, `w₂ ∈ (W₂)_[α₂]` as soon as
  `k + 2 ≥ dim (W₁)_[α₁] + dim (W₂)_[α₂] + dim (W₃)_[α₁+α₂−n−1]`.

Also `C2Rigid.GWModule.toLogV` (a generalized-eigenspace-graded `GWModule` is a `LogVModule`) and
the linear-algebra lemma `sub_pow_finrank_apply_eq_zero` (on a finite-dimensional generalized
eigenspace, `(f − μ)^{dim}` vanishes).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogTensor

open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

/-- On a finite-dimensional generalized eigenspace `E`, `(f − μ)^{dim E}` vanishes. -/
theorem sub_pow_finrank_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : End ℂ M) (μ : ℂ) [FiniteDimensional ℂ (f.maxGenEigenspace μ)] {y : M}
    (hy : y ∈ f.maxGenEigenspace μ) :
    ((f - μ • (1 : End ℂ M)) ^ Module.finrank ℂ (f.maxGenEigenspace μ)) y = 0 := by
  set E := f.maxGenEigenspace μ
  have hE : Set.MapsTo f E E := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  set g : End ℂ E := f.restrict hE
  have hpow : ∀ (k : ℕ) (z : E), (((g - μ • (1 : End ℂ E)) ^ k) z : M)
      = ((f - μ • (1 : End ℂ M)) ^ k) z := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      congr 1
  have hmem : (⟨y, hy⟩ : E) ∈ g.maxGenEigenspace μ := by
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
    exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, Subtype.ext (by rw [hpow]; simpa using hk)⟩
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
    LinearMap.mem_ker] at hmem
  have := congrArg Subtype.val hmem
  rw [hpow] at this
  simpa using this

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A graded weak module graded by generalized `L₀`-eigenspaces (`McRaeM2`'s `IsGenGraded`) is a
logarithmic (grading-restricted generalized) module. -/
def _root_.VOA.C2Rigid.GWModule.toLogV {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : C2Rigid.GWModule W M)
    (h : ∀ α : ℂ, N.weight α ≤ (L0 N.toWeakModule).maxGenEigenspace α) : LogVModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  weight_le_maxGenEigenspace := h
  finrank := N.finrank
  boundedBelow := N.boundedBelow

variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {N₁ : LogVModule W M₁} {N₂ : LogVModule W M₂} {N₃ : LogVModule W M₃}

theorem LogVModule.maxGen_eq_weight' {M : Type*} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (α : ℂ) : (L0 N.toWeakModule).maxGenEigenspace α = N.weight α :=
  (N.weight_eq_maxGenEigenspace α).symm

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

/-- **Weight shift** among logarithmic modules:
`(w₁)_{n;k} w₂ ∈ (W₃)_[α₁+α₂−n−1]` for `w₁ ∈ (W₁)_[α₁]`, `w₂ ∈ (W₂)_[α₂]`. -/
theorem mem_weight
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y)
    {α₁ α₂ : ℂ} {w₁ : M₁} {w₂ : M₂} (h₁ : w₁ ∈ N₁.weight α₁) (h₂ : w₂ ∈ N₂.weight α₂)
    (n : ℂ) (k : ℕ) : Y n k w₁ w₂ ∈ N₃.weight (α₁ + α₂ - n - 1) := by
  rw [← LogVModule.maxGen_eq_weight'] at h₁ h₂ ⊢
  exact hY.mem_maxGenEigenspace h₁ h₂ n k

/-- **Uniform log-degree bound per weight triple** (HLZ II §3): for `w₁ ∈ (W₁)_[α₁]`,
`w₂ ∈ (W₂)_[α₂]`, `(w₁)_{n;k} w₂ = 0` whenever
`dim (W₁)_[α₁] + dim (W₂)_[α₂] + dim (W₃)_[α₁+α₂−n−1] ≤ k + 2`. -/
theorem log_degree_le
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y)
    {α₁ α₂ n : ℂ} {w₁ : M₁} {w₂ : M₂} (h₁ : w₁ ∈ N₁.weight α₁) (h₂ : w₂ ∈ N₂.weight α₂)
    {k : ℕ}
    (hk : Module.finrank ℂ (N₁.weight α₁) + Module.finrank ℂ (N₂.weight α₂)
      + Module.finrank ℂ (N₃.weight (α₁ + α₂ - n - 1)) ≤ k + 2) :
    Y n k w₁ w₂ = 0 := by
  haveI := N₁.finrank α₁
  haveI := N₂.finrank α₂
  haveI := N₃.finrank (α₁ + α₂ - n - 1)
  haveI : FiniteDimensional ℂ ((L0 N₁.toWeakModule).maxGenEigenspace α₁) := by
    rw [LogVModule.maxGen_eq_weight']; infer_instance
  haveI : FiniteDimensional ℂ ((L0 N₂.toWeakModule).maxGenEigenspace α₂) := by
    rw [LogVModule.maxGen_eq_weight']; infer_instance
  haveI : FiniteDimensional ℂ
      ((L0 N₃.toWeakModule).maxGenEigenspace (α₁ + α₂ - n - 1)) := by
    rw [LogVModule.maxGen_eq_weight']; infer_instance
  rw [← LogVModule.maxGen_eq_weight'] at h₁ h₂
  have e₁ := LogVModule.maxGen_eq_weight' N₁ α₁
  have e₂ := LogVModule.maxGen_eq_weight' N₂ α₂
  have e₃ := LogVModule.maxGen_eq_weight' N₃ (α₁ + α₂ - n - 1)
  refine hY.log_degree_bound
    (r := Module.finrank ℂ ((L0 N₃.toWeakModule).maxGenEigenspace (α₁ + α₂ - n - 1)))
    (p := Module.finrank ℂ ((L0 N₁.toWeakModule).maxGenEigenspace α₁))
    (q := Module.finrank ℂ ((L0 N₂.toWeakModule).maxGenEigenspace α₂))
    (fun y hy => sub_pow_finrank_apply_eq_zero _ _ hy)
    (sub_pow_finrank_apply_eq_zero _ _ h₁) (sub_pow_finrank_apply_eq_zero _ _ h₂) ?_
  rw [e₁, e₂, e₃]
  omega

end IsLogIntertwining

end VOA.LogTensor
