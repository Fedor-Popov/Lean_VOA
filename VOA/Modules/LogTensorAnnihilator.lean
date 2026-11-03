/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorIntertwining

/-!
# Annihilators and images of logarithmic intertwining operators — T1

For a logarithmic intertwining operator `𝒴` of type `(W₃ / W₁ W₂)` (HLZ II Def. 3.10):

* the **left annihilator** `leftAnn 𝒴 = {w₁ | 𝒴(w₁, x) = 0}` is a submodule of `W₁`
  (`mode_mem_leftAnn`, from the Jacobi identity at `m = 0`, the associator formula);
* the **right annihilator** `rightAnn 𝒴 = {w₂ | 𝒴(·, x) w₂ = 0}` is a submodule of `W₂`
  (`mode_mem_rightAnn`, from the commutator formula);
* the **image** `image 𝒴 = span{(w₁)_{n;k} w₂}` is a submodule of `W₃` (`mode_mem_image`).

Consequences: a logarithmic intertwining operator is **determined by its values on generators**
of `W₁` (`eq_zero_of_generates_left`) and of `W₂` (`eq_zero_of_generates_right`).  These are
the first reductions towards the finite-dimensionality of fusion spaces.

"Submodule" means a `ℂ`-subspace stable under every mode `u₍ₘ₎` (`ModeStable`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogTensor

open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

/-- A subspace of a weak module stable under all modes `u₍ₘ₎` (a weak submodule). -/
def ModeStable {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (P : Submodule ℂ M) : Prop :=
  ∀ (u : 𝒱) (m : ℤ) (x : M), x ∈ P → mode (A.YM u) m x ∈ P

/-- `S` **generates** the weak module `A`: the only mode-stable subspace containing `S` is
everything. -/
def Generates {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (S : Set M) :
    Prop :=
  ∀ P : Submodule ℂ M, S ⊆ P → ModeStable A P → P = ⊤

/-- The **left annihilator** `{w₁ | 𝒴(w₁, x) = 0}`. -/
def leftAnn (Y : LogModes M₁ M₂ M₃) : Submodule ℂ M₁ where
  carrier := {w₁ | ∀ (n : ℂ) (k : ℕ) (w₂ : M₂), Y n k w₁ w₂ = 0}
  zero_mem' := by intro n k w₂; simp
  add_mem' := by
    intro a b ha hb n k w₂
    simp only [Set.mem_setOf_eq] at ha hb
    rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha n k w₂
    simp only [Set.mem_setOf_eq] at ha
    rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

/-- The **right annihilator** `{w₂ | 𝒴(·, x) w₂ = 0}`. -/
def rightAnn (Y : LogModes M₁ M₂ M₃) : Submodule ℂ M₂ where
  carrier := {w₂ | ∀ (n : ℂ) (k : ℕ) (w₁ : M₁), Y n k w₁ w₂ = 0}
  zero_mem' := by intro n k w₁; simp
  add_mem' := by
    intro a b ha hb n k w₁
    simp only [Set.mem_setOf_eq] at ha hb
    rw [map_add, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha n k w₁
    simp only [Set.mem_setOf_eq] at ha
    rw [map_smul, ha, smul_zero]

/-- The **image** `span{(w₁)_{n;k} w₂}`. -/
def image (Y : LogModes M₁ M₂ M₃) : Submodule ℂ M₃ :=
  Submodule.span ℂ {y | ∃ (n : ℂ) (k : ℕ) (w₁ : M₁) (w₂ : M₂), y = Y n k w₁ w₂}

theorem mem_image (Y : LogModes M₁ M₂ M₃) (n : ℂ) (k : ℕ) (w₁ : M₁) (w₂ : M₂) :
    Y n k w₁ w₂ ∈ image Y :=
  Submodule.subset_span ⟨n, k, w₁, w₂, rfl⟩

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

/-- The associator formula (Jacobi at `m = 0`):
`∑ᵢ (−1)ⁱ C(ℓ,i) (u₍ℓ₋ᵢ₎ (w₁)_{n+i;k} w₂ − (−1)^ℓ (w₁)_{ℓ+n−i;k} u₍ᵢ₎ w₂) = (u₍ℓ₎w₁)_{n;k} w₂`. -/
theorem associator (hY : IsLogIntertwining A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ : ℤ) (n : ℂ) (k : ℕ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (A₃.YM u) (ℓ + 0 - i) (Y (n + i) k w₁ w₂)
          - negOnePow ℓ • Y (ℓ + n - i) k w₁ (mode (A₂.YM u) (0 + i) w₂)))
      = Y n k (mode (A₁.YM u) ℓ w₁) w₂ := by
  rw [hY.jacobi u w₁ w₂ ℓ 0 n k, finsum_eq_single _ (0 : ℤ)]
  · simp
  · intro i hi
    simp [cbz_zero_left, hi]

/-- The left annihilator is a weak submodule. -/
theorem mode_mem_leftAnn (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    ModeStable A₁ (leftAnn Y) := by
  intro u ℓ w₁ hw₁ n k w₂
  have hw : ∀ (n : ℂ) (k : ℕ) (w₂ : M₂), Y n k w₁ w₂ = 0 := hw₁
  rw [← hY.associator u w₁ w₂ ℓ n k]
  simp [hw]

/-- The right annihilator is a weak submodule. -/
theorem mode_mem_rightAnn (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    ModeStable A₂ (rightAnn Y) := by
  intro u m w₂ hw₂ n k w₁
  have hw : ∀ (n : ℂ) (k : ℕ) (w₁ : M₁), Y n k w₁ w₂ = 0 := hw₂
  have h := hY.commutator u w₁ w₂ m n k
  simp only [hw, map_zero, zero_sub, smul_zero, finsum_zero, neg_eq_zero] at h
  exact h

/-- The image is a weak submodule. -/
theorem mode_mem_image (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    ModeStable A₃ (image Y) := by
  intro u m y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, k, w₁, w₂, rfl⟩ := hy
    have h := hY.commutator u w₁ w₂ m n k
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    refine Submodule.add_mem _ ?_ (mem_image Y _ _ _ _)
    rw [finsum_eq_sum_of_support_subset _ (s := (jacR_support_finite (A₁ := A₁) Y u w₁ w₂
      0 m n k).toFinset) ?_]
    · refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (mem_image Y _ _ _ _))
    · intro i hi
      simp only [Set.Finite.coe_toFinset, Function.mem_support, jacR, zero_add] at hi ⊢
      exact hi
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- **Determined by generators of `W₁`**: if `𝒴` vanishes on a generating set of `W₁`, it is
zero. -/
theorem eq_zero_of_generates_left (hY : IsLogIntertwining A₁ A₂ A₃ Y) {S : Set M₁}
    (hS : Generates A₁ S) (h : ∀ s ∈ S, ∀ (n : ℂ) (k : ℕ) (w₂ : M₂), Y n k s w₂ = 0) :
    Y = 0 := by
  have htop := hS (leftAnn Y) (fun s hs => h s hs) hY.mode_mem_leftAnn
  funext n k
  ext w₁ w₂
  have : w₁ ∈ leftAnn Y := by rw [htop]; trivial
  exact this n k w₂

/-- **Determined by generators of `W₂`**. -/
theorem eq_zero_of_generates_right (hY : IsLogIntertwining A₁ A₂ A₃ Y) {S : Set M₂}
    (hS : Generates A₂ S) (h : ∀ s ∈ S, ∀ (n : ℂ) (k : ℕ) (w₁ : M₁), Y n k w₁ s = 0) :
    Y = 0 := by
  have htop := hS (rightAnn Y) (fun s hs => h s hs) hY.mode_mem_rightAnn
  funext n k
  ext w₁ w₂
  have : w₂ ∈ rightAnn Y := by rw [htop]; trivial
  exact this n k w₁

/-- If `W₃` has no proper nonzero weak submodules and `𝒴 ≠ 0`, the coefficients of `𝒴` span `W₃`. -/
theorem image_eq_top (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (hsimple : ∀ P : Submodule ℂ M₃, ModeStable A₃ P → P = ⊥ ∨ P = ⊤) (hne : Y ≠ 0) :
    image Y = ⊤ := by
  rcases hsimple (image Y) hY.mode_mem_image with h | h
  · exfalso; apply hne
    funext n k
    ext w₁ w₂
    have := mem_image Y n k w₁ w₂
    rw [h, Submodule.mem_bot] at this
    exact this
  · exact h

end IsLogIntertwining

end VOA.LogTensor
