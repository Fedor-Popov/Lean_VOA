/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzNilDefect

/-! # Jacobi-mode spaces and nilpotent-defect stability

Lower-truncated bilinear mode families satisfying the genuine intertwiner Jacobi
identity form a linear space before the derivative condition is imposed. Actual
module endomorphisms may be composed in each slot. Consequently the actual nilpotent
L(0) defect preserves this space, and every reconstructed log coefficient has Jacobi.
-/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

abbrev ModeFamily := ℂ → M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃

def ModeTruncated (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) : Prop :=
  ∀ x y n, ∃ K : ℤ, ∀ j : ℤ, K ≤ j → F (n+j) x y = 0

def ModeJacobi (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂) (A₃ : WeakModule W M₃)
    (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) : Prop :=
  ∀ u x y (ell m : ℤ) (n : ℂ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode (A₃.YM u) (ell+m-i) (F (n+i) x y) -
        negOnePow ell • F (ell+n-i) x (mode (A₂.YM u) (m+i) y))) =
      ∑ᶠ i : ℤ, cbz m i • F (m+n-i) (mode (A₁.YM u) (ell+i) x) y

/-- A genuine truncated Jacobi family, before imposing the derivative equation. -/
structure IsJacobiFamily (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) : Prop where
  truncation : ModeTruncated F
  jacobi : ModeJacobi A₁ A₂ A₃ F

variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

def liftModes (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    LogModes M₁ M₂ M₃ := fun n (_ : ℕ) => F n

private theorem log_trunc_of_mode {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : ModeTruncated F) :
    ∀ x y n, ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, liftModes F (n+j) k x y = 0 := by
  intro x y n
  obtain ⟨K,hK⟩ := hF x y n
  exact ⟨K,fun j hj _ => hK j hj⟩

/-- The actual linear subspace of truncated genuine Jacobi mode families. -/
noncomputable def jacobiFamilies (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) : Submodule ℂ (ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) where
  carrier := {F | IsJacobiFamily A₁ A₂ A₃ F}
  zero_mem' := ⟨fun _ _ _ => ⟨0,fun _ _ => rfl⟩,by intro u x y ell m n; simp⟩
  add_mem' := by
    intro F G (hF : IsJacobiFamily A₁ A₂ A₃ F) (hG : IsJacobiFamily A₁ A₂ A₃ G)
    refine ⟨?_,?_⟩
    · intro x y n
      obtain ⟨K,hK⟩ := hF.truncation x y n
      obtain ⟨L,hL⟩ := hG.truncation x y n
      exact ⟨max K L,fun j hj => by
        simp [hK j (le_trans (le_max_left _ _) hj),hL j (le_trans (le_max_right _ _) hj)]⟩
    · intro u x y ell m n
      change (∑ᶠ i, IsLogIntertwining.jacL A₂ A₃
        (liftModes F + liftModes G) u x y ell m n 0 i) =
        ∑ᶠ i, IsLogIntertwining.jacR A₁
          (liftModes F + liftModes G) u x y ell m n 0 i
      simp only [IsLogIntertwining.jacL_add,IsLogIntertwining.jacR_add]
      rw [finsum_add_distrib (IsLogIntertwining.jacL_support_finite
          (log_trunc_of_mode hF.truncation) ..)
          (IsLogIntertwining.jacL_support_finite (log_trunc_of_mode hG.truncation) ..),
        finsum_add_distrib (IsLogIntertwining.jacR_support_finite (A₁ := A₁) (liftModes F) u x y ell m n 0)
          (IsLogIntertwining.jacR_support_finite (A₁ := A₁) (liftModes G) u x y ell m n 0)]
      exact congrArg₂ (·+·) (hF.jacobi u x y ell m n) (hG.jacobi u x y ell m n)
  smul_mem' c F hF := by
    refine ⟨?_,?_⟩
    · intro x y n
      obtain ⟨K,hK⟩ := hF.truncation x y n
      exact ⟨K,fun j hj => by simp [hK j hj]⟩
    · intro u x y ell m n
      change (∑ᶠ i, IsLogIntertwining.jacL A₂ A₃ (c • liftModes F) u x y ell m n 0 i) =
        ∑ᶠ i, IsLogIntertwining.jacR A₁ (c • liftModes F) u x y ell m n 0 i
      simp only [IsLogIntertwining.jacL_smul,IsLogIntertwining.jacR_smul]
      rw [← smul_finsum' c (IsLogIntertwining.jacL_support_finite
          (log_trunc_of_mode hF.truncation) ..),
        ← smul_finsum' c (IsLogIntertwining.jacR_support_finite (A₁ := A₁) (liftModes F) u x y ell m n 0)]
      exact congrArg (c • ·) (hF.jacobi u x y ell m n)

noncomputable def preFirst (E : End ℂ M₁)
    (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) := fun n => F n ∘ₗ E

noncomputable def preSecond (E : End ℂ M₂)
    (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) := fun n => (F n).compl₂ E

noncomputable def postTarget (E : End ℂ M₃)
    (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) := fun n => LinearMap.mk₂ ℂ
      (fun x y => E (F n x y))
      (fun x x' y => by dsimp only; simp)
      (fun c x y => by dsimp only; simp)
      (fun x y y' => by dsimp only; simp)
      (fun c x y => by dsimp only; simp)

theorem IsJacobiFamily.preFirst {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily A₁ A₂ A₃ F) (E : End ℂ M₁)
    (hE : ∀ u p x, E (mode (A₁.YM u) p x) = mode (A₁.YM u) p (E x)) :
    IsJacobiFamily A₁ A₂ A₃ (preFirst E F) := by
  refine ⟨fun x y n => hF.truncation (E x) y n,?_⟩
  intro u x y ell m n
  change (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
    (mode (A₃.YM u) (ell+m-i) (F (n+i) (E x) y) - negOnePow ell •
      F (ell+n-i) (E x) (mode (A₂.YM u) (m+i) y))) =
    ∑ᶠ i : ℤ, cbz m i • F (m+n-i) (E (mode (A₁.YM u) (ell+i) x)) y
  simp_rw [hE]
  exact hF.jacobi u (E x) y ell m n

theorem IsJacobiFamily.preSecond {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily A₁ A₂ A₃ F) (E : End ℂ M₂)
    (hE : ∀ u p y, E (mode (A₂.YM u) p y) = mode (A₂.YM u) p (E y)) :
    IsJacobiFamily A₁ A₂ A₃ (preSecond E F) := by
  refine ⟨fun x y n => hF.truncation x (E y) n,?_⟩
  intro u x y ell m n
  change (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
    (mode (A₃.YM u) (ell+m-i) (F (n+i) x (E y)) - negOnePow ell •
      F (ell+n-i) x (E (mode (A₂.YM u) (m+i) y)))) =
    ∑ᶠ i : ℤ, cbz m i • F (m+n-i) (mode (A₁.YM u) (ell+i) x) (E y)
  simp_rw [hE]
  exact hF.jacobi u x (E y) ell m n

theorem IsJacobiFamily.postTarget {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily A₁ A₂ A₃ F) (E : End ℂ M₃)
    (hE : ∀ u p z, E (mode (A₃.YM u) p z) = mode (A₃.YM u) p (E z)) :
    IsJacobiFamily A₁ A₂ A₃ (postTarget E F) := by
  refine ⟨?_,?_⟩
  · intro x y n
    obtain ⟨K,hK⟩ := hF.truncation x y n
    exact ⟨K,fun j hj => by
      change E (F (n+j) x y) = 0
      rw [hK j hj,map_zero]⟩
  · intro u x y ell m n
    have h := congrArg E (hF.jacobi u x y ell m n)
    change E (∑ᶠ i : ℤ, IsLogIntertwining.jacL A₂ A₃ (liftModes F) u x y ell m n 0 i) =
      E (∑ᶠ i : ℤ, IsLogIntertwining.jacR A₁ (liftModes F) u x y ell m n 0 i) at h
    rw [map_finsum E (IsLogIntertwining.jacL_support_finite (A₂ := A₂) (A₃ := A₃)
        (log_trunc_of_mode hF.truncation) u x y ell m n 0),
      map_finsum E (IsLogIntertwining.jacR_support_finite
        (A₁ := A₁) (liftModes F) u x y ell m n 0)] at h
    simp only [IsLogIntertwining.jacL,IsLogIntertwining.jacR,liftModes,map_smul,map_sub] at h
    simp_rw [hE] at h
    simpa only [postTarget,LinearMap.mk₂_apply] using h

/-- The genuine nilpotent parts commute with modes, so their three-slot defect
preserves the complete actual Jacobi identity. -/
theorem IsJacobiFamily.nilDefect (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F) :
    IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule
      (fun n => Pz.nilDefect N₁ N₂ N₃ (F n)) := by
  have h₁ := hF.preFirst N₁.L0nil (fun u p x =>
    DFunLike.congr_fun (Contra.L0nil_comm_mode N₁ u p) x)
  have h₂ := hF.preSecond N₂.L0nil (fun u p x =>
    DFunLike.congr_fun (Contra.L0nil_comm_mode N₂ u p) x)
  have h₃ := hF.postTarget N₃.L0nil (fun u p x =>
    DFunLike.congr_fun (Contra.L0nil_comm_mode N₃ u p) x)
  change Pz.postTarget N₃.L0nil F ∈ jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule at h₃
  change Pz.preFirst N₁.L0nil F ∈ jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule at h₁
  change Pz.preSecond N₂.L0nil F ∈ jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule at h₂
  have h := (jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule).sub_mem
    ((jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule).sub_mem h₃ h₁) h₂
  convert h using 1

theorem IsJacobiFamily.nilDefect_pow (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F) (k : ℕ) :
    IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule
      (fun n => (Pz.nilDefect N₁ N₂ N₃ ^ k) (F n)) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    simpa only [pow_succ',Module.End.mul_apply] using ih.nilDefect N₁ N₂ N₃

end VOA.LogTensor.Pz
