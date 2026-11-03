/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzJacobiModes

/-! # Extending generalized-module Jacobi from homogeneous inputs -/
namespace VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

/-- Finite homogeneous decompositions extend an actual Jacobi identity to all states
and all vectors. No derivative equation or semisimplicity is used. -/
theorem modeJacobi_of_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (A₃ : WeakModule W M₃) {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (htr : ModeTruncated F)
    (hJ : ∀ (d : ℤ) (u : V), u ∈ W.grading d → ∀ (a b : ℂ) (x : M₁) (y : M₂),
      x ∈ N₁.weight a → y ∈ N₂.weight b → ∀ (ell m : ℤ) (n : ℂ),
      (∑ᶠ i : ℤ, IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u x y ell m n 0 i) =
      ∑ᶠ i : ℤ, IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u x y ell m n 0 i) :
    ModeJacobi N₁.toWeakModule N₂.toWeakModule A₃ F := by
  intro u w₁ w₂ ell m n
  have hlogtr : ∀ x y n, ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ,
      liftModes F (n+j) k x y = 0 := by
    intro x y n
    obtain ⟨K,hK⟩ := htr x y n
    exact ⟨K,fun j hj _ => hK j hj⟩
  have hfinL := fun (u : V) (w₁ : M₁) (w₂ : M₂) =>
    IsLogIntertwining.jacL_support_finite (A₂ := N₂.toWeakModule) (A₃ := A₃) hlogtr u w₁ w₂ ell m n 0
  have hfinR := fun (u : V) (w₁ : M₁) (w₂ : M₂) =>
    IsLogIntertwining.jacR_support_finite (A₁ := N₁.toWeakModule) (liftModes F) u w₁ w₂ ell m n 0
  set D : V → M₁ → M₂ → M₃ := fun u w₁ w₂ =>
    ∑ᶠ i, IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u w₁ w₂ ell m n 0 i
      - ∑ᶠ i, IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u w₁ w₂ ell m n 0 i with hD
  suffices hz : D u w₁ w₂ = 0 from sub_eq_zero.mp hz
  have hDu : ∀ u u' w₁ w₂, D (u + u') w₁ w₂ = D u w₁ w₂ + D u' w₁ w₂ := by
    intro u u' w₁ w₂
    simp only [hD]
    have e1 : ∀ i, IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) (u + u') w₁ w₂ ell m n 0 i
        = IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u w₁ w₂ ell m n 0 i
          + IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u' w₁ w₂ ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacL, map_add, mode_add, LinearMap.add_apply]
      module
    have e2 : ∀ i, IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) (u + u') w₁ w₂ ell m n 0 i
        = IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u w₁ w₂ ell m n 0 i
          + IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u' w₁ w₂ ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacR, map_add, mode_add, LinearMap.add_apply,
        smul_add]
    rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u w₁ w₂) (hfinL u' w₁ w₂),
      finsum_add_distrib (hfinR u w₁ w₂) (hfinR u' w₁ w₂)]
    abel
  have hDw₁ : ∀ u y y' w₂, D u (y + y') w₂ = D u y w₂ + D u y' w₂ := by
    intro u y y' w₂
    simp only [hD]
    have e1 : ∀ i, IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u (y + y') w₂ ell m n 0 i
        = IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u y w₂ ell m n 0 i
          + IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u y' w₂ ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacL, map_add, LinearMap.add_apply]
      module
    have e2 : ∀ i, IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u (y + y') w₂ ell m n 0 i
        = IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u y w₂ ell m n 0 i
          + IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u y' w₂ ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacR, map_add, LinearMap.add_apply, smul_add]
    rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u y w₂) (hfinL u y' w₂),
      finsum_add_distrib (hfinR u y w₂) (hfinR u y' w₂)]
    abel
  have hDw₂ : ∀ u y z z', D u y (z + z') = D u y z + D u y z' := by
    intro u y z z'
    simp only [hD]
    have e1 : ∀ i, IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u y (z + z') ell m n 0 i
        = IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u y z ell m n 0 i
          + IsLogIntertwining.jacL N₂.toWeakModule A₃ (liftModes F) u y z' ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacL, map_add]
      module
    have e2 : ∀ i, IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u y (z + z') ell m n 0 i
        = IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u y z ell m n 0 i
          + IsLogIntertwining.jacR N₁.toWeakModule (liftModes F) u y z' ell m n 0 i := by
      intro i
      simp only [IsLogIntertwining.jacR, map_add, smul_add]
    rw [finsum_congr e1, finsum_congr e2, finsum_add_distrib (hfinL u y z) (hfinL u y z'),
      finsum_add_distrib (hfinR u y z) (hfinR u y z')]
    abel
  have hu : u ∈ ⨆ d, W.grading d := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading (motive := fun u => D u w₁ w₂ = 0) hu ?_ ?_ ?_
  · intro d u hu
    refine LogFin.induction_on N₁ (C := fun x => D u x w₂ = 0) w₁ ?_ ?_ ?_
    · intro a x hx
      refine LogFin.induction_on N₂ (C := fun y => D u x y = 0) w₂ ?_ ?_ ?_
      · intro b y hy
        exact sub_eq_zero.mpr (hJ d u hu a b x y hx hy ell m n)
      · simp [hD,IsLogIntertwining.jacL,IsLogIntertwining.jacR,liftModes]
      · intro y z hy hz; rw [hDw₂,hy,hz,add_zero]
    · simp [hD,IsLogIntertwining.jacL,IsLogIntertwining.jacR,liftModes]
    · intro x y hx hy; rw [hDw₁,hx,hy,add_zero]
  · simp only [hD,IsLogIntertwining.jacL,IsLogIntertwining.jacR,map_zero,
      mode_zero,LinearMap.zero_apply,smul_zero,finsum_zero,sub_self]
  · intro a b ha hb; rw [hDu,ha,hb,add_zero]

end VOA.LogTensor.Pz
