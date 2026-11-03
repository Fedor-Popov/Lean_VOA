/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzHomFinite

/-! # Every actual compatible map lands in the maximal compatible module

Its genuine linear image is stable, truncated, and compatible. The maximal
construction therefore contains that image, without a finite-length premise.
-/
namespace VOA.LogTensor.Pz
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)
variable {psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)}

/-- The genuine image of an actual compatible map is a compatible stable subspace. -/
noncomputable def CompatibleMap.image (hpsi : CompatibleMap N₁ N₂ N psi) :
    CompatibleSpace N₁.toWeakModule N₂.toWeakModule where
  carrier := LinearMap.range psi
  stable d u hu p b hb := by
    obtain ⟨r,rfl⟩ := hb
    exact ⟨mode (N.YM u) p r,hpsi.map_mode d u hu p r⟩
  truncated b hb d u hu := by
    obtain ⟨r,rfl⟩ := hb
    exact hpsi.truncated r d u hu
  compatible b hb d u hu := by
    obtain ⟨r,rfl⟩ := hb
    exact hpsi.compatible r d u hu

/-- Its image belongs to the actual maximal carrier by construction. -/
theorem CompatibleMap.mem_maximal (hpsi : CompatibleMap N₁ N₂ N psi) (r : R) :
    psi r ∈ maximalCarrier N₁.toWeakModule N₂.toWeakModule :=
  compatibleSpace_le_maximal N₁.toWeakModule N₂.toWeakModule (hpsi.image N₁ N₂ N)
    ⟨r,rfl⟩

/-- The genuine compatible map, with codomain restricted to the maximal weak module. -/
noncomputable def CompatibleMap.toMaximalHom (hpsi : CompatibleMap N₁ N₂ N psi) :
    N.toWeakModule.Hom (maximalWeakModule N₁.toWeakModule N₂.toWeakModule) where
  toLinearMap := psi.codRestrict _ (hpsi.mem_maximal N₁ N₂ N)
  map_act u p r := by
    apply Subtype.ext
    have hu : u ∈ ⨆ d, W.grading d := by
      rw [W.isInternal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction W.grading (motive := fun u =>
      psi (mode (N.YM u) p r) =
        (mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field u) p
          ⟨psi r,hpsi.mem_maximal N₁ N₂ N r⟩ : BilinearDual)) hu ?_ ?_ ?_
    · intro d u hu
      rw [CompatibleSpace.mode_field,CompatibleSpace.action_homogeneous _ p hu]
      exact hpsi.map_mode d u hu p r
    · dsimp only
      have h₁ : mode (N.YM (0:V)) p = 0 := by rw [map_zero]; rfl
      have h₂ : mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field (0:V)) p = 0 := by
        rw [map_zero]; rfl
      rw [h₁,h₂]
      simp only [LinearMap.zero_apply,map_zero,Submodule.coe_zero]
    · intro u v hu hv
      dsimp only at hu hv ⊢
      have h₁ : mode (N.YM (u+v)) p r = mode (N.YM u) p r + mode (N.YM v) p r := by
        rw [map_add]; rfl
      have h₂ : mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field (u+v)) p
          ⟨psi r,hpsi.mem_maximal N₁ N₂ N r⟩ =
          mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field u) p
            ⟨psi r,hpsi.mem_maximal N₁ N₂ N r⟩ +
          mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field v) p
            ⟨psi r,hpsi.mem_maximal N₁ N₂ N r⟩ := by rw [map_add]; rfl
      rw [h₁,h₂,map_add,Submodule.coe_add,hu,hv]

@[simp] theorem CompatibleMap.toMaximalHom_apply (hpsi : CompatibleMap N₁ N₂ N psi) (r : R) :
    ((hpsi.toMaximalHom N₁ N₂ N).toLinearMap r : BilinearDual) = psi r := rfl

end VOA.LogTensor.Pz
