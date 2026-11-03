/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzCompatibleFinite

/-! # Actual module-Hom finiteness into the maximal compatible weak module

Every actual module map into a compatible tensor-dual space supplies a genuine
compatible map. The injective logarithmic reconstruction therefore bounds its
Hom space by actual logarithmic fusion. This applies to the canonical maximal
compatible weak module without assuming it already has finite length.
-/

namespace VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ R X : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup R] [Module ℂ R]
  [AddCommGroup X] [Module ℂ X]

/-- The actual linear space of maps intertwining all genuine weak-module modes. -/
noncomputable def moduleHomSpace (A : WeakModule W R) (B : WeakModule W X) :
    Submodule ℂ (R →ₗ[ℂ] X) where
  carrier := {f | ∀ (u : V) (p : ℤ) (r : R),
    f (mode (A.YM u) p r) = mode (B.YM u) p (f r)}
  zero_mem' := by intro u p r; simp
  add_mem' hf hg := by
    intro u p r
    simp only [LinearMap.add_apply,map_add,hf u p r,hg u p r]
  smul_mem' s f hf := by
    intro u p r
    simp only [LinearMap.smul_apply,map_smul,hf u p r]

/-- A member of the actual Hom space, as the library's genuine weak-module Hom. -/
def homOfSpace {A : WeakModule W R} {B : WeakModule W X} (f : moduleHomSpace A B) : A.Hom B where
  toLinearMap := f.1
  map_act := f.2

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)
variable (S : CompatibleSpace N₁.toWeakModule N₂.toWeakModule)

/-- Composing a genuine module Hom with the compatible space's inclusion gives an
actual compatible generalized-module map into the algebraic tensor dual. -/
noncomputable def homToCompatible :
    moduleHomSpace N.toWeakModule S.weakModule →ₗ[ℂ] compatibleMaps N₁ N₂ N where
  toFun f := ⟨S.carrier.subtype ∘ₗ f.1,by
    refine ⟨?_,?_,?_⟩
    · intro d u hu p r
      simp only [LinearMap.comp_apply,f.2 u p r]
      change (mode (S.field u) p (f.1 r) : BilinearDual (M₁ := M₁) (M₂ := M₂)) = _
      rw [S.mode_field,S.action_homogeneous p hu]
      rfl
    · intro r d u hu
      exact S.truncated (f.1 r) (f.1 r).2 d u hu
    · intro r d u hu
      exact S.compatible (f.1 r) (f.1 r).2 d u hu⟩
  map_add' f g := by
    apply Subtype.ext
    ext r x y
    rfl
  map_smul' s f := by
    apply Subtype.ext
    ext r x y
    rfl

/-- The compatible inclusion loses no actual module map. -/
theorem homToCompatible_injective : Function.Injective (homToCompatible N₁ N₂ N S) := by
  intro f g h
  apply Subtype.ext
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  exact congrArg (fun p : compatibleMaps N₁ N₂ N => p.1 r) h

/-- Genuine Hom-finiteness into any compatible weak module follows from actual
C₂ logarithmic fusion finiteness, even when that target has no finite-length bound. -/
theorem finiteDimensional_moduleHomSpace_of_c2Cofinite (hC2 : C2Cofinite W)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
    (h₃ : FinGen (contraLog N).toWeakModule) :
    FiniteDimensional ℂ (moduleHomSpace N.toWeakModule S.weakModule) := by
  haveI := finiteDimensional_compatibleMaps_of_c2Cofinite N₁ N₂ N hC2 h₁ h₂ h₃
  exact FiniteDimensional.of_injective (homToCompatible N₁ N₂ N S)
    (homToCompatible_injective N₁ N₂ N S)

/-- In particular, the canonical maximal compatible weak module has finite actual
Hom spaces from every finite generalized source with finitely generated dual. -/
theorem finiteDimensional_maximalHomSpace_of_c2Cofinite (hC2 : C2Cofinite W)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
    (h₃ : FinGen (contraLog N).toWeakModule) :
    FiniteDimensional ℂ
      (moduleHomSpace N.toWeakModule (maximalWeakModule N₁.toWeakModule N₂.toWeakModule)) :=
  finiteDimensional_moduleHomSpace_of_c2Cofinite N₁ N₂ N
    (maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule) hC2 h₁ h₂ h₃

end VOA.LogTensor.Pz
