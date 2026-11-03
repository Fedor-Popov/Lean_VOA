/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorRepresenting
import VOA.Modules.LogTensorPrecompose

/-! # Genuine tensor functoriality on actual logarithmic module maps

The representing equivalence constructs tensor maps. Their naturality, identity,
and composition laws follow from the proved universal uniqueness, rather than
being supplied as category structure assumptions.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.OrbMcRae
open VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ X₁ X₂ Z₁ Z₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
  [AddCommGroup Z₁] [Module ℂ Z₁] [AddCommGroup Z₂] [Module ℂ Z₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

/-- The actual identity module morphism. -/
def weakIdentity (B : WeakModule W R) : B.Hom B :=
  ⟨LinearMap.id,fun _ _ _ => rfl⟩

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- Concrete universal uniqueness, phrased directly for actual weak-module Homs. -/
theorem tensor_morphism_ext (N : LogVModule W R)
    {f g : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom N.toWeakModule}
    (h : postcompose f (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      postcompose g (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) :
    f.toLinearMap = g.toLinearMap := by
  have he : (⟨f.toLinearMap,f.map_act⟩ :
      moduleHomSpace (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule N.toWeakModule) =
      ⟨g.toLinearMap,g.map_act⟩ :=
    tensorPostcompose_injective hC2 N₁ N₂ h₁ h₂ N h
  exact congrArg Subtype.val he

variable (P₁ : LogVModule W X₁) (P₂ : LogVModule W X₂)
  (hp₁ : FinGen P₁.toWeakModule) (hp₂ : FinGen P₂.toWeakModule)

/-- The genuine tensor of two actual module morphisms, constructed by representation. -/
def tensorMap (f : N₁.toWeakModule.Hom P₁.toWeakModule)
    (g : N₂.toWeakModule.Hom P₂.toWeakModule) :
    (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom
      (tensorModule hC2 P₁ P₂ hp₁ hp₂).toWeakModule :=
  homOfSpace ((tensorRepresentingEquiv hC2 N₁ N₂ h₁ h₂
    (tensorModule hC2 P₁ P₂ hp₁ hp₂)).symm
      (precompose f g (tensorIntertwiner hC2 P₁ P₂ hp₁ hp₂)))

/-- Naturality of the actual canonical logarithmic tensor operator. -/
theorem tensorMap_intertwiner (f : N₁.toWeakModule.Hom P₁.toWeakModule)
    (g : N₂.toWeakModule.Hom P₂.toWeakModule) :
    postcompose (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f g)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      precompose f g (tensorIntertwiner hC2 P₁ P₂ hp₁ hp₂) :=
  (tensorRepresentingEquiv hC2 N₁ N₂ h₁ h₂
    (tensorModule hC2 P₁ P₂ hp₁ hp₂)).apply_symm_apply _

/-- Tensoring actual identity maps gives the actual identity on the tensor carrier. -/
theorem tensorMap_identity :
    (tensorMap hC2 N₁ N₂ h₁ h₂ N₁ N₂ h₁ h₂
      (weakIdentity N₁.toWeakModule) (weakIdentity N₂.toWeakModule)).toLinearMap = LinearMap.id := by
  apply tensor_morphism_ext hC2 N₁ N₂ h₁ h₂
    (tensorModule hC2 N₁ N₂ h₁ h₂)
    (g := weakIdentity (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule)
  rw [tensorMap_intertwiner]
  apply Subtype.ext
  funext n k
  ext x y
  rfl

variable (Q₁ : LogVModule W Z₁) (Q₂ : LogVModule W Z₂)
  (hq₁ : FinGen Q₁.toWeakModule) (hq₂ : FinGen Q₂.toWeakModule)

/-- Tensoring actual composites is the composite of the actual tensor maps. -/
theorem tensorMap_composition (f₁ : N₁.toWeakModule.Hom P₁.toWeakModule)
    (f₂ : N₂.toWeakModule.Hom P₂.toWeakModule)
    (g₁ : P₁.toWeakModule.Hom Q₁.toWeakModule) (g₂ : P₂.toWeakModule.Hom Q₂.toWeakModule) :
    (tensorMap hC2 N₁ N₂ h₁ h₂ Q₁ Q₂ hq₁ hq₂
      (homComp g₁ f₁) (homComp g₂ f₂)).toLinearMap =
      (homComp (tensorMap hC2 P₁ P₂ hp₁ hp₂ Q₁ Q₂ hq₁ hq₂ g₁ g₂)
        (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂)).toLinearMap := by
  apply tensor_morphism_ext hC2 N₁ N₂ h₁ h₂
    (tensorModule hC2 Q₁ Q₂ hq₁ hq₂)
  rw [tensorMap_intertwiner]
  let F := tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂
  let G := tensorMap hC2 P₁ P₂ hp₁ hp₂ Q₁ Q₂ hq₁ hq₂ g₁ g₂
  have hpost : postcompose (homComp G F) (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      postcompose G (postcompose F (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl
  rw [hpost,tensorMap_intertwiner]
  have hswap : postcompose G (precompose f₁ f₂ (tensorIntertwiner hC2 P₁ P₂ hp₁ hp₂)) =
      precompose f₁ f₂ (postcompose G (tensorIntertwiner hC2 P₁ P₂ hp₁ hp₂)) := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl
  rw [hswap,tensorMap_intertwiner]
  apply Subtype.ext
  funext n k
  ext x y
  rfl

end VOA.C2Rigid.LocalInjective
