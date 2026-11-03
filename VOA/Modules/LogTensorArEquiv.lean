/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArInjective
import VOA.Modules.LogTensorFinLength
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Genuine logarithmic contragredient symmetry of finite fusion spaces

Two faithful actual A-transforms, together with canonical double duality,
force equal dimensions. Thus the proved A-transform represents an actual
linear equivalence whenever the target fusion space is finite-dimensional.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

private def identityHom (A : WeakModule W M₁) : A.Hom A :=
  ⟨LinearMap.id,fun _ _ _ => rfl⟩

/-- Actual canonical evaluation into the double contragredient is a module map. -/
noncomputable def doubleDualHom (N : LogVModule W M₂) :
    N.toWeakModule.Hom (contraLog (contraLog N)).toWeakModule where
  toLinearMap := (doubleDualEquiv N).toLinearMap
  map_act := C2Rigid.iota_mode N.toGW

/-- Transport both actual double-dual slots back to the original modules. -/
noncomputable def returnDoubleMap :
    LogIntertwiningOperator N₁.toWeakModule (contraLog (contraLog N₂)).toWeakModule
      (contraLog (contraLog N₃)).toWeakModule →ₗ[ℂ]
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule where
  toFun Y := postcompose (doubleDualInverseHom N₃)
    (precompose (identityHom N₁.toWeakModule) (doubleDualHom N₂) Y)
  map_add' Y Z := by
    apply Subtype.ext
    funext n k
    ext x y
    simp only [postcompose_apply,precompose_apply,Submodule.coe_add,Pi.add_apply,
      LinearMap.add_apply,map_add]
  map_smul' s Y := by
    apply Subtype.ext
    funext n k
    ext x y
    simp only [postcompose_apply,precompose_apply,SetLike.val_smul,Pi.smul_apply,
      LinearMap.smul_apply,map_smul,RingHom.id_apply]

@[simp] theorem returnDoubleMap_apply
    (Y : LogIntertwiningOperator N₁.toWeakModule (contraLog (contraLog N₂)).toWeakModule
      (contraLog (contraLog N₃)).toWeakModule) (n : ℂ) (k : ℕ) (x : M₁) (y : M₂) :
    (returnDoubleMap N₁ N₂ N₃ Y).1 n k x y =
      (doubleDualEquiv N₃).symm (Y.1 n k x (doubleDualEquiv N₂ y)) := rfl

/-- Actual double-dual transport is faithful on every logarithmic coefficient. -/
theorem returnDoubleMap_injective : Function.Injective (returnDoubleMap N₁ N₂ N₃) := by
  intro Y Z h
  apply Subtype.ext
  funext n k
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro t
  have hz := congrArg (fun Q => Q.1 n k x ((doubleDualEquiv N₂).symm t)) h
  simp only [returnDoubleMap_apply,LinearEquiv.apply_symm_apply] at hz
  exact (doubleDualEquiv N₃).symm.injective hz

/-- The second actual A-transform, transported by genuine double duality. -/
noncomputable def reverseTransformMap :
    LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule →ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule :=
  (returnDoubleMap N₁ N₂ N₃).comp (transformMap N₁ (contraLog N₃) (contraLog N₂))

theorem reverseTransformMap_injective : Function.Injective (reverseTransformMap N₁ N₂ N₃) :=
  (returnDoubleMap_injective N₁ N₂ N₃).comp
    (transformMap_injective N₁ (contraLog N₃) (contraLog N₂))

/-- Finite actual fusion spaces have the genuine contragredient fusion symmetry. -/
theorem finrank_transform_eq
    [FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule)] :
    Module.finrank ℂ (LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) =
      Module.finrank ℂ (LogIntertwiningOperator N₁.toWeakModule
        (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule) := by
  haveI := Module.Finite.of_injective (transformMap N₁ N₂ N₃) (transformMap_injective N₁ N₂ N₃)
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective (transformMap_injective N₁ N₂ N₃))
    (LinearMap.finrank_le_finrank_of_injective (reverseTransformMap_injective N₁ N₂ N₃))

/-- Every genuine logarithmic intertwiner in the dual type is an actual A-transform. -/
theorem transformMap_surjective
    [FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule)] :
    Function.Surjective (transformMap N₁ N₂ N₃) := by
  haveI := Module.Finite.of_injective (transformMap N₁ N₂ N₃) (transformMap_injective N₁ N₂ N₃)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_transform_eq N₁ N₂ N₃)).mp (transformMap_injective N₁ N₂ N₃)

/-- The genuine A-transform equivalence of actual finite logarithmic fusion spaces. -/
noncomputable def transformEquiv
    [FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule)] :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule :=
  LinearEquiv.ofBijective (transformMap N₁ N₂ N₃)
    ⟨transformMap_injective N₁ N₂ N₃,transformMap_surjective N₁ N₂ N₃⟩

/-- Actual C2-cofinite finite-length modules discharge the required finiteness. -/
theorem finiteDimensional_transform_target (hC2 : C2Cofinite W)
    (h₁ : IsFiniteLength (Classification.COne.modeAlg N₁.toWeakModule) M₁)
    (h₂ : IsFiniteLength (Classification.COne.modeAlg N₂.toWeakModule) M₂)
    (h₃ : IsFiniteLength (Classification.COne.modeAlg N₃.toWeakModule) M₃) :
    FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule) :=
  LogFin.finiteDimensional_logIntertwining_of_finiteLength hC2 _ _ _ h₁
    (C2Rigid.isFiniteLength_contra N₃.toGW N₃.weight_le_maxGenEigenspace h₃)
    (C2Rigid.isFiniteLength_contra N₂.toGW N₂.weight_le_maxGenEigenspace h₂)

/-- FHL contragredient symmetry on the actual C2 finite-length logarithmic category. -/
noncomputable def transformEquiv_of_finiteLength (hC2 : C2Cofinite W)
    (h₁ : IsFiniteLength (Classification.COne.modeAlg N₁.toWeakModule) M₁)
    (h₂ : IsFiniteLength (Classification.COne.modeAlg N₂.toWeakModule) M₂)
    (h₃ : IsFiniteLength (Classification.COne.modeAlg N₃.toWeakModule) M₃) :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule := by
  letI := finiteDimensional_transform_target N₁ N₂ N₃ hC2 h₁ h₂ h₃
  exact transformEquiv N₁ N₂ N₃

end VOA.LogTensor.Ar
