/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArBranches
import VOA.Modules.LogTensorDualFinGen

/-! # Actual invertible A-transform branches on the finite module category -/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Pz Contra
noncomputable section
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

private def identityHom (N : WeakModule W M₃) : N.Hom N :=
  ⟨LinearMap.id,fun _ _ _ => rfl⟩

/-- The inverse of an integer conformal turn is itself a genuine module map. -/
def branchTurnInverseHom (N : LogVModule W M₁) (r : ℤ) : N.toWeakModule.Hom N.toWeakModule where
  toLinearMap := (branchTurn N r).symm.toLinearMap
  map_act u p x := by
    apply (branchTurn N r).injective
    change branchTurn N r ((branchTurn N r).symm (mode (N.YM u) p x)) =
      branchTurn N r (mode (N.YM u) p ((branchTurn N r).symm x))
    rw [LinearEquiv.apply_symm_apply,branchTurn_mode,LinearEquiv.apply_symm_apply]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

/-- Actual integer branch transport is an equivalence of logarithmic operator spaces. -/
def branchPrecomposeEquiv (r : ℤ) :
    LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule where
  toLinearMap := precomposeLinear (branchTurnHom N₁ r) (identityHom (contraLog N₃).toWeakModule)
  invFun := precompose (branchTurnInverseHom N₁ r) (identityHom (contraLog N₃).toWeakModule)
  left_inv Y := by
    apply Subtype.ext
    funext n k
    ext x t
    change Y.1 n k (branchTurn N₁ r ((branchTurn N₁ r).symm x)) t = _
    rw [LinearEquiv.apply_symm_apply]
  right_inv Y := by
    apply Subtype.ext
    funext n k
    ext x t
    change Y.1 n k ((branchTurn N₁ r).symm (branchTurn N₁ r x)) t = _
    rw [LinearEquiv.symm_apply_apply]

/-- Every genuine A_r branch is a linear equivalence when its fusion target is finite. -/
def transformBranchEquiv (r : ℤ)
    [FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule)] :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule :=
  (transformEquiv N₁ N₂ N₃).trans (branchPrecomposeEquiv N₁ N₂ N₃ r)

@[simp] theorem transformBranchEquiv_apply (r : ℤ)
    [FiniteDimensional ℂ (LogIntertwiningOperator N₁.toWeakModule
      (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule)]
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    transformBranchEquiv N₁ N₂ N₃ r Y = transformBranch N₁ N₂ N₃ Y r := rfl

/-- Genuine C2 finite generation discharges every fusion finiteness premise. -/
def transformBranchEquiv_of_finGen (hC2 : C2Cofinite W) (r : ℤ)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule) :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule := by
  letI := finiteDimensional_transform_target N₁ N₂ N₃ hC2
    (finiteLength_of_finGen hC2 N₁.toWeakModule h₁)
    (finiteLength_of_finGen hC2 N₂.toWeakModule h₂)
    (finiteLength_of_finGen hC2 N₃.toWeakModule h₃)
  exact transformBranchEquiv N₁ N₂ N₃ r

end
end VOA.LogTensor.Ar
