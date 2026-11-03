/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorBalancing
import VOA.Classification.COne.McRaeM2TensorBraiding

/-! # Actual logarithmic tensor balancing

The genuine double Ω action and actual conformal exponentials prove the
balancing equation for the canonical tensor swap maps by universal uniqueness.
The associator and its hexagon remain separate analytic obligations.
-/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open Classification.COne Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Composition
variable {M₁ M₂ M₃ M₄ M₅ X₁ X₂ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}
  {B₁ : WeakModule W X₁} {B₂ : WeakModule W X₂}

private theorem postcompose_comp (f : A₃.Hom A₄) (g : A₄.Hom A₅)
    (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    postcompose (homComp g f) Y = postcompose g (postcompose f Y) := by
  apply Subtype.ext
  funext n k
  ext x y
  rfl

private theorem postcompose_precompose (f : B₁.Hom A₁) (g : B₂.Hom A₂)
    (h : A₃.Hom A₄) (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    postcompose h (precompose f g Y) = precompose f g (postcompose h Y) := by
  apply Subtype.ext
  funext n k
  ext x y
  rfl
end Composition

variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- The actual composition of the two canonical zero-branch tensor swaps. -/
def tensorDoubleSwap : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom
    (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  homComp (tensorBraid hC2 N₂ N₁ h₂ h₁ 0) (tensorBraid hC2 N₁ N₂ h₁ h₂ 0)

/-- The actual composed tensor swaps realize genuine double Ω, on all log coefficients. -/
theorem tensorDoubleSwap_intertwiner :
    postcompose (tensorDoubleSwap hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      omegaEquiv N₂.toWeakModule N₁.toWeakModule (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule 0
        (omegaEquiv N₁.toWeakModule N₂.toWeakModule (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule 0
          (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) := by
  change postcompose
    (homComp (tensorBraid hC2 N₂ N₁ h₂ h₁ 0) (tensorBraid hC2 N₁ N₂ h₁ h₂ 0))
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) = _
  rw [postcompose_comp,tensorBraid_intertwiner,
    ← omega_postcompose (tensorIntertwiner hC2 N₂ N₁ h₂ h₁)
      (tensorBraid hC2 N₂ N₁ h₂ h₁ 0) 0,tensorBraid_intertwiner]

/-- Genuine logarithmic balancing of the actual tensor swap and actual conformal twist. -/
theorem tensor_twist_balancing :
    (twistHom (tensorModule hC2 N₁ N₂ h₁ h₂)).toLinearMap =
      (homComp (tensorDoubleSwap hC2 N₁ N₂ h₁ h₂)
        (tensorMap hC2 N₁ N₂ h₁ h₂ N₁ N₂ h₁ h₂ (twistHom N₁) (twistHom N₂))).toLinearMap := by
  apply tensor_morphism_ext hC2 N₁ N₂ h₁ h₂ (tensorModule hC2 N₁ N₂ h₁ h₂)
  rw [postcompose_comp,tensorMap_intertwiner,postcompose_precompose,tensorDoubleSwap_intertwiner,
    omega_zero_twice_balancing N₁ N₂ (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)]

end VOA.C2Rigid.LocalInjective
