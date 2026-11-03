/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorEvaluationNatural

/-! # Actual dinaturality of the genuine tensor evaluation morphism -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open Classification.COne Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.SelfDual
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

variable {R X : Type u} [AddCommGroup R] [Module ℂ R] [AddCommGroup X] [Module ℂ X]
variable (hC2 : C2Cofinite W)
  (N : LogVModule W R) (P : LogVModule W X) (hN : FinGen N.toWeakModule)
  (hP : FinGen P.toWeakModule) (hs : W.SelfDual) (f : N.toWeakModule.Hom P.toWeakModule)

/-- The actual evaluation maps obey genuine dinaturality with the actual tensor functor. -/
theorem tensorEvaluation_dinatural :
    (homComp (tensorEvaluationHom hC2 N hN hs)
      (tensorMap hC2 N (contraLog P) hN (finGen_contraLog_of_finGen hC2 P hP)
        N (contraLog N) hN (finGen_contraLog_of_finGen hC2 N hN)
        (weakIdentity N.toWeakModule) (transposeLog N P f))).toLinearMap =
    (homComp (tensorEvaluationHom hC2 P hP hs)
      (tensorMap hC2 N (contraLog P) hN (finGen_contraLog_of_finGen hC2 P hP)
        P (contraLog P) hP (finGen_contraLog_of_finGen hC2 P hP)
        f (weakIdentity (contraLog P).toWeakModule))).toLinearMap := by
  apply tensor_morphism_ext hC2 N (contraLog P) hN
    (finGen_contraLog_of_finGen hC2 P hP) (unitLog W)
  rw [postcompose_comp,postcompose_comp,tensorMap_intertwiner,tensorMap_intertwiner,
    postcompose_precompose,postcompose_precompose,
    tensorEvaluation_intertwiner,tensorEvaluation_intertwiner]
  exact evaluationIntertwiner_dinatural N P f hs

end VOA.C2Rigid.LocalInjective
