/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorObject
import VOA.Modules.LogTensorPzForwardCompatible
import VOA.Modules.LogTensorPzImage
import VOA.Modules.LogTensorPzDoubleDual
import VOA.Modules.LogTensorPostcompose

/-! # Universal factorization of the genuine logarithmic tensor intertwiner

Completed evaluation supplies an actual contragredient module map into the
maximal compatible module. Its genuine transpose, followed by inverse double
duality, factors the original logarithmic intertwiner through the tensor object.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.OrbMcRae
open VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
open Module (Dual)
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
  (N : LogVModule W R)
  (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N.toWeakModule)

/-- The actual contragredient target maps into the maximal compatible module. -/
def tensorForward : (contraLog N).toWeakModule.Hom
    (tensorDual hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  (forward_compatibleMap N₁ N₂ N Y).toMaximalHom N₁ N₂ (contraLog N)

@[simp] theorem tensorForward_apply (r : RestrictedDual N.toGW) :
    ((tensorForward hC2 N₁ N₂ h₁ h₂ N Y).toLinearMap r :
      BilinearDual (M₁ := M₁) (M₂ := M₂)) = forward N₁ N₂ N Y r := rfl

/-- The genuine universal factor: transpose of completed evaluation followed by the
actual inverse canonical double-dual isomorphism. -/
def tensorFactor : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom N.toWeakModule :=
  homComp (doubleDualInverseHom N)
    (transposeLog (contraLog N) (tensorDual hC2 N₁ N₂ h₁ h₂)
      (tensorForward hC2 N₁ N₂ h₁ h₂ N Y))

/-- Its actual dual pairing is the completed matrix coefficient. -/
theorem tensorFactor_pair
    (q : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW)
    (r : RestrictedDual N.toGW) :
    dualPairing N.toGW ((tensorFactor hC2 N₁ N₂ h₁ h₂ N Y).toLinearMap q) r =
      dualPairing (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
        ((tensorForward hC2 N₁ N₂ h₁ h₂ N Y).toLinearMap r) q := by
  change dualPairing N.toGW ((doubleDualInverseHom N).toLinearMap
      ((transposeLog (contraLog N) (tensorDual hC2 N₁ N₂ h₁ h₂)
        (tensorForward hC2 N₁ N₂ h₁ h₂ N Y)).toLinearMap q)) r = _
  rw [doubleDualInverseHom_pair,transposeLog_pair]

/-- The canonical tensor operator has the actual zeroth modes of its inclusion. -/
theorem tensorIntertwiner_logZero (n : ℂ) :
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 =
      baseModes N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
        (tensorInclusion hC2 N₁ N₂ h₁ h₂).1 n := by
  change logLift N₁ N₂ (tensorModule hC2 N₁ N₂ h₁ h₂)
    (baseModes N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
      (tensorInclusion hC2 N₁ N₂ h₁ h₂).1) n 0 = _
  exact logLift_zero _ _ _ _ n

/-- The genuine factor map recovers the original logarithmic intertwiner, at every
mode and every logarithmic degree. -/
theorem tensorFactor_comp_intertwiner :
    postcompose (tensorFactor hC2 N₁ N₂ h₁ h₂ N Y)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) = Y := by
  apply evaluateOne_injective N₁ N₂ N
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  funext c
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  rw [map_sub]
  apply sub_eq_zero.mpr
  let r : RestrictedDual N.toGW := DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) c f
  have hr : r ∈ (contraLog N).weight c := ⟨f,rfl⟩
  have hs : (tensorForward hC2 N₁ N₂ h₁ h₂ N Y).toLinearMap r ∈
      (tensorDual hC2 N₁ N₂ h₁ h₂).weight c :=
    gradedHom_of_isGenGraded (contraLog N).toGW (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
      (tensorForward hC2 N₁ N₂ h₁ h₂ N Y)
      (contraLog N).weight_le_maxGenEigenspace
      (tensorDual hC2 N₁ N₂ h₁ h₂).weight_le_maxGenEigenspace c r hr
  have hp := tensorFactor_pair hC2 N₁ N₂ h₁ h₂ N Y
    ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 (a+b-c-1) 0 x y) r
  rw [tensorIntertwiner_logZero,
    pair_baseModes N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
      (tensorInclusion hC2 N₁ N₂ h₁ h₂).1 (a+b-c-1) hx hy hs] at hp
  have hc : c = a+b-(a+b-c-1)-1 := by ring
  simp only [if_pos hc,tensorInclusion_apply,tensorForward_apply] at hp
  rw [forward_homogeneous N₁ N₂ N Y hx hy hr] at hp
  have he : dualPairing N.toGW
      (evaluateOne N₁ N₂ N
        (postcompose (tensorFactor hC2 N₁ N₂ h₁ h₂ N Y)
          (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) x y c) r =
      dualPairing N.toGW (evaluateOne N₁ N₂ N Y x y c) r := by
    rw [evaluateOne_homogeneous N₁ N₂ N _ hx hy c,
      evaluateOne_homogeneous N₁ N₂ N Y hx hy c,postcompose_apply,tensorIntertwiner_logZero]
    exact hp
  change dualPairing N.toGW _ (DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) c f) =
    dualPairing N.toGW _ (DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) c f) at he
  erw [dualPairing_lof_self N.toGW
      (evaluateOne N₁ N₂ N
        (postcompose (tensorFactor hC2 N₁ N₂ h₁ h₂ N Y)
          (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) x y c).2 f,
    dualPairing_lof_self N.toGW (evaluateOne N₁ N₂ N Y x y c).2 f] at he
  exact he

end VOA.C2Rigid.LocalInjective
