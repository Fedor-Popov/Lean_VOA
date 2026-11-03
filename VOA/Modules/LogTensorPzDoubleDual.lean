/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzCompatibleLift
import VOA.Classification.COne.McRaeM2Swap

/-! # Actual logarithmic transposes and inverse double duality

Weak module maps preserve the genuine generalized eigenspace grading. The
restricted-dual transpose and the canonical double-dual isomorphism therefore
act on actual logarithmic modules without any semisimplicity premise.
-/
namespace VOA.LogTensor.Pz
open Module (Dual)
universe u
variable {V R X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] [AddCommGroup X] [Module ℂ X]
  {W : VertexOperatorAlgebra V}

/-- The genuine restricted-dual transpose of an actual logarithmic module map. -/
noncomputable def transposeLog (A : LogVModule W R) (B : LogVModule W X)
    (f : A.toWeakModule.Hom B.toWeakModule) :
    (contraLog B).toWeakModule.Hom (contraLog A).toWeakModule :=
  C2Rigid.transpose A.toGW B.toGW f
    (C2Rigid.gradedHom_of_isGenGraded A.toGW B.toGW f
      A.weight_le_maxGenEigenspace B.weight_le_maxGenEigenspace)

/-- Its pairing is the actual adjunction, on arbitrary vectors. -/
theorem transposeLog_pair (A : LogVModule W R) (B : LogVModule W X)
    (f : A.toWeakModule.Hom B.toWeakModule) (x : R) (r : C2Rigid.RestrictedDual B.toGW) :
    C2Rigid.dualPairing A.toGW x ((transposeLog A B f).toLinearMap r) =
      C2Rigid.dualPairing B.toGW (f.toLinearMap x) r :=
  C2Rigid.pairing_transposeL_all A.toGW B.toGW f _ x r

/-- The actual canonical double-dual linear equivalence. -/
noncomputable def doubleDualEquiv (N : LogVModule W R) :
    R ≃ₗ[ℂ] C2Rigid.RestrictedDual (contraLog N).toGW :=
  LinearEquiv.ofBijective (C2Rigid.iota N.toGW) (C2Rigid.iota_bijective N.toGW)

@[simp] theorem doubleDualEquiv_apply (N : LogVModule W R) (x : R) :
    doubleDualEquiv N x = C2Rigid.iota N.toGW x := rfl

/-- Inverse double duality is itself a genuine weak-module homomorphism. -/
noncomputable def doubleDualInverseHom (N : LogVModule W R) :
    (contraLog (contraLog N)).toWeakModule.Hom N.toWeakModule where
  toLinearMap := (doubleDualEquiv N).symm.toLinearMap
  map_act u p r := by
    apply (doubleDualEquiv N).injective
    change doubleDualEquiv N ((doubleDualEquiv N).symm (mode ((contraLog (contraLog N)).YM u) p r)) =
      doubleDualEquiv N (mode (N.YM u) p ((doubleDualEquiv N).symm r))
    rw [LinearEquiv.apply_symm_apply,doubleDualEquiv_apply]
    have hm : C2Rigid.iota N.toGW (mode (N.YM u) p ((doubleDualEquiv N).symm r)) =
        mode ((contraLog (contraLog N)).YM u) p
          (C2Rigid.iota N.toGW ((doubleDualEquiv N).symm r)) :=
      C2Rigid.iota_mode N.toGW u p ((doubleDualEquiv N).symm r)
    rw [hm]
    change _ = mode ((contraLog (contraLog N)).YM u) p
      (doubleDualEquiv N ((doubleDualEquiv N).symm r))
    rw [LinearEquiv.apply_symm_apply]

/-- The inverse is characterized by the genuine dual pairing. -/
theorem doubleDualInverseHom_pair (N : LogVModule W R)
    (z : C2Rigid.RestrictedDual (contraLog N).toGW) (r : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW ((doubleDualInverseHom N).toLinearMap z) r =
      C2Rigid.dualPairing (contraLog N).toGW r z := by
  rw [← C2Rigid.pairing_iota_all N.toGW]
  change C2Rigid.dualPairing (contraLog N).toGW r
      (doubleDualEquiv N ((doubleDualEquiv N).symm z)) = _
  rw [LinearEquiv.apply_symm_apply]

end VOA.LogTensor.Pz
