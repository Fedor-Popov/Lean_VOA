/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorMaps
import VOA.Modules.LogTensorUnit

/-! # The genuine left unit of the logarithmic tensor construction

The universal factor of the actual module vertex operator is inverse to the
constant vacuum coefficient of the canonical tensor operator. Both directions
are genuine weak-module maps, and both inverse identities are proved.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N : LogVModule W R) (hN : FinGen N.toWeakModule)

abbrev leftUnitTensor :=
  tensorModule hC2 (adjointModule W).toLog N finGen_adjoint hN

/-- The actual module vertex operator induces the genuine left unit morphism. -/
def tensorLeftUnitHom : (leftUnitTensor hC2 N hN).toWeakModule.Hom N.toWeakModule :=
  tensorFactor hC2 (adjointModule W).toLog N finGen_adjoint hN N
    (logModuleIntertwiner N.toWeakModule)

/-- The inverse unit morphism is the actual vacuum coefficient of the canonical
logarithmic tensor operator. -/
def tensorLeftUnitInvHom : N.toWeakModule.Hom (leftUnitTensor hC2 N hN).toWeakModule :=
  homOfSpace (vacuumModeMap N.toWeakModule (leftUnitTensor hC2 N hN).toWeakModule
    (tensorIntertwiner hC2 (adjointModule W).toLog N finGen_adjoint hN))

/-- The actual left unit morphism realizes the actual module vertex operator. -/
theorem tensorLeftUnit_intertwiner :
    postcompose (tensorLeftUnitHom hC2 N hN)
      (tensorIntertwiner hC2 (adjointModule W).toLog N finGen_adjoint hN) =
      logModuleIntertwiner N.toWeakModule :=
  tensorFactor_comp_intertwiner hC2 (adjointModule W).toLog N finGen_adjoint hN N _

/-- The actual constant vacuum coefficient gives the first inverse identity. -/
theorem tensorLeftUnit_hom_inv (x : R) :
    (tensorLeftUnitHom hC2 N hN).toLinearMap
      ((tensorLeftUnitInvHom hC2 N hN).toLinearMap x) = x := by
  have h := congrArg (fun Y : LogIntertwiningOperator (adjointModule W).toWeakModule
      N.toWeakModule N.toWeakModule => Y.1 (-1) 0 W.vacuum x)
    (tensorLeftUnit_intertwiner hC2 N hN)
  dsimp only at h
  rw [postcompose_apply,logModuleIntertwiner_vacuum,LinearMap.id_apply] at h
  exact h

/-- Genuine universal uniqueness and vacuum determination give the other inverse. -/
theorem tensorLeftUnit_inv_hom
    (q : RestrictedDual (tensorDual hC2 (adjointModule W).toLog N finGen_adjoint hN).toGW) :
    (tensorLeftUnitInvHom hC2 N hN).toLinearMap
      ((tensorLeftUnitHom hC2 N hN).toLinearMap q) = q := by
  have he : (homComp (tensorLeftUnitInvHom hC2 N hN)
      (tensorLeftUnitHom hC2 N hN)).toLinearMap = LinearMap.id := by
    apply tensor_morphism_ext hC2 (adjointModule W).toLog N finGen_adjoint hN
      (leftUnitTensor hC2 N hN)
      (g := weakIdentity (leftUnitTensor hC2 N hN).toWeakModule)
    apply (vacuumModeMap_injective N.toWeakModule (leftUnitTensor hC2 N hN).toWeakModule)
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change (tensorLeftUnitInvHom hC2 N hN).toLinearMap
      ((tensorLeftUnitHom hC2 N hN).toLinearMap
        ((tensorLeftUnitInvHom hC2 N hN).toLinearMap x)) =
      (tensorLeftUnitInvHom hC2 N hN).toLinearMap x
    rw [tensorLeftUnit_hom_inv]
  exact congrArg (fun f => f q) he

/-- The actual left tensor unit is a linear equivalence whose two maps are genuine
module morphisms. -/
def tensorLeftUnitEquiv :
    RestrictedDual (tensorDual hC2 (adjointModule W).toLog N finGen_adjoint hN).toGW ≃ₗ[ℂ] R :=
  LinearEquiv.ofLinear (tensorLeftUnitHom hC2 N hN).toLinearMap
    (tensorLeftUnitInvHom hC2 N hN).toLinearMap
    (by ext x; exact tensorLeftUnit_hom_inv hC2 N hN x)
    (by ext q; exact tensorLeftUnit_inv_hom hC2 N hN q)

end VOA.C2Rigid.LocalInjective
