/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorUnit
import VOA.Modules.LogTensorSkewNatural

/-! # The genuine right logarithmic tensor unit

Actual skew naturality and the vacuum-unit equivalence construct both genuine
module maps and prove both inverse identities, retaining every logarithmic term.
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

abbrev rightUnitTensor :=
  tensorModule hC2 N (adjointModule W).toLog hN finGen_adjoint

/-- The genuine right unit operator is the inverse Ω-image of the module operator. -/
def rightUnitIntertwiner : LogIntertwiningOperator N.toWeakModule
    (adjointModule W).toWeakModule N.toWeakModule :=
  (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule N.toWeakModule 0).symm
    (logModuleIntertwiner N.toWeakModule)

/-- Its genuine universal factor gives the actual right unit morphism. -/
def tensorRightUnitHom : (rightUnitTensor hC2 N hN).toWeakModule.Hom N.toWeakModule :=
  tensorFactor hC2 N (adjointModule W).toLog hN finGen_adjoint N
    (rightUnitIntertwiner N)

/-- The genuine inverse is the vacuum constant of the actual Ω-image of the
canonical right-unit tensor operator. -/
def tensorRightUnitInvHom : N.toWeakModule.Hom (rightUnitTensor hC2 N hN).toWeakModule :=
  homOfSpace (vacuumModeMap N.toWeakModule (rightUnitTensor hC2 N hN).toWeakModule
    (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule
      (rightUnitTensor hC2 N hN).toWeakModule 0
      (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint)))

/-- The actual right unit morphism realizes the genuine right unit operator. -/
theorem tensorRightUnit_intertwiner :
    postcompose (tensorRightUnitHom hC2 N hN)
      (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint) =
      rightUnitIntertwiner N :=
  tensorFactor_comp_intertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint N _

/-- Its skew image realizes the literal actual module vertex operator. -/
theorem tensorRightUnitSkew_intertwiner :
    postcompose (tensorRightUnitHom hC2 N hN)
      (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule
        (rightUnitTensor hC2 N hN).toWeakModule 0
        (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint)) =
      logModuleIntertwiner N.toWeakModule := by
  have h := congrArg
    (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule N.toWeakModule 0)
    (tensorRightUnit_intertwiner hC2 N hN)
  exact (omega_postcompose
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint)
    (tensorRightUnitHom hC2 N hN) 0).symm.trans (h.trans (LinearEquiv.apply_symm_apply
      (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule N.toWeakModule 0)
      (logModuleIntertwiner N.toWeakModule)))

/-- The actual constant skewed vacuum coefficient gives the first inverse identity. -/
theorem tensorRightUnit_hom_inv (x : R) :
    (tensorRightUnitHom hC2 N hN).toLinearMap
      ((tensorRightUnitInvHom hC2 N hN).toLinearMap x) = x := by
  have h := congrArg (fun Y : LogIntertwiningOperator (adjointModule W).toWeakModule
      N.toWeakModule N.toWeakModule => Y.1 (-1) 0 W.vacuum x)
    (tensorRightUnitSkew_intertwiner hC2 N hN)
  dsimp only at h
  rw [postcompose_apply,logModuleIntertwiner_vacuum,LinearMap.id_apply] at h
  exact h

/-- Actual Ω-injectivity, vacuum determination, and universal uniqueness give the
other inverse identity. -/
theorem tensorRightUnit_inv_hom
    (q : RestrictedDual (tensorDual hC2 N (adjointModule W).toLog hN finGen_adjoint).toGW) :
    (tensorRightUnitInvHom hC2 N hN).toLinearMap
      ((tensorRightUnitHom hC2 N hN).toLinearMap q) = q := by
  have he : (homComp (tensorRightUnitInvHom hC2 N hN)
      (tensorRightUnitHom hC2 N hN)).toLinearMap = LinearMap.id := by
    apply tensor_morphism_ext hC2 N (adjointModule W).toLog hN finGen_adjoint
      (rightUnitTensor hC2 N hN)
      (g := weakIdentity (rightUnitTensor hC2 N hN).toWeakModule)
    apply (omegaEquiv N.toWeakModule (adjointModule W).toWeakModule
      (rightUnitTensor hC2 N hN).toWeakModule 0).injective
    erw [omega_postcompose
      (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint)
      (homComp (tensorRightUnitInvHom hC2 N hN) (tensorRightUnitHom hC2 N hN)) 0,
      omega_postcompose
      (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint)
      (weakIdentity (rightUnitTensor hC2 N hN).toWeakModule) 0]
    apply (vacuumModeMap_injective N.toWeakModule (rightUnitTensor hC2 N hN).toWeakModule)
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change (tensorRightUnitInvHom hC2 N hN).toLinearMap
      ((tensorRightUnitHom hC2 N hN).toLinearMap
        ((tensorRightUnitInvHom hC2 N hN).toLinearMap x)) =
      (tensorRightUnitInvHom hC2 N hN).toLinearMap x
    rw [tensorRightUnit_hom_inv]
  exact congrArg (fun f => f q) he

/-- The actual right tensor unit is a linear equivalence with genuine module maps
in both directions. -/
def tensorRightUnitEquiv :
    RestrictedDual (tensorDual hC2 N (adjointModule W).toLog hN finGen_adjoint).toGW ≃ₗ[ℂ] R :=
  LinearEquiv.ofLinear (tensorRightUnitHom hC2 N hN).toLinearMap
    (tensorRightUnitInvHom hC2 N hN).toLinearMap
    (by ext x; exact tensorRightUnit_hom_inv hC2 N hN x)
    (by ext q; exact tensorRightUnit_inv_hom hC2 N hN q)

end VOA.C2Rigid.LocalInjective
