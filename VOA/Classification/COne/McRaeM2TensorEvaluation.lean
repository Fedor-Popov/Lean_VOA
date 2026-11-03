/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorSelfDual
import VOA.Modules.LogTensorDualFinGen
import VOA.Classification.COne.McRaeM2TensorRightUnit

/-! # The genuine logarithmic tensor evaluation

The actual module operator, inverse skew symmetry, and proved A-transform
construct the genuine evaluation operator into V′. The invariant-form module
isomorphism transports it into V, and the actual tensor universal property
produces its unique evaluation module morphism.
-/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open Classification.COne VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.SelfDual
universe u
variable {V R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

/-- The actual A-image of the genuine right-unit operator evaluates into the dual unit. -/
def dualUnitEvaluationIntertwiner (N : LogVModule W R) :
    LogIntertwiningOperator N.toWeakModule (contraLog N).toWeakModule (contraLog (unitLog W)).toWeakModule :=
  Ar.transform N (unitLog W) N (rightUnitIntertwiner N)

/-- A fully invariant nondegenerate form gives the actual evaluation into V. -/
def evaluationIntertwinerOfForm (N : LogVModule W R) (B : W.InvariantForm)
    (hfull : B.IsFullyInvariant) (hrad : B.leftRadical = ⊥) :
    LogIntertwiningOperator N.toWeakModule (contraLog N).toWeakModule (unitLog W).toWeakModule :=
  postcompose (formInverseHom B hfull hrad) (dualUnitEvaluationIntertwiner N)

/-- The literal evaluation pairing retains the genuine Jordan-prepared half-turn. -/
theorem evaluationIntertwinerOfForm_pair (N : LogVModule W R) (B : W.InvariantForm)
    (hfull : B.IsFullyInvariant) (hrad : B.leftRadical = ⊥) (n : ℂ) {a : ℂ} {x : R}
    (hx : x ∈ N.weight a) (t : RestrictedDual N.toGW) (v : V) :
    B.form ((evaluationIntertwinerOfForm N B hfull hrad).1 n 0 x t) v =
      dualPairing N.toGW
        (Ar.twI N.toGW (Ar.zeroFamily N (unitLog W) N (Ar.prepared N (unitLog W) N
          (rightUnitIntertwiner N))) a n x v) t := by
  rw [← formMap_pair B]
  change dualPairing (unitLog W).toGW v
    (formMap B ((formEquiv B hrad).symm ((dualUnitEvaluationIntertwiner N).1 n 0 x t))) = _
  rw [← formEquiv_apply B hrad,LinearEquiv.apply_symm_apply]
  change dualPairing (unitLog W).toGW v ((Ar.transform N (unitLog W) N (rightUnitIntertwiner N)).1 n 0 x t) = _
  rw [Ar.transform_logZero,Ar.pair_modes_zero N (unitLog W) N (rightUnitIntertwiner N) n hx]

/-- On a nonzero genuine module the actual evaluation operator is nonzero. -/
theorem evaluationIntertwinerOfForm_ne_zero (N : LogVModule W R) [Nontrivial R]
    (B : W.InvariantForm) (hfull : B.IsFullyInvariant) (hrad : B.leftRadical = ⊥) :
    evaluationIntertwinerOfForm N B hfull hrad ≠ 0 := by
  intro h
  have hd : dualUnitEvaluationIntertwiner N = 0 := by
    apply Subtype.ext
    funext n k
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro t
    have hz := congrArg (fun Y => Y.1 n k x t) h
    change (formEquiv B hrad).symm ((dualUnitEvaluationIntertwiner N).1 n k x t) = 0 at hz
    change (dualUnitEvaluationIntertwiner N).1 n k x t = 0
    apply (formEquiv B hrad).symm.injective
    rw [hz,map_zero]
  have hr := Ar.eq_zero_of_transform N (unitLog W) N (rightUnitIntertwiner N) hd
  have hz := congrArg (omegaEquiv N.toWeakModule (unitLog W).toWeakModule N.toWeakModule 0) hr
  change omegaEquiv N.toWeakModule (unitLog W).toWeakModule N.toWeakModule 0
    ((omegaEquiv N.toWeakModule (unitLog W).toWeakModule N.toWeakModule 0).symm
      (logModuleIntertwiner N.toWeakModule)) = _ at hz
  rw [LinearEquiv.apply_symm_apply] at hz
  have hz0 : (omegaEquiv N.toWeakModule (unitLog W).toWeakModule N.toWeakModule 0) 0 = 0 :=
    LinearEquiv.map_zero _
  exact logModuleIntertwiner_ne_zero N.toWeakModule (hz.trans hz0)

/-- The genuinely chosen invariant form supplied by VOA self-duality. -/
def unitForm (hs : W.SelfDual) : W.InvariantForm := hs.choose

def evaluationIntertwiner (N : LogVModule W R) (hs : W.SelfDual) :
    LogIntertwiningOperator N.toWeakModule (contraLog N).toWeakModule (unitLog W).toWeakModule :=
  evaluationIntertwinerOfForm N (unitForm hs) hs.choose_spec.1 hs.choose_spec.2

variable (hC2 : C2Cofinite W)
  (N : LogVModule W R) (hN : FinGen N.toWeakModule) (hs : W.SelfDual)

abbrev evaluationTensor := tensorModule hC2 N (contraLog N) hN (finGen_contraLog_of_finGen hC2 N hN)

/-- The actual genuine tensor evaluation module morphism, with dual finiteness proved. -/
def tensorEvaluationHom : (evaluationTensor hC2 N hN).toWeakModule.Hom (unitLog W).toWeakModule :=
  tensorFactor hC2 N (contraLog N) hN (finGen_contraLog_of_finGen hC2 N hN)
    (unitLog W) (evaluationIntertwiner N hs)

/-- The actual tensor evaluation realizes the genuine logarithmic evaluation operator. -/
theorem tensorEvaluation_intertwiner :
    postcompose (tensorEvaluationHom hC2 N hN hs)
      (tensorIntertwiner hC2 N (contraLog N) hN (finGen_contraLog_of_finGen hC2 N hN)) =
      evaluationIntertwiner N hs :=
  tensorFactor_comp_intertwiner hC2 N (contraLog N) hN
    (finGen_contraLog_of_finGen hC2 N hN) (unitLog W) _

/-- A nonzero actual module has a nonzero genuine tensor evaluation morphism. -/
theorem tensorEvaluationHom_ne_zero [Nontrivial R] :
    (tensorEvaluationHom hC2 N hN hs).toLinearMap ≠ 0 := by
  intro h
  have hy := tensorEvaluation_intertwiner hC2 N hN hs
  have hz : evaluationIntertwiner N hs = 0 := by
    rw [← hy]
    apply Subtype.ext
    funext n k
    ext x t
    simp only [postcompose_apply,h,LinearMap.zero_apply]
    rfl
  exact evaluationIntertwinerOfForm_ne_zero N (unitForm hs) hs.choose_spec.1 hs.choose_spec.2 hz

end VOA.C2Rigid.LocalInjective
