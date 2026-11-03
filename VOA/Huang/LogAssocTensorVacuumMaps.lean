import VOA.Huang.LogAssocTensorAssociatorEvaluation
import VOA.Huang.LogAssocTensorVacuumProduct
import VOA.Huang.LogAssocCompletedPostcompose
import VOA.Huang.LogAssocIntermediateNatural
import VOA.Classification.COne.McRaeM2TensorUnitCreation

/-! Actual module maps in the logarithmic tensor-unit triangle and the
literal collapse of their canonical completed product vacuum insertion. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open VOA.Classification.COne.McRaeM1
open VOA.Huang.LogAssocTensorOuterModes VOA.Huang.AssocExpansion
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (X : LogVModule W M) (Y : LogVModule W N)
  (hX : FinGen X.toWeakModule) (hY : FinGen Y.toWeakModule)

/-- The actual tensor of the first identity with the second left unit map. -/
def tensorVacuumCollapseHom :
    (rightTripleModule hC2 X (adjointModule W).toLog hX finGen_adjoint Y hY).toWeakModule.Hom
      (tensorModule hC2 X Y hX hY).toWeakModule :=
  tensorMap hC2 X (leftUnitTensor hC2 Y hY) hX
    (tensorModule_finGen hC2 (adjointModule W).toLog Y finGen_adjoint hY)
    X Y hX hY (weakIdentity X.toWeakModule) (tensorLeftUnitHom hC2 Y hY)

/-- The actual long triangle path through the constructed associator. -/
def tensorTriangleLongHom :
    (leftTripleModule hC2 X (adjointModule W).toLog hX finGen_adjoint Y hY).toWeakModule.Hom
      (tensorModule hC2 X Y hX hY).toWeakModule :=
  homComp (tensorVacuumCollapseHom hC2 X Y hX hY)
    (tensorAssociatorHom hC2 X (adjointModule W).toLog Y hX finGen_adjoint hY)

/-- The actual short triangle path through the first right unit map. -/
def tensorTriangleShortHom :
    (leftTripleModule hC2 X (adjointModule W).toLog hX finGen_adjoint Y hY).toWeakModule.Hom
      (tensorModule hC2 X Y hX hY).toWeakModule :=
  tensorMap hC2 (rightUnitTensor hC2 X hX) Y
    (tensorModule_finGen hC2 X (adjointModule W).toLog hX finGen_adjoint) hY
    X Y hX hY (tensorRightUnitHom hC2 X hX) (weakIdentity Y.toWeakModule)

/-- Collapse of the literal canonical vacuum product under the actual left
unit tensor map, retaining the other operator's entire logarithmic evaluation. -/
theorem tensorVacuumCollapse_completed_product
    {a b : ℂ} {x : M} {y : N} (hx : x∈X.weight a) (hy : y∈Y.weight b)
    (ell β : ℂ) (f : RestrictedDual (tensorDual hC2 X Y hX hY).toGW →ₗ[ℂ] ℂ) :
    completedLogProduct X (adjointModule W).toLog Y
      (rightTripleModule hC2 X (adjointModule W).toLog hX finGen_adjoint Y hY)
      (leftUnitTensor hC2 Y hY)
      (tensorIntertwiner hC2 X (leftUnitTensor hC2 Y hY) hX
        (tensorModule_finGen hC2 (adjointModule W).toLog Y finGen_adjoint hY))
      (tensorIntertwiner hC2 (adjointModule W).toLog Y finGen_adjoint hY)
      ell 0 a β (f ∘ₗ (tensorVacuumCollapseHom hC2 X Y hX hY).toLinearMap) ⟨x,hx⟩ W.vacuum y=
      f (pointEvaluationBlock X Y (tensorModule hC2 X Y hX hY)
        (tensorIntertwiner hC2 X Y hX hY) ell a b β ⟨x,hx⟩ ⟨y,hy⟩) := by
  let U := (adjointModule W).toLog
  let T := leftUnitTensor hC2 Y hY
  let R := rightTripleModule hC2 X U hX finGen_adjoint Y hY
  let Q := tensorModule hC2 X Y hX hY
  let g := tensorVacuumCollapseHom hC2 X Y hX hY
  let lY := tensorLeftUnitHom hC2 Y hY
  let η₁ := tensorIntertwiner hC2 X T hX (tensorModule_finGen hC2 U Y finGen_adjoint hY)
  let η₂ := tensorIntertwiner hC2 U Y finGen_adjoint hY
  let η := tensorIntertwiner hC2 X Y hX hY
  have hg : postcompose g η₁=precompose (weakIdentity X.toWeakModule) lY η :=
    tensorMap_intertwiner hC2 X T hX (tensorModule_finGen hC2 U Y finGen_adjoint hY)
      X Y hX hY (weakIdentity X.toWeakModule) lY
  have hl : postcompose lY η₂=logModuleIntertwiner Y.toWeakModule :=
    tensorLeftUnit_intertwiner hC2 Y hY
  have hp := completedLogProduct_postcompose X U Y R T Q g η₁ η₂ ell 0 a β f ⟨x,hx⟩ W.vacuum y
  have hgm := congrArg (fun Z : LogIntertwiningOperator X.toWeakModule T.toWeakModule Q.toWeakModule =>
    completedLogProduct X U Y Q T Z η₂ ell 0 a β f ⟨x,hx⟩ W.vacuum y) hg
  have hi := completedLogProduct_intermediate X U Y Q T Y lY η η₂ ell 0 a β f ⟨x,hx⟩ W.vacuum y
  have hlm := congrArg (fun Z : LogIntertwiningOperator U.toWeakModule Y.toWeakModule Y.toWeakModule =>
    completedLogProduct X U Y Q Y η Z ell 0 a β f ⟨x,hx⟩ W.vacuum y) hl
  exact hp.symm.trans (hgm.trans (hi.trans (hlm.trans
    (completedLogProduct_module_vacuum X Y Q η adjoint_log_vacuum_mem_weight ell a β f ⟨x,hx⟩ hy))))

end VOA.C2Rigid.LocalInjective
