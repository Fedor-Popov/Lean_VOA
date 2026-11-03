import VOA.Huang.LogAssocTensorAssociatorCycle
import VOA.Huang.LogAssocTensorAssociatorSurjectivity

/-! Genuine logarithmic associativity is an actual isomorphism: the analytic
onto theorem and the finite-length cyclic mode-algebra argument prove both
inverse laws. Its inverse is a genuine module map on the actual tensor carrier. -/
set_option maxSynthPendingDepth 3
namespace VOA.C2Rigid.LocalInjective
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The actual associator is injective on the genuine logarithmic tensor carrier. -/
theorem tensorAssociatorHom_injective :
    Function.Injective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap :=
  tensorAssociator_injective_of_cyclic_onto hC2 N₁ N₂ N₃ h₁ h₂ h₃
    (tensorAssociatorHom_surjective hC2 N₁ N₂ N₃ h₁ h₂ h₃)
    (tensorAssociatorHom_surjective hC2 N₂ N₃ N₁ h₂ h₃ h₁)
    (tensorAssociatorHom_surjective hC2 N₃ N₁ N₂ h₃ h₁ h₂)

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The concrete equivalence of the two actual generalized triple tensors. -/
noncomputable def tensorAssociatorEquiv :
    RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW ≃ₗ[ℂ]
      RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW :=
  LinearEquiv.ofBijective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap
    ⟨tensorAssociatorHom_injective hC2 N₁ N₂ N₃ h₁ h₂ h₃,
      tensorAssociatorHom_surjective hC2 N₁ N₂ N₃ h₁ h₂ h₃⟩

@[simp] theorem tensorAssociatorEquiv_apply
    (x : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW) :
    tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃ x=
      (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap x := rfl

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The actual logarithmic associator as a genuine weak-module equivalence. -/
noncomputable def tensorAssociatorModuleEquiv :
    WeakModuleEquiv W
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule where
  toLinearEquiv := tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃
  map_act := (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).map_act

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The actual inverse associator intertwines every genuine VOA mode. -/
noncomputable def tensorAssociatorInverseHom :
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule where
  toLinearMap := (tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).symm.toLinearMap
  map_act u p y := by
    apply (tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).injective
    symm
    change (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap
      ((leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).act u p
        ((tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).symm y))=_
    rw [(tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).map_act]
    change (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).act u p
      ((tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃)
        ((tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).symm y))=_
    rw [LinearEquiv.apply_symm_apply]
    exact ((tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).apply_symm_apply
      ((rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).act u p y)).symm

/-- The inverse followed by the actual associator is the identity. -/
theorem tensorAssociatorHom_inverse_comp :
    (homComp (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
      (tensorAssociatorInverseHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)).toLinearMap=LinearMap.id := by
  apply LinearMap.ext
  intro y
  exact (tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).apply_symm_apply y

/-- The actual associator followed by its inverse is the identity. -/
theorem tensorAssociatorInverseHom_comp :
    (homComp (tensorAssociatorInverseHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
      (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)).toLinearMap=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact (tensorAssociatorEquiv hC2 N₁ N₂ N₃ h₁ h₂ h₃).symm_apply_apply x

end VOA.C2Rigid.LocalInjective
