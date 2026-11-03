import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Classification.COne.McRaeM2TensorBraiding
import VOA.Classification.COne.McRaeM2SurjectiveCycle

/-! The actual cyclic associator arrows use genuine tensor swap isomorphisms.
Their onto property forces injectivity by the actual finite-length mode algebra;
no inverse-associator, finite ambient dimension, or L0 semisimplicity is assumed. -/
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
/-- The actual associator followed by the genuine logarithmic tensor swap. -/
noncomputable def tensorAssociatorCycleStep :
    (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
      (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule :=
  homComp (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
    h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) 0)
    (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Genuine braiding preserves the onto property of the actual associator. -/
theorem tensorAssociatorCycleStep_surjective
    (hα : Function.Surjective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap) :
    Function.Surjective (tensorAssociatorCycleStep hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap := by
  have hb : Function.Surjective (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) 0).toLinearMap :=
    (tensorBraidEquiv hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) 0).surjective
  exact hb.comp hα

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Onto actual cyclic associators are injective. The finite-length source
is the actual triple tensor, with its genuine mode algebra. -/
theorem tensorAssociator_injective_of_cyclic_onto
    (h₁₂₃ : Function.Surjective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap)
    (h₂₃₁ : Function.Surjective (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁).toLinearMap)
    (h₃₁₂ : Function.Surjective (tensorAssociatorHom hC2 N₃ N₁ N₂ h₃ h₁ h₂).toLinearMap) :
    Function.Injective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap := by
  have hA := tensorModule_finiteLength hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
  have hf := (weakCycle_bijective
    (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule
    (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule
    (leftTripleModule hC2 N₃ N₁ h₃ h₁ N₂ h₂).toWeakModule hA
    (tensorAssociatorCycleStep hC2 N₁ N₂ N₃ h₁ h₂ h₃)
    (tensorAssociatorCycleStep hC2 N₂ N₃ N₁ h₂ h₃ h₁)
    (tensorAssociatorCycleStep hC2 N₃ N₁ N₂ h₃ h₁ h₂)
    (tensorAssociatorCycleStep_surjective hC2 N₁ N₂ N₃ h₁ h₂ h₃ h₁₂₃)
    (tensorAssociatorCycleStep_surjective hC2 N₂ N₃ N₁ h₂ h₃ h₁ h₂₃₁)
    (tensorAssociatorCycleStep_surjective hC2 N₃ N₁ N₂ h₃ h₁ h₂ h₃₁₂)).1
  intro x y hxy
  apply hf
  change (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
    h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) 0).toLinearMap
    ((tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap x)=_
  rw [hxy]
  rfl

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Concrete linear inverse after onto actual cyclic maps have been established. -/
noncomputable def tensorAssociatorEquiv_of_cyclic_onto
    (h₁₂₃ : Function.Surjective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap)
    (h₂₃₁ : Function.Surjective (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁).toLinearMap)
    (h₃₁₂ : Function.Surjective (tensorAssociatorHom hC2 N₃ N₁ N₂ h₃ h₁ h₂).toLinearMap) :
    RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW ≃ₗ[ℂ]
      RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW :=
  LinearEquiv.ofBijective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap
    ⟨tensorAssociator_injective_of_cyclic_onto hC2 N₁ N₂ N₃ h₁ h₂ h₃ h₁₂₃ h₂₃₁ h₃₁₂,h₁₂₃⟩

end VOA.C2Rigid.LocalInjective
