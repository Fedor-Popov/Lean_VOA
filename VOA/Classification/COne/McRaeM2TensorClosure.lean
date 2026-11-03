import VOA.Classification.COne.McRaeM2TensorMaps
import VOA.Modules.LogModuleC1Graded
import VOA.Modules.LogTensorUniformNil

/-! Actual finite-module closure of the logarithmic tensor construction.
This discharges the finite-generation and convergence inputs needed when
forming iterated tensor products, rather than assuming them for the tensor. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- The actual logarithmic tensor object has finite length. -/
theorem tensorModule_finiteLength :
    IsFiniteLength (modeAlg (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule)
      (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :=
  C2Rigid.isFiniteLength_contra (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
    (tensorDual hC2 N₁ N₂ h₁ h₂).weight_le_maxGenEigenspace
    (finiteLength_maximal_of_c2 hC2 N₁ N₂ h₁ h₂)

/-- The actual tensor object is finitely generated, so iterated tensors are available. -/
theorem tensorModule_finGen : FinGen (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  finGen_contraLog_of_finiteLength (tensorDual hC2 N₁ N₂ h₁ h₂)
    (finiteLength_maximal_of_c2 hC2 N₁ N₂ h₁ h₂)

/-- The tensor's actual C2 quotient is finite-dimensional. -/
theorem tensorModule_C2_cofinite :
    FiniteDimensional ℂ (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW ⧸
      VOA.Huang.FusionC2.C2M (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule) :=
  ModuleC2.cofinite_of_finGen hC2 _ (tensorModule_finGen hC2 N₁ N₂ h₁ h₂)

/-- The actual C1 quotient of the tensor has a real generalized-weight cutoff. -/
theorem tensorModule_C1_cutoff :
    ∃ b : ℝ, ∀ α : ℂ, b < α.re →
      (tensorModule hC2 N₁ N₂ h₁ h₂).weight α ≤
        ModuleC2.C1M (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  ModuleC2.C1_generalized_weight_cutoff hC2 _
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂)

/-- A single Jordan nilpotence bound works across all tensor weight spaces. -/
theorem tensorModule_uniformJordan :
    IsNilpotent (tensorModule hC2 N₁ N₂ h₁ h₂).L0nil :=
  Contra.L0nil_isNilpotent_of_finGen _ (tensorModule_finGen hC2 N₁ N₂ h₁ h₂)

end VOA.C2Rigid.LocalInjective
