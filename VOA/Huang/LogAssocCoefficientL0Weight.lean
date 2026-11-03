import VOA.Huang.LogAssocCoefficientL0Nilpotence
import VOA.Huang.LogAssocCoefficientCoproductCompatAt
import VOA.Classification.COne.McRaeM2TensorFiniteLength

/-! Literal all-logarithmic collision coefficients have generalized weight
gamma in the actual compatible weak module and the canonical finite-length
maximal logarithmic tensor dual. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct
open VOA.VHat VOA.VHat.DLM3
open Module (End)
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- The compatible weak module's actual conformal operator is the restriction
of the genuine tensor-dual conformal operator. -/
theorem compatible_L0_coe (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (S : CompatibleSpace N₁.toWeakModule N₂.toWeakModule) (b : S.carrier) :
    (L0 S.weakModule b : BilinearDual (M₁ := M₁) (M₂ := M₂)) = dualL0 N₁ N₂ b := by
  change (mode (S.field W.conformalVector) 1 b : BilinearDual (M₁ := M₁) (M₂ := M₂))=_
  rw [S.mode_field,S.action_homogeneous 1 W.conformalVector_mem_grading_two]
  exact (tauEnd_apply N₁.toWeakModule N₂.toWeakModule 2 W.conformalVector 1 b).symm

/-- Genuine generalized eigenvectors in the full dual retain their eigenvalue
when they belong to an actual compatible submodule. -/
theorem compatible_mem_maxGenEigenspace (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (S : CompatibleSpace N₁.toWeakModule N₂.toWeakModule)
    {b : BilinearDual (M₁ := M₁) (M₂ := M₂)} (hb : b∈S.carrier) {γ : ℂ}
    (hγ : b∈(dualL0 N₁ N₂).maxGenEigenspace γ) :
    (⟨b,hb⟩ : S.carrier) ∈ (L0 S.weakModule).maxGenEigenspace γ := by
  let E : End ℂ S.carrier := L0 S.weakModule-γ • 1
  let F : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) := dualL0 N₁ N₂-γ • 1
  have hstep (x : S.carrier) : (E x : BilinearDual (M₁ := M₁) (M₂ := M₂))=F x := by
    change (L0 S.weakModule x : BilinearDual (M₁ := M₁) (M₂ := M₂))-γ • (x : BilinearDual)=_
    rw [compatible_L0_coe N₁ N₂ S]
    rfl
  have hp (q : ℕ) (x : S.carrier) : ((E^q) x : BilinearDual (M₁ := M₁) (M₂ := M₂))=(F^q) x := by
    induction q with
    | zero => rfl
    | succ q ih => rw [pow_succ',Module.End.mul_apply,hstep,ih,pow_succ',Module.End.mul_apply]
  obtain ⟨q,hq⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hγ
  apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
  refine ⟨q,Subtype.ext ?_⟩
  change ((E^q) ⟨b,hb⟩ : BilinearDual (M₁ := M₁) (M₂ := M₂))=0
  rw [hp]
  exact hq

variable {M₃ M₄ M₅ : Type u}
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
  (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
  (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- The actual coefficient weak module carries each generator at its genuine
generalized gamma weight, with all source Jordan terms retained. -/
theorem coefficientWeakModule_mem_maxGenEigenspace :
    (⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k,
      coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz⟩ :
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) ∈
      (L0 (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)).maxGenEigenspace γ :=
  compatible_mem_maxGenEigenspace N₁ N₂
    (coefficientCompatibleSpace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz)
    (coefficient_mem_maxGenEigenspace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz)

/-- The canonical maximal logarithmic module places each literal coefficient
at its true generalized gamma weight. All membership premises are proved. -/
theorem coefficient_mem_maximal_weight :
    (⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k,
      coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz⟩ :
      maximalCarrier N₁.toWeakModule N₂.toWeakModule) ∈
      (C2Rigid.LocalInjective.maximalLogModule hC2 N₁ N₂ hfg₁ hfg₂).weight γ := by
  apply (C2Rigid.LocalInjective.maximalLogModule hC2 N₁ N₂ hfg₁ hfg₂).maxGenEigenspace_le_weight
  exact compatible_mem_maxGenEigenspace N₁ N₂ (maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule)
    (coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz)
    (coefficient_mem_maxGenEigenspace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz)

end
end VOA.Huang.LogAssocCoefficientL0
