import VOA.Huang.LogAssocTensorOuterJacobi
import VOA.Classification.COne.McRaeM2TensorRepresenting
import VOA.Classification.COne.McRaeM2TensorNestedGeneration

/-! Literal outer modes on the actual logarithmic tensor object, obtained
from the actual collision coefficient inclusion in its tensor dual. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct VOA.C2Rigid VOA.C2Rigid.LocalInjective
open VOA.Classification.COne
open Module (Dual)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
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
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅




/-- The literal actual logarithmic outer operator has its genuine universal
tensor factor, as an actual module morphism. -/
noncomputable def tensorOuterFactor :
    (tensorModule hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
      (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃).toWeakModule.Hom N₄.toWeakModule :=
  tensorFactor hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃ N₄
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

/-- Every mode and every genuine logarithmic degree of the outer operator
is recovered by this concrete factor. -/
theorem tensorOuterFactor_comp_intertwiner :
    postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)=
      tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
  tensorFactor_comp_intertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃ N₄
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

theorem tensorOuterFactor_apply (n : ℂ) (k : ℕ)
    (ξ : C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW) (z : M₃) :
    (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap
      ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃).1 n k ξ z)=
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).1 n k ξ z := by
  have he := congrArg (fun Y : LogIntertwiningOperator
      (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule N₃.toWeakModule N₄.toWeakModule => Y.1 n k ξ z)
    (tensorOuterFactor_comp_intertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
  exact he

/-- The actual universal factor is uniquely determined by its canonical
logarithmic intertwiner, using the genuine representing equivalence. -/
theorem tensorOuterFactor_unique
    (f : (tensorModule hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
      (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃).toWeakModule.Hom N₄.toWeakModule)
    (hf : postcompose f (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
      (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)=
      tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    f.toLinearMap=(tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap := by
  let ef : moduleHomSpace
      (tensorModule hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃).toWeakModule N₄.toWeakModule :=
    ⟨f.toLinearMap,f.map_act⟩
  let eg : moduleHomSpace
      (tensorModule hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃).toWeakModule N₄.toWeakModule :=
    ⟨(tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap,
      (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).map_act⟩
  have he : ef=eg := tensorPostcompose_injective hC2
    (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃ N₄
    (hf.trans (tensorOuterFactor_comp_intertwiner hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).symm)
  exact congrArg Subtype.val he

end VOA.Huang.LogAssocTensorOuterModes

namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocTensorOuterModes
open VOA.Classification.COne
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- The concrete associator direction ((N1 tensor N2) tensor N3) to
(N1 tensor (N2 tensor N3)), built from the actual canonical product. -/
noncomputable def tensorAssociatorHom :
    (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule :=
  tensorOuterFactor hC2 N₁ N₂ N₃
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
    (tensorModule hC2 N₂ N₃ h₂ h₃) h₁ h₂ h₃
    (tensorModule_finGen hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
    (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
    (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)


/-- The genuine outer operator for the actual canonical right-associated product. -/
noncomputable def tensorAssociatorOuter :
    LogIntertwiningOperator (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule N₃.toWeakModule
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule :=
  tensorOuterIntertwiner hC2 N₁ N₂ N₃
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
    (tensorModule hC2 N₂ N₃ h₂ h₃) h₁ h₂ h₃
    (tensorModule_finGen hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
    (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
    (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)

/-- The actual associator morphism recovers its canonical outer operator,
including all logarithmic modes. -/
theorem tensorAssociatorHom_comp_intertwiner :
    postcompose (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)=
      tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃ :=
  tensorFactor_comp_intertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
    (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃)

/-- Concrete all-log action of the actual associator on canonical tensor modes. -/
theorem tensorAssociatorHom_apply (n : ℂ) (k : ℕ)
    (ξ : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) (z : M₃) :
    (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap
      ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n k ξ z)=
      (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃).1 n k ξ z := by
  exact congrArg (fun Y : LogIntertwiningOperator (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule
      N₃.toWeakModule (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule => Y.1 n k ξ z)
    (tensorAssociatorHom_comp_intertwiner hC2 N₁ N₂ N₃ h₁ h₂ h₃)

/-- Flattened nested canonical coefficients characterize this actual direction. -/
theorem tensorAssociatorHom_nested (n m : ℂ) (k l : ℕ) (x : M₁) (y : M₂) (z : M₃) :
    (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap
      ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n k
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m l x y) z)=
      (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃).1 n k
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m l x y) z :=
  tensorAssociatorHom_apply hC2 N₁ N₂ N₃ h₁ h₂ h₃ n k _ z

end VOA.C2Rigid.LocalInjective
