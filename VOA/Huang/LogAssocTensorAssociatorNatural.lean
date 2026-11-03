import VOA.Huang.LogAssocTensorOuterAllInputs
import VOA.Huang.LogAssocTensorOuterPostcompose
import VOA.Huang.LogAssocIntermediateNatural

/-! Naturality of the concrete logarithmic associator on the actual tensor
modules. Every operator in the square is the proved canonical operator or the
genuine representing factor, with all logarithmic degrees retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.C2Rigid.LocalInjective
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.Huang.LogAssocTensorOuterModes
universe u
variable {V M₁ M₂ M₃ X₁ X₂ X₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)
  (P₁ : LogVModule W X₁) (P₂ : LogVModule W X₂) (P₃ : LogVModule W X₃)
  (hp₁ : FinGen P₁.toWeakModule) (hp₂ : FinGen P₂.toWeakModule) (hp₃ : FinGen P₃.toWeakModule)
  (f₁ : N₁.toWeakModule.Hom P₁.toWeakModule)
  (f₂ : N₂.toWeakModule.Hom P₂.toWeakModule)
  (f₃ : N₃.toWeakModule.Hom P₃.toWeakModule)

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The canonical genuine outer operator is natural in all three actual inputs. -/
theorem tensorAssociatorOuter_natural :
    postcompose
      (tensorMap hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
        P₁ (tensorModule hC2 P₂ P₃ hp₂ hp₃)
        hp₁ (tensorModule_finGen hC2 P₂ P₃ hp₂ hp₃) f₁
        (tensorMap hC2 N₂ N₃ h₂ h₃ P₂ P₃ hp₂ hp₃ f₂ f₃))
      (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃)=
    precompose (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂) f₃
      (tensorAssociatorOuter hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃) := by
  let S := tensorModule hC2 N₂ N₃ h₂ h₃
  let T := tensorModule hC2 P₂ P₃ hp₂ hp₃
  let hS := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  let hT := tensorModule_finGen hC2 P₂ P₃ hp₂ hp₃
  let R := rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  let Q := rightTripleModule hC2 P₁ P₂ hp₁ hp₂ P₃ hp₃
  let hR := tensorModule_finGen hC2 N₁ S h₁ hS
  let hQ := tensorModule_finGen hC2 P₁ T hp₁ hT
  let ψ := tensorMap hC2 N₂ N₃ h₂ h₃ P₂ P₃ hp₂ hp₃ f₂ f₃
  let g := tensorMap hC2 N₁ S h₁ hS P₁ T hp₁ hT f₁ ψ
  let A := tensorIntertwiner hC2 N₁ S h₁ hS
  let B := tensorIntertwiner hC2 N₂ N₃ h₂ h₃
  let C := tensorIntertwiner hC2 P₁ T hp₁ hT
  let D := tensorIntertwiner hC2 P₂ P₃ hp₂ hp₃
  change postcompose g
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ R S h₁ h₂ h₃ hR hS A B)=_
  rw [← tensorOuterIntertwiner_postcompose hC2 N₁ N₂ N₃ R S h₁ h₂ h₃ hR hS A B Q hQ g]
  have hg : postcompose g A=precompose f₁ ψ C :=
    tensorMap_intertwiner hC2 N₁ S h₁ hS P₁ T hp₁ hT f₁ ψ
  rw [hg]
  have hi := tensorOuterIntertwiner_intermediate N₁ N₂ N₃ Q S T ψ
    (precompose f₁ (weakIdentity T.toWeakModule) C) B hC2
    h₁ h₂ h₃ hQ hS hT
  change tensorOuterIntertwiner hC2 N₁ N₂ N₃ Q S h₁ h₂ h₃ hQ hS
      (precompose (weakIdentity N₁.toWeakModule) ψ
        (precompose f₁ (weakIdentity T.toWeakModule) C)) B=_
  rw [hi]
  have hψ : postcompose ψ B=precompose f₂ f₃ D :=
    tensorMap_intertwiner hC2 N₂ N₃ h₂ h₃ P₂ P₃ hp₂ hp₃ f₂ f₃
  rw [hψ]
  exact tensorOuterIntertwiner_precompose_all hC2 P₁ P₂ P₃ Q T hp₁ hp₂ hp₃ hQ hT
    C D N₁ N₂ h₁ h₂ f₁ f₂ N₃ h₃ f₃

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The square of actual associators and tensor morphisms commutes. -/
theorem tensorAssociatorHom_natural :
    (tensorMap hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
      h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
      P₁ (tensorModule hC2 P₂ P₃ hp₂ hp₃)
      hp₁ (tensorModule_finGen hC2 P₂ P₃ hp₂ hp₃) f₁
      (tensorMap hC2 N₂ N₃ h₂ h₃ P₂ P₃ hp₂ hp₃ f₂ f₃)).toLinearMap.comp
      (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap=
    (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃).toLinearMap.comp
      (tensorMap hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
        (tensorModule hC2 P₁ P₂ hp₁ hp₂) P₃
        (tensorModule_finGen hC2 P₁ P₂ hp₁ hp₂) hp₃
        (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂) f₃).toLinearMap := by
  let T := tensorModule hC2 N₁ N₂ h₁ h₂
  let Q := tensorModule hC2 P₁ P₂ hp₁ hp₂
  let hT := tensorModule_finGen hC2 N₁ N₂ h₁ h₂
  let hQ := tensorModule_finGen hC2 P₁ P₂ hp₁ hp₂
  let L := tensorMap hC2 T N₃ hT h₃ Q P₃ hQ hp₃
    (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂) f₃
  let R := tensorMap hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
    h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
    P₁ (tensorModule hC2 P₂ P₃ hp₂ hp₃)
    hp₁ (tensorModule_finGen hC2 P₂ P₃ hp₂ hp₃) f₁
    (tensorMap hC2 N₂ N₃ h₂ h₃ P₂ P₃ hp₂ hp₃ f₂ f₃)
  apply tensor_morphism_ext hC2 T N₃ hT h₃
    (rightTripleModule hC2 P₁ P₂ hp₁ hp₂ P₃ hp₃)
    (f := homComp R (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃))
    (g := homComp (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃) L)
  have eleft : postcompose (homComp R (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃))
      (tensorIntertwiner hC2 T N₃ hT h₃)=
    postcompose R (postcompose (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
      (tensorIntertwiner hC2 T N₃ hT h₃)) := by
    apply Subtype.ext
    funext n k
    rfl
  have eright : postcompose (homComp (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃) L)
      (tensorIntertwiner hC2 T N₃ hT h₃)=
    postcompose (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃)
      (postcompose L (tensorIntertwiner hC2 T N₃ hT h₃)) := by
    apply Subtype.ext
    funext n k
    rfl
  rw [eleft,eright,tensorAssociatorHom_comp_intertwiner,tensorMap_intertwiner]
  have eswap : postcompose (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃)
      (precompose (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂) f₃
        (tensorIntertwiner hC2 Q P₃ hQ hp₃))=
    precompose (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ hp₁ hp₂ f₁ f₂) f₃
      (postcompose (tensorAssociatorHom hC2 P₁ P₂ P₃ hp₁ hp₂ hp₃)
        (tensorIntertwiner hC2 Q P₃ hQ hp₃)) := by
    apply Subtype.ext
    funext n k
    rfl
  rw [eswap,tensorAssociatorHom_comp_intertwiner]
  exact tensorAssociatorOuter_natural hC2 N₁ N₂ N₃ h₁ h₂ h₃
    P₁ P₂ P₃ hp₁ hp₂ hp₃ f₁ f₂ f₃

end VOA.C2Rigid.LocalInjective
