import VOA.Modules.LogTensorPzPointEvaluation
import VOA.Modules.LogTensorPostcompose
import VOA.Modules.LogTensorTwist

/-! Actual module maps transport genuine completed logarithmic point
evaluations. Common finite logarithmic cutoffs give the identities without
ordinary-module, finite-generation, or semisimplicity hypotheses. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Pz
open VOA.LogTensor.Contra
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ Q : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup Q] [Module ℂ Q]
  {W : VertexOperatorAlgebra V}

/-- The actual map of generalized-weight completions induced by a genuine module map. -/
noncomputable def completionMap (N : LogVModule W M₃) (P : LogVModule W Q)
    (g : N.toWeakModule.Hom P.toWeakModule) : Completion N →ₗ[ℂ] Completion P where
  toFun q c := ⟨g.toLinearMap (q c),hom_mem_weight N P g (q c).2⟩
  map_add' q r := by funext c; apply Subtype.ext; simp
  map_smul' s q := by funext c; apply Subtype.ext; simp

@[simp] theorem completionMap_apply (N : LogVModule W M₃) (P : LogVModule W Q)
    (g : N.toWeakModule.Hom P.toWeakModule) (q : Completion N) (c : ℂ) :
    (completionMap N P g q c : Q)=g.toLinearMap (q c) := rfl

/-- Genuine block evaluation commutes with every actual target module map. -/
theorem pointEvaluationBlock_postcompose
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (P : LogVModule W Q) (g : N₃.toWeakModule.Hom P.toWeakModule)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    (pointEvaluationBlock N₁ N₂ P (postcompose g Y) ell a b c x y : Q)=
      g.toLinearMap (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x y) := by
  let K := pointLogCutoff N₁ N₂ N₃ a b c
  have hK : ∀ k,K≤k → Y.1 (a+b-c-1) k x y=0 :=
    fun k hk => pointLogCutoff_vanish N₁ N₂ N₃ Y a b c x.2 y.2 hk
  have hK' : ∀ k,K≤k → (postcompose g Y).1 (a+b-c-1) k x y=0 := by
    intro k hk
    rw [postcompose_apply,hK k hk,map_zero]
  rw [pointEvaluationBlock_fixed_cutoff N₁ N₂ P (postcompose g Y) ell a b c x y K hK',
    pointEvaluationBlock_fixed_cutoff N₁ N₂ N₃ Y ell a b c x y K hK,
    map_smul,map_sum]
  simp only [postcompose_apply,map_smul]

/-- Full chosen-branch evaluation transports into the actual completed target. -/
theorem evaluatePoint_postcompose
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (P : LogVModule W Q) (g : N₃.toWeakModule.Hom P.toWeakModule)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) (x : M₁) (y : M₂) :
    evaluatePoint N₁ N₂ P (postcompose g Y) ell x y=
      completionMap N₃ P g (evaluatePoint N₁ N₂ N₃ Y ell x y) := by
  refine LogFin.induction_on N₁
    (C := fun x => evaluatePoint N₁ N₂ P (postcompose g Y) ell x y=
      completionMap N₃ P g (evaluatePoint N₁ N₂ N₃ Y ell x y)) x ?_ (by simp) ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => evaluatePoint N₁ N₂ P (postcompose g Y) ell x y=
        completionMap N₃ P g (evaluatePoint N₁ N₂ N₃ Y ell x y)) y ?_ (by simp) ?_
    · intro b y hy
      funext c
      apply Subtype.ext
      rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
      change (pointEvaluationBlock N₁ N₂ P (postcompose g Y) ell a b c ⟨x,hx⟩ ⟨y,hy⟩ : Q)=_
      rw [pointEvaluationBlock_postcompose N₁ N₂ N₃ P g Y]
      rw [completionMap_apply,evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
      rfl
    · intro y z hy hz
      simp only [map_add,hy,hz]
  · intro x z hx hz
    simp only [map_add,LinearMap.add_apply,hx,hz]

end VOA.LogTensor.Pz
