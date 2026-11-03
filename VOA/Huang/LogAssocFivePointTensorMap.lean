import VOA.Huang.LogAssocFivePointEvaluation
import VOA.Modules.LogTensorPzPointPrecompose
import VOA.Modules.LogTensorPzPointPostcompose

/-! The literal canonical tensor point blocks commute with genuine module
maps in both inputs, with every actual logarithmic coefficient retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePoint
open CategoryTheory VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual canonical tensor block types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The actual tensor of maps carries the true point block to its genuine
image block, independently of changes in the finite logarithmic cutoffs. -/
theorem pointTensorBlock_map {N P N' P' : LogModuleCat W} (f : N ⟶ N') (g : P ⟶ P')
    (ell a b c : ℂ) (x : N.act.weight a) (y : P.act.weight b) :
    (tensorMorphism hC2 f g).1 (pointTensorBlock hC2 N P ell a b c x y)=
      (pointTensorBlock hC2 N' P' ell a b c
        ⟨f.1 x,hom_mem_weight N.act N'.act (toWeakHom f) x.2⟩
        ⟨g.1 y,hom_mem_weight P.act P'.act (toWeakHom g) y.2⟩ : tensorObject hC2 N' P') := by
  have h := tensorMap_intertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration
    N'.act P'.act N'.finiteGeneration P'.finiteGeneration (toWeakHom f) (toWeakHom g)
  have hm (n : ℂ) (k : ℕ) :
      (tensorMorphism hC2 f g).1
        ((tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1 n k x y)=
      (tensorIntertwiner hC2 N'.act P'.act N'.finiteGeneration P'.finiteGeneration).1 n k
        (f.1 x) (g.1 y) := by
    exact congrArg (fun J : LogIntertwiningOperator N.act.toWeakModule P.act.toWeakModule
      (tensorObject hC2 N' P').act.toWeakModule => J.1 n k x y) h
  let K := pointLogCutoff N.act P.act (tensorObject hC2 N P).act a b c
  have hK (k : ℕ) (hk : K≤k) :
      (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1 (a+b-c-1) k x y=0 :=
    pointLogCutoff_vanish N.act P.act (tensorObject hC2 N P).act
      (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration) a b c x.2 y.2 hk
  have hK' (k : ℕ) (hk : K≤k) :
      (tensorIntertwiner hC2 N'.act P'.act N'.finiteGeneration P'.finiteGeneration).1 (a+b-c-1) k
        (f.1 x) (g.1 y)=0 := by
    rw [← hm,hK k hk]
    exact (tensorMorphism hC2 f g).1.map_zero
  change (tensorMorphism hC2 f g).1
    (pointEvaluationBlock N.act P.act (tensorObject hC2 N P).act
      (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
      ell a b c x y : tensorObject hC2 N P)=_
  rw [pointEvaluationBlock_fixed_cutoff N.act P.act (tensorObject hC2 N P).act
      (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration) ell a b c x y K hK,
    pointEvaluationBlock_fixed_cutoff N'.act P'.act (tensorObject hC2 N' P').act
      (tensorIntertwiner hC2 N'.act P'.act N'.finiteGeneration P'.finiteGeneration) ell a b c
      ⟨f.1 x,hom_mem_weight N.act N'.act (toWeakHom f) x.2⟩
      ⟨g.1 y,hom_mem_weight P.act P'.act (toWeakHom g) y.2⟩ K hK',map_smul,map_sum]
  simp only [map_smul]
  apply congrArg (fun q : tensorObject hC2 N' P' => Complex.exp (ell*(c-a-b)) • q)
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun q : tensorObject hC2 N' P' => ell^k • q) (hm _ k)

end VOA.Huang.LogAssocFivePoint
