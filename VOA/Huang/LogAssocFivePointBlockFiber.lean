import VOA.Huang.LogAssocFivePointEvaluation
import VOA.Huang.LogAssocFivePointChart
import VOA.Huang.LogAssocTensorAssociatorEvaluation
import VOA.Modules.LogTensorPzPointScaling

/-! Literal canonical block form of logarithmic associativity in every
positive scaled overlap chart. It supplies the fixed-weight pentagon fibers
without a joint convergence or abstract sewing premise. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePoint
open CategoryTheory VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocExpansion VOA.Huang.LogAssocFivePointChart
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The true canonical point evaluation component is its literal block. -/
theorem pointTensor_eq_block (N P : LogModuleCat W) (ell a b c : ℂ)
    (x : N.act.weight a) (y : P.act.weight b) :
    pointTensor hC2 N P ell x y c=pointTensorBlock hC2 N P ell a b c x y :=
  evaluatePoint_eq_block N.act P.act (tensorObject hC2 N P).act
    (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration) ell x.2 y.2 c

-- The actual triple tensor block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Genuine completed logarithmic associativity is exactly the equality
of the two actual canonical block fibers at positive r<s. -/
theorem associator_block_fiber (N P Q : LogModuleCat W) (a b c β : ℂ)
    (x : N.act.weight a) (y : P.act.weight b) (z : Q.act.weight c)
    (r s : ℝ) (hr : 0<r) (hs : 0<s) (hrs : r<s)
    (f : tensorObject hC2 N (tensorObject hC2 P Q) →ₗ[ℂ] ℂ) :
    (∑' γ : ℂ,f (pointTensorBlock hC2 N (tensorObject hC2 P Q)
      (Complex.log (s+r)) a γ β x (pointTensorBlock hC2 P Q (Complex.log s) b c γ y z)))=
    ∑' γ : ℂ,(f ∘ₗ (associatorIso hC2 N P Q).hom.1)
      (pointTensorBlock hC2 (tensorObject hC2 N P) Q (Complex.log s) γ c β
        (pointTensorBlock hC2 N P (Complex.log r) a b γ x y) z) := by
  let t : ℂ := (Real.log (r/s) : ℝ)
  have ht : t∈VOA.Huang.AssocExpansion.overlapDomain := positive_ratio_mem_overlap hr hs hrs
  have hchart := positive_ratio_chart hr hs
  have he := tensorAssociatorHom_completed_shift (β := β) hC2 N.act P.act Q.act
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration x.2 y.2 z.2 f ht (Complex.log s)
  rw [hchart.1,hchart.2,Complex.ofReal_add] at he
  change (∑' γ : ℂ,f (pointTensorBlock hC2 N (tensorObject hC2 P Q)
      (Complex.log (s+r)) a γ β x (pointTensor hC2 P Q (Complex.log s) y z γ)))=
    ∑' γ : ℂ,(f ∘ₗ (associatorIso hC2 N P Q).hom.1)
      (pointTensorBlock hC2 (tensorObject hC2 N P) Q (Complex.log s) γ c β
        (pointTensor hC2 N P (Complex.log r) x y γ) z) at he
  simp_rw [pointTensor_eq_block hC2 P Q (Complex.log s) b c,
    pointTensor_eq_block hC2 N P (Complex.log r) a b] at he
  exact he

end VOA.Huang.LogAssocFivePoint
