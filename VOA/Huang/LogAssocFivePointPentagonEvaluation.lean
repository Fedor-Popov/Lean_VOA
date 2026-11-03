import VOA.Huang.LogAssocFivePointSewing
import VOA.Huang.LogAssocTensorPentagonReduction

/-! The five genuine sewn evaluation edges identify the two actual pentagon
paths on completed four-input evaluations. The only hypotheses here are
absolute convergence of the displayed actual arrays; canonical convergence
and scalar coefficient faithfulness close the carrier equality separately. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePoint
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual fourfold categorical path types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The concrete three-edge sewing path is exactly the actual long pentagon path. -/
theorem fivePathLong_eq (N P Q R : LogModuleCat W) :
    fiveEdge01 hC2 N P Q R ≫ fiveEdge12 hC2 N P Q R ≫ fiveEdge23 hC2 N P Q R=
      tensorPentagonLong hC2 N P Q R := rfl

-- Actual fourfold categorical path types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The concrete two-edge sewing path is exactly the actual short pentagon path. -/
theorem fivePathShort_eq (N P Q R : LogModuleCat W) :
    fiveEdge04 hC2 N P Q R ≫ fiveEdge43 hC2 N P Q R=
      tensorPentagonShort hC2 N P Q R := rfl

-- Actual fourfold categorical point profiles require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The true sewn five-point evaluations agree along the actual pentagon
paths whenever the six displayed genuine arrays converge absolutely. -/
theorem pentagon_evaluation_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ)
    (hLL : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .left a b c d β
      x y z w r s (f ∘ₗ (tensorPentagonLong hC2 N P Q R).1) p.1 p.2))
    (hLS : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .left a b c d β
      x y z w r s (f ∘ₗ (tensorPentagonShort hC2 N P Q R).1) p.1 p.2))
    (hI : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .inner a b c d β
      x y z w r s ((f ∘ₗ (fiveEdge23 hC2 N P Q R).1) ∘ₗ
        (fiveEdge12 hC2 N P Q R).1) p.1 p.2))
    (hM : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .middle a b c d β
      x y z w r s (f ∘ₗ (fiveEdge23 hC2 N P Q R).1) p.1 p.2))
    (hP : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .pair a b c d β
      x y z w r s (f ∘ₗ (fiveEdge43 hC2 N P Q R).1) p.1 p.2))
    (hR : Summable (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .right a b c d β
      x y z w r s f p.1 p.2)) :
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (tensorPentagonLong hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (tensorPentagonShort hC2 N P Q R).1) := by
  have h01 := evaluationEdge01_of_summable hC2 N P Q R a b c d β x y z w r s hD
    ((f ∘ₗ (fiveEdge23 hC2 N P Q R).1) ∘ₗ (fiveEdge12 hC2 N P Q R).1) hLL hI
  have h12 := evaluationEdge12_of_summable hC2 N P Q R a b c d β x y z w r s hD
    (f ∘ₗ (fiveEdge23 hC2 N P Q R).1) hI hM
  have h23 := evaluationEdge23_of_summable hC2 N P Q R a b c d β x y z w r s hD f hM hR
  have h04 := evaluationEdge04_of_summable hC2 N P Q R a b c d β x y z w r s hD
    (f ∘ₗ (fiveEdge43 hC2 N P Q R).1) hLS hP
  have h43 := evaluationEdge43_of_summable hC2 N P Q R a b c d β x y z w r s hD f hP hR
  exact h01.trans (h12.trans (h23.trans (h43.symm.trans h04.symm)))

end VOA.Huang.LogAssocFivePoint
