import VOA.Huang.LogAssocFivePointFiberEdges

/-! Joint absolute convergence turns the proved true fixed-weight fibers
into equality of the literal actual five-point evaluations. These are pure
Fubini consequences for the genuine canonical terms, with no sewing witness. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.LogModuleCat
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- Absolute convergence permits summing the second coordinate first. -/
theorem tsum_prod_reverse (F : ℂ × ℂ → ℂ) (hF : Summable F) :
    (∑' p : ℂ × ℂ,F p)=∑' δ : ℂ,∑' γ : ℂ,F (γ,δ) := by
  rw [← (Equiv.prodComm ℂ ℂ).tsum_eq F]
  exact hF.prod_symm.tsum_prod

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Absolute convergence sums the actual sewing fiber along this concrete edge. -/
theorem evaluationEdge01_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .inner →ₗ[ℂ] ℂ)
    (hL : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .left a b c d β
      x y z w r s (f ∘ₗ (fiveEdge01 hC2 N P Q R).1) p.1 p.2)
    (hR : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .inner a b c d β
      x y z w r s f p.1 p.2) :
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (fiveEdge01 hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .inner a b c d β x y z w r s f := by
  unfold fivePointEvaluation
  rw [tsum_prod_reverse _ hL,tsum_prod_reverse _ hR]
  apply tsum_congr
  intro q
  exact fiberEdge01 hC2 N P Q R a b c d β x y z w r s hD f q

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Absolute convergence sums the actual sewing fiber along this concrete edge. -/
theorem evaluationEdge12_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .middle →ₗ[ℂ] ℂ)
    (hL : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .inner a b c d β
      x y z w r s (f ∘ₗ (fiveEdge12 hC2 N P Q R).1) p.1 p.2)
    (hR : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .middle a b c d β
      x y z w r s f p.1 p.2) :
    fivePointEvaluation hC2 N P Q R .inner a b c d β x y z w r s
      (f ∘ₗ (fiveEdge12 hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .middle a b c d β x y z w r s f := by
  unfold fivePointEvaluation
  rw [hL.tsum_prod,hR.tsum_prod]
  apply tsum_congr
  intro q
  exact fiberEdge12 hC2 N P Q R a b c d β x y z w r s hD f q

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Absolute convergence sums the actual sewing fiber along this concrete edge. -/
theorem evaluationEdge23_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ)
    (hL : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .middle a b c d β
      x y z w r s (f ∘ₗ (fiveEdge23 hC2 N P Q R).1) p.1 p.2)
    (hR : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .right a b c d β
      x y z w r s f p.1 p.2) :
    fivePointEvaluation hC2 N P Q R .middle a b c d β x y z w r s
      (f ∘ₗ (fiveEdge23 hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .right a b c d β x y z w r s f := by
  unfold fivePointEvaluation
  rw [tsum_prod_reverse _ hL,tsum_prod_reverse _ hR]
  apply tsum_congr
  intro q
  exact fiberEdge23 hC2 N P Q R a b c d β x y z w r s hD f q

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Absolute convergence sums the actual sewing fiber along this concrete edge. -/
theorem evaluationEdge04_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .pair →ₗ[ℂ] ℂ)
    (hL : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .left a b c d β
      x y z w r s (f ∘ₗ (fiveEdge04 hC2 N P Q R).1) p.1 p.2)
    (hR : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .pair a b c d β
      x y z w r s f p.1 p.2) :
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (fiveEdge04 hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .pair a b c d β x y z w r s f := by
  unfold fivePointEvaluation
  rw [hL.tsum_prod,hR.tsum_prod]
  apply tsum_congr
  intro q
  exact fiberEdge04 hC2 N P Q R a b c d β x y z w r s hD f q

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- Absolute convergence sums the actual sewing fiber along this concrete edge. -/
theorem evaluationEdge43_of_summable (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ)
    (hL : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .pair a b c d β
      x y z w r s (f ∘ₗ (fiveEdge43 hC2 N P Q R).1) p.1 p.2)
    (hR : Summable fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R .right a b c d β
      x y z w r s f p.1 p.2) :
    fivePointEvaluation hC2 N P Q R .pair a b c d β x y z w r s
      (f ∘ₗ (fiveEdge43 hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .right a b c d β x y z w r s f := by
  unfold fivePointEvaluation
  rw [tsum_prod_reverse _ hL,hR.tsum_prod]
  apply tsum_congr
  intro q
  exact fiberEdge43 hC2 N P Q R a b c d β x y z w r s hD f q

end VOA.Huang.LogAssocFivePoint
