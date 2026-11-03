import VOA.Classification.COne.McRaeM2LogPentagonRows

/-! Absolute convergence of the literal product vertex `N ⊠ (P ⊠ (Q ⊠ R))`
of the logarithmic pentagon. Every term is the genuine product point profile of
the three canonical tensor intertwiners; its natural progression rows are the
proved full-log product arrays at the chart ratios `(1+s)/(1+s+r)` and `1/(1+s)`. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

omit [AddCommGroup V] [Module ℂ V] in
/-- The full-log product array is the literal log polynomial at shifted modes. -/
theorem fullLogProductCoefficient_eq {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
    [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
    [AddCommGroup M₆] [Module ℂ M₆]
    (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (N₆ : LogVModule W M₆)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (f : M₀ →ₗ[ℂ] ℂ) (A B C e₁ e₂ e₃ : ℂ) (m n : ℕ) :
    fullLogProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃ (x := x) (y := y) (z := z) (w := w)
      f A B C e₁ e₂ e₃ m n=
    productLogPolynomial Y₁.1 Y₂.1 Y₃.1 f x y z w (A+m) (B-m+n) (C-n) e₁ e₂ e₃ := rfl

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- The product vertex term is literally the product point profile of the
three actual canonical tensor intertwiners. -/
theorem fivePointTerm_right_eq (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ) (γ δ : ℂ) :
    fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f γ δ=
      productPointProfile
        (tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R))).act N.act P.act Q.act R.act
        (tensorObject hC2 Q R).act (tensorObject hC2 P (tensorObject hC2 Q R)).act
        (tensorIntertwiner hC2 N.act (tensorObject hC2 P (tensorObject hC2 Q R)).act
          N.finiteGeneration (tensorObject hC2 P (tensorObject hC2 Q R)).finiteGeneration)
        (tensorIntertwiner hC2 P.act (tensorObject hC2 Q R).act
          P.finiteGeneration (tensorObject hC2 Q R).finiteGeneration)
        (tensorIntertwiner hC2 Q.act R.act Q.finiteGeneration R.finiteGeneration)
        (Complex.log (1+s+r)) (Complex.log (1+s)) 0 a b c d β γ δ x y z w f := by
  simp only [fivePointTerm]
  rw [pointTensor_eq_block hC2 Q R 0 c d]
  rfl

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- Absolute convergence of the literal product vertex of the logarithmic pentagon. -/
theorem fivePointTerm_right_summable_norm (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f p.1 p.2‖) := by
  apply fivePoint_summable_norm_of_rows
  intro h h'
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  set e₁ : ℂ := Complex.log (1+s+r) with he₁
  set e₂ : ℂ := Complex.log (1+s) with he₂
  have hc₁ : ((1+s+r : ℝ) : ℂ)=1+s+r := by push_cast; ring
  have hc₂ : ((1+s : ℝ) : ℂ)=1+s := by push_cast; ring
  have ht : ‖Complex.exp (e₂-e₁)‖<1 := by
    have := norm_exp_log_sub_log_lt_one (x := 1+s) (y := 1+s+r) (by linarith) (by linarith)
    rwa [hc₁,hc₂] at this
  have hu : ‖Complex.exp (-e₂)‖<1 := by
    have := norm_exp_neg_log_lt_one (y := 1+s) (by linarith)
    rwa [hc₂] at this
  have hG := summable_fullLog_product_double
    (tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R))).act N.act P.act Q.act R.act
    (tensorObject hC2 Q R).act (tensorObject hC2 P (tensorObject hC2 Q R)).act hC2
    (tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R))).finiteGeneration
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration R.finiteGeneration
    (tensorObject hC2 Q R).finiteGeneration
    (tensorObject hC2 P (tensorObject hC2 Q R)).finiteGeneration
    (tensorIntertwiner hC2 N.act (tensorObject hC2 P (tensorObject hC2 Q R)).act
      N.finiteGeneration (tensorObject hC2 P (tensorObject hC2 Q R)).finiteGeneration)
    (tensorIntertwiner hC2 P.act (tensorObject hC2 Q R).act
      P.finiteGeneration (tensorObject hC2 Q R).finiteGeneration)
    (tensorIntertwiner hC2 Q.act R.act Q.finiteGeneration R.finiteGeneration)
    x.2 y.2 z.2 w.2 f (a+h'-β-1) (b+h-h'-1) (c+d-h-1) e₁ e₂ 0 ht hu
  refine summable_row_of_reindex
    (F := fun γ δ => fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f γ δ) h h'
    (Complex.exp (e₁*(β-a-h'))*Complex.exp (e₂*(h'-b-h))) Prod.swap Prod.swap_injective hG ?_
  intro p
  simp only []
  rw [fivePointTerm_right_eq, productPointProfile_eq_polynomial _ _ _ _ _ _ _
    (tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R))).finiteGeneration
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration R.finiteGeneration
    (tensorObject hC2 Q R).finiteGeneration
    (tensorObject hC2 P (tensorObject hC2 Q R)).finiteGeneration,
    Prod.fst_swap, Prod.snd_swap, fullLogProductCoefficient_eq]
  have h1 : a+(h'+(p.2 : ℂ))-β-1=a+h'-β-1+(p.2 : ℂ) := by ring
  have h2 : b+(h+(p.1 : ℂ))-(h'+(p.2 : ℂ))-1=b+h-h'-1-(p.2 : ℂ)+(p.1 : ℂ) := by ring
  have h3 : c+d-(h+(p.1 : ℂ))-1=c+d-h-1-(p.1 : ℂ) := by ring
  rw [h1,h2,h3]
  have hexp : Complex.exp (e₁*(β-a-(h'+(p.2 : ℂ))))*Complex.exp (e₂*((h'+(p.2 : ℂ))-b-(h+(p.1 : ℂ))))*
      Complex.exp (0*((h+(p.1 : ℂ))-c-d))=
      (Complex.exp (e₁*(β-a-h'))*Complex.exp (e₂*(h'-b-h)))*
        (Complex.exp (e₂-e₁)^p.2*Complex.exp (-e₂)^p.1) := by
    rw [← exp_mul_nat, ← exp_mul_nat]
    simp only [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

end VOA.Huang.LogAssocFivePoint
