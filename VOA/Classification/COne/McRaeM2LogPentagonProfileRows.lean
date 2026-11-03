import VOA.Classification.COne.McRaeM2LogPentagonMidPair

/-! Natural-row absolute convergence of the genuine product and
iterate-in-product point profiles, for arbitrary branches whose exponential
ratios lie in the proved convergence regions. These are the abstract inputs
for the root-reflected pentagon vertices. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u

variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
    [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
    [AddCommGroup M₆] [Module ℂ M₆]
    (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (N₆ : LogVModule W M₆)

/-- At the zero branch a point block is the literal log-free coefficient. -/
theorem pointEvaluationBlock_zero_branch
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    (pointEvaluationBlock N₁ N₂ N₃ Y 0 a b c x y : M₃)=Y.1 (a+b-c-1) 0 x y := by
  unfold pointEvaluationBlock
  simp only [zero_mul,Complex.exp_zero,one_smul]
  rw [Finset.sum_eq_single 0]
  · simp [logarithmicBlock]
  · intro k hk hk0
    rw [zero_pow hk0,zero_smul]
  · intro hh
    exfalso
    apply hh
    simp only [Finset.mem_range,pointLogCutoff]
    omega

/-- Exponential coordinate algebra shared by all three-block profiles. -/
theorem exp_three_rows (e₁ e₂ e₃ A B C h h' : ℂ) (m n : ℕ) :
    Complex.exp (e₁*(A-(h'+(n : ℂ))))*Complex.exp (e₂*((h'+(n : ℂ))-(h+(m : ℂ))-B))*
      Complex.exp (e₃*((h+(m : ℂ))-C))=
    (Complex.exp (e₁*(A-h'))*Complex.exp (e₂*(h'-h-B))*Complex.exp (e₃*(h-C)))*
      (Complex.exp (e₂-e₁)^n*Complex.exp (e₃-e₂)^m) := by
  rw [← exp_mul_nat, ← exp_mul_nat]
  simp only [← Complex.exp_add]
  congr 1
  ring

-- Abstract three-block profiles require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Every natural row of a genuine product point profile converges
absolutely when the two exponential coordinate ratios lie in the unit disc. -/
theorem productPointProfile_row_summable (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (h h' : ℂ)
    (ht : ‖Complex.exp (e₂-e₁)‖<1) (hu : ‖Complex.exp (e₃-e₂)‖<1) :
    Summable (fun p : ℕ × ℕ => ‖productPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β (h+p.1) (h'+p.2) x y z w f‖) := by
  have hG := summable_fullLog_product_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ Y₂ Y₃ x.2 y.2 z.2 w.2 f
    (a₁+h'-β-1) (a₂+h-h'-1) (a₃+a₄-h-1) e₁ e₂ e₃ ht hu
  refine summable_row_of_reindex
    (F := fun γ δ => productPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ x y z w f) h h'
    (Complex.exp (e₁*(β-a₁-h'))*Complex.exp (e₂*(h'-h-a₂))*Complex.exp (e₃*(h-(a₃+a₄))))
    Prod.swap Prod.swap_injective hG ?_
  intro p
  simp only []
  rw [productPointProfile_eq_polynomial N₀ N₁ N₂ N₃ N₄ N₅ N₆
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆, Prod.fst_swap, Prod.snd_swap,
    fullLogProductCoefficient_eq]
  have h1 : a₁+(h'+(p.2 : ℂ))-β-1=a₁+h'-β-1+(p.2 : ℂ) := by ring
  have h2 : a₂+(h+(p.1 : ℂ))-(h'+(p.2 : ℂ))-1=a₂+h-h'-1-(p.2 : ℂ)+(p.1 : ℂ) := by ring
  have h3 : a₃+a₄-(h+(p.1 : ℂ))-1=a₃+a₄-h-1-(p.1 : ℂ) := by ring
  rw [h1,h2,h3]
  have hexp := exp_three_rows e₁ e₂ e₃ (β-a₁) a₂ (a₃+a₄) h h' p.1 p.2
  have hA : β-a₁-(h'+(p.2 : ℂ))=(β-a₁)-(h'+(p.2 : ℂ)) := by ring
  have hB : (h'+(p.2 : ℂ))-a₂-(h+(p.1 : ℂ))=(h'+(p.2 : ℂ))-(h+(p.1 : ℂ))-a₂ := by ring
  have hC : (h+(p.1 : ℂ))-a₃-a₄=(h+(p.1 : ℂ))-(a₃+a₄) := by ring
  have hA' : β-a₁-h'=(β-a₁)-h' := by ring
  rw [hA,hB,hC,hexp,hA']
  ring

-- Abstract three-block profiles require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Every natural row of a genuine iterate-in-product point profile
converges absolutely in the proved middle convergence region. -/
theorem midPointProfile_row_summable (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (h h' : ℂ)
    (ht : ‖Complex.exp (e₂-e₁)‖+‖Complex.exp (e₂-e₁)‖*‖Complex.exp (e₃-e₂)‖<1)
    (hu : ‖Complex.exp (e₃-e₂)‖<1) :
    Summable (fun p : ℕ × ℕ => ‖midPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β (h+p.1) (h'+p.2) x y z w f‖) := by
  have hG := summable_fullLog_mid_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ YB Y₃ x.2 y.2 z.2 w.2 f
    (a₁+h'-β-1) (a₂+h-h'-1) (a₃+a₄-h-1) e₁ e₂ e₃ ht hu
  refine summable_row_of_reindex
    (F := fun γ δ => midPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ x y z w f) h h'
    (Complex.exp (e₁*(β-a₁-h'))*Complex.exp (e₂*(h'-h-a₂))*Complex.exp (e₃*(h-(a₃+a₄))))
    Prod.swap Prod.swap_injective hG ?_
  intro p
  simp only []
  rw [midPointProfile_eq_polynomial N₀ N₁ N₂ N₃ N₄ N₅ N₆
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆, Prod.fst_swap, Prod.snd_swap,
    fullLogMidProductCoefficient_eq]
  have h1 : a₁+(h'+(p.2 : ℂ))-β-1=a₁+h'-β-1+(p.2 : ℂ) := by ring
  have h2 : a₂+(h+(p.1 : ℂ))-(h'+(p.2 : ℂ))-1=a₂+h-h'-1-(p.2 : ℂ)+(p.1 : ℂ) := by ring
  have h3 : a₃+a₄-(h+(p.1 : ℂ))-1=a₃+a₄-h-1-(p.1 : ℂ) := by ring
  rw [h1,h2,h3]
  have hexp := exp_three_rows e₁ e₂ e₃ (β-a₁) a₂ (a₃+a₄) h h' p.1 p.2
  have hA : β-a₁-(h'+(p.2 : ℂ))=(β-a₁)-(h'+(p.2 : ℂ)) := by ring
  have hC : (h+(p.1 : ℂ))-a₃-a₄=(h+(p.1 : ℂ))-(a₃+a₄) := by ring
  have hA' : β-a₁-h'=(β-a₁)-h' := by ring
  rw [hA,hC,hexp,hA']
  ring

end VOA.Huang.LogAssocFivePoint
