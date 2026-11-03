import VOA.Huang.LogAssocFivePointPairConvergence
import VOA.Modules.LogTensorPzPointEvaluation

/-! Literal genuine point-block compositions are the complete original
logarithmic coefficient polynomials, multiplied by their three actual
coordinate exponentials. No logarithmic degree is omitted. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators

/-- A finite logarithmic box is exactly the full profile finsum. -/
theorem finsum_logProfile_eq_box (C : ℕ × ℕ × ℕ → ℂ) (K L J : ℕ)
    (hC : ∀ k l j,K ≤ k ∨ L ≤ l ∨ J ≤ j → C (k,l,j)=0) :
    (∑ᶠ p : ℕ × ℕ × ℕ,C p)=
      ∑ k ∈ Finset.range K,∑ l ∈ Finset.range L,∑ j ∈ Finset.range J,C (k,l,j) := by
  classical
  let S : Finset (ℕ × ℕ × ℕ) := Finset.range K ×ˢ Finset.range L ×ˢ Finset.range J
  have he : (∑ᶠ p : ℕ × ℕ × ℕ,C p)=∑ p ∈ S,C p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ S
    by_contra hn
    have hout : K ≤ p.1 ∨ L ≤ p.2.1 ∨ J ≤ p.2.2 := by
      simp only [S,Finset.mem_product,Finset.mem_range] at hn
      omega
    exact hp (hC _ _ _ hout)
  rw [he]
  simp only [S,Finset.sum_product]

universe u
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]

/-- The whole original three-degree product coefficient polynomial. -/
def productLogPolynomial (Y₁ : LogModes M₁ M₆ M₀) (Y₂ : LogModes M₂ M₅ M₆)
    (Y₃ : LogModes M₃ M₄ M₅) (f : M₀ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄)
    (p q r e₁ e₂ e₃ : ℂ) : ℂ :=
  ∑ᶠ k : ℕ × ℕ × ℕ,(e₁^k.1*e₂^k.2.1*e₃^k.2.2)*
    LogAssocFivePoint.productCoeff Y₁ Y₂ Y₃ f x y z w p q r k.1 k.2.1 k.2.2

variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

/-- Literal composition of three actual product point blocks. -/
def productPointProfile
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) : ℂ :=
  f (pointEvaluationBlock N₁ N₆ N₀ Y₁ e₁ a₁ δ β x
    (pointEvaluationBlock N₂ N₅ N₆ Y₂ e₂ a₂ γ δ y
      (pointEvaluationBlock N₃ N₄ N₅ Y₃ e₃ a₃ a₄ γ z w)))

/-- Every product point profile is its true full logarithmic polynomial,
with exactly the three genuine coordinate exponentials. -/
theorem productPointProfile_eq_polynomial
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) :
    productPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ x y z w f =
      (Complex.exp (e₁*(β-a₁-δ))*Complex.exp (e₂*(δ-a₂-γ))*Complex.exp (e₃*(γ-a₃-a₄)))*
        productLogPolynomial Y₁.1 Y₂.1 Y₃.1 f x y z w
          (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₆ N₀ hfg₁ hfg₆ hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₅ N₆ hfg₂ hfg₅ hfg₆
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
  let C : ℕ × ℕ × ℕ → ℂ := fun p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) p.1 p.2.1 p.2.2
  have hC (k l j : ℕ) (h : K ≤ k ∨ L ≤ l ∨ J ≤ j) : C (k,l,j)=0 := by
    rcases h with hk | hl | hj
    · simp only [C,LogAssocFivePoint.productCoeff,hK Y₁ _ k hk,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,LogAssocFivePoint.productCoeff,hL Y₂ _ l hl,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,LogAssocFivePoint.productCoeff,hJ Y₃ _ j hj,LinearMap.zero_apply,map_zero,mul_zero]
  have hpoly : productLogPolynomial Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ =
        ∑ k ∈ Finset.range K,∑ l ∈ Finset.range L,∑ j ∈ Finset.range J,C (k,l,j) :=
    finsum_logProfile_eq_box C K L J hC
  rw [hpoly]
  unfold productPointProfile
  rw [pointEvaluationBlock_fixed_cutoff N₁ N₆ N₀ Y₁ _ _ _ _ _ _ K
      (fun k hk => by rw [hK Y₁ _ k hk]; simp),
    pointEvaluationBlock_fixed_cutoff N₂ N₅ N₆ Y₂ _ _ _ _ _ _ L
      (fun l hl => by rw [hL Y₂ _ l hl]; simp),
    pointEvaluationBlock_fixed_cutoff N₃ N₄ N₅ Y₃ _ _ _ _ _ _ J
      (fun j hj => by rw [hJ Y₃ _ j hj]; simp)]
  simp only [map_smul,map_sum,C,LogAssocFivePoint.productCoeff,smul_eq_mul,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]

end VOA.Huang.LogAssocFivePointGraded
