import VOA.Huang.LogAssocFivePointPointPolynomial

/-! The genuine iterate-in-product point profile retains its whole logarithmic polynomial. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators

universe u
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]

variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

/-- Literal composition of three actual product point blocks. -/
def midPointProfile
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) : ℂ :=
  f (pointEvaluationBlock N₁ N₆ N₀ Y₁ e₁ a₁ δ β x
    (pointEvaluationBlock N₅ N₂ N₆ YB e₂ γ a₂ δ
      (pointEvaluationBlock N₃ N₄ N₅ Y₃ e₃ a₃ a₄ γ z w) y))

/-- Every product point profile is its true full logarithmic polynomial,
with exactly the three genuine coordinate exponentials. -/
theorem midPointProfile_eq_polynomial
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) :
    midPointProfile N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ x y z w f =
      (Complex.exp (e₁*(β-a₁-δ))*Complex.exp (e₂*(δ-γ-a₂))*Complex.exp (e₃*(γ-a₃-a₄)))*
        productLogPolynomial Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
          (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₆ N₀ hfg₁ hfg₆ hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₅ N₂ N₆ hfg₅ hfg₂ hfg₆
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
  let C : ℕ × ℕ × ℕ → ℂ := fun p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
      (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) p.1 p.2.1 p.2.2
  have hC (k l j : ℕ) (h : K ≤ k ∨ L ≤ l ∨ J ≤ j) : C (k,l,j)=0 := by
    rcases h with hk | hl | hj
    · simp only [C,LogAssocFivePoint.productCoeff,flipLogModes,LinearMap.flip_apply,hK Y₁ _ k hk,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,LogAssocFivePoint.productCoeff,flipLogModes,LinearMap.flip_apply,hL YB _ l hl,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,LogAssocFivePoint.productCoeff,flipLogModes,LinearMap.flip_apply,hJ Y₃ _ j hj,LinearMap.zero_apply,map_zero,mul_zero]
  have hpoly : productLogPolynomial Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
      (a₁+δ-β-1) (a₂+γ-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ =
        ∑ k ∈ Finset.range K,∑ l ∈ Finset.range L,∑ j ∈ Finset.range J,C (k,l,j) :=
    finsum_logProfile_eq_box C K L J hC
  rw [hpoly]
  unfold midPointProfile
  rw [pointEvaluationBlock_fixed_cutoff N₁ N₆ N₀ Y₁ _ _ _ _ _ _ K
      (fun k hk => by rw [hK Y₁ _ k hk]; simp),
    pointEvaluationBlock_fixed_cutoff N₅ N₂ N₆ YB _ _ _ _ _ _ L
      (fun l hl => by rw [hL YB _ l hl]; simp),
    pointEvaluationBlock_fixed_cutoff N₃ N₄ N₅ Y₃ _ _ _ _ _ _ J
      (fun j hj => by rw [hJ Y₃ _ j hj]; simp)]
  rw [show γ+a₂-δ-1=a₂+γ-δ-1 by ring]
  simp only [map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,C,LogAssocFivePoint.productCoeff,flipLogModes,LinearMap.flip_apply,smul_eq_mul,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]


end VOA.Huang.LogAssocFivePointGraded
