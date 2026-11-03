import VOA.Huang.LogAssocFivePointMidPointPolynomial

/-! The genuine iterate-in-product point profile retains its whole logarithmic polynomial. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators

universe u
variable {V M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]

/-- The entire original two-cluster logarithmic coefficient polynomial. -/
def pairLogPolynomial (P : LogModes MU MV M₀) (ZT : LogModes M₂ M₁ MV)
    (XY : LogModes M₃ M₄ MU) (f : M₀ →ₗ[ℂ] ℂ)
    (t : M₁) (z : M₂) (x : M₃) (y : M₄) (p q r e₁ e₂ e₃ : ℂ) : ℂ :=
  ∑ᶠ k : ℕ × ℕ × ℕ,(e₁^k.1*e₂^k.2.1*e₃^k.2.2)*
    pairCoeff P ZT XY f t z x y p q r k.1 k.2.1 k.2.2

variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (NU : LogVModule W MU) (NV : LogVModule W MV)

/-- Literal composition of three actual product point blocks. -/
def pairPointProfile
    (P : LogIntertwiningOperator NU.toWeakModule NV.toWeakModule N₀.toWeakModule)
    (ZT : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule NV.toWeakModule)
    (XY : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule NU.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) : ℂ :=
  f (pointEvaluationBlock NU NV N₀ P e₁ γ δ β
    (pointEvaluationBlock N₃ N₄ NU XY e₃ a₃ a₄ γ z w)
    (pointEvaluationBlock N₂ N₁ NV ZT e₂ a₂ a₁ δ y x))

/-- Every product point profile is its true full logarithmic polynomial,
with exactly the three genuine coordinate exponentials. -/
theorem pairPointProfile_eq_polynomial
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfgU : FinGen NU.toWeakModule)
    (hfgV : FinGen NV.toWeakModule)
    (P : LogIntertwiningOperator NU.toWeakModule NV.toWeakModule N₀.toWeakModule)
    (ZT : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule NV.toWeakModule)
    (XY : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule NU.toWeakModule)
    (e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) :
    pairPointProfile N₀ N₁ N₂ N₃ N₄ NU NV P ZT XY
      e₁ e₂ e₃ a₁ a₂ a₃ a₄ β γ δ x y z w f =
      (Complex.exp (e₁*(β-γ-δ))*Complex.exp (e₂*(δ-a₂-a₁))*Complex.exp (e₃*(γ-a₃-a₄)))*
        pairLogPolynomial P.1 ZT.1 XY.1 f x y z w
          (γ+δ-β-1) (a₂+a₁-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen NU NV N₀ hfgU hfgV hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₁ NV hfg₂ hfg₁ hfgV
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ NU hfg₃ hfg₄ hfgU
  let C : ℕ × ℕ × ℕ → ℂ := fun p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*pairCoeff P.1 ZT.1 XY.1 f x y z w
      (γ+δ-β-1) (a₂+a₁-δ-1) (a₃+a₄-γ-1) p.1 p.2.1 p.2.2
  have hC (k l j : ℕ) (h : K ≤ k ∨ L ≤ l ∨ J ≤ j) : C (k,l,j)=0 := by
    rcases h with hk | hl | hj
    · simp only [C,pairCoeff,hK P _ k hk,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,pairCoeff,hL ZT _ l hl,LinearMap.zero_apply,map_zero,mul_zero]
    · simp only [C,pairCoeff,hJ XY _ j hj,LinearMap.zero_apply,map_zero,mul_zero]
  have hpoly : pairLogPolynomial P.1 ZT.1 XY.1 f x y z w
      (γ+δ-β-1) (a₂+a₁-δ-1) (a₃+a₄-γ-1) e₁ e₂ e₃ =
        ∑ k ∈ Finset.range K,∑ l ∈ Finset.range L,∑ j ∈ Finset.range J,C (k,l,j) :=
    finsum_logProfile_eq_box C K L J hC
  rw [hpoly]
  unfold pairPointProfile
  rw [pointEvaluationBlock_fixed_cutoff NU NV N₀ P _ _ _ _ _ _ K
      (fun k hk => by rw [hK P _ k hk]; simp),
    pointEvaluationBlock_fixed_cutoff N₂ N₁ NV ZT _ _ _ _ _ _ L
      (fun l hl => by rw [hL ZT _ l hl]; simp),
    pointEvaluationBlock_fixed_cutoff N₃ N₄ NU XY _ _ _ _ _ _ J
      (fun j hj => by rw [hJ XY _ j hj]; simp)]
  simp only [map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,C,pairCoeff,smul_eq_mul,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]


end VOA.Huang.LogAssocFivePointGraded
