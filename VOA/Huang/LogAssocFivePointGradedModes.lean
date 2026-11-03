import VOA.Huang.LogAssocFivePointGradedCoefficients

/-! # The five slot relations for products of three intertwiners

These finite mode identities move a VOA mode between the four vector slots
and the output functional. They use all three Jacobi identities. The bounds
are explicit; converting them into regular bivariate series relations and a
weight-filtration induction remains separate work.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid PowerSeries
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : C2Rigid.GWModule W M₀} {A₁ : C2Rigid.GWModule W M₁}
  {A₂ : C2Rigid.GWModule W M₂} {A₃ : C2Rigid.GWModule W M₃} {A₄ : C2Rigid.GWModule W M₄}
  {A₅ : C2Rigid.GWModule W M₅} {A₆ : C2Rigid.GWModule W M₆}
variable (Y₁ : IntertwiningModes M₁ M₆ M₀) (Y₂ : IntertwiningModes M₂ M₅ M₆)
  (Y₃ : IntertwiningModes M₃ M₄ M₅)

open VOA.Huang.LogHuangODEModes

variable {Y₁ Y₂ Y₃}
variable (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
  (hY₂ : LogHuangODEProduct.IsGradedJacobiFamily A₂ A₅ A₆ Y₂)
  (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)

include hY₁ hY₂ hY₃ in
/-- Three commutators move an arbitrary integral mode from the terminal vector
onto the other four slots. The specialization `m = -1` is the terminal C₁ relation. -/
theorem product_terminal_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) (m : ℤ) (K : ℕ)
    (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0) :
    f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ (mode (A₄.YM u) m w₄)))) =
      f (mode (A₀.YM u) m (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄))))
      - ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ (m + p - k) (mode (A₁.YM u) k w₁) (Y₂ q w₂ (Y₃ r w₃ w₄)))
      - ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ p w₁ (Y₂ (m + q - k) (mode (A₂.YM u) k w₂) (Y₃ r w₃ w₄)))
      - ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ p w₁ (Y₂ q w₂ (Y₃ (m + r - k) (mode (A₃.YM u) k w₃) w₄))) := by
  rw [comm_range hY₃.toIsJacobiFamily u w₃ w₄ m r K hK₃]
  simp only [map_sub]
  rw [comm_range hY₂.toIsJacobiFamily u w₂ _ m q K hK₂]
  simp only [map_sub]
  rw [comm_range hY₁.toIsJacobiFamily u w₁ _ m p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

include hY₁ hY₂ hY₃ in
/-- The dual-slot relation; its C₁ application restricts `m` using DualC1Graded. -/
theorem product_dual_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) (m : ℤ) (K : ℕ)
    (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0) :
    f (mode (A₀.YM u) m (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)))) =
      f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ (mode (A₄.YM u) m w₄))))
      + ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ (m + p - k) (mode (A₁.YM u) k w₁) (Y₂ q w₂ (Y₃ r w₃ w₄)))
      + ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ p w₁ (Y₂ (m + q - k) (mode (A₂.YM u) k w₂) (Y₃ r w₃ w₄)))
      + ∑ k ∈ Finset.range K, cbz m k *
          f (Y₁ p w₁ (Y₂ q w₂ (Y₃ (m + r - k) (mode (A₃.YM u) k w₃) w₄))) := by
  have hh := product_terminal_mode hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ p q r m K hK₁ hK₂ hK₃
  linear_combination -hh

include hY₁ hY₂ hY₃ in
/-- C₁ in the third insertion: one iterate formula and two outward commutators. -/
theorem product_third_neg_one (u : V) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) (K I : ℕ)
    (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₃ (r + i) w₃ w₄ = 0 ∧
      mode (A₄.YM u) i w₄ = 0) :
    f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r (mode (A₃.YM u) (-1) w₃) w₄))) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (Y₁ p w₁ (Y₂ q w₂ (Y₃ (r + i) w₃ w₄))))
        - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
          f (Y₁ ((-1 - i : ℤ) + p - k) (mode (A₁.YM u) k w₁)
            (Y₂ q w₂ (Y₃ (r + i) w₃ w₄)))
        - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
          f (Y₁ p w₁ (Y₂ ((-1 - i : ℤ) + q - k) (mode (A₂.YM u) k w₂)
            (Y₃ (r + i) w₃ w₄)))
        + f (Y₁ p w₁ (Y₂ q w₂ (Y₃ (r - 1 - i) w₃ (mode (A₄.YM u) i w₄))))) := by
  rw [negOneLeft_range hY₃.toIsJacobiFamily u w₃ w₄ r I hI]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_add, map_add, comm_range hY₂.toIsJacobiFamily u w₂ _ (-1 - i) q K hK₂,
    map_sub, comm_range hY₁.toIsJacobiFamily u w₁ _ (-1 - i) p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

include hY₁ hY₂ hY₃ in
/-- C₁ in the middle insertion, with the inward and outward terms both retained. -/
theorem product_second_neg_one (u : V) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) (K I : ℕ)
    (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₂ (q + i) w₂ (Y₃ r w₃ w₄) = 0 ∧
      mode (A₅.YM u) i (Y₃ r w₃ w₄) = 0) :
    f (Y₁ p w₁ (Y₂ q (mode (A₂.YM u) (-1) w₂) (Y₃ r w₃ w₄))) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (Y₁ p w₁ (Y₂ (q + i) w₂ (Y₃ r w₃ w₄))))
        - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
          f (Y₁ ((-1 - i : ℤ) + p - k) (mode (A₁.YM u) k w₁)
            (Y₂ (q + i) w₂ (Y₃ r w₃ w₄)))
        + f (Y₁ p w₁ (Y₂ (q - 1 - i) w₂ (Y₃ r w₃ (mode (A₄.YM u) i w₄))))
        + ∑ k ∈ Finset.range K, cbz i k *
          f (Y₁ p w₁ (Y₂ (q - 1 - i) w₂
            (Y₃ ((i : ℤ) + r - k) (mode (A₃.YM u) k w₃) w₄)))) := by
  rw [negOneLeft_range hY₂.toIsJacobiFamily u w₂ _ q I hI]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := comm_range hY₃.toIsJacobiFamily u w₃ w₄ (i : ℤ) r K hK₃
  rw [eq_sub_iff_add_eq] at hc
  rw [map_add, map_add, comm_range hY₁.toIsJacobiFamily u w₁ _ (-1 - i) p K hK₁, ← hc]
  simp only [map_sub, map_add, map_sum, map_smul, smul_eq_mul]
  ring

include hY₁ hY₂ hY₃ in
/-- C₁ in the outer insertion: both inner commutator contributions are necessary. -/
theorem product_first_neg_one (u : V) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) (K I : ℕ)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₁ (p + i) w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)) = 0 ∧
      mode (A₆.YM u) i (Y₂ q w₂ (Y₃ r w₃ w₄)) = 0) :
    f (Y₁ p (mode (A₁.YM u) (-1) w₁) (Y₂ q w₂ (Y₃ r w₃ w₄))) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (Y₁ (p + i) w₁ (Y₂ q w₂ (Y₃ r w₃ w₄))))
        + f (Y₁ (p - 1 - i) w₁ (Y₂ q w₂ (Y₃ r w₃ (mode (A₄.YM u) i w₄))))
        + ∑ k ∈ Finset.range K, cbz i k *
          f (Y₁ (p - 1 - i) w₁ (Y₂ q w₂
            (Y₃ ((i : ℤ) + r - k) (mode (A₃.YM u) k w₃) w₄)))
        + ∑ k ∈ Finset.range K, cbz i k *
          f (Y₁ (p - 1 - i) w₁ (Y₂ ((i : ℤ) + q - k) (mode (A₂.YM u) k w₂)
            (Y₃ r w₃ w₄)))) := by
  rw [negOneLeft_range hY₁.toIsJacobiFamily u w₁ _ p I hI, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc₂ := comm_range hY₂.toIsJacobiFamily u w₂ (Y₃ r w₃ w₄) (i : ℤ) q K hK₂
  have hc₃ := comm_range hY₃.toIsJacobiFamily u w₃ w₄ (i : ℤ) r K hK₃
  rw [eq_sub_iff_add_eq] at hc₂ hc₃
  rw [map_add, ← hc₂, ← hc₃]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  ring

end VOA.Huang.LogAssocFivePointGraded
