import VOA.Huang.LogAssocFivePointNormalized

/-! # A regular normalized terminal C₁ relation

The terminal `u(-1)` move has polynomial coefficients with nonnegative
powers of both sewing variables. Every term has strictly smaller total
external level when `wt u > 0`. This is one of the five moves needed for
the five-slot filtration, not a proof of the whole filtration theorem.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid PowerSeries
open VOA.Huang.LogHuangODEProduct
open VOA.Huang.HuangODEProduct (sum_range_trim)
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
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

open VOA.Huang.LogHuangODEProduct

/-- The terminal C₁ move as an identity of genuine normalized bivariate
series. Truncation bounds depend only on the external levels and `wt u`.
The dual contribution is zero when its required output level is negative. -/
theorem normalizedSeries_terminal
    (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hY₂ : LogHuangODEProduct.IsGradedJacobiFamily A₂ A₅ A₆ Y₂)
    (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : LogHuangODEProduct.CosetBase A₀ h₀) (hl₁ : LogHuangODEProduct.CosetBase A₁ h₁)
    (hl₂ : LogHuangODEProduct.CosetBase A₂ h₂) (hl₃ : LogHuangODEProduct.CosetBase A₃ h₃)
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ w₃ (mode (A₄.YM u) (-1) w₄) N₀ (N₀ + N₁ + N₂ + N₃ + (N₄ + d)) =
    (if d ≤ N₀ then X ^ (2 * d) * PowerSeries.C (X ^ (2 * d)) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        (f ∘ₗ mode (A₀.YM u) (-1)) w₁ w₂ w₃ w₄ (N₀ - d)
        ((N₀ - d) + N₁ + N₂ + N₃ + N₄) else 0)
    - ∑ k ∈ Finset.range (N₁ + d), (cbz (-1) k) •
      (X ^ (k + 1) * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₂ + d), (cbz (-1) k) •
      (X ^ 0 * PowerSeries.C (X ^ (k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    - ∑ k ∈ Finset.range (N₃ + d), (cbz (-1) k) •
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄) := by
  classical
  ext m n
  simp only [map_sub, map_sum, coeff_smul, smul_eq_mul, coeff_normalizedSeries]
  unfold normalizedCoeff productCoeff
  rw [product_terminal_mode hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ _ _ _ (-1)
    (N₁ + N₂ + N₃ + 3 * d)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_) ?_
  · split_ifs with hd
    · rw [coeff_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄]
      unfold normalizedCoeff productCoeff
      simp only [LinearMap.comp_apply]
      simp only [Nat.cast_add, Nat.cast_sub hd]
      push_cast
      ring_nf
    · rw [map_zero, map_zero]
      have hz := eq_zero_of_mem_weight_neg hl₀
        (product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄
          (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m)
          (ν - μ - m + n) (μ + (N₀ + N₁ + N₂ + N₃ + (N₄ + d) : ℕ) - n))
        (j := (N₀ : ℤ) - d) (by push_cast; ring) (by omega)
      rw [hz, map_zero, map_zero]
  · rw [sum_range_trim (J := N₁ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₁ hu hw₁ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [coeff_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄]
    unfold normalizedCoeff productCoeff
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k + 1 ≤ N₁ + d)]
    push_cast
    ring_nf
  · rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [coeff_monomial_normalizedSeries hB (by omega)
      (mode_mem_weight_nat hu hw₂ hk') hw₃ hw₄]
    unfold normalizedCoeff productCoeff
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k + 1 ≤ N₂ + d)]
    push_cast
    ring_nf
  · rw [sum_range_trim (J := N₃ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega)]
      simp)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k + 1 ≤ N₃ + d)]
    push_cast
    ring_nf

end VOA.Huang.LogAssocFivePointGraded
