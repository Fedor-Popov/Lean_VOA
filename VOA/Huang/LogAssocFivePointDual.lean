import VOA.Huang.LogAssocFivePointFinite

/-! # The regular normalized dual C₁ move

Dual C₁ generators use mode `2*wt(u)-1+j`, with `j ≥ 0`. That precise
restriction makes all the monomial powers below nonnegative and all the
new total levels strictly smaller. The three insertion moves remain separate.
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

/-- The dual-slot relation in the total-level-normalized series. -/
theorem normalizedSeries_dual
    (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hY₂ : LogHuangODEProduct.IsGradedJacobiFamily A₂ A₅ A₆ Y₂)
    (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₁ : LogHuangODEProduct.CosetBase A₁ h₁) (hl₂ : LogHuangODEProduct.CosetBase A₂ h₂)
    (hl₃ : LogHuangODEProduct.CosetBase A₃ h₃) (hl₄ : LogHuangODEProduct.CosetBase A₄ h₄)
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {d : ℕ} (hd : 1 ≤ d) {u : V} (hu : u ∈ W.grading (d : ℤ))
    (f : M₀ →ₗ[ℂ] ℂ) (j : ℕ) {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      (f ∘ₗ mode (A₀.YM u) (2 * (d : ℤ) - 1 + j)) w₁ w₂ w₃ w₄
      (N₀ + d + j) (N₀ + d + j + N₁ + N₂ + N₃ + N₄) =
    (if d + j ≤ N₄ then X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
      normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ (mode (A₄.YM u) (2 * (d : ℤ) - 1 + j) w₄) N₀
        (N₀ + N₁ + N₂ + N₃ + (N₄ - (d + j))) else 0)
    + ∑ k ∈ Finset.range (N₁ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (j + k + 1) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f (mode (A₁.YM u) k w₁) w₂ w₃ w₄ N₀
          (N₀ + (N₁ + d - (k + 1)) + N₂ + N₃ + N₄))
    + ∑ k ∈ Finset.range (N₂ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (j + k + 1)) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ (mode (A₂.YM u) k w₂) w₃ w₄ N₀
          (N₀ + N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
    + ∑ k ∈ Finset.range (N₃ + d), (cbz (2 * (d : ℤ) - 1 + j) k) •
      (X ^ (2 * (d + j)) * PowerSeries.C (X ^ (2 * (d + j))) *
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ (mode (A₃.YM u) k w₃) w₄ N₀
          (N₀ + N₁ + N₂ + (N₃ + d - (k + 1)) + N₄)) := by
  classical
  ext m n
  simp only [map_add, map_sum, coeff_smul, smul_eq_mul, coeff_normalizedSeries]
  unfold normalizedCoeff productCoeff
  simp only [LinearMap.comp_apply]
  rw [product_dual_mode hY₁ hY₂ hY₃ u f w₁ w₂ w₃ w₄ _ _ _
    (2 * (d : ℤ) - 1 + j) (N₁ + N₂ + N₃ + 3 * d)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₂ hu hw₂ (by omega))
    (fun k hk => mode_eq_zero_of_le hl₃ hu hw₃ (by omega))]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · split_ifs with hlev
    · have hw₄' : mode (A₄.YM u) (2 * (d : ℤ) - 1 + j) w₄ ∈
          A₄.weight (h₄ + ((N₄ - (d + j) : ℕ) : ℂ)) := by
        convert C2Rigid.mode_mem_weight A₄ hu hw₄ (2 * (d : ℤ) - 1 + j) using 1
        congr 1
        rw [Nat.cast_sub hlev]
        push_cast
        ring
      rw [coeff_monomial_normalizedSeries hB (by omega) hw₂ hw₃ hw₄']
      unfold normalizedCoeff productCoeff
      simp only [Nat.cast_add, Nat.cast_sub hlev]
      push_cast
      ring_nf
    · rw [map_zero, map_zero, mode_eq_zero_of_le hl₄ hu hw₄ (by omega)]
      simp
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
    rw [coeff_monomial_normalizedSeries hB (by omega)
      hw₂ (mode_mem_weight_nat hu hw₃ hk') hw₄]
    unfold normalizedCoeff productCoeff
    simp only [Nat.cast_add, Nat.cast_sub (by omega : k + 1 ≤ N₃ + d)]
    push_cast
    ring_nf

end VOA.Huang.LogAssocFivePointGraded
