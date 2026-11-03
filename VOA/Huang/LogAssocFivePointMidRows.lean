import VOA.Huang.LogAssocFivePointMidFamily
import VOA.Huang.LogAssocFivePointProduct

/-! Genuine C2 iterate-in-product row convergence at every original log triple. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA.LogTensor VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁)
  (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

variable (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
  (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
  (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)

/-- Actual C2 convergence of every outer row, including every original log
triple and every integer shift of the inner weight. -/
theorem summable_mid_row (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun m : ℕ =>
      ‖LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j * t^m‖ := by
  have hi := Y₃.2.mem_weight hz hw (c-v) j
  have hs := summable_log_product_homogeneous hC2 N₁ N₅ N₂ N₀ N₆
    hfg₁ hfg₅ hfg₂ hfg₀ hfg₆ Y₁ YB hx hi hy f
    (a-shift) (b+shift+v) k l ht
  refine hs.congr fun m => ?_
  dsimp only [LogAssocFivePoint.productCoeff,flipLogModes,LinearMap.flip_apply]
  congr 5
  ring

/-- Genuine geometric row bounds for the five-point coefficient array. The
constant may depend on the row, while the chosen outer rate is arbitrary >1. -/
theorem mid_row_geometric (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j‖ ≤ K*ρ^m := by
  let C : ℕ → ℂ := fun m => LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
    (a-shift+m) (b+shift-m+v) (c-v) k l j
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have ht : ‖((ρ⁻¹ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
    exact (inv_lt_one₀ hρ0).mpr hρ
  have hs := summable_mid_row N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃ hC2
    hfg₀ hfg₁ hfg₂ hfg₅ hfg₆ hx hy hz hw f a b c k l j shift v ht
  refine ⟨∑' m : ℕ, ‖C m*((ρ⁻¹ : ℝ) : ℂ)^m‖, tsum_nonneg (fun _ => norm_nonneg _),?_⟩
  intro m
  have hb := hs.le_tsum m (fun n hn => norm_nonneg _)
  have hn : ‖((ρ⁻¹ : ℝ) : ℂ)‖ = ρ⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
  have hmul := mul_le_mul_of_nonneg_right hb (pow_nonneg (le_of_lt hρ0) m)
  rw [norm_mul, norm_pow, hn, mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hρ0),
    one_pow, mul_one] at hmul
  exact hmul

end VOA.Huang.LogAssocFivePointGraded
