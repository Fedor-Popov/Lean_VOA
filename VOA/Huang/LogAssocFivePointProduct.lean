/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.LogHuangODEProductMain

/-! # Genuine logarithmic five-point product coefficients

The two internal levels and all three logarithmic degrees are retained. The
actual coupled derivative identities, uniform logarithmic cutoffs, and true
C2 row convergence are established for generalized modules, without a
semisimplicity hypothesis. Joint convergence remains a separate analytic step.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
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

/-- Literal three-operator scalar coefficients, with every log degree explicit. -/
def productCoeff (Y₁ : LogModes M₁ M₆ M₀) (Y₂ : LogModes M₂ M₅ M₆)
    (Y₃ : LogModes M₃ M₄ M₅) (f : M₀ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄)
    (p q r : ℂ) (k l j : ℕ) : ℂ :=
  f (Y₁ p k x (Y₂ q l y (Y₃ r j z w)))

variable (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
  (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)

/-- The genuine threefold coefficient lies in the actual generalized weight. -/
theorem product_mem_weight {a b c d : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b)
    (hz : z ∈ N₃.weight c) (hw : w ∈ N₄.weight d)
    (p q r : ℂ) (k l j : ℕ) :
    Y₁.1 p k x (Y₂.1 q l y (Y₃.1 r j z w)) ∈
      N₀.weight (a+b+c+d-p-q-r-3) := by
  convert Y₁.2.mem_weight hx (Y₂.2.mem_weight hy (Y₃.2.mem_weight hz hw r j) q l) p k using 1
  congr 1
  ring

/-- The first insertion derivative retains the actual successor log degree. -/
theorem productCoeff_Lm1_first (f : M₀ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (p q r : ℂ) (k l j : ℕ) :
    productCoeff Y₁.1 Y₂.1 Y₃.1 f (Lm1 N₁.toWeakModule x) y z w p q r k l j =
      (-p) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w (p-1) q r k l j +
        ((k : ℂ)+1) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w (p-1) q r (k+1) l j := by
  unfold productCoeff
  rw [Y₁.2.L_neg_one, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, map_add, map_smul, map_smul]

/-- The second insertion derivative retains its actual logarithmic correction. -/
theorem productCoeff_Lm1_second (f : M₀ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (p q r : ℂ) (k l j : ℕ) :
    productCoeff Y₁.1 Y₂.1 Y₃.1 f x (Lm1 N₂.toWeakModule y) z w p q r k l j =
      (-q) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w p (q-1) r k l j +
        ((l : ℂ)+1) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w p (q-1) r k (l+1) j := by
  unfold productCoeff
  rw [Y₂.2.L_neg_one, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, map_add, map_smul, map_smul, map_add, map_smul, map_smul]

/-- The innermost derivative, which supplies the coupled inner Euler equation. -/
theorem productCoeff_Lm1_third (f : M₀ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (p q r : ℂ) (k l j : ℕ) :
    productCoeff Y₁.1 Y₂.1 Y₃.1 f x y (Lm1 N₃.toWeakModule z) w p q r k l j =
      (-r) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w p q (r-1) k l j +
        ((j : ℂ)+1) • productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w p q (r-1) k l (j+1) := by
  unfold productCoeff
  rw [Y₃.2.L_neg_one, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, map_add, map_smul, map_smul, map_add, map_smul, map_smul,
    map_add, map_smul, map_smul]

/-- Finitely generated actual generalized modules give a uniform finite box of
all possible logarithmic degrees of the full three-operator product. -/
theorem exists_uniform_log_cutoffs
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule) :
    ∃ K L J : ℕ, ∀ (f : M₀ →ₗ[ℂ] ℂ) x y z w p q r k l j,
      K ≤ k ∨ L ≤ l ∨ J ≤ j → productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w p q r k l j = 0 := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₆ N₀ hfg₁ hfg₆ hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₅ N₆ hfg₂ hfg₅ hfg₆
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
  refine ⟨K,L,J,?_⟩
  intro f x y z w p q r k l j h
  rcases h with hk | hl | hj
  · unfold productCoeff
    rw [hK Y₁ p k hk]
    simp
  · unfold productCoeff
    rw [hL Y₂ q l hl]
    simp
  · unfold productCoeff
    rw [hJ Y₃ r j hj]
    simp

/-- Actual C2 convergence of every outer row, including every original log
triple and every integer shift of the inner weight. -/
theorem summable_product_row (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun m : ℕ =>
      ‖productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j * t^m‖ := by
  have hi := Y₃.2.mem_weight hz hw (c-v) j
  have hs := summable_log_product_homogeneous hC2 N₁ N₂ N₅ N₀ N₆
    hfg₁ hfg₂ hfg₅ hfg₀ hfg₆ Y₁ Y₂ hx hy hi f
    (a-shift) (b+shift+v) k l ht
  refine hs.congr fun m => ?_
  dsimp only [productCoeff]
  congr 5
  ring

/-- Genuine geometric row bounds for the five-point coefficient array. The
constant may depend on the row, while the chosen outer rate is arbitrary >1. -/
theorem product_row_geometric (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j‖ ≤ K*ρ^m := by
  let C : ℕ → ℂ := fun m => productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
    (a-shift+m) (b+shift-m+v) (c-v) k l j
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have ht : ‖((ρ⁻¹ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
    exact (inv_lt_one₀ hρ0).mpr hρ
  have hs := summable_product_row N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃ hC2
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

end VOA.Huang.LogAssocFivePoint
