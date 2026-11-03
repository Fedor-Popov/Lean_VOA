import VOA.Huang.LogAssocFivePointPairFamily
import VOA.Huang.LogAssocFivePointProduct

/-! Genuine C2 iterate-in-product row convergence at every original log triple. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA.LogTensor VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁)
  (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (NU : LogVModule W MU) (NV : LogVModule W MV)

/-- Literal scalar two-cluster coefficient with all three true log degrees. -/
def pairCoeff (P : LogModes MU MV M₀) (ZT : LogModes M₂ M₁ MV)
    (XY : LogModes M₃ M₄ MU) (f : M₀ →ₗ[ℂ] ℂ)
    (t : M₁) (z : M₂) (x : M₃) (y : M₄) (p q r : ℂ) (k l j : ℕ) : ℂ :=
  f (P p k (XY r j x y) (ZT q l z t))

variable (P : LogIntertwiningOperator NU.toWeakModule NV.toWeakModule N₀.toWeakModule)
  (ZT : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule NV.toWeakModule)
  (XY : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule NU.toWeakModule)

/-- Actual C2 convergence of every outer row, including every original log
triple and every integer shift of the inner weight. -/
theorem summable_pair_row (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfgU : FinGen NU.toWeakModule)
    (hfgV : FinGen NV.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun m : ℕ =>
      ‖pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j * t^m‖ := by
  have hi := XY.2.mem_weight hz hw (c-v) j
  have hs := summable_log_product_homogeneous hC2 NU N₂ N₁ N₀ NV
    hfgU hfg₂ hfg₁ hfg₀ hfgV P ZT hi hy hx f
    (a-shift) (b+shift+v) k l ht
  refine hs.congr fun m => ?_
  dsimp only [pairCoeff]
  congr 5
  ring

/-- Genuine geometric row bounds for the five-point coefficient array. The
constant may depend on the row, while the chosen outer rate is arbitrary >1. -/
theorem pair_row_geometric (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfgU : FinGen NU.toWeakModule)
    (hfgV : FinGen NV.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    (shift : ℕ) (v : ℤ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a-shift+m) (b+shift-m+v) (c-v) k l j‖ ≤ K*ρ^m := by
  let C : ℕ → ℂ := fun m => pairCoeff P.1 ZT.1 XY.1 f x y z w
    (a-shift+m) (b+shift-m+v) (c-v) k l j
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have ht : ‖((ρ⁻¹ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
    exact (inv_lt_one₀ hρ0).mpr hρ
  have hs := summable_pair_row N₀ N₁ N₂ N₃ N₄ NU NV P ZT XY hC2
    hfg₀ hfg₁ hfg₂ hfgU hfgV hx hy hz hw f a b c k l j shift v ht
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
