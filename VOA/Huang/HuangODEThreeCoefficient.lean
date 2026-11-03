import VOA.Huang.HuangODEModes

/-! # Three-intertwiner coefficients and their two independent levels

The two indices are the levels in the two intermediate modules. They are
independent: homogeneity eliminates only the third mode index. In product
coordinates the corresponding power-series variables are `z₂/z₁` and `z₃/z₂`.
No convergence or regular-singular equation is asserted in this file.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop PowerSeries
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {A₅ : OrdVModule W M₅} {A₆ : OrdVModule W M₆}
variable (Y₁ : IntertwiningModes M₁ M₆ M₀) (Y₂ : IntertwiningModes M₂ M₅ M₆)
  (Y₃ : IntertwiningModes M₃ M₄ M₅)

/-- The actual scalar coefficient of a product of three intertwiners. -/
def productCoeff (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) : ℂ := f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)))

variable {Y₁ Y₂ Y₃}
variable (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
  (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
  (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)

include hY₁ hY₂ hY₃ in
/-- Homogeneity leaves a two-dimensional plane of potentially nonzero modes. -/
theorem product_mem_weight {α₁ α₂ α₃ α₄ : ℂ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄) (p q r : ℂ) :
    Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)) ∈
      A₀.weight (α₁ + α₂ + α₃ + α₄ - p - q - r - 3) := by
  convert mem_weight hY₁ h₁ (mem_weight hY₂ h₂ (mem_weight hY₃ h₃ h₄ r) q) p using 1
  congr 1
  ring

include hY₁ hY₂ hY₃ in
/-- The supported output functional kills every coefficient off that plane. -/
theorem productCoeff_eq_zero_of_ne {α₀ α₁ α₂ α₃ α₄ : ℂ}
    {f : M₀ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄)
    (hf : SupportedAt A₀ f α₀) (p q r : ℂ)
    (hne : p + q + r ≠ α₁ + α₂ + α₃ + α₄ - α₀ - 3) :
    productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ p q r = 0 := by
  apply hf _ _ _ (product_mem_weight hY₁ hY₂ hY₃ h₁ h₂ h₃ h₄ p q r)
  intro he
  apply hne
  linear_combination -he

include hY₁ hY₂ hY₃ in
/-- The two lowest-weight spectra give a rectangular natural-number indexing
of all nonzero scalar coefficients, without a uniform truncation assumption. -/
theorem productCoeff_ne_zero_levels {α₀ α₁ α₂ α₃ α₄ h₅ h₆ : ℂ}
    (hl₅ : IsLowestWeight A₅ h₅) (hl₆ : IsLowestWeight A₆ h₆)
    {f : M₀ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄)
    (hf : SupportedAt A₀ f α₀) {p q r : ℂ}
    (hne : productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ p q r ≠ 0) :
    ∃ m n : ℕ, p = α₁ + h₆ + m - α₀ - 1 ∧
      q = α₂ + h₅ + n - h₆ - m - 1 ∧ r = α₃ + α₄ - h₅ - n - 1 := by
  have hn₅ : Y₃ r w₃ w₄ ≠ 0 := by
    intro hz
    apply hne
    simp [productCoeff, hz]
  have hn₆ : Y₂ q w₂ (Y₃ r w₃ w₄) ≠ 0 := by
    intro hz
    apply hne
    simp [productCoeff, hz]
  have hw₅ := mem_weight hY₃ h₃ h₄ r
  have hw₆ := mem_weight hY₂ h₂ hw₅ q
  obtain ⟨n, en⟩ := hl₅ _ (fun hz => hn₅ (by
    rw [hz, Submodule.mem_bot] at hw₅
    exact hw₅))
  obtain ⟨m, em⟩ := hl₆ _ (fun hz => hn₆ (by
    rw [hz, Submodule.mem_bot] at hw₆
    exact hw₆))
  have e : p + q + r = α₁ + α₂ + α₃ + α₄ - α₀ - 3 := by
    by_contra hh
    exact hne (productCoeff_eq_zero_of_ne hY₁ hY₂ hY₃ h₁ h₂ h₃ h₄ hf p q r hh)
  refine ⟨m, n, ?_, ?_, ?_⟩
  · linear_combination e + em
  · linear_combination en - em
  · linear_combination -en

include hY₁ in
/-- Translation in each insertion variable, before any infinite summation. -/
theorem productCoeff_Lm1_first (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) :
    productCoeff Y₁ Y₂ Y₃ f (A₁.Lm1 w₁) w₂ w₃ w₄ p q r =
      -p * productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ (p - 1) q r := by
  unfold productCoeff
  rw [hY₁.L_neg_one]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]

include hY₂ in
theorem productCoeff_Lm1_second (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) :
    productCoeff Y₁ Y₂ Y₃ f w₁ (A₂.Lm1 w₂) w₃ w₄ p q r =
      -q * productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ p (q - 1) r := by
  unfold productCoeff
  rw [hY₂.L_neg_one]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]

include hY₃ in
theorem productCoeff_Lm1_third (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (p q r : ℂ) :
    productCoeff Y₁ Y₂ Y₃ f w₁ w₂ (A₃.Lm1 w₃) w₄ p q r =
      -r * productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ p q (r - 1) := by
  unfold productCoeff
  rw [hY₃.L_neg_one]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]

/-- The reduced series on the two intermediate lowest-weight spectra. The
outer power-series variable is `z₂/z₁`; the inner one is `z₃/z₂`. -/
def productSeries (Y₁ : IntertwiningModes M₁ M₆ M₀) (Y₂ : IntertwiningModes M₂ M₅ M₆)
    (Y₃ : IntertwiningModes M₃ M₄ M₅) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (α₀ α₁ α₂ α₃ α₄ h₅ h₆ : ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun m => PowerSeries.mk fun n =>
    productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄
      (α₁ + h₆ + m - α₀ - 1) (α₂ + h₅ + n - h₆ - m - 1) (α₃ + α₄ - h₅ - n - 1)

@[simp] theorem coeff_productSeries (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (α₀ α₁ α₂ α₃ α₄ h₅ h₆ : ℂ) (m n : ℕ) :
    coeff n (coeff m (productSeries Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ α₀ α₁ α₂ α₃ α₄ h₅ h₆)) =
      productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄
        (α₁ + h₆ + m - α₀ - 1) (α₂ + h₅ + n - h₆ - m - 1) (α₃ + α₄ - h₅ - n - 1) := by
  simp [productSeries]

end VOA.Huang.HuangODEThree
