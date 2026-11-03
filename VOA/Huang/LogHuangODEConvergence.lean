import VOA.Huang.LogHuangODEProductMain
import VOA.Huang.LogHuangODEIterateMain

/-! Absolute convergence of genuine logarithmic coset matrix coefficients
in the two-variable product and iterate regions, with their actual complex
powers and logarithmic multipliers retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEConvergence
open VOA VOA.LogTensor
open scoped BigOperators

/-- Coset convergence in a ratio variable gives the actual two-variable
complex powers and both finite logarithmic multipliers. -/
theorem summable_log_coset_twoVar {χ : ℕ → ℂ} {u v : ℂ}
    (hv : v≠0) (hvu : ‖v‖<‖u‖)
    (hs : Summable fun n => ‖χ n * (v/u)^n‖) (A B : ℂ) (k l : ℕ) :
    Summable fun n => ‖χ n * u^(A-n) * v^(B+n) * (Complex.log u)^k * (Complex.log v)^l‖ := by
  have hu : u≠0 := by
    intro he
    rw [he,norm_zero] at hvu
    exact (not_lt_of_ge (norm_nonneg v)) hvu
  have hnorm : ‖u‖≠0 := norm_ne_zero_iff.mpr hu
  refine (hs.mul_left (‖u^A‖ * ‖v^B‖ * ‖(Complex.log u)^k‖ * ‖(Complex.log v)^l‖)).congr ?_
  intro n
  have he₁ : u^(A-(n : ℂ))=u^A/u^n := by
    rw [Complex.cpow_sub _ _ hu,Complex.cpow_natCast]
  have he₂ : v^(B+(n : ℂ))=v^B*v^n := by
    rw [Complex.cpow_add _ _ hv,Complex.cpow_natCast]
  rw [he₁,he₂]
  simp only [norm_mul,norm_div,norm_pow]
  rw [div_pow]
  field_simp

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- Actual products converge absolutely in the product region, at every log degree. -/
theorem summable_log_product_twoVar
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) (k l : ℕ)
    {z₁ z₂ : ℂ} (h₂ : z₂≠0) (h₁₂ : ‖z₂‖<‖z₁‖) :
    Summable fun n : ℕ => ‖f (Y₁.1 (a+n) k x (Y₂.1 (b-n) l y z)) *
      z₁^(-a-n-1) * z₂^(-b+n-1) * (Complex.log z₁)^k * (Complex.log z₂)^l‖ := by
  have h₁ : z₁≠0 := by
    intro he
    rw [he,norm_zero] at h₁₂
    exact (not_lt_of_ge (norm_nonneg z₂)) h₁₂
  have ht : ‖z₂/z₁‖<1 := by
    rw [norm_div,div_lt_one (norm_pos_iff.mpr h₁)]
    exact h₁₂
  have hs := LogHuangODEProduct.summable_log_product hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b k l ht
  have hh := summable_log_coset_twoVar h₂ h₁₂ hs (-a-1) (-b-1) k l
  have ha (n : ℕ) : -a-(n : ℂ)-1=(-a-1)-n := by ring
  have hb (n : ℕ) : -b+(n : ℂ)-1=(-b-1)+n := by ring
  simpa only [ha,hb] using hh

/-- Actual iterates converge absolutely in the iterate region, at every log degree. -/
theorem summable_log_iterate_twoVar
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) (k l : ℕ)
    {z₂ z₀ : ℂ} (h₀ : z₀≠0) (h₀₂ : ‖z₀‖<‖z₂‖) :
    Summable fun n : ℕ => ‖f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) *
      z₂^(-a-n-1) * z₀^(-b+n-1) * (Complex.log z₂)^k * (Complex.log z₀)^l‖ := by
  have h₂ : z₂≠0 := by
    intro he
    rw [he,norm_zero] at h₀₂
    exact (not_lt_of_ge (norm_nonneg z₀)) h₀₂
  have ht : ‖z₀/z₂‖<1 := by
    rw [norm_div,div_lt_one (norm_pos_iff.mpr h₂)]
    exact h₀₂
  have hs := LogHuangODEIterate.summable_log_iterate hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z a b k l ht
  have hh := summable_log_coset_twoVar h₀ h₀₂ hs (-a-1) (-b-1) k l
  have ha (n : ℕ) : -a-(n : ℂ)-1=(-a-1)-n := by ring
  have hb (n : ℕ) : -b+(n : ℂ)-1=(-b-1)+n := by ring
  simpa only [ha,hb] using hh

end VOA.Huang.LogHuangODEConvergence
