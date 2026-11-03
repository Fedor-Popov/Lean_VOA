import VOA.Huang.LogAssocFivePointC1Induction
import VOA.Huang.HuangODEThreeSepMidRing

/-!
# The middle (iterate-in-product) shape as a normalized three-slot series

For `f(𝒴_A(a)_p 𝒴_B(𝒴_C(b)_r c)_q e)` (the vertex `X ⊠ ((Y ⊠ Z) ⊠ T)` and, after skew-symmetry
at the root, `((X ⊠ Y) ⊠ Z) ⊠ T`) we reuse the product normalization verbatim through the
argument flip `swap2 𝒴_B` (`(swap2 𝒴_B)_q e v = (𝒴_B)_q v e`, NOT an intertwining operator):

  `normalizedSeries 𝒴_A (swap2 𝒴_B) 𝒴_C c ν μ f a e b c N₀ s`,

with product slots `(w₁, w₂, w₃, w₄) = (a, e, b, c)`. Only weight compatibility is needed for
the uniform base, the functional congruence and the finite base; the moves are new
(`HuangODEThreeSepMidMoves`). In the chart `x = z₂/z₁`, `y = z₀/z₂` the total level is attached
to the innermost point `z₀`, as for products; this is the normalization for which all five
middle-chart moves are regular (checked monomial by monomial).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid PowerSeries
open VOA.Huang.LogHuangODEProduct VOA.Huang.LogHuangODEModes
open VOA.Huang.FivePointSep
open VOA.Huang.LogHuangODEProduct
open VOA.Huang.HuangODEProduct (sum_range_trim)
open VOA.Huang.HuangODEModes (cbz_neg_one_sub cbz_nat)
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

/-- The argument flip of a mode family (no Jacobi identity is claimed). -/
def swap2 (Y : IntertwiningModes M₅ M₂ M₆) : IntertwiningModes M₂ M₅ M₆ :=
  fun q => (Y q).flip

@[simp] theorem swap2_apply (Y : IntertwiningModes M₅ M₂ M₆) (q : ℂ) (e : M₂) (v : M₅) :
    swap2 Y q e v = Y q v e := rfl

variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {YB : IntertwiningModes M₅ M₂ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

/-- The middle-shape vector lies on one weight. -/
theorem mid_mem_weight (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB) (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    {α₁ α₂ α₃ α₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄) (p q r : ℂ) :
    Y₁ p w₁ (swap2 YB q w₂ (Y₃ r w₃ w₄)) ∈
      A₀.weight (α₁ + α₂ + α₃ + α₄ - p - q - r - 3) := by
  convert hY₁.mem_weight h₁ (hYB.mem_weight (hY₃.mem_weight h₃ h₄ r) h₂ q) p using 1
  congr 1
  ring

/-- Boundedness below gives a uniform base for the flipped middle shape. -/
theorem exists_midUniformBase (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB)
    (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃) (h₂ h₃ h₄ ν₀ μ₀ : ℂ) :
    ∃ K L : ℕ, UniformTwoBase A₂ A₃ A₄ (swap2 YB) Y₃ h₂ h₃ h₄ (ν₀ + K) (μ₀ + L) := by
  obtain ⟨B₅, hB₅⟩ := A₅.boundedBelow
  obtain ⟨B₆, hB₆⟩ := A₆.boundedBelow
  obtain ⟨K, hK⟩ := exists_nat_gt ((h₂ + h₃ + h₄ - ν₀ - 2).re - B₆)
  obtain ⟨L, hL⟩ := exists_nat_gt ((h₃ + h₄ - μ₀ - 1).re - B₅)
  refine ⟨K, L, ?_⟩
  intro N₂ N₃ N₄ s hs w₂ w₃ w₄ hw₂ hw₃ hw₄ m n hmn
  have hs' : (N₂ : ℝ) + N₃ + N₄ ≤ s := by exact_mod_cast hs
  have hv₅ := hY₃.mem_weight hw₃ hw₄ (μ₀ + L + s - n)
  have hv₆ := hYB.mem_weight hv₅ hw₂ (ν₀ + K - (μ₀ + L) - m + n)
  rw [swap2_apply]
  rcases hmn with hm | hn
  · by_contra he
    have hb := hB₆ _ (fun hb => he (by rw [hb, Submodule.mem_bot] at hv₆; exact hv₆))
    have hm' : (m : ℝ) < 0 := by exact_mod_cast hm
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
      Complex.intCast_re, Complex.one_re] at hb hK
    norm_num at hK
    linarith
  · have hz : Y₃ (μ₀ + L + s - n) w₃ w₄ = 0 := by
      by_contra he
      have hb := hB₅ _ (fun hb => he (by rw [hb, Submodule.mem_bot] at hv₅; exact hv₅))
      have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
      have hN₂ : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
      simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
        Complex.intCast_re, Complex.one_re] at hb hL
      linarith
    rw [hz, map_zero, LinearMap.zero_apply]

/-- Only the selected output weight matters (middle shape). -/
theorem midCoeff_congr_functional (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB) (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    {f g : M₀ →ₗ[ℂ] ℂ} (hf : f.domRestrict (A₀.weight (h₀ + N₀)) =
      g.domRestrict (A₀.weight (h₀ + N₀))) (m n : ℂ) :
    normalizedCoeff Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ f w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) m n =
    normalizedCoeff Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ g w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) m n := by
  have hw := mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄
    (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m)
    (ν - μ - m + n) (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n)
  have e : (h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) + (h₄ + N₄) -
      (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m) -
      (ν - μ - m + n) - (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n) - 3 = h₀ + N₀ := by
    push_cast
    ring
  rw [e] at hw
  exact LinearMap.congr_fun hf ⟨_, hw⟩

theorem midSeries_congr_f (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB) (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    {f g : M₀ →ₗ[ℂ] ℂ} (hf : f.domRestrict (A₀.weight (h₀ + N₀)) =
      g.domRestrict (A₀.weight (h₀ + N₀))) :
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ f w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) =
    normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ g w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) := by
  refine PS2.ext fun m n => ?_
  rw [c2_normalizedSeries, c2_normalizedSeries]
  exact midCoeff_congr_functional hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ hf m n

/-- Finitely many tuples span the middle series at fixed levels. -/
theorem exists_finite_span_mid (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB) (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (N₀ N₁ N₂ N₃ N₄ : ℕ) :
    ∃ S : Set PS2, S.Finite ∧
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ Submodule.span ℂ S := by
  classical
  haveI := A₀.finrank (h₀ + N₀)
  haveI := A₁.finrank (h₁ + N₁)
  haveI := A₂.finrank (h₂ + N₂)
  haveI := A₃.finrank (h₃ + N₃)
  haveI := A₄.finrank (h₄ + N₄)
  let E₀ := A₀.weight (h₀ + N₀)
  obtain ⟨E', hE'⟩ := Submodule.exists_isCompl E₀
  let π := Submodule.projectionOnto E₀ E' hE'
  let b₀ := Module.finBasis ℂ (Module.Dual ℂ E₀)
  let b₁ := Module.finBasis ℂ (A₁.weight (h₁ + N₁))
  let b₂ := Module.finBasis ℂ (A₂.weight (h₂ + N₂))
  let b₃ := Module.finBasis ℂ (A₃.weight (h₃ + N₃))
  let b₄ := Module.finBasis ℂ (A₄.weight (h₄ + N₄))
  let c := h₁ + h₂ + h₃ + h₄ - h₀ - 3
  let s := N₀ + N₁ + N₂ + N₃ + N₄
  refine ⟨Set.range (fun q : _ × _ × _ × _ × _ =>
    normalizedSeries Y₁ (swap2 YB) Y₃ c ν μ ((b₀ q.1).comp π) (b₁ q.2.1 : M₁)
      (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2.1 : M₃) (b₄ q.2.2.2.2 : M₄) N₀ s),
    Set.finite_range _, ?_⟩
  intro f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  have hf : f.domRestrict E₀ = ((f.domRestrict E₀).comp π).domRestrict E₀ := by
    ext x
    simp [π, Submodule.projectionOnto_apply_left]
  have he := midSeries_congr_f hY₁ hYB hY₃ (ν := ν) (μ := μ) hw₁ hw₂ hw₃ hw₄ hf
  change normalizedSeries Y₁ (swap2 YB) Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ∈ _
  rw [he]
  have hψ := b₀.sum_repr (f.domRestrict E₀)
  have hcomp : (f.domRestrict E₀).comp π =
      ∑ a, b₀.repr (f.domRestrict E₀) a • (b₀ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change normalizedLinearFunctional Y₁ (swap2 YB) Y₃ c ν μ N₀ s w₁ w₂ w₃ w₄
    ((f.domRestrict E₀).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change normalizedLinearFirst Y₁ (swap2 YB) Y₃ c ν μ N₀ s ((b₀ a).comp π) w₂ w₃ w₄ w₁ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change normalizedLinearSecond Y₁ (swap2 YB) Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁)
    w₃ w₄ w₂ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change normalizedLinearThird Y₁ (swap2 YB) Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁)
    (b₂ j : M₂) w₄ w₃ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₃ _ fun k => ?_
  change normalizedLinearTerminal Y₁ (swap2 YB) Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁)
    (b₂ j : M₂) (b₃ k : M₃) w₄ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₄ _ fun l => ?_
  exact Submodule.subset_span ⟨(a, i, j, k, l), rfl⟩

theorem exists_finite_span_mid_box (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
    (hYB : LogHuangODEProduct.IsGradedJacobiFamily A₅ A₂ A₆ YB) (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (B₀ B₁ B₂ B₃ B₄ : ℕ) :
    ∃ S : Set PS2, S.Finite ∧
      ∀ (N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ ≤ B₀ → N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries Y₁ (swap2 YB) Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ Submodule.span ℂ S := by
  classical
  choose S hfin hS using fun q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) ×
      Fin (B₃ + 1) × Fin (B₄ + 1) =>
    exists_finite_span_mid hY₁ hYB hY₃ h₀ h₁ h₂ h₃ h₄ ν μ
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  refine ⟨⋃ q, S q, Set.finite_iUnion hfin, ?_⟩
  intro N₀ N₁ N₂ N₃ N₄ b₀ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  let q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
    (⟨N₀, by omega⟩, ⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩)
  exact Submodule.span_mono (Set.subset_iUnion S q) (hS q f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄)

/-! ## Coefficients of the middle-chart ring elements times normalized series -/

theorem coeff_X_mul_binom' (a : ℂ) (k i : ℕ) :
    coeff (i + 1) ((X : PowerSeries ℂ) * HuangODEAlgebra.binomSeries a k) =
      (i.choose k : ℂ) * a ^ (i - k) := by
  rw [coeff_succ_X_mul]; simp [HuangODEAlgebra.binomSeries]

section Uniform

variable {h₂ h₃ h₄ ν μ : ℂ} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
  {N₂ N₃ N₄ s : ℕ} (hs : N₂ + N₃ + N₄ ≤ s)
  {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
  (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃))
  (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
  (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (N₀ : ℕ)
include hB hs hw₂ hw₃ hw₄

/-- The inner binomial line `y · Σ C(j,k) (-1)^(j-k) yʲ`. -/
theorem c2_ιy_binomNeg_normalized (k m n J : ℕ) (hJ : n ≤ J) :
    c2 (ιy (X * HuangODEAlgebra.binomSeries (-1) k) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ j ∈ Finset.range J, (j.choose k : ℂ) * (-1) ^ (j - k) *
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s (m : ℂ) ((n : ℂ) - 1 - j) := by
  rw [c2_ιy_mul, Finset.sum_range_succ']
  simp only [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  rw [Finset.sum_eq_zero (s := Finset.Ico n J) (fun j hj => by
    have hj' := (Finset.mem_Ico.mp hj).1
    rw [normalizedCoeff_neg' hB hs hw₂ hw₃ hw₄ c f w₁ N₀ (m : ℤ) ((n : ℤ) - 1 - j)
      (Or.inr (by omega)) (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn := Finset.mem_range.mp hj
  rw [coeff_X_mul_binom', c2_normalizedSeries]
  congr 2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

end Uniform

/-- The two-dimensional series `(1 - x(1+y))^{-k-1}` against a normalized series. -/
theorem c2_ιm_geom_normalized {Y₂ : IntertwiningModes M₂ M₅ M₆} (c ν μ : ℂ)
    (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (N₀ s k m n : ℕ) :
    c2 (ιm (HuangODEAlgebra.geom 1 ^ (k + 1)) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      ((i + k).choose k : ℂ) * (i.choose j : ℂ) *
        normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ((m : ℂ) - i) ((n : ℂ) - j) := by
  rw [c2_ιm_mul]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [c2_normalizedSeries]
  have hgeom : coeff i (HuangODEAlgebra.geom 1 ^ (k + 1)) = ((i + k).choose k : ℂ) := by
    have h := congrArg (coeff (i + k)) (HuangODEAlgebra.binomSeries_eq 1 k)
    rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h
    rw [← h]
    simp [HuangODEAlgebra.binomSeries]
  rw [hgeom]
  congr 2
  · rw [Nat.cast_sub (by omega)]
  · rw [Nat.cast_sub (by omega)]


end VOA.Huang.LogAssocFivePointGraded
