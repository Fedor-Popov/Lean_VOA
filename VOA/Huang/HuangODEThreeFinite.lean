import VOA.Huang.HuangODEThreeTerminal

/-! # Finite base spaces for the normalized five-slot induction

At any fixed five external levels, finitely many basis tuples span all the
normalized series over ℂ. Taking finitely many levels gives the finite base
required for a future C₁ induction. No high-level reduction is assumed proved.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open VOA VOA.Huang.FusionTop PowerSeries
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
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

/-- Linearity in one of the five external slots. -/
def normalizedLinearFunctional (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (N₀ s : ℕ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) :
    (M₀ →ₗ[ℂ] ℂ) →ₗ[ℂ] PowerSeries (PowerSeries ℂ) where
  toFun f := normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
  map_add' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff, map_add]
  map_smul' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff]

/-- Linearity in one of the five external slots. -/
def normalizedLinearFirst (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (N₀ s : ℕ) (f : M₀ →ₗ[ℂ] ℂ) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) :
    M₁ →ₗ[ℂ] PowerSeries (PowerSeries ℂ) where
  toFun w₁ := normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
  map_add' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff, map_add]
  map_smul' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff]

/-- Linearity in one of the five external slots. -/
def normalizedLinearSecond (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (N₀ s : ℕ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₃ : M₃) (w₄ : M₄) :
    M₂ →ₗ[ℂ] PowerSeries (PowerSeries ℂ) where
  toFun w₂ := normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
  map_add' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff, map_add]
  map_smul' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff]

/-- Linearity in one of the five external slots. -/
def normalizedLinearThird (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (N₀ s : ℕ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₄ : M₄) :
    M₃ →ₗ[ℂ] PowerSeries (PowerSeries ℂ) where
  toFun w₃ := normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
  map_add' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff, map_add]
  map_smul' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff]

/-- Linearity in one of the five external slots. -/
def normalizedLinearTerminal (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (N₀ s : ℕ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    M₄ →ₗ[ℂ] PowerSeries (PowerSeries ℂ) where
  toFun w₄ := normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
  map_add' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff, map_add]
  map_smul' a b := by
    ext m n
    simp [normalizedSeries, normalizedCoeff, productCoeff]

/-- Finitely many homogeneous tuples span every normalized five-slot series
at fixed external levels. The output functional is arbitrary. -/
theorem exists_finite_span_normalized
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (N₀ N₁ N₂ N₃ N₄ : ℕ) :
    ∃ S : Set (PowerSeries (PowerSeries ℂ)), S.Finite ∧
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
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
    normalizedSeries Y₁ Y₂ Y₃ c ν μ ((b₀ q.1).comp π) (b₁ q.2.1 : M₁)
      (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2.1 : M₃) (b₄ q.2.2.2.2 : M₄) N₀ s),
    Set.finite_range _, ?_⟩
  intro f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  have hf : f.domRestrict E₀ = ((f.domRestrict E₀).comp π).domRestrict E₀ := by
    ext x
    simp [π, Submodule.projectionOnto_apply_left]
  have he : normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s =
      normalizedSeries Y₁ Y₂ Y₃ c ν μ ((f.domRestrict E₀).comp π) w₁ w₂ w₃ w₄ N₀ s := by
    apply PowerSeries.ext
    intro m
    apply PowerSeries.ext
    intro n
    simp only [coeff_normalizedSeries]
    exact normalizedCoeff_congr_functional hY₁ hY₂ hY₃ (h₀ := h₀)
      hw₁ hw₂ hw₃ hw₄ hf m n
  change normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ∈ _
  rw [he]
  have hψ := b₀.sum_repr (f.domRestrict E₀)
  have hcomp : (f.domRestrict E₀).comp π =
      ∑ a, b₀.repr (f.domRestrict E₀) a • (b₀ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change normalizedLinearFunctional Y₁ Y₂ Y₃ c ν μ N₀ s w₁ w₂ w₃ w₄
    ((f.domRestrict E₀).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change normalizedLinearFirst Y₁ Y₂ Y₃ c ν μ N₀ s ((b₀ a).comp π) w₂ w₃ w₄ w₁ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change normalizedLinearSecond Y₁ Y₂ Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁) w₃ w₄ w₂ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change normalizedLinearThird Y₁ Y₂ Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁)
    (b₂ j : M₂) w₄ w₃ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₃ _ fun k => ?_
  change normalizedLinearTerminal Y₁ Y₂ Y₃ c ν μ N₀ s ((b₀ a).comp π) (b₁ i : M₁)
    (b₂ j : M₂) (b₃ k : M₃) w₄ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₄ _ fun l => ?_
  exact Submodule.subset_span ⟨(a, i, j, k, l), rfl⟩

/-- The finite base for a five-slot induction: one finite set works for every
external level in the prescribed box and all vectors at those levels. -/
theorem exists_finite_span_normalized_box
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (B₀ B₁ B₂ B₃ B₄ : ℕ) :
    ∃ S : Set (PowerSeries (PowerSeries ℂ)), S.Finite ∧
      ∀ (N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ ≤ B₀ → N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ Submodule.span ℂ S := by
  classical
  choose S hfin hS using fun q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) ×
      Fin (B₃ + 1) × Fin (B₄ + 1) =>
    exists_finite_span_normalized hY₁ hY₂ hY₃ h₀ h₁ h₂ h₃ h₄ ν μ
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  refine ⟨⋃ q, S q, Set.finite_iUnion hfin, ?_⟩
  intro N₀ N₁ N₂ N₃ N₄ b₀ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  let q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
    (⟨N₀, by omega⟩, ⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩)
  exact Submodule.span_mono (Set.subset_iUnion S q) (hS q f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄)

end VOA.Huang.HuangODEThree
