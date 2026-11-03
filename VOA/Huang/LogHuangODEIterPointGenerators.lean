import VOA.Huang.LogHuangODEIterPointFinite

/-! Explicit finite collision generators: every spanning series is an
actual genuine generalized-weight tuple of the logarithmic product.
This exposes the provenance needed for uniform collision log and weight bounds. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA VOA.C2Rigid PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : GWModule W M₁} {A₂ : GWModule W M₂} {A₃ : GWModule W M₃}
  {A₄ : GWModule W M₄} {A₅ : GWModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

theorem exists_finite_span_actual {h₁ h₂ h₃ h₄ ν : ℂ} (hY₁ : IsGradedJacobiFamily A₁ A₅ A₄ Y₁)
    (hY₂ : IsGradedJacobiFamily A₂ A₃ A₅ Y₂) (N₁ N₂ N₃ N₄ : ℕ) :
    ∃ T : Set (PowerSeries ℂ), T.Finite ∧
      (∀ g∈T,∃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃),
        w₁∈A₁.weight (h₁+N₁) ∧ w₂∈A₂.weight (h₂+N₂) ∧ w₃∈A₃.weight (h₃+N₃) ∧
        g=QT Y₁ Y₂ (h₁+h₂+h₃-h₄-2) ν f w₁ w₂ w₃ N₄ (N₁+N₂+N₃+N₄)) ∧
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃),
      w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
      QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        ∈ Submodule.span ℂ T := by
  classical
  haveI := A₁.finrank (h₁ + N₁)
  haveI := A₂.finrank (h₂ + N₂)
  haveI := A₃.finrank (h₃ + N₃)
  haveI := A₄.finrank (h₄ + N₄)
  set E₄ := A₄.weight (h₄ + N₄)
  obtain ⟨E', hE'⟩ := Submodule.exists_isCompl E₄
  set π := Submodule.projectionOnto E₄ E' hE'
  set b₁ := Module.finBasis ℂ (A₁.weight (h₁ + N₁))
  set b₂ := Module.finBasis ℂ (A₂.weight (h₂ + N₂))
  set b₃ := Module.finBasis ℂ (A₃.weight (h₃ + N₃))
  set b₄ := Module.finBasis ℂ (Module.Dual ℂ E₄)
  set c := h₁ + h₂ + h₃ - h₄ - 2
  set s := N₁ + N₂ + N₃ + N₄
  refine ⟨Set.range fun q : _ × _ × _ × _ =>
    QT Y₁ Y₂ c ν ((b₄ q.1).comp π) (b₁ q.2.1 : M₁) (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2 : M₃) N₄ s,
    Set.finite_range _, ?_,?_⟩
  · rintro g ⟨q,rfl⟩
    exact ⟨(b₄ q.1).comp π,b₁ q.2.1,b₂ q.2.2.1,b₃ q.2.2.2,
      (b₁ q.2.1).2,(b₂ q.2.2.1).2,(b₃ q.2.2.2).2,rfl⟩
  intro f w₁ w₂ w₃ hw₁ hw₂ hw₃
  -- the functional only matters on `E₄`
  have hres : f.domRestrict E₄ = ((f.domRestrict E₄).comp π).domRestrict E₄ := by
    ext x
    simp [π, Submodule.projectionOnto_apply_left]
  rw [QT_congr_f hY₁ hY₂ hw₁ hw₂ hw₃ hres]
  have hψ := b₄.sum_repr (f.domRestrict E₄)
  have hcomp : (f.domRestrict E₄).comp π
      = ∑ a, b₄.repr (f.domRestrict E₄) a • (b₄ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change QTf (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s w₁ w₂ w₃ ((f.domRestrict E₄).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change QT₁ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) w₂ w₃ w₁ ∈ _
  refine map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change QT₂ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) w₃ w₂ ∈ _
  refine map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change QT₃ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) (b₂ j : M₂) w₃ ∈ _
  refine map_mem_span_basis _ _ hw₃ _ fun k => ?_
  exact Submodule.subset_span ⟨(a, i, j, k), rfl⟩

end VOA.Huang.LogHuangODEIterPoint
