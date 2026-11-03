import VOA.Classification.COne.OrbIcoVNormalizedSpecialization

/-! Fixed independent columns remain bases of an actual finite-dimensional
image family when a proved uniform dimension bound leaves no extra columns. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open Filter Topology

theorem fixed_columns_near_basis {I J X : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace X] (x₀ : X) (cols : X → J → I → ℂ)
    (S : X → Submodule ℂ (I → ℂ))
    (hc : ContinuousAt cols x₀) (hLI : LinearIndependent ℂ (cols x₀))
    (hmem : ∀ x j, cols x j ∈ S x)
    (hbound : ∀ᶠ x in 𝓝 x₀, Module.finrank ℂ (S x) ≤ Fintype.card J) :
    ∀ᶠ x in 𝓝 x₀, LinearIndependent ℂ (cols x) ∧
      Submodule.span ℂ (Set.range (cols x)) = S x := by
  have he := hc.tendsto.eventually hLI.eventually
  filter_upwards [he, hbound] with x hi hd
  refine ⟨hi, Submodule.eq_of_le_of_finrank_le ?_ ?_⟩
  · exact Submodule.span_le.mpr (by rintro v ⟨j,rfl⟩; exact hmem x j)
  · rwa [finrank_span_eq_card hi]

theorem fixed_columns_near_basis_with_defect {I J X : Type*}
    [Fintype I] [Fintype J] [TopologicalSpace X]
    (x₀ : X) (cols : X → J → I → ℂ) (S : X → Submodule ℂ (I → ℂ))
    (defect total : ℕ) (hcard : Fintype.card J + defect = total)
    (hc : ContinuousAt cols x₀) (hLI : LinearIndependent ℂ (cols x₀))
    (hmem : ∀ x j, cols x j ∈ S x)
    (hbound : ∀ᶠ x in 𝓝 x₀, Module.finrank ℂ (S x) + defect ≤ total) :
    ∀ᶠ x in 𝓝 x₀, LinearIndependent ℂ (cols x) ∧
      Submodule.span ℂ (Set.range (cols x)) = S x := by
  apply fixed_columns_near_basis x₀ cols S hc hLI hmem
  filter_upwards [hbound] with x hx
  omega

end VOA.Classification.COne.OrbIcoV
