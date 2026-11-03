import VOA.Huang.HexagonCloseTranslate

/-! # Hexagon closure: headlines

For a strongly rational `W` and any choice of fusion products `F`, the hexagon input
`BraidRibbon.HexagonInput F` (both analytic hexagons for FHL's `Ω₀` and `Ω₋₁`, equivalent to the
two forward hexagons of the braiding) is reduced to **one** analytic statement about a **single**
product of two intertwining operators:

`ProductHalfPlaneContinuation F` — every product four-point function `ζ ↦ Σ_w c_w ζ^{δ-α-w}`
(convergent on `|ζ| > 1`) continues analytically to each open half plane `±Im ζ > 0`.

This is TRUE (the product satisfies a Fuchsian system whose only singular points are
`ζ ∈ {0, 1, ∞}`, none of which lies in an open half plane: Huang 2005, convergence and extension
property).  The braiding, the associator, the hypotheses `It K = Pr G`, `It M = Pr(G ∘ (1 × c))`
and the inner braiding of a product are all handled by proved identities
(`HexagonCloseProduct`, `HexagonCloseIterate`, `HexagonCloseFrame`, `HexagonCloseTranslate`,
`HexagonCloseGlue`).  The only use of the half-plane continuation is to cross the equilateral
configuration `r = e^{∓2πi/3}` (hexagon coordinate), where no iterate or product expansion
converges.

* `hexagonContinuationInput_of_halfPlane`, `hexagonInput_of_halfPlane`;
* `braidedCategory_of_halfPlane : … → BraidedCategory (Ordinary W)`.

`ProductHalfPlaneContinuation F` itself is proved in `HexagonCloseResidual`
(`productHalfPlaneContinuation_pbw`), giving the unconditional `hexagonInput_pbw` and
`braidedCategory_stronglyRational_pbw`.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open Complex
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

variable (F : FusionChoice W)

theorem kap_neg_one : kap (-1) = -(↑Real.pi * Complex.I) := by
  simp [kap]

theorem kap_one : kap 1 = ↑Real.pi * Complex.I := by
  simp [kap]

theorem phase_upper_kap (n : ℂ) : Phase.upper.c n = Complex.exp (kap (-1) * (n + 1)) := by
  rw [kap_neg_one]; exact phase_upper_exp n

theorem phase_upper_inv_kap (n : ℂ) :
    Phase.upper.inv.c n = Complex.exp (kap 1 * (n + 1)) := by
  rw [kap_one]; exact phase_upper_inv_exp n

variable (hV : StronglyRational W)
include hV

/-- **The hexagon continuation identity from the half-plane continuation of products.** -/
theorem hexagonContinuationInput_of_halfPlane (hP : ProductHalfPlaneContinuation F) :
    HexagonContinuationInput F := by
  have h1 := hexagonContinuation_of_glue F hV Phase.upper (s := -1) (Or.inr rfl) hP
    (innerBraidTranslation_of_phase F hV Phase.upper (Or.inr rfl) phase_upper_kap)
  have h2 := hexagonContinuation_of_glue F hV Phase.upper.inv (s := 1) (Or.inl rfl) hP
    (innerBraidTranslation_of_phase F hV Phase.upper.inv (Or.inl rfl) phase_upper_inv_kap)
  rw [kap_neg_one] at h1
  rw [kap_one] at h2
  exact ⟨h1, h2⟩

/-- **The hexagon input from the half-plane continuation of products.** -/
theorem hexagonInput_of_halfPlane (hP : ProductHalfPlaneContinuation F) : HexagonInput F :=
  hexagonInput_of_continuation F hV (hexagonContinuationInput_of_halfPlane F hV hP)

/-- **The braided monoidal category of ordinary modules** of a strongly rational VOA
(on `monoidalCategoryOfStronglyRational_pbw F hV`, braiding FHL's `Ω₀`), conditional only on the
half-plane continuation of single products. -/
abbrev braidedCategory_of_halfPlane (hP : ProductHalfPlaneContinuation F) :
    @BraidedCategory (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV) :=
  braidedCategoryOfStronglyRational_pbw F hV (hexagonInput_of_halfPlane F hV hP)

theorem braidedCategory_of_halfPlane_braiding (hP : ProductHalfPlaneContinuation F)
    (X Y : Ordinary W) :
    @BraidedCategory.braiding (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV)
      (braidedCategory_of_halfPlane F hV hP) X Y = braiding F X Y := rfl

end HexagonClose
end VOA.Huang.TensorCat
