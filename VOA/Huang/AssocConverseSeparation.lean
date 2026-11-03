import VOA.Huang.AssocConverseFormal
import VOA.Huang.AssocConverseRepresentatives

/-! # Remaining analytic and cross-channel separation obligations

Within one irreducible intermediate module the coefficient tensor map is
proved injective. The two residuals here separate the outstanding issues:
uniqueness of the convergent expansion, and independence across inequivalent
intermediate modules. Neither is asserted without a hypothesis.

In particular, irredundancy does not say that lowest weights are distinct
modulo integers. Separating equal-weight channels needs the full mode action.
-/

namespace VOA.Huang.AssocConverse
open VOA VOA.Huang.AssocTarget
open scoped BigOperators

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {ι : Type v} [Fintype ι]

noncomputable def formalProductFamilyMap (P₁ P₂ P₃ P₄ : LWModule W)
    (R : ι → LWModule W) :
    (∀ j, productTensor P₁ P₂ P₃ P₄ (R j)) →ₗ[ℂ]
      (FormalProductData P₁ P₂ P₃ → P₄.carrier) :=
  sumFamily fun j => formalProductTensorMap P₁ P₂ P₃ P₄ (R j)

/-- Analytic vanishing implies vanishing of the summed formal coefficients.
This only asks for uniqueness of the expansion, including coincident exponents;
it does not ask that the individual channels vanish. The intended hypotheses
are strong rationality and a finite family of lowest-weight modules. -/
def ProductCoefficientUniqueness (hV : StronglyRational W)
    (R : ι → LWModule W) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW),
    LinearMap.ker (productFamilyMap hV i₁ i₂ i₃ i₄ R) ≤
      LinearMap.ker (formalProductFamilyMap P₁ P₂ P₃ P₄ R)

/-- Independence of the images of the formal coefficient maps. This is a
purely algebraic target for an irredundant family of irreducible modules;
no distinct-weight or analytic-convergence assumption is built in. -/
def FormalChannelSeparation (R : ι → LWModule W) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W),
    P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → P₃.IsIrreducibleLW →
    P₄.IsIrreducibleLW →
    ∀ t : ∀ j, productTensor P₁ P₂ P₃ P₄ (R j),
      formalProductFamilyMap P₁ P₂ P₃ P₄ R t = 0 →
      ∀ j, formalProductTensorMap P₁ P₂ P₃ P₄ (R j) (t j) = 0

/-- The completed single-channel theorem leaves exactly the two displayed
separation obligations for the original analytic faithfulness target. -/
theorem productChannelFaithful_of_coefficient_separation (hV : StronglyRational W)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcoeff : ProductCoefficientUniqueness hV R)
    (hsep : FormalChannelSeparation R) : ProductChannelFaithful hV R := by
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro t ht
  have hf := hcoeff P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ ht
  have hs := hsep P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ t hf
  funext j
  apply formalProductTensorMap_injective (iR j)
  simpa only [map_zero] using hs j

theorem associativityBoth_of_coefficient_separation (hV : StronglyRational W)
    (R : ι → LWModule W) (hR : CompleteIrredundantFamily R)
    (hcoeff : ProductCoefficientUniqueness hV R)
    (hsep : FormalChannelSeparation R) : AssociativityBoth W :=
  associativityBoth_of_stronglyRational_faithful hV R hR.1 hR.2.1
    (productChannelFaithful_of_coefficient_separation hV R hR.1 hcoeff hsep)

/-- PBW supplies the finite family; the analytic and cross-channel obligations
remain explicit. This is not the unconditional converse theorem. -/
theorem associativityBoth_pbw_of_coefficient_separation (hV : StronglyRational W)
    (hsep : ∀ (n : ℕ) (R : Fin n → LWModule W), CompleteIrredundantFamily R →
      ProductCoefficientUniqueness hV R ∧ FormalChannelSeparation R) :
    AssociativityBoth W := by
  obtain ⟨n, R, hR⟩ := exists_completeIrredundantFamily_pbw hV
  exact associativityBoth_of_coefficient_separation hV R hR
    (hsep n R hR).1 (hsep n R hR).2

end VOA.Huang.AssocConverse
