import VOA.Classification.COne.McRaeM2LogMonoidal

/-! # The logarithmic braiding isomorphism and its naturality

The braiding of the logarithmic tensor category is the actual swap map induced
by HLZ's skew-symmetry `Ω₀(𝒴)(w₂, x)w₁ = e^{xL(−1)}𝒴(w₁, e^{πi}x)w₂` on the
canonical intertwiner (`tensorBraid … 0`), with inverse induced by `Ω₋₁`. Both
swaps (`r = 0` and `r = -1`) are natural in both factors; this is formal from
the universal property and the naturality of `Ω` in its source and target. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ X₁ X₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
  (P₁ : LogVModule W X₁) (P₂ : LogVModule W X₂)
  (p₁ : FinGen P₁.toWeakModule) (p₂ : FinGen P₂.toWeakModule)

/-- The actual tensor swap is natural in both factors, for every branch `r`. -/
theorem tensorBraid_natural (f : N₁.toWeakModule.Hom P₁.toWeakModule)
    (g : N₂.toWeakModule.Hom P₂.toWeakModule) (r : ℤ) :
    (homComp (tensorBraid hC2 P₁ P₂ p₁ p₂ r)
      (tensorMap hC2 N₁ N₂ h₁ h₂ P₁ P₂ p₁ p₂ f g)).toLinearMap =
    (homComp (tensorMap hC2 N₂ N₁ h₂ h₁ P₂ P₁ p₂ p₁ g f)
      (tensorBraid hC2 N₁ N₂ h₁ h₂ r)).toLinearMap := by
  apply tensor_morphism_ext hC2 N₁ N₂ h₁ h₂ (tensorModule hC2 P₂ P₁ p₂ p₁)
  rw [postcompose_homComp', postcompose_homComp', tensorMap_intertwiner,
    postcompose_precompose', tensorBraid_intertwiner, tensorBraid_intertwiner]
  have h1 := omega_postcompose (tensorIntertwiner hC2 N₂ N₁ h₂ h₁)
    (tensorMap hC2 N₂ N₁ h₂ h₁ P₂ P₁ p₂ p₁ g f) r
  rw [tensorMap_intertwiner] at h1
  rw [← h1]
  exact (omega_precompose (tensorIntertwiner hC2 P₂ P₁ p₂ p₁) g f r).symm

end VOA.C2Rigid.LocalInjective

namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The categorical swap isomorphisms are natural in both factors. -/
theorem swapIso_naturality {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) (g : N₂ ⟶ P₂)
    (r : ℤ) :
    tensorMorphism hC2 f g ≫ (swapIso hC2 P₁ P₂ r).hom =
      (swapIso hC2 N₁ N₂ r).hom ≫ tensorMorphism hC2 g f := by
  apply hom_ext
  intro q
  exact congrArg (fun F => F q) (tensorBraid_natural hC2 N₁.act N₂.act
    N₁.finiteGeneration N₂.finiteGeneration P₁.act P₂.act P₁.finiteGeneration
    P₂.finiteGeneration (toWeakHom f) (toWeakHom g) r)

/-- **The logarithmic braiding** `c_{N,P} : N ⊠ P ≅ P ⊠ N`, induced by `Ω₀`,
with inverse induced by `Ω₋₁`. -/
abbrev braidingIso (N P : LogModuleCat W) : tensorObject hC2 N P ≅ tensorObject hC2 P N :=
  swapIso hC2 N P 0

/-- The braiding is natural in both factors. -/
theorem braidingIso_naturality {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) (g : N₂ ⟶ P₂) :
    tensorMorphism hC2 f g ≫ (braidingIso hC2 P₁ P₂).hom =
      (braidingIso hC2 N₁ N₂).hom ≫ tensorMorphism hC2 g f :=
  swapIso_naturality hC2 f g 0

end VOA.LogTensor.LogModuleCat
