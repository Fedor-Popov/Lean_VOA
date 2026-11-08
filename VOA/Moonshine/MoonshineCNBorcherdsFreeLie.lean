import VOA.Moonshine.MoonshineCNBorcherdsTensorEnveloping
import Mathlib.Algebra.Lie.Free
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-! Freeness of the positive part on U.

For a Lie algebra `L`, a Lie-generating subspace `S` with a basis `b`, and injective
`T(S) → U(L)`, the Lie map from the free Lie algebra on the basis index is bijective: its
composite with `L → U(L)` is `U(free) ≅ FreeAlgebra ≅ T(S) → U(L)` after the embedding of the
free Lie algebra in its enveloping algebra.  For Borcherds data this says `𝔲⁺` is free on `U`,
compatibly with every symmetry of the data. -/

noncomputable section
open Module
namespace VOA.Moonshine.ConwayNorton

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] (S : Submodule ℂ L)
variable {ι : Type*} (b : Basis ι ℂ S)

/-- The Lie map from the free Lie algebra on a basis of `S`, sending generators to the basis. -/
def freeLieGeneratorMap : FreeLieAlgebra ℂ ι →ₗ⁅ℂ⁆ L :=
  FreeLieAlgebra.lift ℂ (fun i => (b i : L))

@[simp] theorem freeLieGeneratorMap_of (i : ι) :
    freeLieGeneratorMap S b (FreeLieAlgebra.of ℂ i) = b i :=
  FreeLieAlgebra.lift_of_apply _ _

/-- The basis-free linear inclusion of `S` into the free Lie algebra on its basis. -/
def freeLieGeneratorLinear : S →ₗ[ℂ] FreeLieAlgebra ℂ ι :=
  b.constr ℂ (FreeLieAlgebra.of ℂ)

theorem freeLieGeneratorMap_linear (u : S) :
    freeLieGeneratorMap S b (freeLieGeneratorLinear S b u) = u := by
  have h : (freeLieGeneratorMap S b).toLinearMap.comp (freeLieGeneratorLinear S b) =
      S.subtype := by
    apply b.ext
    intro i
    simp [freeLieGeneratorLinear]
  exact LinearMap.congr_fun h u

/-- If `S` generates `L`, the free Lie map is surjective. -/
theorem freeLieGeneratorMap_surjective (hS : LieSubalgebra.lieSpan ℂ L (S : Set L) = ⊤) :
    Function.Surjective (freeLieGeneratorMap S b) := by
  intro x
  have hle : LieSubalgebra.lieSpan ℂ L (S : Set L) ≤ (freeLieGeneratorMap S b).range := by
    apply LieSubalgebra.lieSpan_le.mpr
    intro u hu
    exact ⟨freeLieGeneratorLinear S b ⟨u, hu⟩, freeLieGeneratorMap_linear S b ⟨u, hu⟩⟩
  rw [hS] at hle
  exact hle (LieSubalgebra.mem_top x)

/-- If `T(S) → U(L)` is injective, the free Lie map is injective. -/
theorem freeLieGeneratorMap_injective
    (hτ : Function.Injective (tensorGeneratorToEnveloping S)) :
    Function.Injective (freeLieGeneratorMap S b) := by
  let Ψ : UniversalEnvelopingAlgebra ℂ (FreeLieAlgebra ℂ ι) →ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ L :=
    (tensorGeneratorToEnveloping S).comp ((TensorAlgebra.equivFreeAlgebra b).symm.toAlgHom.comp
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℂ ι).toAlgHom)
  have hΨ : Function.Injective Ψ :=
    hτ.comp ((TensorAlgebra.equivFreeAlgebra b).symm.injective.comp
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℂ ι).injective)
  have hcomp : (UniversalEnvelopingAlgebra.ι ℂ).comp (freeLieGeneratorMap S b) =
      Ψ.toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [Ψ]
  intro x y hxy
  apply envelopingEmbedding_injective (FreeLieAlgebra ℂ ι)
  apply hΨ
  have hx := LieHom.congr_fun hcomp x
  have hy := LieHom.congr_fun hcomp y
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom] at hx hy
  rw [← hx, ← hy, hxy]

/-- A Lie map preserving `S` lifts to the free Lie algebra on the basis. -/
def freeLieInducedMap (φ : L →ₗ⁅ℂ⁆ L) (hφ : ∀ u ∈ S, φ u ∈ S) :
    FreeLieAlgebra ℂ ι →ₗ⁅ℂ⁆ FreeLieAlgebra ℂ ι :=
  FreeLieAlgebra.lift ℂ (fun i =>
    freeLieGeneratorLinear S b (φ.toLinearMap.restrict (p := S) (q := S) hφ (b i)))

/-- The free Lie map intertwines the lifted map with the original one. -/
theorem freeLieGeneratorMap_natural (φ : L →ₗ⁅ℂ⁆ L) (hφ : ∀ u ∈ S, φ u ∈ S)
    (x : FreeLieAlgebra ℂ ι) :
    freeLieGeneratorMap S b (freeLieInducedMap S b φ hφ x) = φ (freeLieGeneratorMap S b x) := by
  have h : (freeLieGeneratorMap S b).comp (freeLieInducedMap S b φ hφ) =
      φ.comp (freeLieGeneratorMap S b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp only [LieHom.coe_comp, Function.comp_apply, freeLieInducedMap,
      FreeLieAlgebra.lift_of_apply, freeLieGeneratorMap_linear, freeLieGeneratorMap_of]
    rfl
  exact LieHom.congr_fun h x

namespace BorcherdsData
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)
variable (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
  (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)

/-- A chosen basis of the generating space U. -/
def positiveGeneratorBasis :
    Basis (Basis.ofVectorSpaceIndex ℂ (D.positiveGeneratorSpace e)) ℂ
      (D.positiveGeneratorSpace e) :=
  Basis.ofVectorSpace ℂ (D.positiveGeneratorSpace e)

include he hf hef in
/-- The positive part is the free Lie algebra on U. -/
theorem positivePartFreeLie_bijective :
    Function.Bijective (freeLieGeneratorMap (D.positiveGeneratorSpace e)
      (D.positiveGeneratorBasis e)) :=
  ⟨freeLieGeneratorMap_injective _ _
      (D.positiveTensorGeneratorToEnveloping_bijective e f he hf hef).1,
    freeLieGeneratorMap_surjective _ _ (D.positiveGeneratorSpace_lieSpan e f he hf hef)⟩

/-- The Lie algebra isomorphism from the free Lie algebra on a basis of U onto `𝔲⁺`. -/
def positivePartFreeLieEquiv :
    FreeLieAlgebra ℂ (Basis.ofVectorSpaceIndex ℂ (D.positiveGeneratorSpace e)) ≃ₗ⁅ℂ⁆
      D.positivePart :=
  LieEquiv.ofBijective _ (D.positivePartFreeLie_bijective e f he hf hef)

/-- The isomorphism with the free Lie algebra intertwines every symmetry of the data. -/
theorem positivePartFreeLieEquiv_equivariant {G : Type*} [Group G] (A : D.GAction G) (σ : G)
    (x : FreeLieAlgebra ℂ (Basis.ofVectorSpaceIndex ℂ (D.positiveGeneratorSpace e))) :
    D.positivePartFreeLieEquiv e f he hf hef
        (freeLieInducedMap _ (D.positiveGeneratorBasis e) (D.positivePartAction A σ)
          (D.positiveGenerator_action_mem e he A σ) x) =
      D.positivePartAction A σ (D.positivePartFreeLieEquiv e f he hf hef x) :=
  freeLieGeneratorMap_natural _ _ _ _ x

end BorcherdsData
end VOA.Moonshine.ConwayNorton
