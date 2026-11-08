import VOA.Moonshine.MoonshineCNRelativeInduction
import Mathlib.Algebra.Exact

/-! The actual multiplication map onto the augmentation kernel.
This proves exactness at the enveloping algebra, not injectivity of multiplication. -/
noncomputable section
open scoped TensorProduct
namespace VOA.Moonshine.ConwayNorton
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]

def envelopingGeneratorMultiplication (S : Submodule ℂ g) :
    (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] S) →ₗ[ℂ] UniversalEnvelopingAlgebra ℂ g :=
  TensorProduct.lift ((LinearMap.mul ℂ (UniversalEnvelopingAlgebra ℂ g)).compl₂
    ((UniversalEnvelopingAlgebra.ι ℂ).toLinearMap.comp S.subtype))

@[simp] theorem envelopingGeneratorMultiplication_tmul (S : Submodule ℂ g)
    (a : UniversalEnvelopingAlgebra ℂ g) (u : S) :
    envelopingGeneratorMultiplication S (a ⊗ₜ[ℂ] u) =
      a * UniversalEnvelopingAlgebra.ι ℂ (u : g) := rfl

theorem envelopingGeneratorMultiplication_left (S : Submodule ℂ g)
    (a : UniversalEnvelopingAlgebra ℂ g) (t : UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] S) :
    envelopingGeneratorMultiplication S (relativeTensorLeft a t) =
      a * envelopingGeneratorMultiplication S t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b u => simp only [relativeTensorLeft_tmul,
      envelopingGeneratorMultiplication_tmul, mul_assoc]
  | add t s ht hs => simp only [map_add, ht, hs, mul_add]

theorem envelopingGeneratorMultiplication_range (S : Submodule ℂ g) :
    LinearMap.range (envelopingGeneratorMultiplication S) =
      (envelopingGeneratorLeftIdeal S).restrictScalars ℂ := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
        exact (envelopingGeneratorLeftIdeal S).smul_mem a
          (Submodule.subset_span ⟨u, u.property, rfl⟩)
    | add t s ht hs =>
        simpa only [map_add] using Submodule.add_mem _ ht hs
  · intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨u, hu, rfl⟩ := ha
        exact ⟨1 ⊗ₜ[ℂ] (⟨u, hu⟩ : S), by simp⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a b _ hb =>
        obtain ⟨t, rfl⟩ := hb
        exact ⟨relativeTensorLeft a t, envelopingGeneratorMultiplication_left S a t⟩

theorem envelopingGeneratorMultiplication_exact (S : Submodule ℂ g)
    (hS : LieSubalgebra.lieSpan ℂ g (S : Set g) = ⊤) :
    Function.Exact (envelopingGeneratorMultiplication S)
      (envelopingAugmentation (g := g)).toLinearMap := by
  apply LinearMap.exact_iff.mpr
  rw [enveloping_augmentationIdeal_eq S hS, envelopingGeneratorMultiplication_range]

theorem envelopingAugmentation_surjective :
    Function.Surjective (envelopingAugmentation (g := g)) :=
  fun c => ⟨algebraMap ℂ _ c, by simp⟩

/-- The canonical map from the tensor algebra on a Lie-generating subspace. -/
def tensorGeneratorToEnveloping (S : Submodule ℂ g) :
    TensorAlgebra ℂ S →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ g :=
  TensorAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).toLinearMap.comp S.subtype)

@[simp] theorem tensorGeneratorToEnveloping_generator (S : Submodule ℂ g) (u : S) :
    tensorGeneratorToEnveloping S (TensorAlgebra.ι ℂ u) =
      UniversalEnvelopingAlgebra.ι ℂ (u : g) :=
  TensorAlgebra.lift_ι_apply _ _

theorem enveloping_lieSpan_mem_tensorRange (S : Submodule ℂ g)
    {x : g} (hx : x ∈ LieSubalgebra.lieSpan ℂ g (S : Set g)) :
    UniversalEnvelopingAlgebra.ι ℂ x ∈ (tensorGeneratorToEnveloping S).range := by
  let R := (tensorGeneratorToEnveloping S).range
  change UniversalEnvelopingAlgebra.ι ℂ x ∈ R
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
      exact ⟨TensorAlgebra.ι ℂ (⟨x, hx⟩ : S), tensorGeneratorToEnveloping_generator S _⟩
  | zero => simpa only [map_zero] using R.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using R.add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using R.smul_mem hx c
  | lie x y _ _ hx hy =>
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      exact R.sub_mem (R.mul_mem hx hy) (R.mul_mem hy hx)

theorem tensorGeneratorToEnveloping_surjective (S : Submodule ℂ g)
    (hS : LieSubalgebra.lieSpan ℂ g (S : Set g) = ⊤) :
    Function.Surjective (tensorGeneratorToEnveloping S) := by
  intro a
  change a ∈ (tensorGeneratorToEnveloping S).range
  induction a using envelopingAlgebra_induction with
  | hscalar c => exact Subalgebra.algebraMap_mem _ c
  | hlie x =>
      apply enveloping_lieSpan_mem_tensorRange S
      rw [hS]
      trivial
  | hmul a b ha hb => exact Subalgebra.mul_mem _ ha hb
  | hadd a b ha hb => exact Subalgebra.add_mem _ ha hb

namespace BorcherdsData
variable (D : BorcherdsData g)

/-- Range calculation for the length-one resolution, in the PBW source coordinates. -/
theorem positiveGeneratorMultiplication_exact (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    Function.Exact (envelopingGeneratorMultiplication (D.positiveGeneratorSpace e))
      (envelopingAugmentation (g := D.positivePart)).toLinearMap :=
  envelopingGeneratorMultiplication_exact _ (D.positiveGeneratorSpace_lieSpan e f he hf hef)

/-- The surjectivity half of the tensor-algebra description of the enveloping algebra; no
injectivity or freeness conclusion is asserted. -/
theorem positiveTensorGeneratorToEnveloping_surjective (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    Function.Surjective (tensorGeneratorToEnveloping (D.positiveGeneratorSpace e)) :=
  tensorGeneratorToEnveloping_surjective _ (D.positiveGeneratorSpace_lieSpan e f he hf hef)

end BorcherdsData
end VOA.Moonshine.ConwayNorton

