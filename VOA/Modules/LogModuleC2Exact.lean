import VOA.Huang.BuhlSpanningMain
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Right exactness of the actual module C₂ quotient

Actual weak-module homomorphisms descend to their C₂ quotients. A surjection
maps C₂ onto C₂, and an actual short exact sequence stays right exact after
quotienting. Thus module C₂-cofiniteness is closed under extensions, without
an ordinary or semisimple L(0) hypothesis on the middle module.
-/
namespace VOA.LogTensor.ModuleC2
open VOA.Huang.FusionC2
universe u
variable {V X Y Z : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z] {W : VertexOperatorAlgebra V}
variable {A : WeakModule W X} {B : WeakModule W Y} {C : WeakModule W Z}

theorem C2_hom (f : A.Hom B) : C2M A ≤ (C2M B).comap f.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,m,rfl⟩
  change f.toLinearMap (A.act a (-2) m) ∈ C2M B
  rw [f.map_act]
  exact Submodule.subset_span ⟨a,f.toLinearMap m,rfl⟩

theorem map_C2_of_surjective (f : A.Hom B) (hf : Function.Surjective f.toLinearMap) :
    (C2M A).map f.toLinearMap = C2M B := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact C2_hom f hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,m,rfl⟩
    obtain ⟨x,rfl⟩ := hf m
    exact ⟨A.act a (-2) x,Submodule.subset_span ⟨a,x,rfl⟩,f.map_act a (-2) x⟩

/-- The genuine induced map on actual module C₂ quotients. -/
def quotientMap (f : A.Hom B) : (X ⧸ C2M A) →ₗ[ℂ] (Y ⧸ C2M B) :=
  (C2M A).mapQ (C2M B) f.toLinearMap (C2_hom f)

theorem quotientMap_mk (f : A.Hom B) (x : X) :
    quotientMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.toLinearMap x) := rfl

theorem quotientMap_surjective (f : A.Hom B) (hf : Function.Surjective f.toLinearMap) :
    Function.Surjective (quotientMap f) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x,rfl⟩

/-- Right exactness, using the actual weak action in every quotient. -/
theorem quotient_exact (f : A.Hom B) (g : B.Hom C)
    (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (hg : Function.Surjective g.toLinearMap) :
    LinearMap.range (quotientMap f) = LinearMap.ker (quotientMap g) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (g.toLinearMap (f.toLinearMap x)) = 0
      have hz : g.toLinearMap (f.toLinearMap x) = 0 :=
        (LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f.toLinearMap x))
      rw [hz,Submodule.Quotient.mk_zero]
  · intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have hgy : g.toLinearMap y ∈ C2M C :=
        (Submodule.Quotient.mk_eq_zero _).mp hy
      rw [← map_C2_of_surjective g hg] at hgy
      obtain ⟨z,hz,he⟩ := hgy
      have hyz : y-z ∈ LinearMap.range f.toLinearMap := by
        rw [hex,LinearMap.mem_ker,map_sub,he,sub_self]
      obtain ⟨x,hx⟩ := hyz
      refine ⟨Submodule.Quotient.mk x,?_⟩
      rw [quotientMap_mk,hx,Submodule.Quotient.mk_sub,
        (Submodule.Quotient.mk_eq_zero _).mpr hz,sub_zero]

/-- Module C₂-cofiniteness is closed under actual weak-module extensions. -/
theorem cofinite_of_exact (f : A.Hom B) (g : B.Hom C)
    (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (hg : Function.Surjective g.toLinearMap)
    (hA : ModuleC2Cofinite A) (hC : ModuleC2Cofinite C) : ModuleC2Cofinite B := by
  haveI : FiniteDimensional ℂ (X ⧸ C2M A) := hA
  haveI : FiniteDimensional ℂ (Z ⧸ C2M C) := hC
  haveI : FiniteDimensional ℂ (LinearMap.ker (quotientMap g)) := by
    rw [← quotient_exact f g hex hg]
    infer_instance
  haveI : FiniteDimensional ℂ ((Y ⧸ C2M B) ⧸ LinearMap.ker (quotientMap g)) :=
    Module.Finite.of_surjective (quotientMap g).quotKerEquivRange.symm.toLinearMap
      (quotientMap g).quotKerEquivRange.symm.surjective
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (quotientMap g))


/-- A genuine weak-module quotient of a C₂-cofinite module is C₂-cofinite. -/
theorem cofinite_of_surjective (f : A.Hom B) (hf : Function.Surjective f.toLinearMap)
    (hA : ModuleC2Cofinite A) : ModuleC2Cofinite B := by
  haveI : FiniteDimensional ℂ (X ⧸ C2M A) := hA
  exact Module.Finite.of_surjective (quotientMap f) (quotientMap_surjective f hf)

end VOA.LogTensor.ModuleC2
