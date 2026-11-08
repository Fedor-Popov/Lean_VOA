import VOA.Foundations.PBWTheorem.Induced
import VOA.Moonshine.MoonshineCNBorcherdsAugmentation

/-! The induced quotient, its enveloping action, and the relative PBW coordinate map. -/

noncomputable section
open scoped TensorProduct
namespace VOA.Moonshine.ConwayNorton

open Module Finsupp
variable {g U : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup U] [Module ℂ U]
variable (p : LieSubalgebra ℂ g) (ρ : p →ₗ⁅ℂ⁆ End ℂ U)

abbrev relativeInducedSpace :=
  (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] U) ⧸ PBWTheorem.balancing p ρ

def relativeTensorLeft (a : UniversalEnvelopingAlgebra ℂ g) :
    End ℂ (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] U) :=
  (LinearMap.mulLeft ℂ a).rTensor U

theorem relativeTensorLeft_tmul (a b : UniversalEnvelopingAlgebra ℂ g) (u : U) :
    relativeTensorLeft a (b ⊗ₜ[ℂ] u) = (a * b) ⊗ₜ[ℂ] u := rfl

theorem relativeBalancing_left_stable (a : UniversalEnvelopingAlgebra ℂ g) :
    PBWTheorem.balancing p ρ ≤ (PBWTheorem.balancing p ρ).comap (relativeTensorLeft a) := by
  intro t ht
  change relativeTensorLeft a t ∈ PBWTheorem.balancing p ρ
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨b, x, u, rfl⟩ := ht
      rw [map_sub, relativeTensorLeft_tmul, relativeTensorLeft_tmul, ← mul_assoc]
      exact Submodule.subset_span ⟨a * b, x, u, rfl⟩
  | zero => simpa only [map_zero] using (PBWTheorem.balancing p ρ).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c t _ ht => simpa only [map_smul] using Submodule.smul_mem _ c ht

def relativeInducedLeft (a : UniversalEnvelopingAlgebra ℂ g) : End ℂ (relativeInducedSpace p ρ) :=
  (PBWTheorem.balancing p ρ).mapQ _ (relativeTensorLeft a) (relativeBalancing_left_stable p ρ a)

theorem relativeInducedLeft_mk (a : UniversalEnvelopingAlgebra ℂ g)
    (t : UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] U) :
    relativeInducedLeft p ρ a (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (relativeTensorLeft a t) := rfl

theorem relativeInducedLeft_tmul (a b : UniversalEnvelopingAlgebra ℂ g) (u : U) :
    relativeInducedLeft p ρ a (Submodule.Quotient.mk (b ⊗ₜ[ℂ] u)) =
      Submodule.Quotient.mk ((a * b) ⊗ₜ[ℂ] u) := rfl

theorem relativeInduced_ext {f h : End ℂ (relativeInducedSpace p ρ)}
    (heq : ∀ (a : UniversalEnvelopingAlgebra ℂ g) (u : U),
      f (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) = h (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u))) : f = h := by
  apply LinearMap.ext
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => exact heq a u
  | add t s ht hs => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) ht hs

/-- Left multiplication descends to the balanced quotient. -/
def relativeInducedAlgebra :
    UniversalEnvelopingAlgebra ℂ g →ₐ[ℂ] End ℂ (relativeInducedSpace p ρ) where
  toFun := relativeInducedLeft p ρ
  map_one' := by
    apply relativeInduced_ext p ρ
    intro a u
    simp [relativeInducedLeft_tmul]
  map_mul' a b := by
    apply relativeInduced_ext p ρ
    intro c u
    simp only [Module.End.mul_apply, relativeInducedLeft_tmul, mul_assoc]
  map_zero' := by
    apply relativeInduced_ext p ρ
    intro a u
    simp [relativeInducedLeft_tmul]
  map_add' a b := by
    apply relativeInduced_ext p ρ
    intro c u
    simp [relativeInducedLeft_tmul, add_mul, TensorProduct.add_tmul]
  commutes' c := by
    apply relativeInduced_ext p ρ
    intro a u
    simp only [relativeInducedLeft_tmul, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_apply, Module.End.one_apply]
    rw [← TensorProduct.smul_tmul', Submodule.Quotient.mk_smul]

def relativeInducedRep : g →ₗ⁅ℂ⁆ End ℂ (relativeInducedSpace p ρ) :=
  (relativeInducedAlgebra p ρ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)

theorem relativeInduced_bottom_relation (x : p) (u : U) :
    (Submodule.Quotient.mk (UniversalEnvelopingAlgebra.ι ℂ (x : g) ⊗ₜ[ℂ] u) :
      relativeInducedSpace p ρ) = PBWTheorem.bottom p ρ (ρ x u) := by
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.subset_span ⟨1, x, u, by simp⟩

theorem relativeInducedRep_bottom (x : p) (u : U) :
    relativeInducedRep p ρ (x : g) (PBWTheorem.bottom p ρ u) =
      PBWTheorem.bottom p ρ (ρ x u) := by
  change Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ (x : g) * 1) ⊗ₜ[ℂ] u) = _
  rw [mul_one]
  exact relativeInduced_bottom_relation p ρ x u

variable {A : Type*} [LinearOrder A] {c : Submodule ℂ g}
variable (hc : IsCompl p.toSubmodule c) (bc : Basis A ℂ c)

/-- Evaluation in the proved relative PBW representation. -/
def relativePBWEvaluation :
    (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] U) →ₗ[ℂ] (Multiset A →₀ U) :=
  TensorProduct.lift (LinearMap.lcomp ℂ _ (Finsupp.lsingle 0) ∘ₗ
    (UniversalEnvelopingAlgebra.lift ℂ (PBWTheorem.rep p hc bc ρ)).toLinearMap)

/-- PBW coordinates on the genuine balanced quotient. -/
def relativePBWCoordinates : relativeInducedSpace p ρ →ₗ[ℂ] (Multiset A →₀ U) :=
  (PBWTheorem.balancing p ρ).liftQ (relativePBWEvaluation p ρ hc bc) (by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, u, rfl⟩
    change relativePBWEvaluation p ρ hc bc _ = 0
    simp only [map_sub, relativePBWEvaluation, TensorProduct.lift.tmul,
      LinearMap.comp_apply, LinearMap.lcomp_apply, AlgHom.toLinearMap_apply,
      map_mul, Module.End.mul_apply, UniversalEnvelopingAlgebra.lift_ι_apply,
      Finsupp.lsingle_apply]
    rw [PBWTheorem.rep_p_zero, sub_self])

theorem relativePBWCoordinates_mk (a : UniversalEnvelopingAlgebra ℂ g) (u : U) :
    relativePBWCoordinates p ρ hc bc (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) =
      UniversalEnvelopingAlgebra.lift ℂ (PBWTheorem.rep p hc bc ρ) a (single 0 u) := rfl

theorem relativePBWCoordinates_bottom (u : U) :
    relativePBWCoordinates p ρ hc bc (PBWTheorem.bottom p ρ u) = single 0 u := by
  change relativePBWCoordinates p ρ hc bc (Submodule.Quotient.mk (1 ⊗ₜ[ℂ] u)) = _
  rw [relativePBWCoordinates_mk, map_one, Module.End.one_apply]

theorem relativePBWCoordinates_left (z : g) (q : relativeInducedSpace p ρ) :
    relativePBWCoordinates p ρ hc bc (relativeInducedRep p ρ z q) =
      PBWTheorem.rep p hc bc ρ z (relativePBWCoordinates p ρ hc bc q) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      change relativePBWCoordinates p ρ hc bc
        (Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ z * a) ⊗ₜ[ℂ] u)) = _
      rw [relativePBWCoordinates_mk, relativePBWCoordinates_mk, map_mul,
        Module.End.mul_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
  | add t s ht hs => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) ht hs

end VOA.Moonshine.ConwayNorton
