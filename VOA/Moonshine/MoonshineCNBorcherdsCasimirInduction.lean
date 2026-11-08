import VOA.Moonshine.MoonshineCNBorcherdsCasimirCentral
import VOA.Moonshine.MoonshineCNRelativeInduction

/-! Propagation of Casimir eigenvalues through enveloping actions and induced modules.
An admissible grading on the induced quotient is an explicit input here. -/
noncomputable section
open scoped TensorProduct
namespace VOA.Moonshine.ConwayNorton
open Module
variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

theorem casimirOperator_commutes_enveloping
    (a : UniversalEnvelopingAlgebra ℂ g) (v : M) :
    A.casimirOperator (UniversalEnvelopingAlgebra.lift ℂ ρ a v) =
      UniversalEnvelopingAlgebra.lift ℂ ρ a (A.casimirOperator v) := by
  induction a using envelopingAlgebra_induction generalizing v with
  | hscalar c =>
      simp only [Algebra.algebraMap_eq_smul_one,
        LinearMap.smul_apply, Module.End.one_apply, map_smul, map_one]
  | hlie x =>
      simpa only [UniversalEnvelopingAlgebra.lift_ι_apply] using
        A.casimirOperator_commutes x v
  | hmul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

theorem casimirOperator_enveloping_eigenvector (c : ℂ) {v : M}
    (hv : A.casimirOperator v = c • v) (a : UniversalEnvelopingAlgebra ℂ g) :
    A.casimirOperator (UniversalEnvelopingAlgebra.lift ℂ ρ a v) =
      c • UniversalEnvelopingAlgebra.lift ℂ ρ a v := by
  rw [A.casimirOperator_commutes_enveloping, hv, map_smul]

theorem casimirOperator_simple_lowest_enveloping {α : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace α) (hα : borcherdsSimpleRoot α)
    (hlow : ∀ β, borcherdsPositiveRoot β → ∀ x ∈ D.weightSpace (-β), ρ x v = 0)
    (a : UniversalEnvelopingAlgebra ℂ g) :
    A.casimirOperator (UniversalEnvelopingAlgebra.lift ℂ ρ a v) = 0 := by
  have hfirst : α.1 = 1 := by
    rcases hα with rfl | ⟨j, _, rfl⟩ <;> rfl
  have he : A.casimirOperator v = (0 : ℂ) • v := by
    rw [A.casimirOperator_lowest_vector hv hlow, borcherdsCasimirScalar_eq, hfirst]
    simp
  simpa only [zero_smul] using A.casimirOperator_enveloping_eigenvector 0 he a

end BorcherdsAdmissible

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable (p : LieSubalgebra ℂ g) (σ : p →ₗ⁅ℂ⁆ End ℂ W)

theorem relativeInducedAlgebra_eq_lift :
    relativeInducedAlgebra p σ =
      UniversalEnvelopingAlgebra.lift ℂ (relativeInducedRep p σ) := by
  apply (UniversalEnvelopingAlgebra.lift_unique ℂ (relativeInducedRep p σ) _).mp
  rfl

/-- Scalar action on the bottom of an admissibly graded induced module propagates
to the whole actual balanced quotient. The grading is not constructed by this theorem. -/
theorem inducedCasimir_scalar_of_bottom (D : BorcherdsData g)
    (A : BorcherdsAdmissible D (relativeInducedRep p σ)) (c : ℂ)
    (hbottom : ∀ w : W,
      A.casimirOperator (PBWTheorem.bottom p σ w) = c • PBWTheorem.bottom p σ w) :
    A.casimirOperator = c • LinearMap.id := by
  apply relativeInduced_ext p σ
  intro a w
  have h := A.casimirOperator_commutes_enveloping a (PBWTheorem.bottom p σ w)
  rw [← relativeInducedAlgebra_eq_lift p σ, hbottom, map_smul] at h
  change A.casimirOperator (relativeInducedLeft p σ a (PBWTheorem.bottom p σ w)) =
    c • relativeInducedLeft p σ a (PBWTheorem.bottom p σ w) at h
  change A.casimirOperator (Submodule.Quotient.mk (a ⊗ₜ[ℂ] w)) =
    c • Submodule.Quotient.mk (a ⊗ₜ[ℂ] w)
  change A.casimirOperator (relativeInducedLeft p σ a
      (Submodule.Quotient.mk (1 ⊗ₜ[ℂ] w))) =
    c • relativeInducedLeft p σ a (Submodule.Quotient.mk (1 ⊗ₜ[ℂ] w)) at h
  simpa only [relativeInducedLeft_tmul, mul_one] using h

end VOA.Moonshine.ConwayNorton

