import VOA.Huang.NgSchauenburgCenterDimension

/-! # The regular-object calculation for center induction

The arithmetic part of the center-dimension theorem is proved from an actual
adjunction to the forgetful functor and actual underlying coend isomorphisms.
The construction of that adjunction with those isomorphisms is not supplied here.
No braiding or modularity of the base category is used by the calculation.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Dimension is additive on any finite biproduct, not only a simple decomposition. -/
theorem SphericalFusion.dimension_biproduct (F : SphericalFusion C)
    {J : Type} [Fintype J] (X : J → C) :
    F.dimension (⨁ X) = ∑ j, F.dimension (X j) := by
  unfold SphericalFusion.dimension
  change F.unitScalar.symm (F.toPivotal.traceStructure.trL (𝟙 _)) = _
  rw [F.toPivotal.traceStructure.trL_biproduct]
  simp [map_sum, TensorCat.PivotalStructure.trL, Pivotal.traceStructure,
    Pivotal.traceRight]

/-- The underlying coend object in the standard induction construction. -/
def inductionUnderlying (F : SphericalFusion C) (X : C) : C :=
  ⨁ fun i : F.Label => (F.simple i ⊗ X) ⊗ (F.simple i)ᘁ

/-- The coend object's dimension is global dimension times the input dimension. -/
theorem inductionUnderlying_dimension (F : SphericalFusion C) (X : C) :
    F.dimension (inductionUnderlying F X) = F.globalDimension * F.dimension X := by
  rw [inductionUnderlying, F.dimension_biproduct]
  simp only [F.dimension_tensor, F.dimension_dual, SphericalFusion.globalDimension,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- An adjunction to the forgetful functor is automatically linear on Hom spaces.
No independent linearity hypothesis on its left adjoint is needed. -/
def centerInductionHomEquiv (I : C ⥤ Center C) (hI : I ⊣ Center.forget C)
    (X : C) (A : Center C) : (I.obj X ⟶ A) ≃ₗ[ℂ] (X ⟶ A.1) :=
  { hI.homEquiv X A with
    map_add' := by
      intro f g
      change hI.unit.app X ≫ (f.f + g.f) =
        hI.unit.app X ≫ f.f + hI.unit.app X ≫ g.f
      erw [Preadditive.comp_add]
    map_smul' := by
      intro z f
      change hI.unit.app X ≫ (z • f.f) = z • (hI.unit.app X ≫ f.f)
      erw [Linear.comp_smul] }

/-- The regular-object double sum for any adjoint to forgetting.
It is independent of the explicit coend construction. -/
theorem center_globalDimension_eq_induction_sum (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (I : C ⥤ Center C) (hI : I ⊣ Center.forget C) :
    Z.globalDimension = ∑ i : F.Label,
      F.dimension (F.simple i) * Z.dimension (I.obj (F.simple i)) := by
  have hd (A : Center C) : Z.dimension A = F.dimension A.1 := hc A (𝟙 A)
  have hn (i : F.Label) (a : Z.Label) :
      Module.finrank ℂ (F.simple i ⟶ (Z.simple a).1) =
        Module.finrank ℂ (Z.simple a ⟶ I.obj (F.simple i)) := by
    rw [Z.finrank_hom_symm]
    exact (centerInductionHomEquiv I hI (F.simple i) (Z.simple a)).finrank_eq.symm
  unfold SphericalFusion.globalDimension
  calc
    (∑ a, Z.dimension (Z.simple a) ^ 2) =
        ∑ a, Z.dimension (Z.simple a) *
          (∑ i, (Module.finrank ℂ (F.simple i ⟶ (Z.simple a).1) : ℂ) *
            F.dimension (F.simple i)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← F.dimension_eq_sum, ← hd, pow_two]
    _ = ∑ i, F.dimension (F.simple i) * Z.dimension (I.obj (F.simple i)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Z.dimension_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [hn]
      ring

/-- The center-dimension calculation from a genuine induction adjunction with
its standard underlying object. These construction hypotheses remain explicit. -/
theorem center_globalDimension_of_induction (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (I : C ⥤ Center C) (hI : I ⊣ Center.forget C)
    (hobj : ∀ i : F.Label,
      Nonempty ((I.obj (F.simple i)).1 ≅ inductionUnderlying F (F.simple i))) :
    Z.globalDimension = F.globalDimension ^ 2 := by
  rw [center_globalDimension_eq_induction_sum F Z hc I hI]
  have hd (i : F.Label) : Z.dimension (I.obj (F.simple i)) =
      F.globalDimension * F.dimension (F.simple i) := by
    have ht : Z.dimension (I.obj (F.simple i)) =
        F.dimension (I.obj (F.simple i)).1 := hc _ (𝟙 _)
    rw [ht, F.dimension_iso (hobj i).some, inductionUnderlying_dimension]
  simp only [hd]
  calc
    (∑ i, F.dimension (F.simple i) * (F.globalDimension * F.dimension (F.simple i))) =
        F.globalDimension * ∑ i, F.dimension (F.simple i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = F.globalDimension ^ 2 := (pow_two _).symm

end VOA.Huang.NgSchauenburg
