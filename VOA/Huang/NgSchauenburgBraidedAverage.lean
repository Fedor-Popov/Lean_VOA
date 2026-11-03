import VOA.Huang.NgSchauenburgKillingRing

/-! # Averaging between the two braided embeddings

For a modular base category the average from the inverse-braided lift to
the braided lift is the unit-isotypic projection on the underlying Hom space.
In particular its values are central. This concerns these two embeddings;
it does not identify the average for arbitrary objects of the center.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The loop on a map between opposite braided lifts is actual monodromy
on its source, followed by the map. -/
theorem halfBraidingLoop_opposite_braided (F : SphericalFusion C)
    {X Y : C} (f : X ⟶ Y) (U : C) :
    halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
      (Center.ofBraidedObj Y) U f = monodromyLoop F.toPivotal U X ≫ f := by
  change F.toPivotal.partialTraceLeft U
    ((β_ U X).hom ≫ f ▷ U ≫ (β_ Y U).hom) = _
  rw [braiding_naturality_left]
  simpa only [monodromyLoop, monodromy, Category.assoc] using
    F.toPivotal.partialTraceLeft_postcomp U (monodromy U X) f

/-- The killing ring is used in the base category, with its own simple labels. -/
theorem halfBraidingAverage_opposite_braided (F : SphericalFusion C) (M : Modular F)
    {X Y : C} (f : X ⟶ Y) :
    halfBraidingAverage F (oppositeBraidedCenter X) (Center.ofBraidedObj Y) f =
      F.simpleProjector F.unitLabel X ≫ f := by
  simp only [halfBraidingAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    halfBraidingLoop_opposite_braided]
  change F.globalDimension⁻¹ • (∑ i, F.dimension (F.simple i) •
    (monodromyLoop F.toPivotal (F.simple i) X ≫ f)) = _
  rw [← normalized_monodromy_killingRing F M X]
  simp only [Linear.smul_comp, Preadditive.sum_comp]

/-- A map which factors through the tensor unit intertwines the two braidings. -/
theorem braided_comm_of_unit_factor {X Y : C}
    (p : X ⟶ 𝟙_ C) (q : 𝟙_ C ⟶ Y) (U : C) :
    (p ≫ q) ▷ U ≫ (β_ Y U).hom = (β_ U X).inv ≫ U ◁ (p ≫ q) := by
  apply (cancel_epi (β_ U X).hom).mp
  simp only [Iso.hom_inv_id_assoc, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]
  rw [braiding_naturality_left, ← Category.assoc,
    ← braiding_naturality_right]
  simp [braiding_tensorUnit_left, braiding_tensorUnit_right]

/-- The unit-channel part of any underlying map has the required open-strand
half-braiding equation. -/
theorem unitProjector_braided_comm (F : SphericalFusion C)
    {X Y : C} (f : X ⟶ Y) (U : C) :
    (F.simpleProjector F.unitLabel X ≫ f) ▷ U ≫ (β_ Y U).hom =
      (β_ U X).inv ≫ U ◁ (F.simpleProjector F.unitLabel X ≫ f) := by
  unfold SphericalFusion.simpleProjector
  simp only [Preadditive.sum_comp, sum_whiskerRight, whiskerLeft_sum,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h := braided_comm_of_unit_factor
    (F.compositionDual (F.simpleHomBasis X F.unitLabel) a ≫ F.unitIso.hom)
    (F.unitIso.inv ≫ F.simpleHomBasis X F.unitLabel a ≫ f) U
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- Centrality of the actual average for arbitrary underlying maps between
the inverse-braided and braided embeddings of a modular category. -/
theorem halfBraidingAverage_opposite_braided_comm (F : SphericalFusion C)
    (M : Modular F) {X Y : C} (f : X ⟶ Y) (U : C) :
    halfBraidingAverage F (oppositeBraidedCenter X) (Center.ofBraidedObj Y) f ▷ U ≫
        (β_ Y U).hom =
      (β_ U X).inv ≫ U ◁
        halfBraidingAverage F (oppositeBraidedCenter X) (Center.ofBraidedObj Y) f := by
  rw [halfBraidingAverage_opposite_braided F M]
  exact unitProjector_braided_comm F f U

/-- Between the two embeddings, being central is equivalent to being entirely
supported on the unit isotypic component. -/
theorem opposite_braided_comm_iff (F : SphericalFusion C) (M : Modular F)
    {X Y : C} (f : X ⟶ Y) :
    (∀ U : C, f ▷ U ≫ (β_ Y U).hom = (β_ U X).inv ≫ U ◁ f) ↔
      F.simpleProjector F.unitLabel X ≫ f = f := by
  constructor
  · intro h
    let g : oppositeBraidedCenter X ⟶ Center.ofBraidedObj Y := ⟨f, h⟩
    simpa only [halfBraidingAverage_opposite_braided F M] using
      halfBraidingAverage_central F g
  · intro h U
    conv_lhs => rw [← h]
    rw [unitProjector_braided_comm F f U, h]

/-- The verified average, bundled as a linear map to the actual central
Hom space. No spherical fusion structure on the center is required. -/
def oppositeBraidedRetraction (F : SphericalFusion C) (M : Modular F) (X Y : C) :
    (X ⟶ Y) →ₗ[ℂ] (oppositeBraidedCenter X ⟶ Center.ofBraidedObj Y) where
  toFun f := ⟨halfBraidingAverage F (oppositeBraidedCenter X) (Center.ofBraidedObj Y) f,
    halfBraidingAverage_opposite_braided_comm F M f⟩
  map_add' f g := by ext; exact map_add _ f g
  map_smul' z f := by ext; exact map_smul _ z f

/-- Forgetting and then averaging a central map returns that map. -/
theorem oppositeBraidedRetraction_forget (F : SphericalFusion C) (M : Modular F)
    {X Y : C} (f : oppositeBraidedCenter X ⟶ Center.ofBraidedObj Y) :
    oppositeBraidedRetraction F M X Y f.f = f := by
  apply Center.ext
  exact halfBraidingAverage_central F f

/-- A non-vacuum simple in the inverse-braided embedding has no morphisms
to any object of the braided embedding. -/
theorem opposite_braided_hom_eq_zero (F : SphericalFusion C) (M : Modular F)
    (i : F.Label) (hi : i ≠ F.unitLabel) (Y : C)
    (f : oppositeBraidedCenter (F.simple i) ⟶ Center.ofBraidedObj Y) : f = 0 := by
  apply Center.ext
  have h := halfBraidingAverage_central F f
  rw [halfBraidingAverage_opposite_braided F M] at h
  have hp : F.simpleProjector F.unitLabel (F.simple i) = 0 := by
    simpa [hi] using F.comp_simpleProjector F.unitLabel i (𝟙 (F.simple i))
  simpa only [hp, zero_comp] using h.symm

variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- On these two embeddings the average is the central trace
projection, with the existing trace-compatibility premise kept explicit. -/
theorem halfBraidingAverage_opposite_braided_eq_projection (F : SphericalFusion C)
    (M : Modular F) (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (X Y : C) :
    halfBraidingAverage F (oppositeBraidedCenter X) (Center.ofBraidedObj Y) =
      centralTraceProjection F Z (oppositeBraidedCenter X) (Center.ofBraidedObj Y) := by
  apply (halfBraidingAverage_eq_projection_iff F Z hc _ _).mpr
  intro f U
  exact halfBraidingAverage_opposite_braided_comm F M f U

end VOA.Huang.NgSchauenburg
