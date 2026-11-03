import VOA.Huang.NgSchauenburgModularRelations

/-! # Mixed central objects and their positive probe spectrum

The objects are genuine tensor products in Mathlib's Drinfeld center.
Positive braided probes recover the first simple label. This establishes
orthogonality across distinct first labels, not simplicity or completeness
of the mixed family.
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

/-- The positive and inverse-braided tensor product in the actual center. -/
def mixedCenter (X Y : C) : Center C := Center.ofBraidedObj X ⊗ oppositeBraidedCenter Y

/-- The mixed half-braiding, with all associators retained. -/
theorem mixedCenter_halfBraiding (X Y U : C) :
    ((mixedCenter X Y).2.β U).hom =
      (α_ X Y U).hom ≫ X ◁ (β_ U Y).inv ≫ (α_ X U Y).inv ≫
        (β_ X U).hom ▷ Y ≫ (α_ U X Y).hom := rfl

/-- Close a positive braided probe around an arbitrary central object. -/
def positiveProbe (F : SphericalFusion C) (A : Center C) (U : C) : A.1 ⟶ A.1 :=
  F.toPivotal.partialTraceLeft U ((β_ U A.1).hom ≫ (A.2.β U).hom)

/-- Probes are natural under actual central morphisms. -/
theorem positiveProbe_naturality (F : SphericalFusion C) {A B : Center C}
    (f : A ⟶ B) (U : C) :
    positiveProbe F A U ≫ f.f = f.f ≫ positiveProbe F B U := by
  unfold positiveProbe
  rw [← F.toPivotal.partialTraceLeft_postcomp, ← F.toPivotal.partialTraceLeft_precomp]
  congr 1
  rw [Category.assoc, ← f.comm, ← Category.assoc, ← braiding_naturality_right]
  simp only [Category.assoc]

/-- The opposite-braided factor cancels from a positive probe diagram. -/
theorem positiveProbe_mixedCenter (F : SphericalFusion C) (X Y U : C) :
    positiveProbe F (mixedCenter X Y) U = monodromyLoop F.toPivotal U X ▷ Y := by
  unfold positiveProbe
  rw [mixedCenter_halfBraiding]
  change F.toPivotal.partialTraceLeft U
    ((β_ U (X ⊗ Y)).hom ≫ (α_ X Y U).hom ≫ X ◁ (β_ U Y).inv ≫
      (α_ X U Y).inv ≫ (β_ X U).hom ▷ Y ≫ (α_ U X Y).hom) = _
  rw [braiding_tensor_right_hom]
  have h :
      ((α_ U X Y).inv ≫ (β_ U X).hom ▷ Y ≫ (α_ X U Y).hom ≫
        X ◁ (β_ U Y).hom ≫ (α_ X Y U).inv) ≫
      (α_ X Y U).hom ≫ X ◁ (β_ U Y).inv ≫ (α_ X U Y).inv ≫
        (β_ X U).hom ▷ Y ≫ (α_ U X Y).hom =
      (α_ U X Y).inv ≫ (monodromy U X) ▷ Y ≫ (α_ U X Y).hom := by
    simp [monodromy]
  rw [h, F.toPivotal.partialTraceLeft_whisker]
  rfl

/-- The actual probe eigenvalue on each mixed object. -/
theorem positiveProbe_mixed_simple (F : SphericalFusion C) (i j a : F.Label) :
    positiveProbe F (mixedCenter (F.simple i) (F.simple j)) (F.simple a)ᘁ =
      (categoricalS F a i / F.dimension (F.simple i)) •
        𝟙 (F.simple i ⊗ F.simple j) := by
  rw [positiveProbe_mixedCenter, monodromyLoop_simple]
  simp

open Classical in
/-- Fourier projection in the positive probe variable, on an arbitrary central object. -/
def positiveProbeProjector (F : SphericalFusion C) (i : F.Label) (A : Center C) : A.1 ⟶ A.1 :=
  ∑ a, (F.dimension (F.simple i) * (categoricalS F)⁻¹ i a) •
    positiveProbe F A (F.simple a)ᘁ

open Classical in
/-- The Fourier probe is natural on the center, as an underlying morphism. -/
theorem positiveProbeProjector_naturality (F : SphericalFusion C) (i : F.Label)
    {A B : Center C} (f : A ⟶ B) :
    positiveProbeProjector F i A ≫ f.f = f.f ≫ positiveProbeProjector F i B := by
  simp only [positiveProbeProjector, Preadditive.sum_comp, Preadditive.comp_sum,
    Linear.smul_comp, Linear.comp_smul, positiveProbe_naturality]

open Classical in
/-- On a mixed object this is the first-factor isotypic projector. -/
theorem positiveProbeProjector_mixedCenter (F : SphericalFusion C) (M : Modular F)
    (i : F.Label) (X Y : C) :
    positiveProbeProjector F i (mixedCenter X Y) = F.simpleProjector i X ▷ Y := by
  rw [simpleProjector_eq_sum_loops F M]
  simp only [positiveProbeProjector, positiveProbe_mixedCenter,
    sum_whiskerRight, MonoidalLinear.smul_whiskerRight]
  rfl

open Classical in
/-- Positive probes separate the first labels of the actual mixed objects. -/
theorem positiveProbeProjector_mixed_simple (F : SphericalFusion C) (M : Modular F)
    (a i j : F.Label) :
    positiveProbeProjector F a (mixedCenter (F.simple i) (F.simple j)) =
      if i = a then 𝟙 (F.simple i ⊗ F.simple j) else 0 := by
  rw [positiveProbeProjector_mixedCenter F M]
  have h := F.comp_simpleProjector a i (𝟙 (F.simple i))
  simp only [Category.id_comp] at h
  rw [h]
  split_ifs <;> simp

/-- Distinct first labels have no central morphisms, regardless of the second labels. -/
theorem mixedCenter_hom_eq_zero_of_first_ne (F : SphericalFusion C) (M : Modular F)
    (i j k l : F.Label) (hik : i ≠ k)
    (f : mixedCenter (F.simple i) (F.simple j) ⟶
      mixedCenter (F.simple k) (F.simple l)) : f = 0 := by
  classical
  apply Center.ext
  have h := positiveProbeProjector_naturality F i f
  rw [positiveProbeProjector_mixed_simple F M,
    positiveProbeProjector_mixed_simple F M] at h
  change f.f = 0
  simp only [if_true, if_neg (Ne.symm hik)] at h
  change (𝟙 (F.simple i ⊗ F.simple j)) ≫ f.f =
    f.f ≫ (0 : F.simple k ⊗ F.simple l ⟶ F.simple k ⊗ F.simple l) at h
  erw [Category.id_comp, comp_zero] at h
  exact h

/-- The underlying dimension of each mixed object is the product of dimensions. -/
theorem mixedCenter_dimension (F : SphericalFusion C) (X Y : C) :
    F.dimension (mixedCenter X Y).1 = F.dimension X * F.dimension Y :=
  F.dimension_tensor X Y

/-- The total squared underlying dimension of the mixed family.
This is not a dimension theorem for the center or an exhaustion claim. -/
theorem mixedCenter_dimension_mass (F : SphericalFusion C) :
    (∑ i, ∑ j, F.dimension (mixedCenter (F.simple i) (F.simple j)).1 ^ 2) =
      F.globalDimension ^ 2 := by
  simp only [mixedCenter_dimension, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← SphericalFusion.globalDimension, pow_two]

/-- The genuine zero-power indicator on mixed objects is its fusion multiplicity. -/
theorem generalizedIndicatorInt_mixed_zero (F : SphericalFusion C) (i j : F.Label)
    (V : C) (n : ℕ) :
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n 0 =
      (F.fusionMultiplicity i j (tensorPower V (n + 1)) : ℂ) := by
  rw [generalizedIndicatorInt_zero]
  change (Module.finrank ℂ (F.simple i ⊗ F.simple j ⟶ tensorPower V (n + 1)) : ℂ) = _
  rw [F.finrank_hom_symm]
  rfl

end VOA.Huang.NgSchauenburg
