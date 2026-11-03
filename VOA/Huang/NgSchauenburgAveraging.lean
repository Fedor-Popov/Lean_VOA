import VOA.Huang.NgSchauenburgFourier

/-! # The dimension-weighted half-braiding average

This is the explicit cup-cap averaging operator on underlying Hom spaces.
It fixes central maps and has the correct trace pairings. Its identification
with the central projection is reduced to the still unproved assertion that
its values are central. No centrality or handle-slide identity is assumed here.
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

/-- Close the conjugation of an underlying map by the two half-braidings.
This construction does not require a braiding on the base category. -/
def halfBraidingLoop (P : Pivotal C) (X Y : Center C) (U : C) :
    Module.End ℂ (X.1 ⟶ Y.1) where
  toFun f := P.partialTraceLeft U ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom)
  map_add' f g := by
    simp [Pivotal.partialTraceLeft, MonoidalPreadditive.add_whiskerRight,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' z f := by simp [Pivotal.partialTraceLeft]

/-- A central morphism can be pulled through each individual loop. -/
theorem halfBraidingLoop_central (F : SphericalFusion C) {X Y : Center C}
    (f : X ⟶ Y) (U : C) :
    halfBraidingLoop F.toPivotal X Y U f.f = F.dimension U • f.f := by
  change F.toPivotal.partialTraceLeft U (_ ≫ _ ≫ _) = _
  rw [f.comm, Iso.inv_hom_id_assoc, F.partialTraceLeft_whiskerLeft]

/-- Pairing a loop with a reverse central map closes it to a categorical
dimension. This calculation uses trace cyclicity and sphericality. -/
theorem halfBraidingLoop_pair (F : SphericalFusion C) {X Y : Center C}
    (f : X.1 ⟶ Y.1) (g : Y ⟶ X) (U : C) :
    F.scalarTrace X.1 (halfBraidingLoop F.toPivotal X Y U f ≫ g.f) =
      F.dimension U * F.scalarTrace X.1 (f ≫ g.f) := by
  change F.scalarTrace X.1 (F.toPivotal.partialTraceLeft U _ ≫ g.f) = _
  rw [← F.toPivotal.partialTraceLeft_postcomp, F.scalarTrace_partialTraceLeft]
  have he : ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom) ≫ U ◁ g.f =
      (X.2.β U).inv ≫ (f ≫ g.f) ▷ U ≫ (X.2.β U).hom := by
    rw [Category.assoc, Category.assoc, ← g.comm, comp_whiskerRight]
    simp only [Category.assoc]
  rw [he, F.scalarTrace_comp_comm (X.2.β U).inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, F.scalarTrace_whiskerRight,
    mul_comm]

/-- The coefficient is `d_i / globalDimension`, conventionally `d_i / D²`. -/
def halfBraidingAverage (F : SphericalFusion C) (X Y : Center C) :
    Module.End ℂ (X.1 ⟶ Y.1) :=
  F.globalDimension⁻¹ • ∑ i, F.dimension (F.simple i) •
    halfBraidingLoop F.toPivotal X Y (F.simple i)

/-- Normalization of the genuine loop average on central maps. -/
theorem halfBraidingAverage_central (F : SphericalFusion C) {X Y : Center C}
    (f : X ⟶ Y) : halfBraidingAverage F X Y f.f = f.f := by
  simp only [halfBraidingAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    halfBraidingLoop_central, smul_smul, ← pow_two, ← Finset.sum_smul]
  rw [← SphericalFusion.globalDimension,
    inv_mul_cancel₀ F.globalDimension_ne_zero, one_smul]

/-- The normalized average preserves pairing with every reverse central map. -/
theorem halfBraidingAverage_pair (F : SphericalFusion C) {X Y : Center C}
    (f : X.1 ⟶ Y.1) (g : Y ⟶ X) :
    F.scalarTrace X.1 (halfBraidingAverage F X Y f ≫ g.f) =
      F.scalarTrace X.1 (f ≫ g.f) := by
  simp only [halfBraidingAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Linear.smul_comp, Preadditive.sum_comp, map_smul, map_sum,
    halfBraidingLoop_pair, smul_eq_mul]
  simp only [← mul_assoc, ← pow_two, ← Finset.sum_mul]
  rw [← SphericalFusion.globalDimension,
    inv_mul_cancel₀ F.globalDimension_ne_zero, one_mul]

variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- The average and the identity have the same image under the trace retraction.
This does not assert that the average itself takes central values. -/
theorem centralTraceRetraction_average (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) {X Y : Center C} (f : X.1 ⟶ Y.1) :
    centralTraceRetraction F Z X Y (halfBraidingAverage F X Y f) =
      centralTraceRetraction F Z X Y f := by
  symm
  apply centralTraceRetraction_unique
  intro g
  rw [centralTraceRetraction_pair, F.scalarTrace_comp_comm g.f,
    F.scalarTrace_comp_comm g.f, halfBraidingAverage_pair]

/-- The missing averaging theorem is precisely centrality of the explicit
loop sum: its trace-pairing characterization is already proved above. -/
theorem halfBraidingAverage_eq_projection_iff (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (X Y : Center C) :
    halfBraidingAverage F X Y = centralTraceProjection F Z X Y ↔
      ∀ (f : X.1 ⟶ Y.1) (U : C),
        halfBraidingAverage F X Y f ▷ U ≫ (Y.2.β U).hom =
          (X.2.β U).hom ≫ U ◁ halfBraidingAverage F X Y f := by
  constructor
  · intro h f U
    rw [h]
    exact (centralTraceRetraction F Z X Y f).comm U
  · intro h
    apply LinearMap.ext
    intro f
    let q : X ⟶ Y := ⟨halfBraidingAverage F X Y f, h f⟩
    have he := centralTraceRetraction_forget F Z hc q
    rw [centralTraceRetraction_average] at he
    exact (congrArg Center.Hom.f he).symm

end VOA.Huang.NgSchauenburg
