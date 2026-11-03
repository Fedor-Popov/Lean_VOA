import VOA.Huang.NgSchauenburgLoopFusion

/-! # Absorption and idempotence of the explicit half-braiding average

These fusion-algebra identities do not assert that the image of the average
consists of central morphisms. The open-strand slide needed for that assertion
is distinct from the absorption of a closed loop proved here.
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

namespace SphericalFusion

/-- The right-handed weighted fusion identity; no braiding is needed. -/
theorem fusion_dimension_source (F : SphericalFusion C) (U V : C) :
    (∑ i, (Module.finrank ℂ (V ⟶ F.simple i ⊗ U) : ℂ) *
      F.dimension (F.simple i)) = F.dimension U * F.dimension V := by
  have h (i : F.Label) : Module.finrank ℂ (V ⟶ F.simple i ⊗ U) =
      Module.finrank ℂ (F.simple i ⟶ V ⊗ Uᘁ) := by
    rw [← F.finrank_hom_symm (V ⊗ Uᘁ) (F.simple i),
      (rightDuality V Uᘁ (F.simple i)).finrank_eq]
    exact (homCongr (Iso.refl V) (whiskerLeftIso (F.simple i) (F.j U))).finrank_eq
  simp only [h]
  rw [← F.dimension_eq_sum, F.dimension_tensor, F.dimension_dual, mul_comm]

end SphericalFusion

theorem halfBraidingLoop_mul (F : SphericalFusion C) (X Y : Center C) (U V : C) :
    halfBraidingLoop F.toPivotal X Y V * halfBraidingLoop F.toPivotal X Y U =
      halfBraidingLoop F.toPivotal X Y (U ⊗ V) :=
  (halfBraidingLoop_tensor F X Y U V).symm

/-- A loop followed by the average is absorbed with its categorical dimension. -/
theorem halfBraidingAverage_comp_simple (F : SphericalFusion C)
    (X Y : Center C) (i : F.Label) :
    (halfBraidingAverage F X Y).comp (halfBraidingLoop F.toPivotal X Y (F.simple i)) =
      F.dimension (F.simple i) • halfBraidingAverage F X Y := by
  classical
  change halfBraidingAverage F X Y * halfBraidingLoop F.toPivotal X Y (F.simple i) = _
  unfold halfBraidingAverage
  simp only [smul_mul_assoc, Finset.sum_mul, halfBraidingLoop_mul]
  rw [smul_comm (F.dimension (F.simple i))]
  congr 1
  simp only [halfBraidingLoop_eq_sum_simples F X Y (F.simple i ⊗ _),
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [SphericalFusion.fusionMultiplicity, mul_comm] using
    F.fusion_dimension_target i (F.simple j)

/-- The average followed by any loop is absorbed with its categorical dimension. -/
theorem halfBraidingLoop_comp_average (F : SphericalFusion C)
    (X Y : Center C) (U : C) :
    (halfBraidingLoop F.toPivotal X Y U).comp (halfBraidingAverage F X Y) =
      F.dimension U • halfBraidingAverage F X Y := by
  classical
  change halfBraidingLoop F.toPivotal X Y U * halfBraidingAverage F X Y = _
  unfold halfBraidingAverage
  simp only [mul_smul_comm, Finset.mul_sum, halfBraidingLoop_mul]
  rw [smul_comm (F.dimension U)]
  congr 1
  simp only [halfBraidingLoop_eq_sum_simples F X Y (_ ⊗ U),
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [mul_comm] using F.fusion_dimension_source U (F.simple j)

/-- Idempotence of the dimension-weighted cup-cap average itself. -/
theorem halfBraidingAverage_idempotent (F : SphericalFusion C) (X Y : Center C) :
    halfBraidingAverage F X Y * halfBraidingAverage F X Y =
      halfBraidingAverage F X Y := by
  conv_lhs => lhs; unfold halfBraidingAverage
  have h (U : C) : halfBraidingLoop F.toPivotal X Y U * halfBraidingAverage F X Y =
      F.dimension U • halfBraidingAverage F X Y := halfBraidingLoop_comp_average F X Y U
  simp only [smul_mul_assoc, Finset.sum_mul, h,
    smul_smul, ← pow_two, ← Finset.sum_smul]
  rw [← SphericalFusion.globalDimension,
    inv_mul_cancel₀ F.globalDimension_ne_zero, one_smul]

/-- The fixed space of the average is the simultaneous dimension-eigenspace
of all closed loops. Identifying it with central Hom still needs a slide. -/
theorem halfBraidingAverage_fixed_iff_loops (F : SphericalFusion C)
    (X Y : Center C) (f : X.1 ⟶ Y.1) :
    halfBraidingAverage F X Y f = f ↔
      ∀ U : C, halfBraidingLoop F.toPivotal X Y U f = F.dimension U • f := by
  constructor
  · intro hf U
    have h := congrArg (fun L : Module.End ℂ (X.1 ⟶ Y.1) => L f)
      (halfBraidingLoop_comp_average F X Y U)
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hf] using h
  · intro h
    simp only [halfBraidingAverage, LinearMap.smul_apply, LinearMap.sum_apply, h,
      smul_smul, ← pow_two, ← Finset.sum_smul]
    rw [← SphericalFusion.globalDimension,
      inv_mul_cancel₀ F.globalDimension_ne_zero, one_smul]

end VOA.Huang.NgSchauenburg
