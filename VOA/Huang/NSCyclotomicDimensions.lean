import VOA.Huang.NSCyclotomicField

/-! # Mixed S cyclotomicity reduced to dimensions

The remaining unconditional input is isolated as `SimpleDimensionsCyclotomic`.
It follows from the FS exponent identity, which is currently available in the
library under the explicit `BantayFormula` hypothesis.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Simple categorical dimensions belong to the field of the raw twist order. -/
def SimpleDimensionsCyclotomic (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ i, F.dimension (F.simple i) ∈ cycloField M.toRibbon.twistOrder

theorem twistScalar_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (i : F.Label) : M.twistScalar i ∈ cycloField M.toRibbon.twistOrder :=
  mem_cycloField_of_pow_eq_one M.toRibbon.finite_twist.1 (twistScalar_pow_twistOrder M i)

theorem simpleDimensionsCyclotomic_of_isFSExponent (F : SphericalFusion C) (M : Modular F)
    (h : IsFSExponent F M.toRibbon.twistOrder) : SimpleDimensionsCyclotomic F M := by
  intro i
  rw [← h.2 (F.simple i)]
  exact cyclotomicIntegers_le_cycloField _ (indicator_cyclotomic F (F.simple i) h.1)

theorem simpleDimensionsCyclotomic_of_bantay (F : SphericalFusion C) (M : Modular F)
    (hb : BantayFormula F M) : SimpleDimensionsCyclotomic F M :=
  simpleDimensionsCyclotomic_of_isFSExponent F M
    ((isFSExponent_iff_twistOrder_dvd F M hb M.toRibbon.finite_twist.1).mpr dvd_rfl)

theorem dimension_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (hd : SimpleDimensionsCyclotomic F M) (X : C) :
    F.dimension X ∈ cycloField M.toRibbon.twistOrder := by
  rw [F.dimension_eq_sum]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hd i)

theorem globalDimension_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (hd : SimpleDimensionsCyclotomic F M) :
    F.globalDimension ∈ cycloField M.toRibbon.twistOrder :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (hd i) 2

theorem categoricalS_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (hd : SimpleDimensionsCyclotomic F M) (i j : F.Label) :
    categoricalS F i j ∈ cycloField M.toRibbon.twistOrder := by
  rw [M.toRibbon.categoricalS_balancing]
  apply Subalgebra.sum_mem
  intro k _
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
    (cycloField_div_mem M.toRibbon.finite_twist.1 (twistScalar_mem_cycloField F M k)
      (Subalgebra.mul_mem _ (twistScalar_mem_cycloField F M i)
        (twistScalar_mem_cycloField F M j)))) (hd k)

open Classical in
theorem categoricalS_inv_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (hd : SimpleDimensionsCyclotomic F M) (i j : F.Label) :
    (categoricalS F)⁻¹ i j ∈ cycloField M.toRibbon.twistOrder := by
  rw [categoricalS_inv_apply F M]
  exact Subalgebra.mul_mem _
    (cycloField_inv_mem M.toRibbon.finite_twist.1 (globalDimension_mem_cycloField F M hd))
    (categoricalS_mem_cycloField F M hd _ _)

theorem mixedSCyclotomic_of_dimensions (F : SphericalFusion C) (M : Modular F)
    (hd : SimpleDimensionsCyclotomic F M) : MixedSCyclotomic F M := by
  intro p q
  rw [mixedS_apply]
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (cycloField_inv_mem M.toRibbon.finite_twist.1 (globalDimension_mem_cycloField F M hd))
    (categoricalS_mem_cycloField F M hd _ _)) (categoricalS_mem_cycloField F M hd _ _)

theorem mixedSCyclotomic_of_isFSExponent (F : SphericalFusion C) (M : Modular F)
    (h : IsFSExponent F M.toRibbon.twistOrder) : MixedSCyclotomic F M :=
  mixedSCyclotomic_of_dimensions F M (simpleDimensionsCyclotomic_of_isFSExponent F M h)

theorem mixedSCyclotomic_of_bantay (F : SphericalFusion C) (M : Modular F)
    (hb : BantayFormula F M) : MixedSCyclotomic F M :=
  mixedSCyclotomic_of_dimensions F M (simpleDimensionsCyclotomic_of_bantay F M hb)

/-- The mixed S contract in fact recovers every simple dimension from its unit entries. -/
theorem simpleDimensionsCyclotomic_of_mixedS (F : SphericalFusion C) (M : Modular F)
    (hc : MixedSCyclotomic F M) : SimpleDimensionsCyclotomic F M := by
  have h0 := hc (F.unitLabel, F.unitLabel) (F.unitLabel, F.unitLabel)
  simp only [mixedS_apply, categoricalS_unit_right, F.dimension_dualLabel,
    F.dimension_unitLabel, mul_one] at h0
  intro i
  have hi := hc (i, F.unitLabel) (F.unitLabel, F.unitLabel)
  simp only [mixedS_apply, categoricalS_unit_right, F.dimension_dualLabel,
    F.dimension_unitLabel, mul_one] at hi
  have h := Subalgebra.mul_mem _ (cycloField_inv_mem M.toRibbon.finite_twist.1 h0) hi
  simpa [inv_inv, ← mul_assoc, F.globalDimension_ne_zero] using h

/-- Exact characterization of the remaining unconditional cyclotomicity input. -/
theorem mixedSCyclotomic_iff_dimensions (F : SphericalFusion C) (M : Modular F) :
    MixedSCyclotomic F M ↔ SimpleDimensionsCyclotomic F M :=
  ⟨simpleDimensionsCyclotomic_of_mixedS F M, mixedSCyclotomic_of_dimensions F M⟩

end VOA.Huang.NSCongruence
