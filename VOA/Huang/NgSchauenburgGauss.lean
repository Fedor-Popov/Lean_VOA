import VOA.Huang.NgSchauenburgSRelations

/-! # Categorical Gauss sums

The positive and negative Gauss sums are formed from the specified ribbon
structure. Their product and nonvanishing are consequences of balancing,
loop fusion, and nondegeneracy, rather than additional modular-data inputs.
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

/-- Positive categorical Gauss sum. -/
def gaussPlus (F : SphericalFusion C) (R : Ribbon F.toPivotal) : ℂ :=
  ∑ i, R.twistScalar i * F.dimension (F.simple i) ^ 2

/-- Negative categorical Gauss sum. -/
def gaussMinus (F : SphericalFusion C) (R : Ribbon F.toPivotal) : ℂ :=
  ∑ i, (R.twistScalar i)⁻¹ * F.dimension (F.simple i) ^ 2

/-- The twist-weighted dimension vector transforms by the positive Gauss sum. -/
theorem categoricalS_gauss (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (j : F.Label) :
    (∑ i, categoricalS F i j * R.twistScalar i * F.dimension (F.simple i)) =
      gaussPlus F R * (R.twistScalar j)⁻¹ * F.dimension (F.simple j) := by
  have he (i : F.Label) :
      categoricalS F i j * R.twistScalar i * F.dimension (F.simple i) =
        (R.twistScalar j)⁻¹ * ∑ r,
          (F.fusionMultiplicity (F.dualLabel i) j (F.simple r) : ℂ) *
            F.dimension (F.simple i) * R.twistScalar r * F.dimension (F.simple r) := by
    rw [R.categoricalS_balancing]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    field_simp [R.twistScalar_ne_zero]
  simp only [he, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (i r : F.Label) :
      F.fusionMultiplicity (F.dualLabel i) j (F.simple r) =
        F.fusionMultiplicity j (F.dualLabel r) (F.simple i) := by
    rw [F.fusion_reciprocity, F.dualLabel_involutive i,
      F.fusion_comm i, F.fusion_reciprocity, F.fusion_comm (F.dualLabel r)]
  simp only [hf, ← Finset.sum_mul, F.fusion_dimension, F.dimension_dualLabel]
  unfold gaussPlus
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The two categorical Gauss sums multiply to global dimension. -/
theorem gaussPlus_mul_gaussMinus (F : SphericalFusion C) (M : Modular F) :
    gaussPlus F M.toRibbon * gaussMinus F M.toRibbon = F.globalDimension := by
  classical
  have he (i : F.Label) : gaussPlus F M.toRibbon *
      ((M.twistScalar i)⁻¹ * F.dimension (F.simple i) ^ 2) =
      ∑ j, F.dimension (F.simple i) *
        (categoricalS F j i * M.twistScalar j * F.dimension (F.simple j)) := by
    rw [← Finset.mul_sum, categoricalS_gauss F M.toRibbon]
    ring
  rw [gaussMinus, Finset.mul_sum]
  simp only [he]
  rw [Finset.sum_comm]
  have hs (j : F.Label) :
      (∑ i, F.dimension (F.simple i) *
        (categoricalS F j i * M.twistScalar j * F.dimension (F.simple j))) =
      (if j = F.unitLabel then F.globalDimension else 0) *
        M.twistScalar j * F.dimension (F.simple j) := by
    rw [← categoricalS_dimension_sum F M j]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [categoricalS_symm F M.toRibbon j]
    ring
  simp only [hs, ite_mul, zero_mul]
  simp [M.toRibbon.twistScalar_unitLabel]

/-- Neither categorical Gauss sum vanishes in a modular category. -/
theorem gauss_ne_zero (F : SphericalFusion C) (M : Modular F) :
    gaussPlus F M.toRibbon ≠ 0 ∧ gaussMinus F M.toRibbon ≠ 0 := by
  exact mul_ne_zero_iff.mp ((gaussPlus_mul_gaussMinus F M).symm ▸ F.globalDimension_ne_zero)

end VOA.Huang.NgSchauenburg
