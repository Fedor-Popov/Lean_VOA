import VOA.Huang.NgSchauenburgGauss

/-! # Modular relations derived from categorical traces

The raw twist is used with the dual-first-index, unnormalized S matrix.
Consequently the scalar in the cubic relation is the positive Gauss sum.
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

open Classical in
/-- The raw categorical twist matrix. -/
def categoricalT (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    Matrix F.Label F.Label ℂ := Matrix.diagonal R.twistScalar

open Classical in
/-- The inverse raw twist, written without a matrix inverse choice. -/
def categoricalTInv (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    Matrix F.Label F.Label ℂ := Matrix.diagonal (fun i => (R.twistScalar i)⁻¹)

open Classical in
/-- The displayed inverse twist really is an inverse. -/
theorem categoricalTInv_mul_T (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    categoricalTInv F R * categoricalT F R = 1 := by
  ext i j
  simp only [categoricalTInv, categoricalT, Matrix.mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst j; simp [R.twistScalar_ne_zero]
  · simp

open Classical in
/-- Charge conjugation commutes with the ribbon twist by dual compatibility. -/
theorem chargeConjugation_mul_T (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    chargeConjugation F * categoricalT F R = categoricalT F R * chargeConjugation F := by
  ext i j
  simp only [categoricalT, Matrix.mul_diagonal, Matrix.diagonal_mul, chargeConjugation]
  by_cases h : j = F.dualLabel i
  · subst j; simp [R.twistScalar_dualLabel]
  · simp [h]

open Classical in
/-- The inverse-S transform of the positive twist-dimension vector. -/
theorem categoricalS_inv_gauss (F : SphericalFusion C) (M : Modular F) (k : F.Label) :
    (∑ r, (categoricalS F)⁻¹ k r * M.twistScalar r * F.dimension (F.simple r)) =
      F.globalDimension⁻¹ * gaussPlus F M.toRibbon *
        (M.twistScalar k)⁻¹ * F.dimension (F.simple k) := by
  simp only [categoricalS_inv_apply F M, mul_assoc, ← Finset.mul_sum]
  simp_rw [categoricalS_symm F M.toRibbon (F.dualLabel k)]
  have h := categoricalS_gauss F M.toRibbon (F.dualLabel k)
  simp only [M.toRibbon.twistScalar_dualLabel, F.dimension_dualLabel] at h
  simp only [mul_assoc] at h
  rw [h]

open Classical in
/-- The entrywise TST relation, obtained from balancing and categorical Verlinde. -/
theorem categoricalTST_apply (F : SphericalFusion C) (M : Modular F) (i j : F.Label) :
    M.twistScalar i * categoricalS F i j * M.twistScalar j =
      gaussPlus F M.toRibbon * ∑ k,
        (categoricalS F)⁻¹ i k * (M.twistScalar k)⁻¹ * categoricalS F k j := by
  have hb : M.twistScalar i * categoricalS F i j * M.twistScalar j =
      ∑ r, (F.fusionMultiplicity (F.dualLabel i) j (F.simple r) : ℂ) *
        M.twistScalar r * F.dimension (F.simple r) := by
    rw [M.toRibbon.categoricalS_balancing]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    field_simp [M.toRibbon.twistScalar_ne_zero]
  calc
    _ = _ := hb
    _ = ∑ k, categoricalS F j k *
        (categoricalS F (F.dualLabel i) k / F.dimension (F.simple k)) *
          (∑ r, (categoricalS F)⁻¹ k r * M.twistScalar r * F.dimension (F.simple r)) := by
      simp_rw [categorical_verlinde F M]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      simp only [categoricalS_inv_gauss, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [categoricalS_inv_apply F M, categoricalS_symm F M.toRibbon k j]
      field_simp [F.dimension_simple_ne_zero]

open Classical in
/-- The matrix TST relation for the actual categorical S and T. -/
theorem categoricalTST (F : SphericalFusion C) (M : Modular F) :
    categoricalT F M.toRibbon * categoricalS F * categoricalT F M.toRibbon =
      gaussPlus F M.toRibbon •
        ((categoricalS F)⁻¹ * categoricalTInv F M.toRibbon * categoricalS F) := by
  ext i j
  simp only [categoricalT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change M.twistScalar i * categoricalS F i j * M.twistScalar j = _
  rw [Matrix.smul_apply, Matrix.mul_apply]
  simp only [categoricalTInv, Matrix.mul_diagonal, smul_eq_mul]
  exact categoricalTST_apply F M i j

open Classical in
/-- The cubic modular relation with its positive Gauss normalization. -/
theorem categoricalST_cube (F : SphericalFusion C) (M : Modular F) :
    (categoricalS F * categoricalT F M.toRibbon) ^ 3 =
      gaussPlus F M.toRibbon • (categoricalS F * categoricalS F) := by
  let S := categoricalS F
  let T := categoricalT F M.toRibbon
  let Ti := categoricalTInv F M.toRibbon
  let p := gaussPlus F M.toRibbon
  have h : T * S * T = p • (S⁻¹ * Ti * S) := categoricalTST F M
  have hc : (S * S) * T = T * (S * S) := by
    dsimp only [S, T]
    rw [categoricalS_sq F M, Matrix.smul_mul, Matrix.mul_smul,
      chargeConjugation_mul_T]
  have hi : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr M.nondegenerate)
  have ht : Ti * T = 1 := categoricalTInv_mul_T F M.toRibbon
  change (S * T) ^ 3 = p • (S * S)
  calc
    _ = S * (T * S * T) * S * T := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = p • (Ti * (S * S) * T) := by
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [← mul_assoc, hi, one_mul]
    _ = p • (S * S) := by rw [mul_assoc Ti, hc, ← mul_assoc Ti, ht, one_mul]

end VOA.Huang.NgSchauenburg
