import VOA.Huang.NgSchauenburgModularRelations
import VOA.Huang.NgSchauenburgCongruence

/-! # Mixed modular generators without a fusion structure on the center

The double of an invertible matrix is its tensor product with its contragredient.
Scalar anomalies cancel. Applied to the actual categorical matrices, this gives
exact modular generator relations on pairs of base simple labels.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg

section Matrices
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Tensor an invertible matrix with its contragredient. -/
def matrixDouble : (Matrix I I ℂ)ˣ →* Matrix (I × I) (I × I) ℂ where
  toFun A := Matrix.kronecker (A : Matrix I I ℂ) ((↑A⁻¹ : Matrix I I ℂ).transpose)
  map_one' := by simp
  map_mul' A B := by
    simp only [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
    exact Matrix.mul_kronecker_mul _ _ _ _

/-- The double is unchanged by a nonzero scalar normalization. -/
theorem matrixDouble_eq_of_smul (A B : (Matrix I I ℂ)ˣ) {c : ℂ} (hc : c ≠ 0)
    (h : (A : Matrix I I ℂ) = c • (B : Matrix I I ℂ)) :
    matrixDouble A = matrixDouble B := by
  have hi' : (A : Matrix I I ℂ) * (c⁻¹ • (↑B⁻¹ : Matrix I I ℂ)) = 1 := by
    rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp [hc]
  have hi : (↑A⁻¹ : Matrix I I ℂ) = c⁻¹ • (↑B⁻¹ : Matrix I I ℂ) := by
    calc
      _ = (↑A⁻¹ : Matrix I I ℂ) *
          ((A : Matrix I I ℂ) * (c⁻¹ • (↑B⁻¹ : Matrix I I ℂ))) := by rw [hi', mul_one]
      _ = _ := by rw [← mul_assoc]; simp
  change Matrix.kronecker (A : Matrix I I ℂ) (↑A⁻¹ : Matrix I I ℂ).transpose = _
  rw [h, hi]
  ext ⟨i, j⟩ ⟨k, l⟩
  change (c * (B : Matrix I I ℂ) i k) *
    (c⁻¹ * (↑B⁻¹ : Matrix I I ℂ) l j) = _
  change _ = (B : Matrix I I ℂ) i k * (↑B⁻¹ : Matrix I I ℂ) l j
  field_simp

/-- A scalar matrix acts trivially in the double. -/
theorem matrixDouble_eq_one_of_scalar (A : (Matrix I I ℂ)ˣ) {c : ℂ} (hc : c ≠ 0)
    (h : (A : Matrix I I ℂ) = c • (1 : Matrix I I ℂ)) : matrixDouble A = 1 := by
  simpa using matrixDouble_eq_of_smul A 1 hc h
end Matrices

open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The actual categorical S as an invertible matrix. -/
def categoricalSUnit (F : SphericalFusion C) (M : Modular F) :
    (Matrix F.Label F.Label ℂ)ˣ :=
  Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr M.nondegenerate)

open Classical in
/-- The actual categorical T as an invertible matrix. -/
def categoricalTUnit (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    (Matrix F.Label F.Label ℂ)ˣ where
  val := categoricalT F R
  inv := categoricalTInv F R
  val_inv := by
    ext i j
    simp only [categoricalT, categoricalTInv, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [R.twistScalar_ne_zero]
  inv_val := categoricalTInv_mul_T F R

open Classical in
/-- Mixed S on pairs of base labels, independent of any center decomposition. -/
def mixedS (F : SphericalFusion C) (M : Modular F) :
    Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ :=
  matrixDouble (categoricalSUnit F M)

open Classical in
/-- Mixed T on pairs of base labels. -/
def mixedT (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ :=
  matrixDouble (categoricalTUnit F R)

open Classical in
theorem mixedS_apply (F : SphericalFusion C) (M : Modular F)
    (i j k l : F.Label) :
    mixedS F M (i, j) (k, l) = F.globalDimension⁻¹ *
      categoricalS F i k * categoricalS F (F.dualLabel j) l := by
  change categoricalS F i k * (categoricalS F)⁻¹ l j = _
  rw [categoricalS_inv_apply F M, categoricalS_dual_left F M.toRibbon,
    categoricalS_symm F M.toRibbon l (F.dualLabel j)]
  ring

open Classical in
theorem mixedT_eq_diagonal (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    mixedT F R = Matrix.diagonal (fun p => R.twistScalar p.1 / R.twistScalar p.2) := by
  change Matrix.kronecker (categoricalT F R) (categoricalTInv F R).transpose = _
  simp [categoricalT, categoricalTInv, Matrix.diagonal_kronecker_diagonal, div_eq_mul_inv]

open Classical in
theorem chargeConjugation_sq (F : SphericalFusion C) :
    chargeConjugation F * chargeConjugation F = 1 := by
  ext i j
  simp only [Matrix.mul_apply, chargeConjugation, ite_mul, one_mul, zero_mul]
  simp [F.dualLabel_involutive i, Matrix.one_apply, eq_comm]

open Classical in
/-- All normalization anomalies cancel in the mixed cubic relation. -/
theorem mixedST_cube (F : SphericalFusion C) (M : Modular F) :
    (mixedS F M * mixedT F M.toRibbon) ^ 3 = mixedS F M ^ 2 := by
  change (matrixDouble (categoricalSUnit F M) *
    matrixDouble (categoricalTUnit F M.toRibbon)) ^ 3 = _
  rw [← map_mul, ← map_pow]
  change matrixDouble _ = (matrixDouble (categoricalSUnit F M)) ^ 2
  rw [← map_pow]
  apply matrixDouble_eq_of_smul _ _ (gauss_ne_zero F M).1
  change (categoricalS F * categoricalT F M.toRibbon) ^ 3 =
    gaussPlus F M.toRibbon • categoricalS F ^ 2
  simpa only [pow_two] using categoricalST_cube F M

open Classical in
/-- The mixed S has fourth power one. -/
theorem mixedS_fourth (F : SphericalFusion C) (M : Modular F) :
    mixedS F M ^ 4 = 1 := by
  change matrixDouble (categoricalSUnit F M) ^ 4 = 1
  rw [← map_pow]
  apply matrixDouble_eq_one_of_scalar _ (pow_ne_zero 2 F.globalDimension_ne_zero)
  change categoricalS F ^ 4 = F.globalDimension ^ 2 • (1 : Matrix F.Label F.Label ℂ)
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two (categoricalS F),
    categoricalS_sq F M, smul_pow, pow_two (chargeConjugation F), chargeConjugation_sq]

open Classical in
/-- The mixed twist has exactly the same annihilating powers as the raw twist. -/
theorem mixedT_pow_eq_one_iff (F : SphericalFusion C) (R : Ribbon F.toPivotal) (n : ℕ) :
    mixedT F R ^ n = 1 ↔ ∀ i, R.twistScalar i ^ n = 1 := by
  rw [mixedT_eq_diagonal, Matrix.diagonal_pow]
  constructor
  · intro h i
    have hi := congrArg (fun A : Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ =>
      A (i, F.unitLabel) (i, F.unitLabel)) h
    simpa [R.twistScalar_unitLabel] using hi
  · intro h
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.diagonal_apply, Matrix.one_apply, div_pow, h]

open Classical in
/-- Exact mixed level: no factor of two or scalar normalization enlarges T's order. -/
theorem mixedT_orderOf (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    orderOf (mixedT F R) = R.twistOrder := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, mixedT_pow_eq_one_iff]
    intro i
    exact congrFun (pow_orderOf_eq_one R.twistScalar) i
  · rw [Ribbon.twistOrder, orderOf_dvd_iff_pow_eq_one]
    ext i
    exact (mixedT_pow_eq_one_iff F R _).mp (pow_orderOf_eq_one (mixedT F R)) i

open Classical in
/-- Positivity of the exact mixed twist order follows from the proved Vafa theorem. -/
theorem mixedT_orderOf_pos (F : SphericalFusion C) (M : Modular F) :
    0 < orderOf (mixedT F M.toRibbon) := by
  rw [mixedT_orderOf]
  exact M.toRibbon.finite_twist.1

end VOA.Huang.NgSchauenburg
