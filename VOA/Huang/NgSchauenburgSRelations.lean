import VOA.Huang.NgSchauenburgVerlinde

/-! # Orthogonality and inversion of the categorical S matrix

These statements concern the unnormalized categorical S. Its square is
`globalDimension` times charge conjugation. No numerical S relation is assumed.
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

/-- Symmetry for the S convention with a dual on the first index. -/
theorem categoricalS_symm (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (i j : F.Label) : categoricalS F i j = categoricalS F j i := by
  rw [R.categoricalS_balancing, R.categoricalS_balancing]
  calc
    _ = ∑ k, (F.fusionMultiplicity (F.dualLabel i) j
        (F.simple (F.dualLabel k)) : ℂ) *
        (R.twistScalar (F.dualLabel k) / (R.twistScalar i * R.twistScalar j)) *
        F.dimension (F.simple (F.dualLabel k)) :=
      ((F.dualLabelEquiv).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hf := F.fusion_dual_all i (F.dualLabel j) k
      rw [F.dualLabel_involutive j, F.fusion_comm i] at hf
      rw [hf, R.twistScalar_dualLabel, F.dimension_dualLabel, mul_comm (R.twistScalar i)]

/-- Simultaneously dualizing the two labels preserves S. -/
theorem categoricalS_dual_both (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (i j : F.Label) :
    categoricalS F (F.dualLabel i) (F.dualLabel j) = categoricalS F i j := by
  rw [R.categoricalS_balancing, R.categoricalS_balancing]
  calc
    _ = ∑ k, (F.fusionMultiplicity (F.dualLabel (F.dualLabel i)) (F.dualLabel j)
        (F.simple (F.dualLabel k)) : ℂ) *
        (R.twistScalar (F.dualLabel k) /
          (R.twistScalar (F.dualLabel i) * R.twistScalar (F.dualLabel j))) *
        F.dimension (F.simple (F.dualLabel k)) :=
      ((F.dualLabelEquiv).sum_comp _).symm
    _ = _ := by
      simp only [F.fusion_dual_all, R.twistScalar_dualLabel, F.dimension_dualLabel]

/-- Move a dual from one S index to the other. -/
theorem categoricalS_dual_left (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (i j : F.Label) :
    categoricalS F (F.dualLabel i) j = categoricalS F i (F.dualLabel j) := by
  simpa only [F.dualLabel_involutive j] using categoricalS_dual_both F R i (F.dualLabel j)

/-- The vacuum row is the categorical dimension vector. -/
theorem categoricalS_unit_left (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (i : F.Label) : categoricalS F F.unitLabel i = F.dimension (F.simple i) := by
  rw [categoricalS_symm F R, categoricalS_unit_right]

open Classical in
/-- Exact multiplicity of the unit in a simple tensor product. -/
theorem fusion_unit_target (F : SphericalFusion C) (i j : F.Label) :
    F.fusionMultiplicity i j (F.simple F.unitLabel) =
      if j = F.dualLabel i then 1 else 0 := by
  rw [F.fusion_reciprocity, F.fusion_comm, F.fusion_unit_left]

open Classical in
/-- Row orthogonality from loop fusion and the modular killing ring. -/
theorem categoricalS_orthogonality (F : SphericalFusion C) (M : Modular F)
    (i j : F.Label) :
    (∑ k, categoricalS F i k * categoricalS F j k) =
      if j = F.dualLabel i then F.globalDimension else 0 := by
  have he (k : F.Label) : categoricalS F i k * categoricalS F j k =
      ∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) *
        (F.dimension (F.simple k) * categoricalS F r k) := by
    have h := categoricalS_fusion F i j k
    have h' := (eq_div_iff (F.dimension_simple_ne_zero k)).mp h
    rw [← h', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [he]
  rw [Finset.sum_comm]
  have hs (r : F.Label) :
      (∑ k, F.dimension (F.simple k) * categoricalS F r k) =
        if r = F.unitLabel then F.globalDimension else 0 := by
    simp_rw [categoricalS_symm F M.toRibbon r]
    exact categoricalS_dimension_sum F M r
  simp only [← Finset.mul_sum, hs, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), fusion_unit_target]
  split_ifs <;> simp

open Classical in
/-- Charge conjugation on the actual simple labels. -/
def chargeConjugation (F : SphericalFusion C) : Matrix F.Label F.Label ℂ :=
  fun i j => if j = F.dualLabel i then 1 else 0

open Classical in
/-- The unnormalized categorical S square, including its exact scalar. -/
theorem categoricalS_sq (F : SphericalFusion C) (M : Modular F) :
    categoricalS F * categoricalS F = F.globalDimension • chargeConjugation F := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, chargeConjugation, smul_eq_mul]
  simp_rw [categoricalS_symm F M.toRibbon _ j]
  rw [categoricalS_orthogonality F M]
  split_ifs <;> simp

open Classical in
/-- Inverse S expressed in categorical dimensions and dual labels. -/
theorem categoricalS_inv_apply (F : SphericalFusion C) (M : Modular F)
    (i j : F.Label) :
    (categoricalS F)⁻¹ i j = F.globalDimension⁻¹ * categoricalS F (F.dualLabel i) j := by
  let B : Matrix F.Label F.Label ℂ :=
    fun i j => F.globalDimension⁻¹ * categoricalS F (F.dualLabel i) j
  have hb : B * categoricalS F = 1 := by
    ext a b
    simp only [B, Matrix.mul_apply, mul_assoc, ← Finset.mul_sum]
    simp_rw [categoricalS_symm F M.toRibbon _ b]
    rw [categoricalS_orthogonality F M, F.dualLabel_involutive]
    by_cases h : b = a
    · subst b; simp [F.globalDimension_ne_zero]
    · simp [h, Ne.symm h]
  have hB : B = (categoricalS F)⁻¹ := by
    calc
      B = B * (categoricalS F * (categoricalS F)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr M.nondegenerate), Matrix.mul_one]
      _ = (categoricalS F)⁻¹ := by rw [← Matrix.mul_assoc, hb, Matrix.one_mul]
  exact congrArg (fun A : Matrix F.Label F.Label ℂ => A i j) hB.symm

/-- The familiar three-S form of Verlinde with the specified orientation. -/
theorem categorical_verlinde_three_S (F : SphericalFusion C) (M : Modular F)
    (i j r : F.Label) :
    (F.fusionMultiplicity i j (F.simple r) : ℂ) =
      F.globalDimension⁻¹ * ∑ k,
        categoricalS F i k * categoricalS F j k * categoricalS F (F.dualLabel r) k /
          F.dimension (F.simple k) := by
  rw [categorical_verlinde F M, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [categoricalS_inv_apply F M, categoricalS_dual_left F M.toRibbon,
    categoricalS_symm F M.toRibbon k]
  ring

end VOA.Huang.NgSchauenburg
