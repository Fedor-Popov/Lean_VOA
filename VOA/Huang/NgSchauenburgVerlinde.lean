import VOA.Huang.NgSchauenburgBantayOne

/-! # Categorical Verlinde from actual monodromy loops

The fusion eigenvalue equation is derived from tensoring closed loops.
Nondegeneracy is used only to invert the resulting matrix equation.
The S convention retains the dual on its first index.
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

/-- Isomorphic loop labels give the same actual monodromy operator. -/
theorem monodromyLoop_iso (F : SphericalFusion C) {U V : C} (e : U ≅ V) (X : C) :
    monodromyLoop F.toPivotal U X = monodromyLoop F.toPivotal V X := by
  have h := congrArg (fun L : Module.End ℂ (X ⟶ X) => L (𝟙 X))
    (halfBraidingLoop_iso F (oppositeBraidedCenter X) (Center.ofBraidedObj X) e)
  change halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
    (Center.ofBraidedObj X) U (𝟙 X) =
    halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
      (Center.ofBraidedObj X) V (𝟙 X) at h
  simpa only [halfBraidingLoop_braided_id] using h

/-- Tensoring loop labels composes their monodromy operators. -/
theorem monodromyLoop_tensor (F : SphericalFusion C) (U V X : C) :
    monodromyLoop F.toPivotal (U ⊗ V) X =
      monodromyLoop F.toPivotal V X ≫ monodromyLoop F.toPivotal U X := by
  have h := congrArg (fun L : Module.End ℂ (X ⟶ X) => L (𝟙 X))
    (halfBraidingLoop_tensor F (oppositeBraidedCenter X) (Center.ofBraidedObj X) U V)
  change halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
    (Center.ofBraidedObj X) (U ⊗ V) (𝟙 X) =
    halfBraidingLoop F.toPivotal (oppositeBraidedCenter X) (Center.ofBraidedObj X) V
      (halfBraidingLoop F.toPivotal (oppositeBraidedCenter X) (Center.ofBraidedObj X) U
        (𝟙 X)) at h
  simpa only [LinearMap.comp_apply, halfBraidingLoop_braided_id,
    halfBraidingLoop_opposite_braided, Category.comp_id] using h

/-- The loop decomposes by the genuine multiplicities of its label. -/
theorem monodromyLoop_decomposition (F : SphericalFusion C) (U X : C) :
    monodromyLoop F.toPivotal U X =
      ∑ i, (Module.finrank ℂ (F.simple i ⟶ U) : ℂ) •
        monodromyLoop F.toPivotal (F.simple i) X := by
  have h := congrArg (fun L : Module.End ℂ (X ⟶ X) => L (𝟙 X))
    (halfBraidingLoop_eq_sum_simples F (oppositeBraidedCenter X)
      (Center.ofBraidedObj X) U)
  change halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
    (Center.ofBraidedObj X) U (𝟙 X) =
    (∑ i, (Module.finrank ℂ (F.simple i ⟶ U) : ℂ) •
      halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
        (Center.ofBraidedObj X) (F.simple i)) (𝟙 X) at h
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply,
    halfBraidingLoop_braided_id] using h

/-- The simple-label form of the loop eigenvalue, with the dual convention explicit. -/
theorem monodromyLoop_simple_label (F : SphericalFusion C) (i k : F.Label) :
    monodromyLoop F.toPivotal (F.simple i) (F.simple k) =
      (categoricalS F (F.dualLabel i) k / F.dimension (F.simple k)) • 𝟙 (F.simple k) := by
  rw [← monodromyLoop_simple]
  simpa only [F.dualLabel_involutive i] using
    (monodromyLoop_iso F (F.dualLabelIso (F.dualLabel i)) (F.simple k)).symm

namespace SphericalFusion
/-- Dualizing all three labels preserves the genuine fusion coefficient. -/
theorem fusion_dual_all (F : SphericalFusion C) (i j k : F.Label) :
    F.fusionMultiplicity (F.dualLabel i) (F.dualLabel j) (F.simple (F.dualLabel k)) =
      F.fusionMultiplicity i j (F.simple k) := by
  rw [F.fusion_reciprocity, F.dualLabel_involutive,
    F.fusion_comm i, F.fusion_reciprocity, F.dualLabel_involutive,
    F.fusion_comm k, F.fusion_reciprocity, F.dualLabel_involutive,
    F.fusion_comm j]
end SphericalFusion

/-- Loop fusion gives a character of the fusion ring on each simple channel. -/
theorem categoricalS_fusion_dual (F : SphericalFusion C) (i j k : F.Label) :
    (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) *
      categoricalS F (F.dualLabel r) k) =
    categoricalS F (F.dualLabel i) k * categoricalS F (F.dualLabel j) k /
      F.dimension (F.simple k) := by
  have h := congrArg (F.scalarTrace (F.simple k))
    (monodromyLoop_tensor F (F.simple i) (F.simple j) (F.simple k))
  rw [monodromyLoop_decomposition] at h
  simp only [map_sum, map_smul, monodromyLoop_simple_label,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    F.scalarTrace_id, smul_eq_mul] at h
  simp only [div_mul_cancel₀ _ (F.dimension_simple_ne_zero k)] at h
  change (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) *
    categoricalS F (F.dualLabel r) k) = _ at h
  rw [h]
  field_simp

/-- The categorical fusion eigenvalue identity; it needs no modularity assumption. -/
theorem categoricalS_fusion (F : SphericalFusion C) (i j k : F.Label) :
    (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) * categoricalS F r k) =
      categoricalS F i k * categoricalS F j k / F.dimension (F.simple k) := by
  have h := categoricalS_fusion_dual F (F.dualLabel i) (F.dualLabel j) k
  simp only [F.dualLabel_involutive i, F.dualLabel_involutive j] at h
  rw [← h]
  symm
  calc
    _ = ∑ r, (F.fusionMultiplicity (F.dualLabel i) (F.dualLabel j)
        (F.simple (F.dualLabel r)) : ℂ) * categoricalS F (F.dualLabel (F.dualLabel r)) k :=
      ((F.dualLabelEquiv).sum_comp _).symm
    _ = _ := by simp only [F.fusion_dual_all, F.dualLabel_involutive _]

/-- Fusion acts on row labels; this orientation fixes the diagonalization convention. -/
def fusionMatrix (F : SphericalFusion C) (i : F.Label) : Matrix F.Label F.Label ℂ :=
  fun j r => (F.fusionMultiplicity i j (F.simple r) : ℂ)

open Classical in
/-- The actual S matrix diagonalizes the actual fusion matrices. -/
theorem fusionMatrix_mul_categoricalS (F : SphericalFusion C) (i : F.Label) :
    fusionMatrix F i * categoricalS F = categoricalS F *
      Matrix.diagonal (fun k => categoricalS F i k / F.dimension (F.simple k)) := by
  classical
  ext j k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  change (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) * categoricalS F r k) = _
  rw [categoricalS_fusion]
  ring

open Classical in
/-- Categorical Verlinde, as matrix conjugation with the actual inverse S. -/
theorem categorical_verlinde_matrix (F : SphericalFusion C) (M : Modular F)
    (i : F.Label) :
    fusionMatrix F i = categoricalS F *
      Matrix.diagonal (fun k => categoricalS F i k / F.dimension (F.simple k)) *
        (categoricalS F)⁻¹ := by
  classical
  rw [← fusionMatrix_mul_categoricalS, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr M.nondegenerate), Matrix.mul_one]

open Classical in
/-- Entrywise categorical Verlinde, without an assumed numerical fusion rule. -/
theorem categorical_verlinde (F : SphericalFusion C) (M : Modular F)
    (i j r : F.Label) :
    (F.fusionMultiplicity i j (F.simple r) : ℂ) =
      ∑ k, categoricalS F j k * (categoricalS F i k / F.dimension (F.simple k)) *
        (categoricalS F)⁻¹ k r := by
  classical
  have h := congrArg (fun A : Matrix F.Label F.Label ℂ => A j r)
    (categorical_verlinde_matrix F M i)
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simpa only [fusionMatrix, Matrix.mul_diagonal] using h

end VOA.Huang.NgSchauenburg
