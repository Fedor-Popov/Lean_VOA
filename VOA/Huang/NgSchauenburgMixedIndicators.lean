import VOA.Huang.NgSchauenburgMixedCenter

/-! # The zero-second-index indicators of mixed central objects

This computes the genuine trace of the zeroth rotation power in every
positive degree from the base modular data. Nonzero second indices,
in particular the Bantay case, require a separate rotation-trace argument.
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

/-- Resolve the target of a fusion multiplicity by its actual simple summands. -/
theorem fusionMultiplicity_decomposition (F : SphericalFusion C) (i j : F.Label) (V : C) :
    F.fusionMultiplicity i j V = ∑ r,
      Module.finrank ℂ (F.simple r ⟶ V) * F.fusionMultiplicity i j (F.simple r) := by
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition V
  letI := F.homFinite
  unfold SphericalFusion.fusionMultiplicity
  rw [(F.homSourceDecomposition e _).finrank_eq, Module.finrank_pi_fintype]
  exact F.sum_decomposition e (fun r =>
    Module.finrank ℂ (F.simple r ⟶ F.simple i ⊗ F.simple j))

open Classical in
/-- Tensor-power multiplicities are the unit row of the fusion-matrix power. -/
theorem tensorPower_multiplicity_matrix (F : SphericalFusion C) (a r : F.Label) (n : ℕ) :
    (Module.finrank ℂ (F.simple r ⟶ tensorPower (F.simple a) n) : ℂ) =
      (fusionMatrix F a ^ n) F.unitLabel r := by
  induction n using Nat.twoStepInduction generalizing r with
  | zero =>
    change (Module.finrank ℂ (F.simple r ⟶ 𝟙_ C) : ℂ) = _
    rw [← (homCongr (Iso.refl (F.simple r)) F.unitIso).finrank_eq, F.finrank_hom_simple]
    simp [eq_comm, Matrix.one_apply]
  | one =>
    change (Module.finrank ℂ (F.simple r ⟶ F.simple a) : ℂ) = _
    rw [F.finrank_hom_simple]
    simp [fusionMatrix, F.fusion_comm a F.unitLabel, F.fusion_unit_left]
  | more n _ ih =>
    change (Module.finrank ℂ (F.simple r ⟶
      F.simple a ⊗ tensorPower (F.simple a) (n + 1)) : ℂ) = _
    rw [F.finrank_leftTensor, Nat.cast_sum, pow_succ, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_mul, ih k]
    rfl

open Classical in
/-- Every fusion-matrix power has the same categorical eigenvectors. -/
theorem fusionMatrix_pow (F : SphericalFusion C) (M : Modular F) (a : F.Label) (n : ℕ) :
    fusionMatrix F a ^ n = categoricalS F *
      Matrix.diagonal (fun k => (categoricalS F a k / F.dimension (F.simple k)) ^ n) *
        (categoricalS F)⁻¹ := by
  have h : fusionMatrix F a ^ n * categoricalS F = categoricalS F *
      Matrix.diagonal (fun k => (categoricalS F a k / F.dimension (F.simple k)) ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.mul_assoc, fusionMatrix_mul_categoricalS,
        ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      simp only [pow_succ]
  calc
    _ = (fusionMatrix F a ^ n * categoricalS F) * (categoricalS F)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr M.nondegenerate), Matrix.mul_one]
    _ = _ := by rw [h]

/-- The multiplicity of a simple in every tensor power, in base modular data. -/
theorem tensorPower_multiplicity_modular (F : SphericalFusion C) (M : Modular F)
    (a r : F.Label) (n : ℕ) :
    (Module.finrank ℂ (F.simple r ⟶ tensorPower (F.simple a) n) : ℂ) =
      F.globalDimension⁻¹ * ∑ k,
        F.dimension (F.simple k) *
          (categoricalS F a k / F.dimension (F.simple k)) ^ n *
            categoricalS F (F.dualLabel r) k := by
  classical
  rw [tensorPower_multiplicity_matrix, fusionMatrix_pow F M, Matrix.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal, categoricalS_unit_left F M.toRibbon,
    categoricalS_inv_apply F M, categoricalS_dual_left F M.toRibbon,
    categoricalS_symm F M.toRibbon k]
  ring

/-- A formula for actual generalized indicators on mixed objects for every
positive first index, restricted explicitly to second index zero. -/
theorem generalizedIndicatorInt_mixed_zero_modular (F : SphericalFusion C) (M : Modular F)
    (i j a : F.Label) (n : ℕ) :
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j))
      (F.simple a) n 0 =
      F.globalDimension⁻¹ * ∑ k,
        categoricalS F (F.dualLabel i) k * categoricalS F (F.dualLabel j) k *
          (categoricalS F a k / F.dimension (F.simple k)) ^ (n + 1) := by
  rw [generalizedIndicatorInt_mixed_zero, fusionMultiplicity_decomposition,
    Nat.cast_sum]
  simp only [Nat.cast_mul, tensorPower_multiplicity_modular F M, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = F.globalDimension⁻¹ *
        (F.dimension (F.simple k) *
          (categoricalS F a k / F.dimension (F.simple k)) ^ (n + 1)) *
        (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) *
          categoricalS F (F.dualLabel r) k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [categoricalS_fusion_dual]
      field_simp [F.dimension_simple_ne_zero]

end VOA.Huang.NgSchauenburg
