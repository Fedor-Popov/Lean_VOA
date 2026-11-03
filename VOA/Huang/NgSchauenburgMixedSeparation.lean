import VOA.Huang.NgSchauenburgMixedModular

/-! # A precise separation statement using categorical Verlinde

The common commutant of fusion and its S conjugate consists of scalars.
This is a separation theorem on base-label matrices; it does not assert that
the mixed indicator functionals span the full square-dimensional dual space.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg

section Matrices
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Invertibility separates normalized columns; no assumption on distinct twists. -/
theorem normalized_columns_separate (S : Matrix I I ℂ) (hS : IsUnit S)
    (d : I → ℂ) (hd : ∀ i, d i ≠ 0) (k l : I)
    (h : ∀ i, S i k / d k = S i l / d l) : k = l := by
  have he : S.mulVec (Pi.single k (d k)⁻¹) = S.mulVec (Pi.single l (d l)⁻¹) := by
    ext i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, div_eq_mul_inv] using h i
  have hv := Matrix.mulVec_injective_of_isUnit hS he
  by_contra hn
  have hk := congrFun hv k
  simp [hn, hd k] at hk

/-- Commuting with the full set of normalized character diagonals forces diagonal form. -/
theorem diagonal_of_commute_characters (S : Matrix I I ℂ) (hS : IsUnit S)
    (d : I → ℂ) (hd : ∀ i, d i ≠ 0) (A : Matrix I I ℂ)
    (h : ∀ i, A * Matrix.diagonal (fun k => S i k / d k) =
      Matrix.diagonal (fun k => S i k / d k) * A) :
    A = Matrix.diagonal (fun k => A k k) := by
  ext k l
  by_cases he : k = l
  · subst l; simp
  · rw [Matrix.diagonal_apply_ne _ he]
    by_contra hn
    apply he
    apply normalized_columns_separate S hS d hd k l
    intro i
    have hi := congrArg (fun B : Matrix I I ℂ => B k l) (h i)
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hi
    apply mul_left_cancel₀ hn
    calc
      A k l * (S i k / d k) = (S i k / d k) * A k l := mul_comm _ _
      _ = _ := hi.symm
end Matrices

open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The fusion commutant is diagonal in the actual categorical S basis. -/
theorem fusion_commutant_diagonal (F : SphericalFusion C) (M : Modular F)
    (A : Matrix F.Label F.Label ℂ)
    (h : ∀ i, A * fusionMatrix F i = fusionMatrix F i * A) :
    ∃ d, (categoricalS F)⁻¹ * A * categoricalS F = Matrix.diagonal d := by
  refine ⟨fun k => ((categoricalS F)⁻¹ * A * categoricalS F) k k, ?_⟩
  apply diagonal_of_commute_characters (categoricalS F)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr M.nondegenerate))
    (fun k => F.dimension (F.simple k)) F.dimension_simple_ne_zero
  intro i
  have hi := congrArg (fun B : Matrix F.Label F.Label ℂ =>
    (categoricalS F)⁻¹ * B * categoricalS F) (h i)
  rw [categorical_verlinde_matrix F M] at hi
  have hs := isUnit_iff_ne_zero.mpr M.nondegenerate
  simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hs,
    Matrix.nonsing_inv_mul _ hs, Matrix.mul_one] using hi

open Classical in
/-- A diagonal fusion-commuting matrix is scalar, detected on the vacuum row. -/
theorem scalar_of_diagonal_fusion_commutant (F : SphericalFusion C)
    (d : F.Label → ℂ)
    (h : ∀ i, Matrix.diagonal d * fusionMatrix F i =
      fusionMatrix F i * Matrix.diagonal d) :
    Matrix.diagonal d = d F.unitLabel • (1 : Matrix F.Label F.Label ℂ) := by
  have hd (i : F.Label) : d i = d F.unitLabel := by
    have hi := congrArg (fun A : Matrix F.Label F.Label ℂ => A F.unitLabel i) (h i)
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, fusionMatrix,
      F.fusion_comm i F.unitLabel, F.fusion_unit_left] at hi
    exact hi.symm
  ext i j
  simp [hd, Matrix.diagonal_apply, Matrix.one_apply]

open Classical in
/-- Exact sufficient separation: commuting with fusion and its S conjugate
forces a scalar. This requires no spherical fusion structure on the center. -/
theorem scalar_of_fusion_and_S_commutants (F : SphericalFusion C) (M : Modular F)
    (A : Matrix F.Label F.Label ℂ)
    (h : ∀ i, A * fusionMatrix F i = fusionMatrix F i * A)
    (hS : ∀ i, (categoricalS F * A * (categoricalS F)⁻¹) * fusionMatrix F i =
      fusionMatrix F i * (categoricalS F * A * (categoricalS F)⁻¹)) :
    ∃ c : ℂ, A = c • (1 : Matrix F.Label F.Label ℂ) := by
  obtain ⟨d, hd⟩ := fusion_commutant_diagonal F M _ hS
  have hs := isUnit_iff_ne_zero.mpr M.nondegenerate
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hs,
    Matrix.nonsing_inv_mul _ hs, Matrix.mul_one] at hd
  refine ⟨d F.unitLabel, hd.trans (scalar_of_diagonal_fusion_commutant F d ?_)⟩
  intro i
  rw [← hd]
  exact h i

end VOA.Huang.NgSchauenburg
