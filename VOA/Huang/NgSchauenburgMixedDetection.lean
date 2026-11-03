import VOA.Huang.NgSchauenburgMixedSeparation
import VOA.Huang.NgSchauenburgMixedIndicators

/-! # Mixed indicator detection of scalar matrices

Only the actual (1,0) indicators on mixed objects are used. Their invariance
for a matrix and its S conjugate is sufficient to force that matrix scalar.
No claim that all mixed indicator functionals span the full dual space is needed.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg

section Matrices
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Row invariance under the double is exactly commutation with a pairing matrix. -/
theorem matrixDouble_row_invariant_iff (A : (Matrix I I ℂ)ˣ) (H : Matrix I I ℂ) :
    (∀ k l, (∑ p : I × I, H p.1 p.2 * matrixDouble A p (k, l)) = H k l) ↔
      (A : Matrix I I ℂ).transpose * H = H * (A : Matrix I I ℂ).transpose := by
  have he (k l : I) :
      (∑ p : I × I, H p.1 p.2 * matrixDouble A p (k, l)) =
        ((A : Matrix I I ℂ).transpose * H * (↑A⁻¹ : Matrix I I ℂ).transpose) k l := by
    rw [Fintype.sum_prod_type, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change H j i * ((A : Matrix I I ℂ) j k * (↑A⁻¹ : Matrix I I ℂ) l i) =
      ((A : Matrix I I ℂ) j k * H j i) * (↑A⁻¹ : Matrix I I ℂ) l i
    ring
  have hl : (↑A⁻¹ : Matrix I I ℂ).transpose * (A : Matrix I I ℂ).transpose = 1 := by
    rw [← Matrix.transpose_mul]; simp
  have hr : (A : Matrix I I ℂ).transpose * (↑A⁻¹ : Matrix I I ℂ).transpose = 1 := by
    rw [← Matrix.transpose_mul]; simp
  simp only [he]
  constructor
  · intro h
    have hh : (A : Matrix I I ℂ).transpose * H * (↑A⁻¹ : Matrix I I ℂ).transpose = H :=
      Matrix.ext h
    have h' := congrArg (fun B => B * (A : Matrix I I ℂ).transpose) hh
    simpa only [Matrix.mul_assoc, hl, Matrix.mul_one] using h'
  · intro h k l
    have hh : (A : Matrix I I ℂ).transpose * H * (↑A⁻¹ : Matrix I I ℂ).transpose = H := by
      rw [h, Matrix.mul_assoc, hr, Matrix.mul_one]
    exact congrArg (fun B : Matrix I I ℂ => B k l) hh
end Matrices

open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The pair multiplicities are the actual mixed indicators at (1,0). -/
theorem mixed_indicator_one_zero (F : SphericalFusion C) (a i j : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
      (F.simple a) 1 0 = (F.fusionMultiplicity i j (F.simple a) : ℂ) := by
  rw [show (1 : ℤ) = (0 : ℕ) + 1 by rfl, generalizedIndicatorAll_positive,
    generalizedIndicatorInt_mixed_zero]
  rfl

open Classical in
/-- The mixed (1,0) row is charge conjugation times the fusion matrix. -/
theorem mixed_indicator_one_zero_matrix (F : SphericalFusion C) (a : F.Label) :
    (fun i j => generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
      (F.simple a) 1 0) = chargeConjugation F * fusionMatrix F a := by
  ext i j
  simp only [Matrix.mul_apply, chargeConjugation, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), mixed_indicator_one_zero]
  change (F.fusionMultiplicity i j (F.simple a) : ℂ) =
    (F.fusionMultiplicity a (F.dualLabel i) (F.simple j) : ℂ)
  rw [F.fusion_reciprocity, F.fusion_comm]

open Classical in
/-- Invariance of all actual mixed (1,0) rows forces the transpose to commute with fusion. -/
theorem fusion_commutant_of_mixed_indicator_invariance (F : SphericalFusion C)
    (A : (Matrix F.Label F.Label ℂ)ˣ)
    (h : ∀ a k l, (∑ p : F.Label × F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 * matrixDouble A p (k, l)) =
      generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l))
        (F.simple a) 1 0) :
    ∀ i, (A : Matrix F.Label F.Label ℂ).transpose * fusionMatrix F i =
      fusionMatrix F i * (A : Matrix F.Label F.Label ℂ).transpose := by
  have hh (a : F.Label) := (matrixDouble_row_invariant_iff A
    (fun i j => generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
      (F.simple a) 1 0)).mp (h a)
  simp only [mixed_indicator_one_zero_matrix] at hh
  have h0 : fusionMatrix F F.unitLabel = 1 := by
    ext i j
    simp [fusionMatrix, F.fusion_unit_left, Matrix.one_apply, eq_comm]
  have hc := hh F.unitLabel
  rw [h0, Matrix.mul_one] at hc
  intro i
  have hi := congrArg (fun B => chargeConjugation F * B) (hh i)
  rw [← Matrix.mul_assoc (A : Matrix F.Label F.Label ℂ).transpose, hc] at hi
  simpa only [← Matrix.mul_assoc, chargeConjugation_sq, Matrix.one_mul] using hi

open Classical in
/-- The exact separation needed for the modular route: (1,0)-row invariance
for A and its S conjugate forces A to be a nonzero scalar. Both invariance
premises concern genuine categorical indicators, not an arbitrary family. -/
theorem scalar_of_mixed_indicator_invariance (F : SphericalFusion C) (M : Modular F)
    (A : (Matrix F.Label F.Label ℂ)ˣ)
    (h : ∀ a k l, (∑ p : F.Label × F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 * matrixDouble A p (k, l)) =
      generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l))
        (F.simple a) 1 0)
    (hS : ∀ a k l, (∑ p : F.Label × F.Label,
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 *
          matrixDouble ((categoricalSUnit F M)⁻¹ * A * categoricalSUnit F M) p (k, l)) =
      generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l))
        (F.simple a) 1 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (A : Matrix F.Label F.Label ℂ) = c • 1 := by
  have hs : (categoricalS F).transpose = categoricalS F := by
    ext i j
    exact categoricalS_symm F M.toRibbon j i
  have ht := fusion_commutant_of_mixed_indicator_invariance F _ hS
  change ∀ i, ((categoricalS F)⁻¹ * (A : Matrix F.Label F.Label ℂ) *
    categoricalS F).transpose * fusionMatrix F i = fusionMatrix F i *
      ((categoricalS F)⁻¹ * (A : Matrix F.Label F.Label ℂ) * categoricalS F).transpose at ht
  simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs, ← Matrix.mul_assoc] at ht
  obtain ⟨c, hc⟩ := scalar_of_fusion_and_S_commutants F M
    (A : Matrix F.Label F.Label ℂ).transpose
    (fusion_commutant_of_mixed_indicator_invariance F A h)
    (fun i => by simpa only [Matrix.mul_assoc] using ht i)
  have ha : (A : Matrix F.Label F.Label ℂ) = c • 1 := by
    have he := congrArg Matrix.transpose hc
    simpa only [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] using he
  refine ⟨c, ?_, ha⟩
  intro hz
  have hone : (1 : Matrix F.Label F.Label ℂ) = 0 := by
    calc
      _ = (A : Matrix F.Label F.Label ℂ) * (↑A⁻¹ : Matrix F.Label F.Label ℂ) := by simp
      _ = 0 := by rw [ha, hz, zero_smul, Matrix.zero_mul]
  have he := congrArg (fun B : Matrix F.Label F.Label ℂ => B F.unitLabel F.unitLabel) hone
  simp at he

end VOA.Huang.NgSchauenburg
