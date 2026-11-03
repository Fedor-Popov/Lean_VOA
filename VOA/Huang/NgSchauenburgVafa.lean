import VOA.Huang.NgSchauenburgDualSimples

/-! # Vafa's theorem from categorical channel determinants

The proof specializes the three-channel identity to `(i,i*,i,i)`. Its integer
exponent matrix has diagonal contribution `4d` and row sum `3d`, where `d>0`
is an actual triple-product Hom dimension. Strict dominance supplies torsion.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- The positive triple-product multiplicity in the Vafa specialization. -/
def vafaDegree (i : F.Label) : ℕ :=
  ∑ p, F.fusionMultiplicity i (F.dualLabel i) (F.simple p) *
    F.fusionMultiplicity p i (F.simple i)

/-- The sum of the three channel multiplicity products, all intrinsic dimensions. -/
def vafaRow (i p : F.Label) : ℕ :=
  F.fusionMultiplicity i (F.dualLabel i) (F.simple p) * F.fusionMultiplicity p i (F.simple i) +
  F.fusionMultiplicity i i (F.simple p) * F.fusionMultiplicity p (F.dualLabel i) (F.simple i) +
  F.fusionMultiplicity (F.dualLabel i) i (F.simple p) * F.fusionMultiplicity i p (F.simple i)

theorem vafaDegree_pos (i : F.Label) : 0 < F.vafaDegree i := F.vafa_row_pos i

theorem vafa_middle_sum (i : F.Label) :
    (∑ p, F.fusionMultiplicity i i (F.simple p) *
      F.fusionMultiplicity p (F.dualLabel i) (F.simple i)) = F.vafaDegree i := by
  classical
  rw [F.fusion_assoc]
  unfold vafaDegree
  congr 1
  funext p
  rw [F.fusion_comm i p]

theorem vafa_last_sum (i : F.Label) :
    (∑ p, F.fusionMultiplicity (F.dualLabel i) i (F.simple p) *
      F.fusionMultiplicity i p (F.simple i)) = F.vafaDegree i :=
  (F.fusion_assoc i (F.dualLabel i) i i).symm

/-- The categorical coefficient matrix has row sum exactly three times its degree. -/
theorem vafaRow_sum (i : F.Label) : ∑ p, F.vafaRow i p = 3 * F.vafaDegree i := by
  classical
  simp only [vafaRow, Finset.sum_add_distrib, F.vafa_middle_sum, F.vafa_last_sum]
  change F.vafaDegree i + F.vafaDegree i + F.vafaDegree i = _
  omega

end SphericalFusion

namespace Ribbon
variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- The dominant integer monomial relations, derived from categorical determinants. -/
theorem vafa_relation (i : F.Label) :
    R.twistScalar i ^ (4 * F.vafaDegree i) = ∏ p, R.twistScalar p ^ F.vafaRow i p := by
  classical
  have h := R.three_channel_determinant i (F.dualLabel i) i i
  simp only [R.twistScalar_dualLabel] at h
  have hc (p : F.Label) : R.twistScalar i / (R.twistScalar p * R.twistScalar i) =
      (R.twistScalar p)⁻¹ := by
    field_simp [R.twistScalar_ne_zero]
  simp only [hc, inv_pow, Finset.prod_inv_distrib, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, F.vafa_middle_sum, F.vafa_last_sum] at h
  have hn : (∏ p, R.twistScalar p ^
      (F.fusionMultiplicity i (F.dualLabel i) (F.simple p) *
        F.fusionMultiplicity p i (F.simple i))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (R.twistScalar_ne_zero p)
  have hi := R.twistScalar_ne_zero i
  field_simp [hi, hn] at h
  simp only [SphericalFusion.vafaRow, pow_add, Finset.prod_mul_distrib]
  simpa only [← pow_mul, show 2 * F.vafaDegree i * 2 = 4 * F.vafaDegree i by omega] using h

/-- Vafa torsion for every simple twist in a complex ribbon fusion category. -/
theorem twistScalar_isOfFinOrder (i : F.Label) : IsOfFinOrder (R.twistScalar i) := by
  classical
  let t : F.Label → ℂˣ := fun j => Units.mk0 (R.twistScalar j) (R.twistScalar_ne_zero j)
  have ht : ∀ j, IsOfFinOrder (t j) := finite_order_of_vafa_rows t F.vafaDegree F.vafaRow
    F.vafaDegree_pos F.vafaRow_sum (fun j => by
      apply Units.ext
      simpa [t] using R.vafa_relation j)
  obtain ⟨n, hn, hh⟩ := isOfFinOrder_iff_pow_eq_one.mp (ht i)
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  simpa [t] using congrArg (fun x : ℂˣ => (x : ℂ)) hh

/-- A uniform positive order annihilates the twist on every object. -/
theorem finite_twist : 0 < R.twistOrder ∧ ∀ X : C, R.twistPower X R.twistOrder = 𝟙 X :=
  R.finite_twist_of_simple_roots R.twistScalar_isOfFinOrder

end Ribbon

/-- The existing Vafa target is discharged with no additional premise. -/
theorem vafaTheorem_holds (F : SphericalFusion C) (M : Modular F) : VafaTheorem F M :=
  M.toRibbon.twistScalar_isOfFinOrder

end VOA.Huang.NgSchauenburg
