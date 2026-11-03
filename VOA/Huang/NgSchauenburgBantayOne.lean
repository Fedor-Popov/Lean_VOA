import VOA.Huang.NgSchauenburgBraidedAverage
import VOA.Huang.NgSchauenburgBalancing

/-! # The degree-one Bantay formula from the modular killing ring

The genuine indicator at degree one equals the twist-weighted fusion sum.
This is the degree-one case only; higher rotation traces remain separate.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion

/-- Pivotal duality makes the permutation of simple labels involutive. -/
theorem dualLabel_involutive (F : SphericalFusion C) : Function.Involutive F.dualLabel := by
  intro i
  apply F.distinct
  refine ⟨(F.dualLabelIso (F.dualLabel i)).symm ≪≫ ?_ ≪≫ (F.j (F.simple i)).symm⟩
  exact
    { hom := (F.dualLabelIso i).homᘁ
      inv := (F.dualLabelIso i).invᘁ
      hom_inv_id := by rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
      inv_hom_id := by rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id] }

/-- Duality is a permutation of the specified complete family. -/
def dualLabelEquiv (F : SphericalFusion C) : F.Label ≃ F.Label :=
  F.dualLabel_involutive.toPerm

end SphericalFusion

variable [BraidedCategory C]

/-- Reindexing the base-simple killing ring by duality keeps its dimensions. -/
theorem monodromy_killingRing_dual (F : SphericalFusion C) (M : Modular F) (X : C) :
    (∑ i, F.dimension (F.simple i) • monodromyLoop F.toPivotal (F.simple i)ᘁ X) =
      F.globalDimension • F.simpleProjector F.unitLabel X := by
  have hi (i : F.Label) : monodromyLoop F.toPivotal (F.simple i)ᘁ X =
      monodromyLoop F.toPivotal (F.simple (F.dualLabel i)) X := by
    have h := congrArg
      (fun L : Module.End ℂ (X ⟶ X) => L (𝟙 X))
      (halfBraidingLoop_iso F (oppositeBraidedCenter X) (Center.ofBraidedObj X)
        (F.dualLabelIso i))
    change halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
      (Center.ofBraidedObj X) (F.simple i)ᘁ (𝟙 X) =
      halfBraidingLoop F.toPivotal (oppositeBraidedCenter X)
        (Center.ofBraidedObj X) (F.simple (F.dualLabel i)) (𝟙 X) at h
    simpa only [halfBraidingLoop_braided_id] using h
  simp only [hi]
  conv_lhs => arg 2; intro i; rw [← F.dimension_dualLabel i]
  exact ((F.dualLabelEquiv).sum_comp
    (fun i => F.dimension (F.simple i) • monodromyLoop F.toPivotal (F.simple i) X)).trans
      (monodromy_killingRing F M X)

open Classical in
/-- Vacuum orthogonality for the actual categorical S matrix. -/
theorem categoricalS_dimension_sum (F : SphericalFusion C) (M : Modular F)
    (k : F.Label) :
    (∑ i, F.dimension (F.simple i) * categoricalS F i k) =
      if k = F.unitLabel then F.globalDimension else 0 := by
  have h := congrArg (F.scalarTrace (F.simple k))
    (monodromy_killingRing_dual F M (F.simple k))
  have hp : F.simpleProjector F.unitLabel (F.simple k) =
      if k = F.unitLabel then 𝟙 (F.simple k) else 0 := by
    simpa using F.comp_simpleProjector F.unitLabel k (𝟙 (F.simple k))
  simp only [map_sum, map_smul, monodromyLoop_simple, F.scalarTrace_id,
    smul_eq_mul, hp] at h
  simp only [div_mul_cancel₀ _ (F.dimension_simple_ne_zero k)] at h
  by_cases hk : k = F.unitLabel
  · subst k
    simpa using h
  · simpa [hk] using h

/-- The twist-weighted fusion sum is a weighted S column, before modularity
is used. This is categorical balancing and rigidity reciprocity. -/
theorem bantay_one_sum_eq_S (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (k : F.Label) :
    (∑ i, ∑ j, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
      F.dimension (F.simple i) * F.dimension (F.simple j) *
        (R.twistScalar i / R.twistScalar j)) =
      R.twistScalar k * ∑ j, F.dimension (F.simple j) * categoricalS F j k := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [R.categoricalS_balancing, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [F.fusion_comm i j, F.fusion_reciprocity j i k]
  field_simp [R.twistScalar_ne_zero]

open Classical in
/-- Degree-one Bantay numerator on each actual simple object. -/
theorem bantay_one_sum_simple (F : SphericalFusion C) (M : Modular F)
    (k : F.Label) :
    (∑ i, ∑ j, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
      F.dimension (F.simple i) * F.dimension (F.simple j) *
        (M.twistScalar i / M.twistScalar j)) =
      if k = F.unitLabel then F.globalDimension else 0 := by
  rw [bantay_one_sum_eq_S, categoricalS_dimension_sum F M]
  by_cases hk : k = F.unitLabel
  · subst k
    simp [M.toRibbon.twistScalar_unitLabel]
  · simp [hk]

/-- The degree-one case of the existing BantayFormula target, for every
object, with no indicator-exchange or center-factorization hypothesis. -/
theorem bantayFormula_one (F : SphericalFusion C) (M : Modular F) (V : C) :
    indicator F.toPivotal V 1 = F.globalDimension⁻¹ *
      ∑ i, ∑ j, (F.fusionMultiplicity i j V : ℂ) *
        F.dimension (F.simple i) * F.dimension (F.simple j) *
          (M.twistScalar i / M.twistScalar j) ^ 1 := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition V
  letI := F.homFinite
  have hn (i j : F.Label) : F.fusionMultiplicity i j V =
      ∑ k, F.fusionMultiplicity i j (F.simple (a k)) := by
    unfold SphericalFusion.fusionMultiplicity
    rw [(F.homSourceDecomposition e _).finrank_eq, Module.finrank_pi_fintype]
  have hu (i : F.Label) : Module.finrank ℂ (𝟙_ C ⟶ F.simple i) =
      if i = F.unitLabel then 1 else 0 := by
    rw [← (homCongr F.unitIso (Iso.refl (F.simple i))).finrank_eq,
      F.finrank_hom_simple]
    simp [eq_comm]
  rw [indicator_one, (F.homDecomposition e (𝟙_ C)).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [hn, Nat.cast_sum, pow_one, Finset.sum_mul]
  conv_rhs => arg 2; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => arg 2; rw [Finset.sum_comm]; arg 2; intro k; rw [Finset.sum_comm]
  simp only [bantay_one_sum_simple F M, hu]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [F.globalDimension_ne_zero]

end VOA.Huang.NgSchauenburg
