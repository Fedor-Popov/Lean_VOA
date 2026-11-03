import VOA.Huang.NgSchauenburgDimensions

/-! # The balancing formula for the actual categorical S matrix

No numerical balancing identity is assumed: the scalar sum is obtained by
taking the pivotal trace of the ribbon balancing equation on simple channels.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- Compute a categorical trace from eigenvalues on a supplied decomposition. -/
theorem trace_of_channel_projections {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (f : X ⟶ X) (t : Fin n → ℂ)
    (hf : ∀ k, f ≫ e.hom ≫ biproduct.π _ k = t k • (e.hom ≫ biproduct.π _ k)) :
    F.unitScalar.symm (F.traceRight f) = ∑ k, t k * F.dimension (F.simple (a k)) := by
  change F.unitScalar.symm (F.toPivotal.traceStructure.trL f) = _
  rw [← F.toPivotal.traceStructure.trL_conj e.symm f,
    F.toPivotal.traceStructure.trL_biproduct, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [hf]
  simp only [Linear.comp_smul, Iso.inv_hom_id_assoc, biproduct.ι_π_self,
    F.toPivotal.traceStructure.trL_smul, map_smul]
  rfl

end SphericalFusion
variable [BraidedCategory C]
namespace Ribbon
variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- The trace of double braiding is its fusion-channel sum. -/
theorem trace_monodromy (i j : F.Label) :
    F.unitScalar.symm (F.traceRight (monodromy (F.simple i) (F.simple j))) =
      ∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
        (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) *
        F.dimension (F.simple k) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition (F.simple i ⊗ F.simple j)
  rw [F.trace_of_channel_projections e _
    (fun k => R.twistScalar (a k) / (R.twistScalar i * R.twistScalar j))
    (fun k => R.monodromy_projection i j (a k) _)]
  simp only [SphericalFusion.fusionMultiplicity, F.multiplicity_eq_card e,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_mul, one_mul]
  rw [← Finset.sum_fiberwise_of_maps_to
    (f := fun k => R.twistScalar (a k) / (R.twistScalar i * R.twistScalar j) *
      F.dimension (F.simple (a k))) (fun k _ => Finset.mem_univ (a k))]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b hb => by
    rw [(Finset.mem_filter.mp hb).2]

/-- Balancing for S with the specified dual on its first index. -/
theorem categoricalS_balancing (i j : F.Label) :
    categoricalS F i j =
      ∑ k, (F.fusionMultiplicity (F.dualLabel i) j (F.simple k) : ℂ) *
        (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) *
        F.dimension (F.simple k) := by
  have hc : (F.dualLabelIso i).hom ▷ F.simple j ≫
      monodromy (F.simple (F.dualLabel i)) (F.simple j) ≫
      (F.dualLabelIso i).inv ▷ F.simple j =
      monodromy (F.simple i)ᘁ (F.simple j) := by
    simp [monodromy, ← comp_whiskerRight]
  change F.unitScalar.symm (F.toPivotal.traceStructure.trL
    (monodromy (F.simple i)ᘁ (F.simple j))) = _
  have ht := F.toPivotal.traceStructure.trL_conj
    (whiskerRightIso (F.dualLabelIso i) (F.simple j))
    (monodromy (F.simple (F.dualLabel i)) (F.simple j))
  dsimp only [whiskerRightIso] at ht
  rw [← hc, ht]
  change F.unitScalar.symm (F.traceRight _) = _
  rw [R.trace_monodromy, R.twistScalar_dualLabel]

end Ribbon
end VOA.Huang.NgSchauenburg
