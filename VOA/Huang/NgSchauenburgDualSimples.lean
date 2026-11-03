import VOA.Huang.NgSchauenburgDeterminants

/-! # Dual labels and nonzero Vafa rows -/
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

/-- In this semisimple category, a one-dimensional endomorphism space detects a simple. -/
theorem exists_simple_iso_of_finrank_end (X : C)
    (h : Module.finrank ℂ (X ⟶ X) = 1) : ∃ i, Nonempty (X ≅ F.simple i) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  letI := fun k => F.homFinite X (F.simple (a k))
  have hs : ∑ k, Module.finrank ℂ (X ⟶ F.simple (a k)) = 1 := by
    rw [← Module.finrank_pi_fintype, ← (F.homDecomposition e X).finrank_eq, h]
  have hp (k : Fin n) : 1 ≤ Module.finrank ℂ (X ⟶ F.simple (a k)) := by
    letI := F.simple_isSimple (a k)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨e.hom ≫ biproduct.π _ k, ?_⟩
    intro hz
    have hh := congrArg (fun g => (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv) ≫ g) hz
    have : 𝟙 (F.simple (a k)) = 0 := by simpa using hh
    exact id_nonzero _ this
  have hn : n = 1 := by
    have hnle : n ≤ 1 := calc
      n = ∑ _k : Fin n, 1 := by simp
      _ ≤ ∑ k, Module.finrank ℂ (X ⟶ F.simple (a k)) := Finset.sum_le_sum fun k _ => hp k
      _ = 1 := hs
    have hn0 : n ≠ 0 := by intro hh; subst n; simp at hs
    omega
  subst n
  refine ⟨a 0, ⟨e ≪≫ ?_⟩⟩
  exact biproductUniqueIso (fun k => F.simple (a k))

/-- Rigidity gives equal dimensions of the endomorphism spaces of an object and its dual. -/
theorem finrank_end_dual (X : C) :
    Module.finrank ℂ (Xᘁ ⟶ Xᘁ) = Module.finrank ℂ (X ⟶ X) := by
  classical
  calc
    _ = Module.finrank ℂ (Xᘁ ⊗ (𝟙_ C) ⟶ Xᘁ) :=
      (homCongr (ρ_ Xᘁ).symm (Iso.refl Xᘁ)).finrank_eq
    _ = Module.finrank ℂ (𝟙_ C ⟶ X ⊗ Xᘁ) := (leftDuality (𝟙_ C) X Xᘁ).finrank_eq
    _ = Module.finrank ℂ ((𝟙_ C) ⊗ X ⟶ X) := (rightDuality (𝟙_ C) X X).finrank_eq.symm
    _ = _ := (homCongr (λ_ X) (Iso.refl X)).finrank_eq

/-- Duals of the specified simple objects occur in the specified simple family. -/
theorem exists_dualLabel (i : F.Label) : ∃ j, Nonempty ((F.simple i)ᘁ ≅ F.simple j) := by
  classical
  apply F.exists_simple_iso_of_finrank_end
  rw [finrank_end_dual, F.finrank_hom_simple]
  simp

/-- A chosen label for the right dual. -/
def dualLabel (i : F.Label) : F.Label := (F.exists_dualLabel i).choose

/-- The actual isomorphism pinning the dual label. -/
def dualLabelIso (i : F.Label) : (F.simple i)ᘁ ≅ F.simple (F.dualLabel i) :=
  (F.exists_dualLabel i).choose_spec.some

variable [BraidedCategory C]

/-- Commutativity of the actual fusion dimensions, induced by the braiding. -/
theorem fusion_comm (i j : F.Label) (Z : C) :
    F.fusionMultiplicity i j Z = F.fusionMultiplicity j i Z :=
  (homCongr (Iso.refl Z) (β_ (F.simple i) (F.simple j))).finrank_eq

/-- The unit occurs in the product of a simple and its labelled dual. -/
theorem fusion_dual_unit (i : F.Label) :
    F.fusionMultiplicity i (F.dualLabel i) (F.simple F.unitLabel) = 1 := by
  classical
  unfold fusionMultiplicity
  rw [(homCongr F.unitIso (whiskerLeftIso (F.simple i) (F.dualLabelIso i).symm)).finrank_eq]
  rw [← (rightDuality (𝟙_ C) (F.simple i) (F.simple i)).finrank_eq,
    (homCongr (λ_ (F.simple i)) (Iso.refl (F.simple i))).finrank_eq,
    F.finrank_hom_simple]
  simp

open Classical in
/-- The left unit has the expected fusion coefficient. -/
theorem fusion_unit_left (i r : F.Label) :
    F.fusionMultiplicity F.unitLabel i (F.simple r) = if r = i then 1 else 0 := by
  classical
  unfold fusionMultiplicity
  rw [(homCongr (Iso.refl (F.simple r))
    (whiskerRightIso F.unitIso (F.simple i) ≪≫ λ_ (F.simple i))).finrank_eq]
  exact F.finrank_hom_simple r i

/-- Positive dimension of the Vafa specialization `Hom(Xᵢ,(Xᵢ⊗Xᵢ*)⊗Xᵢ)`. -/
theorem vafa_row_pos (i : F.Label) :
    0 < ∑ p, F.fusionMultiplicity i (F.dualLabel i) (F.simple p) *
      F.fusionMultiplicity p i (F.simple i) := by
  classical
  have h := Finset.single_le_sum (fun p (_ : p ∈ Finset.univ) =>
    Nat.zero_le (F.fusionMultiplicity i (F.dualLabel i) (F.simple p) *
      F.fusionMultiplicity p i (F.simple i))) (Finset.mem_univ F.unitLabel)
  rw [F.fusion_dual_unit, F.fusion_unit_left] at h
  simpa using h

end SphericalFusion

namespace Ribbon
variable [BraidedCategory C] {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- Scalar multiplication commutes with the chosen right-adjoint mate. -/
theorem rightAdjointMate_smul {X Y : C} (z : ℂ) (f : X ⟶ Y) :
    (z • f)ᘁ = z • fᘁ := by
  classical
  simp [rightAdjointMate]

/-- Ribbon duality pins equal twist eigenvalues on dual labels. -/
theorem twistScalar_dualLabel (i : F.Label) : R.twistScalar (F.dualLabel i) = R.twistScalar i := by
  classical
  letI := F.simple_isSimple (F.dualLabel i)
  have h := R.naturality (F.dualLabelIso i).hom
  rw [R.dual, ← R.twistScalar_smul_id i, ← R.twistScalar_smul_id (F.dualLabel i),
    rightAdjointMate_smul, rightAdjointMate_id] at h
  have hh := congrArg (fun f => (F.dualLabelIso i).inv ≫ f) h
  apply smul_left_injective ℂ (id_nonzero (F.simple (F.dualLabel i)))
  simpa using hh

end Ribbon
end VOA.Huang.NgSchauenburg
