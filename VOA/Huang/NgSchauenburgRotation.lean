import VOA.Huang.NgSchauenburgIndicators

/-! # Coherence of the degree-one pivotal rotation

The chosen dual of the unit need not be definitionally the unit.  The
evaluation characterization of `dualUnit` is used explicitly below.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

theorem Pivotal.unit_evaluation (P : Pivotal C) :
    ε_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ (𝟙_ C)ᘁ).hom ≫ P.dualUnit.inv := by
  apply (cancel_epi (P.dualUnit.hom ▷ (𝟙_ C))).mp
  rw [P.dualUnit_eval, rightUnitor_naturality_assoc]
  simp only [Iso.hom_inv_id, Category.comp_id]
  monoidal_coherence

theorem Pivotal.unit_coevaluation (P : Pivotal C) :
    η_ (𝟙_ C) (𝟙_ C)ᘁ = P.dualUnit.hom ≫ (λ_ (𝟙_ C)ᘁ).inv := by
  have h := tensorRightHomEquiv_whiskerRight_comp_evaluation P.dualUnit.hom
  rw [P.dualUnit_eval] at h
  simpa [tensorRightHomEquiv, unitors_equal] using h

/-- Bending a morphism out of the unit is its right mate, with the
chosen dual-unit comparison removed. -/
theorem bend_unit (P : Pivotal C) {V : C} (f : 𝟙_ C ⟶ V) :
    (ρ_ Vᘁ).inv ≫ (leftDuality (𝟙_ C) V (𝟙_ C)).symm
      (f ≫ (ρ_ V).inv) = fᘁ ≫ P.dualUnit.inv := by
  have h := rightAdjointMate_comp_evaluation f
  rw [P.unit_evaluation, rightUnitor_naturality_assoc] at h
  calc
    _ = (ρ_ Vᘁ).inv ≫ Vᘁ ◁ f ≫ ε_ V Vᘁ := by
      dsimp [leftDuality, tensorLeftHomEquiv]
      monoidal
    _ = _ := by rw [← h]; simp

/-- The second bend is the right mate, with the dual-unit comparison inserted. -/
theorem unbend_unit (P : Pivotal C) {V : C} (g : Vᘁ ⟶ 𝟙_ C) :
    η_ Vᘁ (Vᘁ)ᘁ ≫ g ▷ (Vᘁ)ᘁ ≫ (λ_ (Vᘁ)ᘁ).hom =
      P.dualUnit.hom ≫ gᘁ := by
  rw [← coevaluation_comp_rightAdjointMate_assoc, P.unit_coevaluation]
  simp

/-- The unreduced degree-one rotation agrees with the identity convention. -/
theorem rotation_unit (P : Pivotal C) {V : C} (f : 𝟙_ C ⟶ V) :
    rotation P V (𝟙_ C) (f ≫ (ρ_ V).inv) ≫ (λ_ V).hom = f := by
  have hb := bend_unit P f
  have hu := unbend_unit P (fᘁ ≫ P.dualUnit.inv)
  have hn := P.naturality f
  rw [P.unit] at hn
  calc
    _ = η_ Vᘁ (Vᘁ)ᘁ ≫
        ((ρ_ Vᘁ).inv ≫ (leftDuality (𝟙_ C) V (𝟙_ C)).symm
          (f ≫ (ρ_ V).inv)) ▷ (Vᘁ)ᘁ ≫ (λ_ (Vᘁ)ᘁ).hom ≫ (P.j V).inv := by
      dsimp [rotation, homCongr, rightDuality, tensorRightHomEquiv]
      monoidal
    _ = P.dualUnit.hom ≫ (P.dualUnit.inv)ᘁ ≫ (fᘁ)ᘁ ≫ (P.j V).inv := by
      rw [hb, reassoc_of% hu, comp_rightAdjointMate]
      simp
    _ = f := by rw [← Category.assoc, ← Category.assoc, ← hn]; simp

/-- The literal unreduced diagram, as an equivalence of the invariant space. -/
def unreducedRotationOne (P : Pivotal C) (V : C) :
    (𝟙_ C ⟶ V) ≃ₗ[ℂ] (𝟙_ C ⟶ V) :=
  (homCongr (Iso.refl _) (ρ_ V).symm).trans
    ((rotation P V (𝟙_ C)).trans (homCongr (Iso.refl _) (λ_ V)))

theorem unreducedRotationOne_eq (P : Pivotal C) (V : C) :
    unreducedRotationOne P V = fsRotation P V 1 := by
  ext f
  simpa [unreducedRotationOne, homCongr, fsRotation] using rotation_unit P f

/-- At the central unit the half-braiding is exactly the unitor change
used by the ordinary rotation. -/
theorem centerRotation_unit (P : Pivotal C) (V W : C) :
    centerRotation P (𝟙_ (Center C)) V W = rotation P V W := rfl

/-- Agreement of ordinary and generalized single rotations at every positive
first index, including the degree-one comparison. -/
theorem generalizedRotation_unit (P : Pivotal C) (V : C) (n : ℕ) :
    generalizedRotation P (𝟙_ (Center C)) V n = fsRotation P V (n + 1) := by
  cases n with
  | zero => exact unreducedRotationOne_eq P V
  | succ n => rfl

end VOA.Huang.NgSchauenburg
