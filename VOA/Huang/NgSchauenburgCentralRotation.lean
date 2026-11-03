import VOA.Huang.NgSchauenburgGeneralizedTwist
import VOA.Huang.NgSchauenburgRotationOrder

/-! # Tensor-block composition for rotations with a central source -/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- Cup-cap expression for rotation with an arbitrary central source. -/
theorem centerRotation_eq_cup (P : Pivotal C) (A : Center C) {X Y : C}
    (f : A.1 ⟶ X ⊗ Y) :
    centerRotation P A X Y f =
      (ρ_ A.1).inv ≫ A.1 ◁ P.cup X ≫ (α_ A.1 Xᘁ X).inv ≫
        (A.2.β Xᘁ).hom ▷ X ≫ ((leftDuality A.1 X Y).symm f) ▷ X := by
  calc
    _ = (ρ_ A.1).inv ≫ A.1 ◁ η_ Xᘁ (Xᘁ)ᘁ ≫ (α_ A.1 Xᘁ (Xᘁ)ᘁ).inv ≫
        (A.2.β Xᘁ).hom ▷ (Xᘁ)ᘁ ≫ ((leftDuality A.1 X Y).symm f) ▷ (Xᘁ)ᘁ ≫
        Y ◁ (P.j X).inv := by
      dsimp [centerRotation, homCongr, rightDuality, tensorRightHomEquiv]
      monoidal
    _ = _ := by
      dsimp [Pivotal.cup]
      simp only [whiskerLeft_comp, Category.assoc]
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        whisker_exchange]


/-- Bending a tensor block with an arbitrary source. -/
theorem centerBend_tensor (P : Pivotal C) {A X Y Z : C} (f : A ⟶ (X ⊗ Y) ⊗ Z) :
    (P.dualTensor X Y).hom ▷ A ≫ (leftDuality A (X ⊗ Y) Z).symm f =
      (α_ Yᘁ Xᘁ A).hom ≫
        (leftDuality (Xᘁ ⊗ A) Y Z).symm
          ((leftDuality A X (Y ⊗ Z)).symm (f ≫ (α_ X Y Z).hom)) := by
  dsimp [leftDuality, tensorLeftHomEquiv]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, P.dualTensor_eval]
  dsimp [tensorDualEvaluation]
  monoidal

/-- Moving a tensor block equals moving its two factors successively. -/
theorem centerRotation_tensor (P : Pivotal C) (A : Center C) {X Y Z : C}
    (f : A.1 ⟶ (X ⊗ Y) ⊗ Z) :
    centerRotation P A (X ⊗ Y) Z f =
      centerRotation P A Y (Z ⊗ X)
        (centerRotation P A X (Y ⊗ Z) (f ≫ (α_ X Y Z).hom) ≫ (α_ Y Z X).hom) ≫
      (α_ Z X Y).hom := by
  rw [centerRotation_eq_cup]
  calc
    _ = (ρ_ A.1).inv ≫
        A.1 ◁ (P.cup (X ⊗ Y) ≫ (P.dualTensor X Y).inv ▷ (X ⊗ Y)) ≫
        (α_ A.1 (Yᘁ ⊗ Xᘁ) (X ⊗ Y)).inv ≫
        (A.2.β (Yᘁ ⊗ Xᘁ)).hom ▷ (X ⊗ Y) ≫
        ((P.dualTensor X Y).hom ▷ A.1 ≫
          (leftDuality A.1 (X ⊗ Y) Z).symm f) ▷ (X ⊗ Y) := by
      simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      rw [associator_inv_naturality_middle_assoc,
        ← comp_whiskerRight_assoc, A.2.naturality]
      simp
    _ = _ := by
      rw [P.cup_tensor, centerBend_tensor, A.2.monoidal]
      let b := (leftDuality (Xᘁ ⊗ A.1) Y Z).symm
        ((leftDuality A.1 X (Y ⊗ Z)).symm (f ≫ (α_ X Y Z).hom))
      let h := (α_ Yᘁ A.1 (Xᘁ ⊗ X)).hom ▷ Y ≫
        (Yᘁ ◁ (α_ A.1 Xᘁ X).inv) ▷ Y ≫
        (Yᘁ ◁ ((A.2.β Xᘁ).hom ▷ X)) ▷ Y ≫
        (α_ Yᘁ (Xᘁ ⊗ A.1) X).inv ▷ Y ≫
        (α_ (Yᘁ ⊗ (Xᘁ ⊗ A.1)) X Y).hom ≫ b ▷ (X ⊗ Y)
      calc
        _ = (ρ_ A.1).inv ≫ A.1 ◁ P.cup Y ≫ (α_ A.1 Yᘁ Y).inv ≫
            ((ρ_ (A.1 ⊗ Yᘁ)).inv ≫ (A.1 ⊗ Yᘁ) ◁ P.cup X ≫
              (A.2.β Yᘁ).hom ▷ (Xᘁ ⊗ X)) ▷ Y ≫ h := by
          dsimp [h, b]
          monoidal
        _ = (ρ_ A.1).inv ≫ A.1 ◁ P.cup Y ≫ (α_ A.1 Yᘁ Y).inv ≫
            ((A.2.β Yᘁ).hom ≫ (ρ_ (Yᘁ ⊗ A.1)).inv ≫
              (Yᘁ ⊗ A.1) ◁ P.cup X) ▷ Y ≫ h := by
          rw [whisker_exchange, rightUnitor_inv_naturality_assoc]
        _ = _ := by
          simp only [centerRotation_eq_cup]
          dsimp [h, b, leftDuality, tensorLeftHomEquiv]
          monoidal

/-- Naturality in the block that stays on the left after rotation. -/
theorem centerRotation_naturality_right (P : Pivotal C) (A : Center C) {X Y Z : C}
    (f : A.1 ⟶ X ⊗ Y) (g : Y ⟶ Z) :
    centerRotation P A X Z (f ≫ X ◁ g) = centerRotation P A X Y f ≫ g ▷ X := by
  simp only [centerRotation_eq_cup]
  dsimp [leftDuality, tensorLeftHomEquiv]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]
  simp

/-- Naturality in the block being moved. -/
theorem centerRotation_naturality_left (P : Pivotal C) (A : Center C) {X Y Z : C}
    (f : A.1 ⟶ X ⊗ Z) (g : X ⟶ Y) :
    centerRotation P A Y Z (f ≫ g ▷ Z) = centerRotation P A X Z f ≫ Z ◁ g := by
  have hb : (leftDuality A.1 Y Z).symm (f ≫ g ▷ Z) =
      gᘁ ▷ A.1 ≫ (leftDuality A.1 X Z).symm f := by
    dsimp [leftDuality, tensorLeftHomEquiv]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation, comp_whiskerRight]
    monoidal
  simp only [centerRotation_eq_cup, hb, comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← A.2.naturality,
    comp_whiskerRight, Category.assoc, ← associator_inv_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, P.cup_naturality]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    whisker_exchange]

/-- Rotating both blocks once is one degree-one rotation of the entire output. -/
theorem centerRotation_rotation (P : Pivotal C) (A : Center C) {X Y : C}
    (f : A.1 ⟶ X ⊗ Y) :
    centerRotation P A Y X (centerRotation P A X Y f) =
      generalizedRotation P A (X ⊗ Y) 0 f := by
  have h := congrArg (fun g => g ≫ (λ_ (X ⊗ Y)).hom)
    (centerRotation_tensor P A (f ≫ (ρ_ (X ⊗ Y)).inv))
  have h₁ : (f ≫ (ρ_ (X ⊗ Y)).inv) ≫ (α_ X Y (𝟙_ C)).hom =
      f ≫ X ◁ (ρ_ Y).inv := by monoidal
  rw [h₁, centerRotation_naturality_right] at h
  have h₂ : (centerRotation P A X Y f ≫ (ρ_ Y).inv ▷ X) ≫ (α_ Y (𝟙_ C) X).hom =
      centerRotation P A X Y f ≫ Y ◁ (λ_ X).inv := by monoidal
  rw [h₂, centerRotation_naturality_right] at h
  simpa [generalizedRotation, homCongr] using h.symm

/-- Rotation with unit output is the identity, even for a nontrivial central source. -/
theorem generalizedRotation_unit_output (P : Pivotal C) (A : Center C)
    (f : A.1 ⟶ 𝟙_ C) : generalizedRotation P A (𝟙_ C) 0 f = f := by
  have h (g : A.1 ⟶ (𝟙_ C) ⊗ (𝟙_ C)) :
      centerRotation P A (𝟙_ C) (𝟙_ C) g =
        centralDrinfeldMorphism A ≫ (P.j A.1).inv ≫ g := by
    apply (cancel_mono (λ_ (𝟙_ C)).hom).mp
    have he := generalizedRotation_one_centralDrinfeld P A (𝟙_ C)
      (g ≫ (λ_ (𝟙_ C)).hom)
    change 𝟙 _ ≫ centerRotation P A (𝟙_ C) (𝟙_ C)
      (𝟙 _ ≫ (g ≫ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (𝟙_ C)).inv) ≫
        (λ_ (𝟙_ C)).hom = _ at he
    simpa [unitors_equal, Category.assoc] using he
  have he (g : A.1 ⟶ (𝟙_ C) ⊗ (𝟙_ C)) :
      centerRotation P A (𝟙_ C) (𝟙_ C) g = g := by
    apply (centerRotation P A (𝟙_ C) (𝟙_ C)).injective
    rw [centerRotation_rotation, generalizedRotation_one_centralDrinfeld, h]
  change 𝟙 _ ≫ centerRotation P A (𝟙_ C) (𝟙_ C)
    (𝟙 _ ≫ f ≫ (ρ_ (𝟙_ C)).inv) ≫ (λ_ (𝟙_ C)).hom = _
  rw [he]
  simp [unitors_equal]

/-- On maps to the unit the inverse central twist acts trivially. -/
theorem centralDrinfeld_unit_output (P : Pivotal C) (A : Center C) (f : A.1 ⟶ 𝟙_ C) :
    centralDrinfeldMorphism A ≫ (P.j A.1).inv ≫ f = f := by
  rw [← generalizedRotation_one_centralDrinfeld, generalizedRotation_unit_output]

end VOA.Huang.NgSchauenburg
