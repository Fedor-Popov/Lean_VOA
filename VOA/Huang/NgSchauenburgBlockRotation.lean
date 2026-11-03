import VOA.Huang.NgSchauenburgDualCoherence

/-! # Tensor-block composition of pivotal rotations -/

noncomputable section
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The cup with the pivotal identification on its second output. -/
def Pivotal.cup (P : Pivotal C) (X : C) : 𝟙_ C ⟶ Xᘁ ⊗ X :=
  η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ (P.j X).inv

/-- Inverse form of the monoidality equation. -/
theorem Pivotal.monoidal_inv (P : Pivotal C) (X Y : C) :
    (P.j (X ⊗ Y)).inv = ((P.dualTensor X Y).hom)ᘁ ≫
      (P.dualTensor Yᘁ Xᘁ).inv ≫ ((P.j X).inv ⊗ₘ (P.j Y).inv) := by
  apply (cancel_epi (P.j (X ⊗ Y)).hom).mp
  rw [Iso.hom_inv_id, P.monoidal]
  have hc : (P.dualTensor X Y).invᘁ ≫ (P.dualTensor X Y).homᘁ = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id]
  simp only [Category.assoc, reassoc_of% hc, Iso.hom_inv_id_assoc]
  simp

/-- The pivotal cup on a tensor product is the nested pair of pivotal cups. -/
theorem Pivotal.cup_tensor (P : Pivotal C) (X Y : C) :
    P.cup (X ⊗ Y) ≫ (P.dualTensor X Y).inv ▷ (X ⊗ Y) =
      P.cup Y ≫ Yᘁ ◁ (λ_ Y).inv ≫ Yᘁ ◁ (P.cup X ▷ Y) ≫
        Yᘁ ◁ (α_ Xᘁ X Y).hom ≫ (α_ Yᘁ Xᘁ (X ⊗ Y)).inv := by
  calc
    _ = η_ (Yᘁ ⊗ Xᘁ) (Yᘁ ⊗ Xᘁ)ᘁ ≫
        (Yᘁ ⊗ Xᘁ) ◁ (P.dualTensor Yᘁ Xᘁ).inv ≫
        (Yᘁ ⊗ Xᘁ) ◁ ((P.j X).inv ⊗ₘ (P.j Y).inv) := by
      rw [Pivotal.cup, P.monoidal_inv]
      simp only [whiskerLeft_comp, Category.assoc]
      rw [coevaluation_comp_rightAdjointMate_assoc]
      rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
      simp
    _ = _ := by
      rw [← P.dualTensor_coevaluation Yᘁ Xᘁ]
      simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
        whiskerLeft_id, Category.id_comp]
      dsimp [Pivotal.cup]
      have h := leftUnitor_inv_naturality (P.j Y).inv
      have hx := whisker_exchange (η_ Xᘁ (Xᘁ)ᘁ) (P.j Y).inv
      calc
        _ = η_ Yᘁ (Yᘁ)ᘁ ≫ Yᘁ ◁ (λ_ (Yᘁ)ᘁ).inv ≫
            Yᘁ ◁ (η_ Xᘁ (Xᘁ)ᘁ ▷ (Yᘁ)ᘁ ≫
              (Xᘁ ⊗ (Xᘁ)ᘁ) ◁ (P.j Y).inv) ≫
            Yᘁ ◁ ((Xᘁ ◁ (P.j X).inv) ▷ Y) ≫
            Yᘁ ◁ (α_ Xᘁ X Y).hom ≫ (α_ Yᘁ Xᘁ (X ⊗ Y)).inv := by
          simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
          monoidal
        _ = _ := by
          rw [← hx]
          simp only [whiskerLeft_comp, Category.assoc]
          rw [← whiskerLeft_comp_assoc, ← h]
          simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]

/-- Dinaturality of the pivotal cup. -/
theorem Pivotal.cup_naturality (P : Pivotal C) {X Y : C} (f : X ⟶ Y) :
    P.cup Y ≫ fᘁ ▷ Y = P.cup X ≫ Xᘁ ◁ f := by
  have hn : (fᘁ)ᘁ ≫ (P.j Y).inv = (P.j X).inv ≫ f := by
    apply (cancel_epi (P.j X).hom).mp
    rw [← Category.assoc, ← P.naturality f]
    simp
  dsimp [Pivotal.cup]
  rw [Category.assoc, whisker_exchange, ← Category.assoc,
    ← coevaluation_comp_rightAdjointMate, Category.assoc, ← whiskerLeft_comp, hn]
  simp

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The first bend of a rotation, with the unit removed. -/
def bend {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) : Xᘁ ⟶ Y :=
  (ρ_ Xᘁ).inv ≫ (leftDuality (𝟙_ C) X Y).symm f

/-- Rotation as a pivotal cup followed by its first bend. -/
theorem rotation_eq_cup (P : Pivotal C) {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) :
    rotation P X Y f = P.cup X ≫ bend f ▷ X := by
  calc
    _ = η_ Xᘁ (Xᘁ)ᘁ ≫ bend f ▷ (Xᘁ)ᘁ ≫ Y ◁ (P.j X).inv := by
      dsimp [rotation, homCongr, rightDuality, tensorRightHomEquiv, bend]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      simp only [Pivotal.cup, Category.assoc]

/-- Bending a tensor block is successive bending of its two factors. -/
theorem bend_tensor (P : Pivotal C) {X Y Z : C} (f : 𝟙_ C ⟶ (X ⊗ Y) ⊗ Z) :
    (P.dualTensor X Y).hom ≫ bend f =
      (leftDuality Xᘁ Y Z).symm (bend (f ≫ (α_ X Y Z).hom)) := by
  dsimp [bend, leftDuality, tensorLeftHomEquiv]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    P.dualTensor_eval]
  dsimp [tensorDualEvaluation]
  monoidal

/-- Ng–Schauenburg's block composition law, with every associator explicit. -/
theorem rotation_tensor (P : Pivotal C) {X Y Z : C}
    (f : 𝟙_ C ⟶ (X ⊗ Y) ⊗ Z) :
    rotation P (X ⊗ Y) Z f =
      rotation P Y (Z ⊗ X)
        (rotation P X (Y ⊗ Z) (f ≫ (α_ X Y Z).hom) ≫ (α_ Y Z X).hom) ≫
      (α_ Z X Y).hom := by
  simp only [rotation_eq_cup]
  calc
    _ = (P.cup (X ⊗ Y) ≫ (P.dualTensor X Y).inv ▷ (X ⊗ Y)) ≫
        ((P.dualTensor X Y).hom ≫ bend f) ▷ (X ⊗ Y) := by simp
    _ = _ := by
      rw [P.cup_tensor, bend_tensor]
      dsimp [bend, leftDuality, tensorLeftHomEquiv]
      monoidal

/-- Naturality in the remaining tensor block. -/
theorem rotation_naturality_right (P : Pivotal C) {X Y Z : C}
    (f : 𝟙_ C ⟶ X ⊗ Y) (g : Y ⟶ Z) :
    rotation P X Z (f ≫ X ◁ g) = rotation P X Y f ≫ g ▷ X := by
  simp only [rotation_eq_cup]
  dsimp [bend, leftDuality, tensorLeftHomEquiv]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]
  simp

/-- Naturality in the tensor block that is moved. -/
theorem rotation_naturality_left (P : Pivotal C) {X Y Z : C}
    (f : 𝟙_ C ⟶ X ⊗ Z) (g : X ⟶ Y) :
    rotation P Y Z (f ≫ g ▷ Z) = rotation P X Z f ≫ Z ◁ g := by
  have hb : bend (f ≫ g ▷ Z) = gᘁ ≫ bend f := by
    dsimp [bend, leftDuality, tensorLeftHomEquiv]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      rightAdjointMate_comp_evaluation, comp_whiskerRight]
    monoidal
  simp only [rotation_eq_cup, hb, comp_whiskerRight]
  rw [← Category.assoc, P.cup_naturality, Category.assoc, whisker_exchange]
  simp only [Category.assoc]

/-- Moving both tensor blocks once is the identity. -/
theorem rotation_rotation (P : Pivotal C) {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) :
    rotation P Y X (rotation P X Y f) = f := by
  have h := congrArg (fun g => g ≫ (λ_ (X ⊗ Y)).hom)
    (rotation_tensor P (f ≫ (ρ_ (X ⊗ Y)).inv))
  dsimp only at h
  rw [rotation_unit] at h
  have h₁ : (f ≫ (ρ_ (X ⊗ Y)).inv) ≫ (α_ X Y (𝟙_ C)).hom =
      f ≫ X ◁ (ρ_ Y).inv := by monoidal
  rw [h₁, rotation_naturality_right] at h
  have h₂ : (rotation P X Y f ≫ (ρ_ Y).inv ▷ X) ≫ (α_ Y (𝟙_ C) X).hom =
      rotation P X Y f ≫ Y ◁ (λ_ X).inv := by monoidal
  rw [h₂, rotation_naturality_right] at h
  simpa using h.symm

/-- Degree two already has the prescribed cyclic order. -/
theorem fsRotation_two_pow (P : Pivotal C) (V : C) :
    (fsRotation P V 2).toLinearMap ^ 2 = 1 := by
  ext f
  change fsRotation P V 2 (fsRotation P V 2 f) = f
  change (𝟙 _ ≫ rotation P V V (𝟙 _ ≫ rotation P V V f ≫ 𝟙 _) ≫ 𝟙 _) = f
  simpa only [Category.id_comp, Category.comp_id] using rotation_rotation P f

end VOA.Huang.NgSchauenburg
