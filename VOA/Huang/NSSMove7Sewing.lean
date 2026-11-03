import VOA.Huang.NSSMove6Assembly

/-! # Braided normal forms for the two sewing maps

The identities in this module are open morphism identities, before taking
any categorical trace. In particular no multiplicity information is lost.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The left unbending map is precisely the pivotal cap on the first pair. -/
theorem leftUnbendAdjoint_id_cap (P : Pivotal C) (X A : C) :
    leftUnbendAdjoint P (𝟙 (Xᘁ ⊗ A)) =
      (α_ X Xᘁ A).inv ≫ pivotalCap P X ▷ A ≫ (λ_ A).hom := by
  dsimp [leftUnbendAdjoint, leftDuality, tensorLeftHomEquiv, pivotalCap]
  monoidal

/-- The cup in the inverse sewing map is the pivotal cup. -/
theorem rightBendEquiv_symm_id_cup (P : Pivotal C) (Y A : C) :
    (rightBendEquiv P A (A ⊗ Yᘁ) Y).symm (𝟙 _) =
      (ρ_ A).inv ≫ A ◁ P.cup Y ≫ (α_ A Yᘁ Y).inv := by
  dsimp [rightBendEquiv, homCongr, rightDuality, tensorRightHomEquiv, Pivotal.cup]
  monoidal

/-- Forward sewing, using only the specified cup, cap and ordinary braiding. -/
theorem forwardSewingMap_explicit (F : SphericalFusion C) (X : C)
    (i j : F.Label) (h : Xᘁ ⊗ F.simple i ⟶ Xᘁ ⊗ F.simple i) :
    forwardSewingMap F X i j h =
      (𝟙 (F.simple i ⊗ F.simple j) ⊗≫ η_ X Xᘁ ▷ (F.simple i ⊗ F.simple j) ⊗≫
        X ◁ (β_ (F.simple j) (Xᘁ ⊗ F.simple i)).inv ⊗≫
        (β_ X (F.simple j)).hom ▷ (Xᘁ ⊗ F.simple i) ⊗≫
        F.simple j ◁ (X ◁ h) ⊗≫
        F.simple j ◁ (pivotalCap F.toPivotal X ▷ F.simple i) ⊗≫
        𝟙 (F.simple j ⊗ F.simple i)) := by
  change (_ ≫ _ ≫ F.simple j ◁ (X ◁ h ≫ leftUnbendAdjoint _ _)) = _
  rw [leftUnbendAdjoint_id_cap, mixedCenter_halfBraiding]
  dsimp [leftDuality, tensorLeftHomEquiv]
  monoidal

/-- Inverse sewing in the same explicit cup-cap language. -/
theorem inverseSewingMap_explicit (F : SphericalFusion C) (Y : C)
    (i j : F.Label) (h : F.simple j ⊗ Yᘁ ⟶ F.simple j ⊗ Yᘁ) :
    inverseSewingMap F Y i j h =
      (𝟙 (F.simple i ⊗ F.simple j) ⊗≫
        (F.simple i ⊗ F.simple j) ◁ F.toPivotal.cup Y ⊗≫
        (β_ (F.simple j ⊗ Yᘁ) (F.simple i)).inv ▷ Y ⊗≫
        (F.simple j ⊗ Yᘁ) ◁ (β_ (F.simple i) Y).hom ⊗≫
        h ▷ Y ▷ F.simple i ⊗≫
        (F.simple j ◁ ε_ Y Yᘁ) ▷ F.simple i ⊗≫
        𝟙 (F.simple j ⊗ F.simple i)) := by
  change (_ ≫ _ ≫ (_ ≫ _) ▷ F.simple i) = _
  rw [rightBendEquiv_symm_id_cup, mixedCenter_halfBraiding_inv]
  dsimp [rightDuality, tensorRightHomEquiv]
  monoidal

/-- Pull the exterior inverse braiding out of forward sewing. The remaining
crossing is a genuine monodromy between the positive factor and the right
exterior strand. The inserted endomorphism remains arbitrary. -/
theorem forwardSewingMap_monodromy (F : SphericalFusion C) (X : C)
    (i j : F.Label) (h : Xᘁ ⊗ F.simple i ⟶ Xᘁ ⊗ F.simple i) :
    forwardSewingMap F X i j h =
      ((β_ (F.simple j) (F.simple i)).inv ⊗≫
        F.simple j ◁ η_ X Xᘁ ▷ F.simple i ⊗≫
        monodromy (F.simple j) X ▷ (Xᘁ ⊗ F.simple i) ⊗≫
        F.simple j ◁ (X ◁ h) ⊗≫
        F.simple j ◁ (pivotalCap F.toPivotal X ▷ F.simple i) ⊗≫
        𝟙 (F.simple j ⊗ F.simple i)) := by
  rw [forwardSewingMap_explicit, braiding_tensor_right_inv]
  have hc := halfBraiding_coevaluation (Center.ofBraidedObj (F.simple j)) X
  change (ρ_ (F.simple j)).inv ≫ F.simple j ◁ η_ X Xᘁ ≫
      (α_ (F.simple j) X Xᘁ).inv ≫ (β_ (F.simple j) X).hom ▷ Xᘁ =
    (λ_ (F.simple j)).inv ≫ η_ X Xᘁ ▷ F.simple j ≫
      (α_ X Xᘁ (F.simple j)).hom ≫ X ◁ (β_ (F.simple j) Xᘁ).inv ≫
      (α_ X (F.simple j) Xᘁ).inv at hc
  calc
    _ = (β_ (F.simple j) (F.simple i)).inv ⊗≫
        ((λ_ (F.simple j)).inv ≫ η_ X Xᘁ ▷ F.simple j ≫
          (α_ X Xᘁ (F.simple j)).hom ≫ X ◁ (β_ (F.simple j) Xᘁ).inv ≫
          (α_ X (F.simple j) Xᘁ).inv) ▷ F.simple i ⊗≫
        (β_ X (F.simple j)).hom ▷ (Xᘁ ⊗ F.simple i) ⊗≫
        F.simple j ◁ (X ◁ h) ⊗≫
        F.simple j ◁ (pivotalCap F.toPivotal X ▷ F.simple i) ⊗≫
        𝟙 (F.simple j ⊗ F.simple i) := by
      calc
        _ = 𝟙 (F.simple i ⊗ F.simple j) ⊗≫
            (η_ X Xᘁ ▷ (F.simple i ⊗ F.simple j) ≫
              (X ⊗ Xᘁ) ◁ (β_ (F.simple j) (F.simple i)).inv) ⊗≫
            X ◁ (β_ (F.simple j) Xᘁ).inv ▷ F.simple i ⊗≫
            (β_ X (F.simple j)).hom ▷ (Xᘁ ⊗ F.simple i) ⊗≫
            F.simple j ◁ (X ◁ h) ⊗≫
            F.simple j ◁ (pivotalCap F.toPivotal X ▷ F.simple i) ⊗≫
            𝟙 (F.simple j ⊗ F.simple i) := by monoidal
        _ = _ := by rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [← hc]
      dsimp [monodromy]
      monoidal

/-- Sliding an arbitrary cup through the inverse braiding on its first leg.
This is naturality at that cup followed by the reverse hexagon. -/
theorem inverseBraiding_cup_slide (A B U : C) (c : 𝟙_ C ⟶ A ⊗ B) :
    (ρ_ U).inv ≫ U ◁ c ≫ (α_ U A B).inv ≫ (β_ A U).inv ▷ B =
      (λ_ U).inv ≫ c ▷ U ≫ (α_ A B U).hom ≫ A ◁ (β_ B U).hom ≫
        (α_ A U B).inv := by
  apply (cancel_mono ((α_ A U B).hom ≫ A ◁ (β_ B U).inv ≫
    (α_ A B U).inv)).mp
  calc
    _ = (ρ_ U).inv ≫ U ◁ c ≫ (β_ (A ⊗ B) U).inv := by
      rw [braiding_tensor_left_inv]
      simp only [Category.assoc]
    _ = (λ_ U).inv ≫ c ▷ U := by
      rw [braiding_inv_naturality_right]
      simp
    _ = _ := by simp

/-- Pull the same exterior inverse braiding out of inverse sewing. -/
theorem inverseSewingMap_monodromy (F : SphericalFusion C) (Y : C)
    (i j : F.Label) (h : F.simple j ⊗ Yᘁ ⟶ F.simple j ⊗ Yᘁ) :
    inverseSewingMap F Y i j h =
      ((β_ (F.simple j) (F.simple i)).inv ⊗≫
        F.simple j ◁ (F.toPivotal.cup Y ▷ F.simple i) ⊗≫
        F.simple j ◁ (Yᘁ ◁ monodromy Y (F.simple i)) ⊗≫
        h ▷ Y ▷ F.simple i ⊗≫
        (F.simple j ◁ ε_ Y Yᘁ) ▷ F.simple i ⊗≫
        𝟙 (F.simple j ⊗ F.simple i)) := by
  rw [inverseSewingMap_explicit, braiding_tensor_left_inv]
  have hc := inverseBraiding_cup_slide Yᘁ Y (F.simple i) (F.toPivotal.cup Y)
  calc
    _ = (β_ (F.simple j) (F.simple i)).inv ⊗≫
        F.simple j ◁ ((ρ_ (F.simple i)).inv ≫ F.simple i ◁ F.toPivotal.cup Y ≫
          (α_ (F.simple i) Yᘁ Y).inv ≫ (β_ Yᘁ (F.simple i)).inv ▷ Y) ⊗≫
        (F.simple j ⊗ Yᘁ) ◁ (β_ (F.simple i) Y).hom ⊗≫
        h ▷ Y ▷ F.simple i ⊗≫
        (F.simple j ◁ ε_ Y Yᘁ) ▷ F.simple i ⊗≫
        𝟙 (F.simple j ⊗ F.simple i) := by
      calc
        _ = 𝟙 (F.simple i ⊗ F.simple j) ⊗≫
            ((F.simple i ⊗ F.simple j) ◁ F.toPivotal.cup Y ≫
              (β_ (F.simple j) (F.simple i)).inv ▷ (Yᘁ ⊗ Y)) ⊗≫
            F.simple j ◁ ((β_ Yᘁ (F.simple i)).inv ▷ Y) ⊗≫
            (F.simple j ⊗ Yᘁ) ◁ (β_ (F.simple i) Y).hom ⊗≫
            h ▷ Y ▷ F.simple i ⊗≫
            (F.simple j ◁ ε_ Y Yᘁ) ▷ F.simple i ⊗≫
            𝟙 (F.simple j ⊗ F.simple i) := by monoidal
        _ = _ := by rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [hc]
      dsimp [monodromy]
      monoidal

end VOA.Huang.NSCongruence
