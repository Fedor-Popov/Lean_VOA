import VOA.Huang.NgSchauenburgRotation
import VOA.Huang.DeligneTrace

/-! # Uniqueness of dual comparisons

The evaluation equations in the pivotal bundle pin the comparison maps;
the corresponding coevaluation equations follow from rigidity.
-/

noncomputable section
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Evaluation detects every morphism into a chosen dual. -/
theorem dual_map_ext {X A B : C} [pB : ExactPairing X B] {f g : A ⟶ B}
    (h : f ▷ X ≫ ε_ X B = g ▷ X ≫ ε_ X B) : f = g := by
  letI : HasRightDual X := { rightDual := B, exact := inferInstance }
  have he := congrArg (tensorRightHomEquiv A X B (𝟙_ C)) h
  erw [@tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X A
    { rightDual := B, exact := pB } f,
    @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X A
    { rightDual := B, exact := pB } g] at he
  exact (cancel_mono (λ_ B).inv).mp he

/-- The evaluation-characterized dual comparison also transports coevaluation. -/
theorem coevaluation_of_evaluation {X A B : C} [pA : ExactPairing X A]
    [pB : ExactPairing X B] (f : A ⟶ B)
    (h : f ▷ X ≫ ε_ X B = ε_ X A) :
    η_ X A ≫ X ◁ f = η_ X B := by
  have hm : (rightDualIso pA pB).hom = f := by
    apply dual_map_ext (X := X)
    change (@rightAdjointMate C _ _ X X
      { rightDual := B, exact := pB } { rightDual := A, exact := pA } (𝟙 X)) ▷ X ≫ ε_ X B = _
    erw [@rightAdjointMate_comp_evaluation C _ _ X X
      { rightDual := B, exact := pB } { rightDual := A, exact := pA } (𝟙 X), h]
    simp
  rw [← hm]
  change η_ X A ≫ X ◁ (@rightAdjointMate C _ _ X X
      { rightDual := B, exact := pB } { rightDual := A, exact := pA } (𝟙 X)) = _
  erw [@coevaluation_comp_rightAdjointMate C _ _ X X
      { rightDual := B, exact := pB } { rightDual := A, exact := pA } (𝟙 X)]
  simp

variable [RightRigidCategory C]

/-- The tensor comparison is uniquely determined by its evaluation equation. -/
theorem Pivotal.dualTensor_unique (P : Pivotal C) (X Y : C)
    (f : Yᘁ ⊗ Xᘁ ⟶ (X ⊗ Y)ᘁ)
    (h : f ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (X ⊗ Y)ᘁ = tensorDualEvaluation C X Y) :
    f = (P.dualTensor X Y).hom :=
  dual_map_ext (h.trans (P.dualTensor_eval X Y).symm)

/-- Coevaluation compatibility is a consequence of the evaluation equation;
it is not an additional assumption on the pivotal bundle. -/
theorem Pivotal.dualTensor_coevaluation (P : Pivotal C) (X Y : C) :
    (η_ X Xᘁ ≫ X ◁ (λ_ Xᘁ).inv ≫ X ◁ (η_ Y Yᘁ ▷ Xᘁ) ≫
      X ◁ (α_ Y Yᘁ Xᘁ).hom ≫ (α_ X Y (Yᘁ ⊗ Xᘁ)).inv) ≫
      (X ⊗ Y) ◁ (P.dualTensor X Y).hom = η_ (X ⊗ Y) (X ⊗ Y)ᘁ := by
  let pairXY := TensorCat.tensorPairing X Xᘁ Y Yᘁ
  have he : (P.dualTensor X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (X ⊗ Y)ᘁ =
      @ExactPairing.evaluation C _ _ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) pairXY := by
    rw [P.dualTensor_eval]
    change tensorDualEvaluation C X Y =
      (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ (X ⊗ Y)) ⊗≫ Yᘁ ◁ ε_ X Xᘁ ▷ Y ⊗≫ ε_ Y Yᘁ)
    dsimp [tensorDualEvaluation]
    monoidal
  have h := @coevaluation_of_evaluation C _ _ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)
    (X ⊗ Y)ᘁ pairXY inferInstance (P.dualTensor X Y).hom he
  calc
    _ = (η_ X Xᘁ ⊗≫ X ◁ η_ Y Yᘁ ▷ Xᘁ ⊗≫ 𝟙 ((X ⊗ Y) ⊗ (Yᘁ ⊗ Xᘁ))) ≫
        (X ⊗ Y) ◁ (P.dualTensor X Y).hom := by monoidal
    _ = _ := h

end VOA.Huang.NgSchauenburg
