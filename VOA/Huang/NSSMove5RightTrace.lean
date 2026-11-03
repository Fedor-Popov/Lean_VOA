import VOA.Huang.NSSMove5Forward

/-! # Right pivotal partial traces for the forward rotation calculation -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The pivotal cap with its first input identified by `j`. -/
def pivotalCap (P : Pivotal C) (X : C) : X ⊗ Xᘁ ⟶ 𝟙_ C :=
  (P.j X).hom ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ

/-- Tensor compatibility of the pivotal cap. -/
theorem pivotalCap_tensor (P : Pivotal C) (X Y : C) :
    (X ⊗ Y) ◁ (P.dualTensor X Y).hom ≫ pivotalCap P (X ⊗ Y) =
      (α_ X Y (Yᘁ ⊗ Xᘁ)).hom ≫ X ◁ (α_ Y Yᘁ Xᘁ).inv ≫
        X ◁ (pivotalCap P Y ▷ Xᘁ) ≫ X ◁ (λ_ Xᘁ).hom ≫ pivotalCap P X := by
  dsimp only [pivotalCap]
  rw [P.monoidal]
  simp only [comp_whiskerRight, Category.assoc]
  rw [rightAdjointMate_comp_evaluation]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  rw [P.dualTensor_eval]
  dsimp only [tensorDualEvaluation]
  simp only [tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc (P.j X).hom,
    ← whisker_exchange_assoc (P.j X).hom, ← whisker_exchange_assoc (P.j X).hom]
  monoidal

/-- Close the right tensor factor using the chosen cup and the pivotal cap. -/
def partialTraceRight (P : Pivotal C) (X : C) {Y Z : C}
    (f : Y ⊗ X ⟶ Z ⊗ X) : Y ⟶ Z :=
  (ρ_ Y).inv ≫ Y ◁ η_ X Xᘁ ≫ (α_ Y X Xᘁ).inv ≫
    f ▷ Xᘁ ≫ (α_ Z X Xᘁ).hom ≫ Z ◁ pivotalCap P X ≫ (ρ_ Z).hom

/-- Full closure of a right partial trace is the original pivotal trace. -/
theorem traceRight_partialTraceRight (P : Pivotal C) (X Y : C)
    (f : Y ⊗ X ⟶ Y ⊗ X) :
    P.traceRight (partialTraceRight P X f) = P.traceRight f := by
  have he : η_ (Y ⊗ X) (Y ⊗ X)ᘁ =
      (η_ Y Yᘁ ≫ Y ◁ (λ_ Yᘁ).inv ≫ Y ◁ (η_ X Xᘁ ▷ Yᘁ) ≫
        Y ◁ (α_ X Xᘁ Yᘁ).hom ≫ (α_ Y X (Xᘁ ⊗ Yᘁ)).inv) ≫
          (Y ⊗ X) ◁ (P.dualTensor Y X).hom :=
    (P.dualTensor_coevaluation Y X).symm
  change _ = η_ (Y ⊗ X) (Y ⊗ X)ᘁ ≫ f ▷ (Y ⊗ X)ᘁ ≫ pivotalCap P (Y ⊗ X)
  rw [he]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, pivotalCap_tensor]
  dsimp [Pivotal.traceRight, partialTraceRight, pivotalCap]
  monoidal

variable [HasKernels C] [HasFiniteBiproducts C]

/-- Scalar version of the full right closure. -/
theorem scalarTrace_partialTraceRight (F : SphericalFusion C) (X Y : C)
    (f : Y ⊗ X ⟶ Y ⊗ X) :
    F.scalarTrace Y (partialTraceRight F.toPivotal X f) =
      F.scalarTrace (Y ⊗ X) f :=
  congrArg F.unitScalar.symm (traceRight_partialTraceRight F.toPivotal X Y f)

end VOA.Huang.NSCongruence
