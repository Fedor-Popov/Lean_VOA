import VOA.Huang.NgSchauenburgCentralProjection

/-! # Pivotal partial traces and categorical monodromy loops

The loop is defined by cups, caps and the actual braiding. Its scalar on a
simple object is computed from the categorical S matrix, not stipulated.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

namespace Pivotal

/-- Close the left tensor factor using the pivotal cup and the chosen evaluation. -/
def partialTraceLeft (P : Pivotal C) (X : C) {Y Z : C}
    (f : X ⊗ Y ⟶ X ⊗ Z) : Y ⟶ Z :=
  (λ_ Y).inv ≫ P.cup X ▷ Y ≫ (α_ Xᘁ X Y).hom ≫
    Xᘁ ◁ f ≫ (α_ Xᘁ X Z).inv ≫ ε_ X Xᘁ ▷ Z ≫ (λ_ Z).hom

theorem partialTraceLeft_precomp (P : Pivotal C) (X : C) {W Y Z : C}
    (a : W ⟶ Y) (f : X ⊗ Y ⟶ X ⊗ Z) :
    P.partialTraceLeft X (X ◁ a ≫ f) = a ≫ P.partialTraceLeft X f := by
  dsimp [partialTraceLeft]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

theorem partialTraceLeft_postcomp (P : Pivotal C) (X : C) {Y Z W : C}
    (f : X ⊗ Y ⟶ X ⊗ Z) (b : Z ⟶ W) :
    P.partialTraceLeft X (f ≫ X ◁ b) = P.partialTraceLeft X f ≫ b := by
  dsimp [partialTraceLeft]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]

theorem traceLeft_eq_cup (P : Pivotal C) {X : C} (f : X ⟶ X) :
    P.traceLeft f = P.cup X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  simp [traceLeft, cup]

/-- Closing a partial trace gives the trace of the original tensor endomorphism. -/
theorem traceLeft_partialTraceLeft (P : Pivotal C) (X Y : C)
    (f : X ⊗ Y ⟶ X ⊗ Y) :
    P.traceLeft (P.partialTraceLeft X f) = P.traceLeft f := by
  have he : ε_ (X ⊗ Y) (X ⊗ Y)ᘁ =
      (P.dualTensor X Y).inv ▷ (X ⊗ Y) ≫ tensorDualEvaluation C X Y := by
    rw [← P.dualTensor_eval, ← comp_whiskerRight_assoc]
    simp
  rw [P.traceLeft_eq_cup f, he, whisker_exchange_assoc,
    ← Category.assoc, P.cup_tensor, P.traceLeft_eq_cup]
  dsimp [partialTraceLeft, tensorDualEvaluation]
  monoidal

end Pivotal

variable [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion

theorem partialTraceLeft_whiskerRight (F : SphericalFusion C) {X : C} (Y : C)
    (f : X ⟶ X) :
    F.toPivotal.partialTraceLeft X (f ▷ Y) = F.scalarTrace X f • 𝟙 Y := by
  have ht : F.toPivotal.cup X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ =
      F.scalarTrace X f • 𝟙 (𝟙_ C) := by
    rw [← F.toPivotal.traceLeft_eq_cup, F.spherical]
    exact (F.unitScalar_apply _).symm.trans (F.unitScalar.apply_symm_apply _)
      |>.symm
  calc
    _ = (λ_ Y).inv ≫ ((F.toPivotal.cup X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ) ▷ Y) ≫
        (λ_ Y).hom := by
      dsimp [Pivotal.partialTraceLeft]
      monoidal
    _ = _ := by rw [ht]; simp

theorem partialTraceLeft_whiskerLeft (F : SphericalFusion C) (X : C) {Y Z : C}
    (f : Y ⟶ Z) :
    F.toPivotal.partialTraceLeft X (X ◁ f) = F.dimension X • f := by
  have h := F.toPivotal.partialTraceLeft_postcomp X (𝟙 (X ⊗ Y)) f
  simp only [Category.id_comp] at h
  rw [h, ← id_whiskerRight X Y, F.partialTraceLeft_whiskerRight,
    F.scalarTrace_id, Linear.smul_comp, Category.id_comp]

theorem scalarTrace_partialTraceLeft (F : SphericalFusion C) (X Y : C)
    (f : X ⊗ Y ⟶ X ⊗ Y) :
    F.scalarTrace Y (F.toPivotal.partialTraceLeft X f) = F.scalarTrace (X ⊗ Y) f := by
  change F.unitScalar.symm (F.traceRight _) = F.unitScalar.symm (F.traceRight _)
  rw [← F.spherical, ← F.spherical, F.toPivotal.traceLeft_partialTraceLeft]

theorem scalarTrace_whiskerRight (F : SphericalFusion C) {X : C} (Y : C)
    (f : X ⟶ X) :
    F.scalarTrace (X ⊗ Y) (f ▷ Y) = F.scalarTrace X f * F.dimension Y := by
  rw [← F.scalarTrace_partialTraceLeft, F.partialTraceLeft_whiskerRight,
    map_smul, F.scalarTrace_id]
  rfl

end SphericalFusion

variable [BraidedCategory C]

/-- The actual loop of `X` around `Y`, with the left leg closed pivotally. -/
def monodromyLoop (P : Pivotal C) (X Y : C) : Y ⟶ Y :=
  P.partialTraceLeft X (monodromy X Y)

/-- The encircling loop is natural in the object it encircles. -/
theorem monodromyLoop_naturality (P : Pivotal C) (X : C) {Y Z : C} (f : Y ⟶ Z) :
    f ≫ monodromyLoop P X Z = monodromyLoop P X Y ≫ f := by
  rw [monodromyLoop, monodromyLoop, ← P.partialTraceLeft_precomp,
    ← P.partialTraceLeft_postcomp]
  congr 1
  simp [monodromy]

/-- The dual on the loop label agrees with the library's NS S convention. -/
theorem monodromyLoop_simple (F : SphericalFusion C) (i j : F.Label) :
    monodromyLoop F.toPivotal (F.simple i)ᘁ (F.simple j) =
      (categoricalS F i j / F.dimension (F.simple j)) • 𝟙 (F.simple j) := by
  rw [F.simple_end_eq_trace j (monodromyLoop F.toPivotal (F.simple i)ᘁ (F.simple j))]
  rw [monodromyLoop, F.scalarTrace_partialTraceLeft]
  rfl

end VOA.Huang.NgSchauenburg
