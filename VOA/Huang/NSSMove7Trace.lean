import VOA.Huang.NSSMove7Sewing

/-! # Partial-trace identities for the local loop diagrams -/
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

/-- Naturality on the output of a right partial trace. -/
theorem partialTraceRight_postcomp (P : Pivotal C) (X : C) {A B D : C}
    (f : A ⊗ X ⟶ B ⊗ X) (g : B ⟶ D) :
    partialTraceRight P X (f ≫ g ▷ X) = partialTraceRight P X f ≫ g := by
  dsimp [partialTraceRight]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

/-- Sphericality moves a traced strand from right to left across a braiding.
The proof uses the full trace pairing and is valid for arbitrary open maps. -/
theorem partialTraceRight_eq_left_braiding (F : SphericalFusion C) (X : C)
    {A B : C} (f : A ⊗ X ⟶ B ⊗ X) :
    partialTraceRight F.toPivotal X f =
      F.toPivotal.partialTraceLeft X
        ((β_ X A).hom ≫ f ≫ (β_ X B).inv) := by
  apply F.hom_ext_trace
  intro q
  rw [← partialTraceRight_postcomp, scalarTrace_partialTraceRight,
    ← F.toPivotal.partialTraceLeft_postcomp, F.scalarTrace_partialTraceLeft]
  simp only [Category.assoc]
  rw [F.scalarTrace_comp_comm (β_ X A).hom]
  congr 1
  simp only [Category.assoc]
  rw [← braiding_inv_naturality_left_assoc]
  simp

/-- Closing either side of a double crossing gives the same open loop. -/
theorem partialTraceRight_monodromy (F : SphericalFusion C) (X A : C) :
    partialTraceRight F.toPivotal X (monodromy A X) =
      monodromyLoop F.toPivotal X A := by
  rw [partialTraceRight_eq_left_braiding]
  simp [monodromyLoop, monodromy]

/-- With an identity inserted, forward sewing is a loop on the right exterior
strand followed by the fixed inverse exterior crossing. -/
theorem forwardSewingMap_id (F : SphericalFusion C) (X : C) (i j : F.Label) :
    forwardSewingMap F X i j (𝟙 _) =
      (β_ (F.simple j) (F.simple i)).inv ≫
        monodromyLoop F.toPivotal X (F.simple j) ▷ F.simple i := by
  rw [forwardSewingMap_monodromy, ← partialTraceRight_monodromy]
  dsimp [partialTraceRight]
  monoidal

/-- With an identity inserted, inverse sewing is a loop on the left exterior
strand, with the same fixed inverse exterior crossing. -/
theorem inverseSewingMap_id (F : SphericalFusion C) (Y : C) (i j : F.Label) :
    inverseSewingMap F Y i j (𝟙 _) =
      (β_ (F.simple j) (F.simple i)).inv ≫
        F.simple j ◁ monodromyLoop F.toPivotal Y (F.simple i) := by
  rw [inverseSewingMap_monodromy]
  dsimp [monodromyLoop, Pivotal.partialTraceLeft]
  monoidal

end VOA.Huang.NSCongruence
