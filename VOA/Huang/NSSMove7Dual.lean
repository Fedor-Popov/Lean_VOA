import VOA.Huang.NSSMove7Transparent
import VOA.Huang.ZhuRepRibbonPivotal

/-! # Dual compatibility of the two interacting monodromies

The isomorphism identifying their underlying objects is explicit. This
handles dualizing the crossing; it does not transpose the complete sewn
open diagram.
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

/-- Braiding with both duals is the right mate of the original braiding,
using the specified evaluation-characterized tensor-dual comparison. -/
@[reassoc] theorem braiding_rightMate (P : Pivotal C) (X Y : C) :
    (P.dualTensor Y X).hom ≫ ((β_ X Y).hom)ᘁ =
      (β_ Xᘁ Yᘁ).hom ≫ (P.dualTensor X Y).hom := by
  apply dual_map_ext (X := X ⊗ Y)
  simp only [comp_whiskerRight, Category.assoc]
  rw [rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    P.dualTensor_eval, P.dualTensor_eval,
    VOA.Huang.ZhuRep.whiskerLeft_braiding_tensorDualEvaluation]

/-- The mate reverses the order of the two dual strands of a monodromy. -/
@[reassoc] theorem monodromy_rightMate (P : Pivotal C) (X Y : C) :
    (P.dualTensor X Y).hom ≫ (monodromy X Y)ᘁ =
      monodromy Yᘁ Xᘁ ≫ (P.dualTensor X Y).hom := by
  simp only [monodromy, comp_rightAdjointMate, Category.assoc]
  rw [braiding_rightMate_assoc, braiding_rightMate]

/-- The explicit identification between the spaces of the dual interactions. -/
def dualMonodromyPairIso (P : Pivotal C) (X Y : C) :
    X ⊗ Yᘁ ≅ (Y ⊗ Xᘁ)ᘁ :=
  whiskerRightIso (P.j X) Yᘁ ≪≫ P.dualTensor Y Xᘁ

/-- The full, potentially nonscalar dual monodromies are mates under this
identification. No ribbon twist or nondegeneracy is required. -/
theorem dualMonodromyPairIso_intertwines (P : Pivotal C) (X Y : C) :
    (dualMonodromyPairIso P X Y).hom ≫ (monodromy Y Xᘁ)ᘁ =
      monodromy X Yᘁ ≫ (dualMonodromyPairIso P X Y).hom := by
  dsimp only [dualMonodromyPairIso, Iso.trans_hom, whiskerRightIso_hom]
  rw [Category.assoc, monodromy_rightMate]
  simp [monodromy]

/-- Scalarity of either dual interaction implies scalarity of the other,
with exactly the same scalar, by actual duality of morphisms. -/
theorem scalar_dual_monodromy_transfer (P : Pivotal C) (X Y : C) (z : ℂ)
    (h : monodromy Y Xᘁ = z • 𝟙 _) :
    monodromy X Yᘁ = z • 𝟙 _ := by
  have ht := dualMonodromyPairIso_intertwines P X Y
  rw [h] at ht
  have hm : (z • 𝟙 (Y ⊗ Xᘁ))ᘁ = z • 𝟙 (Y ⊗ Xᘁ)ᘁ := by
    simp [rightAdjointMate]
  rw [hm] at ht
  apply (cancel_mono (dualMonodromyPairIso P X Y).hom).mp
  simpa using ht.symm

end VOA.Huang.NSCongruence
