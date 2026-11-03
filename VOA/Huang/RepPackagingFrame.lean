import VOA.Huang.RepPackagingTwist

/-! A proved structural frame, with no rigidity or numerical ribbon assumptions. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Huang.FusionProduct CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Structural data for a small braided realization of actual ordinary modules. -/
structure StructuralModel where
  F : FusionChoice W
  stronglyRational : StronglyRational W
  C : Type
  [cat : Category.{0} C]
  [preadditive : Preadditive C]
  [linear : Linear ℂ C]
  [monoidal : MonoidalCategory C]
  [monoidalPreadditive : MonoidalPreadditive C]
  [monoidalLinear : MonoidalLinear ℂ C]
  [braided : BraidedCategory C]
  [kernels : HasKernels C]
  [biproducts : HasFiniteBiproducts C]
  E : C ≌ Ordinary W
  [additive : E.functor.Additive]
  [linearFunctor : E.functor.Linear ℂ]
  monoidalFunctor :
    letI := monoidalCategoryOfStronglyRational_pbw F stronglyRational
    E.functor.Monoidal
  braiding_eq :
    letI := monoidalCategoryOfStronglyRational_pbw F stronglyRational
    letI := monoidalFunctor
    ∀ X Y : C, Functor.LaxMonoidal.μ E.functor X Y ≫ E.functor.map (β_ X Y).hom =
      (braiding F (E.functor.obj X) (E.functor.obj Y)).hom ≫ Functor.LaxMonoidal.μ E.functor Y X
  unit : E.functor.obj (𝟙_ C) ≅ vacuumObject (W := W)
  balance : ∀ X Y : C, (modelTwist E (X ⊗ Y)).hom =
    ((modelTwist E X).hom ⊗ₘ (modelTwist E Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom

attribute [instance] StructuralModel.cat StructuralModel.preadditive StructuralModel.linear
  StructuralModel.monoidal StructuralModel.monoidalPreadditive StructuralModel.monoidalLinear
  StructuralModel.braided StructuralModel.kernels StructuralModel.biproducts StructuralModel.additive StructuralModel.linearFunctor

variable {W}

/-- All structural fields are supplied by proved module theory and the proved Huang braiding. -/
def structuralModel (F : FusionChoice W) (hW : StronglyRational W)
    (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) : StructuralModel W := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := braidedCategory_stronglyRational_pbw F hW
  letI := smallRepMonoidal F hW D hD
  letI := smallRepMonoidalPreadditive F hW D hD
  letI := smallRepMonoidalLinear F hW D hD
  letI := smallRepBraided F hW D hD
  letI := realizationMonoidal F hW D hD
  letI := realizationBraided F hW D hD
  refine
    { F := F
      stronglyRational := hW
      C := SmallRep hW D hD
      E := smallEquivalence hW D hD
      monoidalFunctor := realizationMonoidal F hW D hD
      braiding_eq := fun X Y => Functor.Braided.braided (F := (smallEquivalence hW D hD).functor) X Y
      unit := (Functor.Monoidal.εIso (smallEquivalence hW D hD).functor).symm
      balance := modelTwist_balance (smallEquivalence hW D hD) ?_ }
  exact fun X Y => twist_balance F X Y

namespace StructuralModel
variable (M : StructuralModel W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)

/-- The fusion structure adds only a choice of right duals to the structural frame. -/
@[implicit_reducible]
def fusion [RightRigidCategory M.C] : FusionCategory M.C :=
  fusionOfEquivalence M.E M.stronglyRational
    (finite_irreducibleClasses D hD) D hD M.unit

include D hD in
/-- The tensor unit is simple, independently of rigidity. -/
theorem unit_simple : Simple (𝟙_ M.C) := by
  letI := simple_module D hD D.vac
  let e : M.E.functor.obj (𝟙_ M.C) ≅ Ordinary.of (D.module D.vac) :=
    M.unit ≪≫ (Ordinary.isoOfModuleEquiv hD.vac_iso.some).symm
  letI : Simple (M.E.functor.obj (𝟙_ M.C)) := Simple.of_iso e
  exact simple_of_image M.E _

end StructuralModel
end VOA.Huang.TensorCat.RepPackaging
