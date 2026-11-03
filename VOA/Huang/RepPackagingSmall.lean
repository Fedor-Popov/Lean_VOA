import VOA.Huang.RepPackagingSemisimple
import VOA.Huang.HexagonCloseResidual
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.EssentiallySmall

/-! A small model with transported linear, monoidal and braided structures. -/
set_option backward.inferInstanceAs.wrap.data false
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Huang.FusionProduct CategoryTheory CategoryTheory.Limits CategoryTheory.Monoidal
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Finite-dimensional complex Hom spaces are small even for a large carrier universe. -/
theorem locallySmall (hW : StronglyRational W) (hΦ : Finite (Φ W)) :
    LocallySmall.{0} (Ordinary W) where
  hom_small X Y := by
    letI := finiteDimensional_hom hW hΦ X Y
    exact small_of_injective (Module.finBasis ℂ (X ⟶ Y)).repr.injective

/-- Finite words of simple labels surject onto the isomorphism classes. -/
theorem essentiallySmall (hW : StronglyRational W) (hΦ : Finite (Φ W))
    (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    EssentiallySmall.{0} (Ordinary W) := by
  letI := locallySmall hW hΦ
  apply (essentiallySmall_iff _).mpr
  refine ⟨?_, inferInstance⟩
  let f : (Σ n : ℕ, Fin n → D.ι) → Skeleton (Ordinary W) :=
    fun p => toSkeleton (⨁ fun j => Ordinary.of (D.module (p.2 j)))
  apply small_of_surjective (f := f)
  intro X
  induction X using Quotient.inductionOn with
  | h X =>
    obtain ⟨n, lab, ⟨e⟩⟩ := semisimple D hD hW hΦ X
    exact ⟨⟨n, lab⟩, Quotient.sound ⟨e.symm⟩⟩

section Transfer
universe v w
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℂ C]
  {S : Type} [Category.{0} S] (E : S ≌ C)

/-- Pull the additive structure back through the chosen fully faithful realization. -/
@[implicit_reducible]
def modelPreadditive : Preadditive S := Preadditive.ofFullyFaithful E.fullyFaithfulFunctor

/-- The interpretation preserves the pulled-back addition. -/
theorem modelFunctorAdditive :
    letI := modelPreadditive E
    E.functor.Additive := E.fullyFaithfulFunctor.additive_ofFullyFaithful

/-- Pull scalars back using the same Hom equivalences as addition. -/
@[implicit_reducible]
def modelLinear :
    letI := modelPreadditive E
    Linear ℂ S := by
  letI := modelPreadditive E
  exact
    { homModule := fun X Y => Equiv.module ℂ (E.fullyFaithfulFunctor.homEquiv (X := X) (Y := Y))
      smul_comp := fun X Y Z c f g => E.functor.map_injective (by
        simp [Equiv.smul_def])
      comp_smul := fun X Y Z f c g => E.functor.map_injective (by
        simp [Equiv.smul_def]) }

theorem modelFunctorLinear :
    letI := modelPreadditive E
    letI := modelLinear E
    E.functor.Linear ℂ := by
  letI := modelPreadditive E
  letI := modelLinear E
  exact { map_smul := by intros; simp [Equiv.smul_def] }

end Transfer

variable (F : FusionChoice W) (hW : StronglyRational W)
  (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)

/-- The universe-small category equivalent to all ordinary modules. -/
def SmallRep : Type :=
  letI := essentiallySmall hW (finite_irreducibleClasses D hD) D hD
  ShrinkHoms.{0} (Shrink.{0} (Skeleton (Ordinary W)))

instance smallRepCategory : Category.{0} (SmallRep hW D hD) := by
  letI := essentiallySmall hW (finite_irreducibleClasses D hD) D hD
  letI : LocallySmall.{0} (Skeleton (Ordinary W)) := locallySmall_of_faithful (fromSkeleton _)
  exact inferInstanceAs (Category (ShrinkHoms.{0} (Shrink.{0} (Skeleton (Ordinary W)))))

/-- First shrink the skeleton's objects and then shrink its Hom types. -/
def smallSkeletonEquivalence : SmallRep hW D hD ≌ Skeleton (Ordinary W) := by
  letI := essentiallySmall hW (finite_irreducibleClasses D hD) D hD
  letI : LocallySmall.{0} (Skeleton (Ordinary W)) := locallySmall_of_faithful (fromSkeleton _)
  exact (ShrinkHoms.equivalence.{0} (Shrink.{0} (Skeleton (Ordinary W)))).symm.trans
    (Shrink.equivalence.{0} (Skeleton (Ordinary W))).symm

/-- Interpretation of the small model as actual modules. -/
def smallEquivalence : SmallRep hW D hD ≌ Ordinary W :=
  (smallSkeletonEquivalence hW D hD).trans (skeletonEquivalence (Ordinary W))

/-- The small model is genuinely skeletal as well as having small Hom types. -/
theorem smallRep_skeletal : Skeletal (SmallRep hW D hD) := by
  letI := essentiallySmall hW (finite_irreducibleClasses D hD) D hD
  intro X Y h
  apply (equivShrink (Skeleton (Ordinary W))).symm.injective
  exact skeleton_skeletal (Ordinary W)
    (h.map (smallSkeletonEquivalence hW D hD).functor.mapIso)

instance smallRepPreadditive : Preadditive (SmallRep hW D hD) := modelPreadditive (smallEquivalence hW D hD)
instance smallRepLinear : Linear ℂ (SmallRep hW D hD) := modelLinear (smallEquivalence hW D hD)
instance smallEquivalenceAdditive : (smallEquivalence hW D hD).functor.Additive := modelFunctorAdditive _
instance smallEquivalenceLinear : (smallEquivalence hW D hD).functor.Linear ℂ := modelFunctorLinear _

instance smallRepFiniteProducts : HasFiniteProducts (SmallRep hW D hD) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (smallEquivalence hW D hD).functor⟩

instance smallRepFiniteBiproducts : HasFiniteBiproducts (SmallRep hW D hD) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance smallRepAbelian : Abelian (SmallRep hW D hD) :=
  abelianOfEquivalence (smallEquivalence hW D hD).functor

/-- The monoidal structure is exactly Mathlib's transport of the proved fusion product. -/
@[implicit_reducible]
def smallRepMonoidal : MonoidalCategory (SmallRep hW D hD) :=
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  transport (smallEquivalence hW D hD).symm

/-- The interpretation is a strong monoidal equivalence for this transport. -/
@[implicit_reducible]
def realizationMonoidal :
    letI := monoidalCategoryOfStronglyRational_pbw F hW
    letI := smallRepMonoidal F hW D hD
    (smallEquivalence hW D hD).functor.Monoidal := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  change letI := smallRepMonoidal F hW D hD; (smallEquivalence hW D hD).functor.Monoidal
  dsimp +instances only [smallRepMonoidal, transport]
  infer_instance

/-- The small model carries precisely the transported Huang braiding. -/
@[implicit_reducible]
def smallRepBraided :
    letI := smallRepMonoidal F hW D hD
    BraidedCategory (SmallRep hW D hD) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := braidedCategory_stronglyRational_pbw F hW
  exact Transported.instBraidedCategory (smallEquivalence hW D hD).symm

@[implicit_reducible]
def realizationBraided :
    letI := monoidalCategoryOfStronglyRational_pbw F hW
    letI := braidedCategory_stronglyRational_pbw F hW
    letI := smallRepMonoidal F hW D hD
    letI := smallRepBraided F hW D hD
    letI := realizationMonoidal F hW D hD
    (smallEquivalence hW D hD).functor.Braided := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := braidedCategory_stronglyRational_pbw F hW
  letI := smallRepMonoidal F hW D hD
  letI := smallRepBraided F hW D hD
  letI := realizationMonoidal F hW D hD
  refine { braided := ?_ }
  intro X Y
  exact Functor.LaxBraided.braided (F := (equivalenceTransported (smallEquivalence hW D hD).symm).inverse) X Y

theorem smallRepMonoidalPreadditive :
    letI := smallRepMonoidal F hW D hD
    MonoidalPreadditive (SmallRep hW D hD) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := monoidalPreadditive_pbw F hW
  letI := smallRepMonoidal F hW D hD
  letI := realizationMonoidal F hW D hD
  exact monoidalPreadditive_of_faithful (smallEquivalence hW D hD).functor

theorem smallRepMonoidalLinear :
    letI := smallRepMonoidal F hW D hD
    letI := smallRepMonoidalPreadditive F hW D hD
    MonoidalLinear ℂ (SmallRep hW D hD) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := monoidalPreadditive_pbw F hW
  letI := monoidalLinear_pbw F hW
  letI := smallRepMonoidal F hW D hD
  letI := smallRepMonoidalPreadditive F hW D hD
  letI := realizationMonoidal F hW D hD
  exact MonoidalLinear.ofFaithful ℂ (smallEquivalence hW D hD).functor

end VOA.Huang.TensorCat.RepPackaging
