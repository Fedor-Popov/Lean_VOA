import VOA.Huang.RepPackagingFusion

/-! Transport of the actual conformal twist, including its scalar on every simple. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open VOA.Huang.TensorCat.BraidRibbon
universe u v w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (E : C ≌ Ordinary W) [E.functor.Additive] [E.functor.Linear ℂ]

/-- The transported twist is defined by the actual `exp(2πi L(0))` module map. -/
def modelTwist (X : C) : X ≅ X := E.functor.preimageIso (twistIso (E.functor.obj X))

@[simp] theorem map_modelTwist (X : C) :
    E.functor.map (modelTwist E X).hom = (twistIso (E.functor.obj X)).hom := by
  simp [modelTwist]

theorem modelTwist_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (modelTwist E Y).hom = (modelTwist E X).hom ≫ f := by
  apply E.functor.map_injective
  simpa only [Functor.map_comp, map_modelTwist] using twist_naturality (E.functor.map f)

/-- The transported twist has precisely the prescribed eigenvalue on each labelled simple. -/
theorem modelTwist_simple (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (a : D.ι) : (modelTwist E (modelSimple E D a)).hom =
      Complex.exp (2 * Real.pi * Complex.I * (D.h a : ℂ)) • 𝟙 (modelSimple E D a) := by
  apply E.functor.map_injective
  rw [map_modelTwist, Functor.map_smul, E.functor.map_id]
  apply (cancel_mono (modelSimpleIso E D a).hom).mp
  rw [← twist_naturality (modelSimpleIso E D a).hom, twistIso_module_eq D hD a]
  simp

section Balanced
variable [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory (Ordinary W)] [BraidedCategory (Ordinary W)]
  [E.functor.Braided]

/-- Balancing transports across the same monoidal braided equivalence. -/
theorem modelTwist_balance
    (hb : ∀ X Y : Ordinary W, (twistIso (X ⊗ Y)).hom =
      ((twistIso X).hom ⊗ₘ (twistIso Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom)
    (X Y : C) : (modelTwist E (X ⊗ Y)).hom =
      ((modelTwist E X).hom ⊗ₘ (modelTwist E Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom := by
  apply E.functor.map_injective
  apply (cancel_epi (Functor.LaxMonoidal.μ E.functor X Y)).mp
  simp only [Functor.map_comp, Functor.Monoidal.map_tensor, Functor.map_braiding,
    map_modelTwist, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [twist_naturality, hb]
  simp only [Category.assoc]

end Balanced
end VOA.Huang.TensorCat.RepPackaging
