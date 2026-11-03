import VOA.Huang.RepPackagingSmall

/-! Fusion-category packaging separates the proved finite semisimplicity from rigidity. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open VOA.Huang.TensorCat.BraidRibbon
universe u v w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Generic
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (E : C ≌ Ordinary W) [E.functor.Additive] [E.functor.Linear ℂ]

/-- Simplicity is reflected by the interpretation equivalence. -/
theorem simple_of_image (X : C) [Simple (E.functor.obj X)] : Simple X := by
  constructor
  intro Y f hf
  rw [← isIso_iff_of_reflects_iso f E.functor, Simple.mono_isIso_iff_nonzero]
  apply not_congr
  constructor
  · intro h; apply E.functor.map_injective; simpa using h
  · intro h; simp [h]

variable (hW : StronglyRational W) (hΦ : Finite (Φ W))
  (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)

/-- The small model's simple indexed by the original modular-data label. -/
def modelSimple (a : D.ι) : C := E.inverse.obj (Ordinary.of (D.module a))

include hD in
theorem modelSimple_isSimple (a : D.ι) : Simple (modelSimple E D a) := by
  letI := simple_module D hD a
  let e : E.functor.obj (modelSimple E D a) ≅ Ordinary.of (D.module a) := E.counitIso.app _
  letI : Simple (E.functor.obj (modelSimple E D a)) := Simple.of_iso e
  exact simple_of_image E _

/-- The interpretation sends each chosen simple back to exactly its given module. -/
def modelSimpleIso (a : D.ι) : E.functor.obj (modelSimple E D a) ≅ Ordinary.of (D.module a) :=
  E.counitIso.app _

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C]

/-- All fields of `FusionCategory` except the separately supplied rigidity are proved. -/
@[implicit_reducible]
def fusionOfEquivalence (unit : E.functor.obj (𝟙_ C) ≅ vacuumObject (W := W)) : FusionCategory C where
  ι := D.ι
  simple := modelSimple E D
  isSimple := modelSimple_isSimple E D hD
  unitLabel := D.vac
  unitIso := E.functor.preimageIso
    (modelSimpleIso E D D.vac ≪≫ Ordinary.isoOfModuleEquiv hD.vac_iso.some ≪≫ unit.symm)
  inequivalent a b e := module_injective D hD a b
    (e.map fun e => (modelSimpleIso E D a).symm ≪≫ E.functor.mapIso e ≪≫ modelSimpleIso E D b)
  semisimple X := by
    letI := E.inverse_additive
    obtain ⟨n, lab, ⟨e⟩⟩ := semisimple D hD hW hΦ (E.functor.obj X)
    exact ⟨n, lab, ⟨E.unitIso.app X ≪≫ E.inverse.mapIso e ≪≫
      E.inverse.mapBiproduct (fun j => Ordinary.of (D.module (lab j)))⟩⟩
  finiteDimensional X Y := by
    letI := finiteDimensional_hom hW hΦ (E.functor.obj X) (E.functor.obj Y)
    exact Module.Finite.of_injective (E.functor.mapLinearMap ℂ) E.functor.map_injective

end Generic
end VOA.Huang.TensorCat.RepPackaging
