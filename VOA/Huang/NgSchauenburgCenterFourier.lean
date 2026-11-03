import VOA.Huang.NgSchauenburgAveraging

/-! # Half-braiding loops on objects of the center

The center loop is expanded into its underlying half-braidings and chosen
central cup and cap. The S eigenvalues and Fourier inversion are then actual
underlying morphism equalities. The encircled object here belongs to the center;
this is not yet the indicator diagram exchange for an arbitrary base object.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- Forget the categorical monodromy loop in the center. -/
def centerMonodromyLoop (Z : SphericalFusion (Center C)) (A B : Center C) :
    B.1 ⟶ B.1 := (monodromyLoop Z.toPivotal A B).f

/-- An explicit half-braiding diagram in the base category. Cups and caps are
the underlying maps of the supplied rigid pivotal structure on the center. -/
theorem centerMonodromyLoop_diagram (Z : SphericalFusion (Center C)) (A B : Center C) :
    centerMonodromyLoop Z A B =
      (λ_ B.1).inv ≫ (Z.toPivotal.cup A).f ▷ B.1 ≫
        (α_ (Aᘁ).1 A.1 B.1).hom ≫
        (Aᘁ).1 ◁ ((A.2.β B.1).hom ≫ (B.2.β A.1).hom) ≫
        (α_ (Aᘁ).1 A.1 B.1).inv ≫ (ε_ A Aᘁ).f ▷ B.1 ≫ (λ_ B.1).hom := by
  simp only [centerMonodromyLoop, monodromyLoop, Pivotal.partialTraceLeft,
    monodromy, Center.comp_f, Center.leftUnitor_inv_f, Center.whiskerRight_f,
    Center.associator_hom_f, Center.whiskerLeft_f, Center.associator_inv_f,
    Center.leftUnitor_hom_f]
  rfl

/-- For simple central objects the genuine half-braiding loop has the
categorical S eigenvalue, with the NS dual on the first label. -/
theorem centerMonodromyLoop_simple (Z : SphericalFusion (Center C)) (i j : Z.Label) :
    centerMonodromyLoop Z (Z.simple i)ᘁ (Z.simple j) =
      (categoricalS Z i j / Z.dimension (Z.simple j)) • 𝟙 (Z.simple j).1 :=
  congrArg Center.Hom.f (monodromyLoop_simple Z i j)

/-- Loop Fourier expansion after forgetting to the base category. -/
theorem centerMonodromyLoop_eq_sum_projectors (Z : SphericalFusion (Center C))
    (i : Z.Label) (B : Center C) :
    centerMonodromyLoop Z (Z.simple i)ᘁ B =
      ∑ j, (categoricalS Z i j / Z.dimension (Z.simple j)) • (Z.simpleProjector j B).f := by
  have h := congrArg (centralForgetHom B B) (monodromyLoop_eq_sum_projectors Z i B)
  simpa only [map_sum, map_smul] using h

open Classical in
/-- Each central isotypic projector, on the underlying object, is an inverse-S
weighted sum of the explicit half-braiding diagrams above. -/
theorem centerSimpleProjector_eq_sum_loops (Z : SphericalFusion (Center C))
    (M : Modular Z) (j : Z.Label) (B : Center C) :
    (Z.simpleProjector j B).f =
      ∑ i, (Z.dimension (Z.simple j) * (categoricalS Z)⁻¹ j i) •
        centerMonodromyLoop Z (Z.simple i)ᘁ B := by
  have h := congrArg (centralForgetHom B B) (simpleProjector_eq_sum_loops Z M j B)
  simpa only [map_sum, map_smul] using h

end VOA.Huang.NgSchauenburg
