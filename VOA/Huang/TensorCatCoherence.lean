import VOA.Huang.TensorCatReassociation
import Mathlib.CategoryTheory.Monoidal.Category

/-! # Coherence can be checked on nested universal coefficients

The two coefficient predicates below are algebraic residuals for a supplied
associator. They are not proofs of analytic five-point compatibility. Their
truth for the intended VOA associator requires compatible reassociation of
products of three intertwiners (and coefficient uniqueness), with consistent
coordinates and branches. Pairwise existence of analytic expansions alone
does not discharge them.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- Left-associated three-fold universal coefficient. -/
def tripleMode (X Y Z : Ordinary W) (p q : ℂ)
    (x : X.carrier) (y : Y.carrier) (z : Z.carrier) :
    (tensorObj F (tensorObj F X Y) Z).carrier :=
  (F (tensorObj F X Y) Z).intertwiner.val q ((F X Y).intertwiner.val p x y) z

/-- Left-associated four-fold universal coefficient (a five-point matrix coefficient
after pairing with an output functional). -/
def fourfoldMode (X Y Z T : Ordinary W) (p q r : ℂ)
    (x : X.carrier) (y : Y.carrier) (z : Z.carrier) (t : T.carrier) :
    (tensorObj F (tensorObj F (tensorObj F X Y) Z) T).carrier :=
  (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.val r
    (tripleMode F X Y Z p q x y z) t

theorem triple_linear_ext (X Y Z : Ordinary W)
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f g : (tensorObj F (tensorObj F X Y) Z).carrier →ₗ[ℂ] N)
    (h : ∀ p q x y z, f (tripleMode F X Y Z p q x y z) =
      g (tripleMode F X Y Z p q x y z)) : f = g := by
  apply tensor_linear_ext (F (tensorObj F X Y) Z)
  intro q a z
  exact congrArg (fun k : (F X Y).carrier →ₗ[ℂ] N => k a)
    (tensor_linear_ext (F X Y)
      (f.comp (((F (tensorObj F X Y) Z).intertwiner.val q).flip z))
      (g.comp (((F (tensorObj F X Y) Z).intertwiner.val q).flip z))
      (fun p x y => h p q x y z))

theorem fourfold_linear_ext (X Y Z T : Ordinary W)
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f g : (tensorObj F (tensorObj F (tensorObj F X Y) Z) T).carrier →ₗ[ℂ] N)
    (h : ∀ p q r x y z t, f (fourfoldMode F X Y Z T p q r x y z t) =
      g (fourfoldMode F X Y Z T p q r x y z t)) : f = g := by
  apply tensor_linear_ext (F (tensorObj F (tensorObj F X Y) Z) T)
  intro r a t
  exact congrArg (fun k : (tensorObj F (tensorObj F X Y) Z).carrier →ₗ[ℂ] N => k a)
    (triple_linear_ext F X Y Z
      (f.comp (((F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.val r).flip t))
      (g.comp (((F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.val r).flip t))
      (fun p q x y z => h p q r x y z t))

/-- The type of candidate associator families, before any coherence assertion. -/
abbrev AssociatorFamily := ∀ X Y Z : Ordinary W,
  tensorObj F (tensorObj F X Y) Z ≅ tensorObj F X (tensorObj F Y Z)

variable (a : AssociatorFamily F)

/-- The long route through the associativity pentagon. -/
def pentagonLong (X Y Z T : Ordinary W) :=
  tensorHom F (a X Y Z).hom (𝟙 T) ≫
    (a X (tensorObj F Y Z) T).hom ≫ tensorHom F (𝟙 X) (a Y Z T).hom

/-- The short route through the associativity pentagon. -/
def pentagonShort (X Y Z T : Ordinary W) :=
  (a (tensorObj F X Y) Z T).hom ≫ (a X Y (tensorObj F Z T)).hom

/-- Five-point coefficient compatibility of the two reassociation routes.
It is a meaningful target for the analytically constructed associator, not
an assertion about every possible family of module isomorphisms. -/
def PentagonOnModes : Prop := ∀ (X Y Z T : Ordinary W) (p q r : ℂ)
    (x : X.carrier) (y : Y.carrier) (z : Z.carrier) (t : T.carrier),
  (pentagonLong F a X Y Z T).val (fourfoldMode F X Y Z T p q r x y z t) =
    (pentagonShort F a X Y Z T).val (fourfoldMode F X Y Z T p q r x y z t)

/-- Vacuum compatibility on the source's actual universal coefficients. -/
def TriangleOnModes : Prop := ∀ (X Y : Ordinary W) (p q : ℂ)
    (x : X.carrier) (v : V) (y : Y.carrier),
  ((a X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom).val
      (tripleMode F X vacuumObject Y p q x v y) =
    (tensorHom F (rightUnitor F X).hom (𝟙 Y)).val
      (tripleMode F X vacuumObject Y p q x v y)

/-- Four-fold spanning upgrades coefficient compatibility to the full pentagon. -/
theorem pentagon_of_modes (h : PentagonOnModes F a) (X Y Z T : Ordinary W) :
    pentagonLong F a X Y Z T = pentagonShort F a X Y Z T :=
  Subtype.ext (fourfold_linear_ext F X Y Z T _ _ (h X Y Z T))

/-- Three-fold spanning upgrades vacuum coefficient compatibility to the triangle. -/
theorem triangle_of_modes (h : TriangleOnModes F a) (X Y : Ordinary W) :
    (a X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom =
      tensorHom F (rightUnitor F X).hom (𝟙 Y) :=
  Subtype.ext (triple_linear_ext F X vacuumObject Y _ _ (h X Y))

/-- Conditional packaging on the actual ordinary-module category. All tensor
functor and unitor laws are already proved. The displayed associator naturality
and coefficient compatibility hypotheses remain mathematical obligations. -/
abbrev monoidalCategoryOfModes
    (hnat : ∀ {X Y Z X' Y' Z' : Ordinary W}
      (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
      tensorHom F (tensorHom F f g) h ≫ (a X' Y' Z').hom =
        (a X Y Z).hom ≫ tensorHom F f (tensorHom F g h))
    (hp : PentagonOnModes F a) (ht : TriangleOnModes F a) : MonoidalCategory (Ordinary W) := by
  letI : MonoidalCategoryStruct (Ordinary W) :=
    { tensorObj := tensorObj F
      tensorHom := tensorHom F
      whiskerLeft := fun X _ _ f => tensorHom F (𝟙 X) f
      whiskerRight := fun f Y => tensorHom F f (𝟙 Y)
      tensorUnit := vacuumObject
      associator := a
      leftUnitor := leftUnitor F
      rightUnitor := rightUnitor F }
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorHom_id F)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (tensorHom_comp F f f' g g').symm)
    (associator_naturality := hnat)
    (leftUnitor_naturality := leftUnitor_naturality F)
    (rightUnitor_naturality := rightUnitor_naturality F)
    (pentagon := pentagon_of_modes F a hp)
    (triangle := triangle_of_modes F a ht)

end VOA.Huang.TensorCat
