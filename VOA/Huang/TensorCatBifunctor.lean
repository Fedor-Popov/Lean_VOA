import VOA.Huang.TensorCatOrdinary

/-! # Fusion on module morphisms

This construction works for any choice of representing products. Strong
rationality is used only to supply such a choice, with finiteness explicit.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- A choice of genuine representing objects for every pair of ordinary modules. -/
abbrev FusionChoice (W : VertexOperatorAlgebra V) :=
  ∀ X Y : Ordinary W, Product X.isMod Y.isMod

/-- The finite semisimple construction supplies all products. -/
def fusionChoice (hV : StronglyRational W) (hΦ : Finite (Φ W)) : FusionChoice W :=
  fun X Y => fusionProduct hV hΦ X.isMod Y.isMod

/-- Specialization using the existing project PBW witness. -/
def fusionChoice_pbw (hV : StronglyRational W) : FusionChoice W :=
  fusionChoice hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)

variable (F : FusionChoice W)

/-- Fusion on objects. -/
def tensorObj (X Y : Ordinary W) : Ordinary W := Ordinary.ofProduct (F X Y)

/-- Fusion on morphisms is the unique factor of the restricted universal intertwiner. -/
def tensorHom {X X' Y Y' : Ordinary W} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj F X Y ⟶ tensorObj F X' Y' :=
  (F X Y).lift (F X' Y').isMod (restrictInputs f g (F X' Y').intertwiner)

/-- The defining equation holds for every complex mode and all input vectors. -/
@[simp] theorem tensorHom_intertwiner {X X' Y Y' : Ordinary W}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℂ) (x : X.carrier) (y : Y.carrier) :
    (tensorHom F f g).val ((F X Y).intertwiner.val n x y) =
      (F X' Y').intertwiner.val n (f.val x) (g.val y) :=
  congrArg (fun Z : IntertwiningOperator X.isMod Y.isMod (F X' Y').isMod => Z.val n x y)
    ((F X Y).lift_spec _ _)

/-- Universal modes determine every morphism out of a tensor product. -/
theorem tensor_hom_ext {X Y Z : Ordinary W} (f g : tensorObj F X Y ⟶ Z)
    (h : ∀ n x y, f.val ((F X Y).intertwiner.val n x y) =
      g.val ((F X Y).intertwiner.val n x y)) : f = g :=
  (F X Y).hom_ext Z.isMod f g h

@[simp] theorem tensorHom_id (X Y : Ordinary W) :
    tensorHom F (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj F X Y) := by
  apply tensor_hom_ext F
  intro n x y
  simp

@[simp] theorem tensorHom_comp {X X' X'' Y Y' Y'' : Ordinary W}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorHom F (f ≫ f') (g ≫ g') = tensorHom F f g ≫ tensorHom F f' g' := by
  apply tensor_hom_ext F
  intro n x y
  simp

/-- The actual fusion bifunctor, with its identity and composition laws proved. -/
def tensorBifunctor : Ordinary W × Ordinary W ⥤ Ordinary W where
  obj p := tensorObj F p.1 p.2
  map f := tensorHom F f.1 f.2
  map_id p := tensorHom_id F p.1 p.2
  map_comp f g := tensorHom_comp F f.1 g.1 f.2 g.2

@[simp] theorem tensorHom_add_left {X X' Y Y' : Ordinary W}
    (f f' : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom F (f + f') g = tensorHom F f g + tensorHom F f' g := by
  apply tensor_hom_ext F
  intro n x y
  change (tensorHom F (f + f') g).val _ =
    (tensorHom F f g).val _ + (tensorHom F f' g).val _
  simp only [tensorHom_intertwiner]
  exact congrArg (fun z => z (g.val y))
    ((F X' Y').intertwiner.val n |>.map_add (f.val x) (f'.val x))

@[simp] theorem tensorHom_add_right {X X' Y Y' : Ordinary W}
    (f : X ⟶ X') (g g' : Y ⟶ Y') :
    tensorHom F f (g + g') = tensorHom F f g + tensorHom F f g' := by
  apply tensor_hom_ext F
  intro n x y
  change (tensorHom F f (g + g')).val _ =
    (tensorHom F f g).val _ + (tensorHom F f g').val _
  simp only [tensorHom_intertwiner]
  exact map_add _ _ _

@[simp] theorem tensorHom_smul_left {X X' Y Y' : Ordinary W}
    (c : ℂ) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom F (c • f) g = c • tensorHom F f g := by
  apply tensor_hom_ext F
  intro n x y
  change (tensorHom F (c • f) g).val _ = c • (tensorHom F f g).val _
  simp only [tensorHom_intertwiner]
  change (F X' Y').intertwiner.val n (c • f.val x) (g.val y) = _
  rw [map_smul, LinearMap.smul_apply]
  rfl

@[simp] theorem tensorHom_smul_right {X X' Y Y' : Ordinary W}
    (c : ℂ) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom F f (c • g) = c • tensorHom F f g := by
  apply tensor_hom_ext F
  intro n x y
  change (tensorHom F f (c • g)).val _ = c • (tensorHom F f g).val _
  simp only [tensorHom_intertwiner]
  exact map_smul _ _ _

/-- Applying fusion to a pair of isomorphisms yields an isomorphism. -/
def tensorIso {X X' Y Y' : Ordinary W} (e : X ≅ X') (d : Y ≅ Y') :
    tensorObj F X Y ≅ tensorObj F X' Y' where
  hom := tensorHom F e.hom d.hom
  inv := tensorHom F e.inv d.inv
  hom_inv_id := by rw [← tensorHom_comp]; simp
  inv_hom_id := by rw [← tensorHom_comp]; simp

end VOA.Huang.TensorCat
