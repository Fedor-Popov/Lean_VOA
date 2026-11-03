import VOA.Huang.TensorCatBifunctor

/-! # The vacuum left unitor and independence of the choice of fusion products -/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- The vacuum left unitor, from the proved universality of the module vertex operator. -/
def leftUnitor (X : Ordinary W) : tensorObj F vacuumObject X ≅ X :=
  Ordinary.isoOfModuleEquiv (productIso (F vacuumObject X) (unitProduct X.isMod))

@[simp] theorem leftUnitor_intertwiner (X : Ordinary W) (n : ℂ) (v : V) (x : X.carrier) :
    (leftUnitor F X).hom.val ((F vacuumObject X).intertwiner.val n v x) =
      (moduleIntertwiner X.isMod).val n v x :=
  productIso_intertwiner (F vacuumObject X) (unitProduct X.isMod) n v x

/-- Naturality is a consequence of mode equivariance of the module map. -/
theorem leftUnitor_naturality {X Y : Ordinary W} (f : X ⟶ Y) :
    tensorHom F (𝟙 vacuumObject) f ≫ (leftUnitor F Y).hom =
      (leftUnitor F X).hom ≫ f := by
  apply tensor_hom_ext F
  intro n v x
  simp only [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply,
    leftUnitor_intertwiner]
  change moduleModes Y.isMod n v (f.val x) = f.val (moduleModes X.isMod n v x)
  classical
  unfold moduleModes
  split_ifs with h
  · exact (f.property v h.choose x).symm
  · simp

/-- The chosen left unit isomorphisms form a natural isomorphism. -/
def leftUnitorNatIso :
    ({ obj := fun X => tensorObj F vacuumObject X
       map := fun f => tensorHom F (𝟙 vacuumObject) f
       map_id := fun X => tensorHom_id F vacuumObject X
       map_comp := fun f g => by rw [← tensorHom_comp]; simp } : Ordinary W ⥤ Ordinary W)
      ≅ 𝟭 (Ordinary W) :=
  NatIso.ofComponents (leftUnitor F) (fun f => leftUnitor_naturality F f)

variable (G : FusionChoice W)

/-- Changing the chosen representing products gives their canonical isomorphism. -/
def tensorChoiceIso (X Y : Ordinary W) : tensorObj F X Y ≅ tensorObj G X Y :=
  Ordinary.isoOfModuleEquiv (productIso (F X Y) (G X Y))

@[simp] theorem tensorChoiceIso_intertwiner (X Y : Ordinary W)
    (n : ℂ) (x : X.carrier) (y : Y.carrier) :
    (tensorChoiceIso F G X Y).hom.val ((F X Y).intertwiner.val n x y) =
      (G X Y).intertwiner.val n x y :=
  productIso_intertwiner (F X Y) (G X Y) n x y

theorem tensorChoiceIso_naturality {X X' Y Y' : Ordinary W}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom F f g ≫ (tensorChoiceIso F G X' Y').hom =
      (tensorChoiceIso F G X Y).hom ≫ tensorHom G f g := by
  apply tensor_hom_ext F
  intro n x y
  simp

/-- The fusion bifunctor is independent, up to canonical natural isomorphism,
of the finite representatives and bases used to construct its products. -/
def tensorChoiceNatIso : tensorBifunctor F ≅ tensorBifunctor G :=
  NatIso.ofComponents (fun p => tensorChoiceIso F G p.1 p.2)
    (fun f => tensorChoiceIso_naturality F G f.1 f.2)

end VOA.Huang.TensorCat
