import VOA.Huang.TensorCatGenerators

/-! # Representability converts reassociation of intertwiner spaces into an isomorphism

The natural intertwiner-space comparison remains explicit. The existing
four-point analytic associativity theorem has irreducible external modules;
its extension and transport to these represented ordinary-module spaces is
not supplied by this file. No pentagon follows from this interface alone.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The precise representability bridge still needed after analytic four-point
associativity: an invertible linear comparison, natural in the actual output
module. Under strong rationality this is the expected transport of the common
space of analytic products and iterates; no existence is asserted here. -/
structure Reassociation (F : FusionChoice W) (X Y Z : Ordinary W) where
  compare (T : Ordinary W) :
    IntertwiningOperator (F X Y).isMod Z.isMod T.isMod ≃ₗ[ℂ]
      IntertwiningOperator X.isMod (F Y Z).isMod T.isMod
  natural {T U : Ordinary W} (I : IntertwiningOperator (F X Y).isMod Z.isMod T.isMod)
    (f : T ⟶ U) :
    compare U (postcompose I U.isMod f) = postcompose (compare T I) U.isMod f

/-- The remaining four-point comparison target, strictly below monoidal coherence.
This Prop requires the comparison data; it does not install it as an axiom. -/
def ReassociationInput (F : FusionChoice W) : Prop :=
  ∀ X Y Z : Ordinary W, Nonempty (Reassociation F X Y Z)

variable {F : FusionChoice W} {X Y Z : Ordinary W}

/-- The universal properties on both sides convert the comparison into a Hom equivalence. -/
def Reassociation.homEquiv (R : Reassociation F X Y Z) (T : Ordinary W) :
    (tensorObj F (tensorObj F X Y) Z ⟶ T) ≃ₗ[ℂ]
      (tensorObj F X (tensorObj F Y Z) ⟶ T) :=
  ((FusionProduct.homEquiv ((F (tensorObj F X Y) Z).universal T.carrier T.isMod)).trans
    (R.compare T)).trans
      (FusionProduct.homEquiv ((F X (tensorObj F Y Z)).universal T.carrier T.isMod)).symm

theorem Reassociation.homEquiv_natural (R : Reassociation F X Y Z)
    {T U : Ordinary W} (f : tensorObj F (tensorObj F X Y) Z ⟶ T) (g : T ⟶ U) :
    R.homEquiv U (f ≫ g) = R.homEquiv T f ≫ g := by
  apply (F X (tensorObj F Y Z)).universal U.carrier U.isMod |>.1
  have hs (T : Ordinary W) (f : tensorObj F (tensorObj F X Y) Z ⟶ T) :
      postcompose (F X (tensorObj F Y Z)).intertwiner T.isMod (R.homEquiv T f) =
        R.compare T (postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod f) :=
    (FusionProduct.homEquiv
      ((F X (tensorObj F Y Z)).universal T.carrier T.isMod)).apply_symm_apply _
  rw [hs]
  change R.compare U
    (postcompose (postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod f) U.isMod g) =
      postcompose (postcompose (F X (tensorObj F Y Z)).intertwiner T.isMod
        (R.homEquiv T f)) U.isMod g
  exact (R.natural _ g).trans
    (congrArg (fun I => postcompose I U.isMod g) (hs T f).symm)

/-- Yoneda's argument, spelled out for actual module maps. -/
def Reassociation.associator (R : Reassociation F X Y Z) :
    tensorObj F (tensorObj F X Y) Z ≅ tensorObj F X (tensorObj F Y Z) where
  hom := (R.homEquiv _).symm (𝟙 _)
  inv := R.homEquiv _ (𝟙 _)
  hom_inv_id := by
    apply (R.homEquiv _).injective
    rw [R.homEquiv_natural, LinearEquiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← R.homEquiv_natural, Category.id_comp, LinearEquiv.apply_symm_apply]

/-- The resulting isomorphism represents exactly the supplied comparison. -/
theorem Reassociation.homEquiv_eq_precompose (R : Reassociation F X Y Z)
    (T : Ordinary W) (f : tensorObj F (tensorObj F X Y) Z ⟶ T) :
    R.homEquiv T f = R.associator.inv ≫ f := by
  simpa only [Category.id_comp] using R.homEquiv_natural (𝟙 _) f

/-- Proved implication from the named comparison target to actual associator isomorphisms.
This is conditional: it does not prove ReassociationInput from strong rationality. -/
theorem associators_of_reassociationInput (h : ReassociationInput F) :
    ∀ X Y Z : Ordinary W,
      Nonempty (tensorObj F (tensorObj F X Y) Z ≅ tensorObj F X (tensorObj F Y Z)) :=
  fun X Y Z => ⟨(Classical.choice (h X Y Z)).associator⟩

end VOA.Huang.TensorCat
