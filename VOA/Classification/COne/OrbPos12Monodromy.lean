import VOA.Classification.COne.OrbPos12Twist
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Separable

/-! Finite-order monodromy on the induced object, not on its action target.
The spectral decomposition is not asserted to be an algebra-module decomposition. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.TensorCat.BraidRibbon
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Forget an ordinary-module automorphism to its carrier endomorphism. -/
def autEnd (X : Ordinary W) : CategoryTheory.Aut X →* Module.End ℂ X.carrier where
  toFun f := f.hom.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem autEnd_injective (X : Ordinary W) : Function.Injective (autEnd X) := by
  intro f g h
  apply Iso.ext
  exact Subtype.ext h

theorem twistIso_finiteOrder (hW : StronglyRational W) (X : Ordinary W) :
    @IsOfFinOrder (CategoryTheory.Aut X) _ (twistIso X) := by
  let t : CategoryTheory.Aut X := twistIso X
  change IsOfFinOrder t
  exact ((autEnd_injective X).isOfFinOrder_iff (x := t)).mp (twistEnd_finiteOrder hW X)

/-- Tensor product of actual ordinary-module automorphisms. -/
def tensorAut (F : FusionChoice W) (X Y : Ordinary W) :
    CategoryTheory.Aut X × CategoryTheory.Aut Y →* CategoryTheory.Aut (tensorObj F X Y) where
  toFun f := tensorIso F f.1 f.2
  map_one' := by apply Iso.ext; exact tensorHom_id F X Y
  map_mul' f g := by
    apply Iso.ext
    exact tensorHom_comp F g.1.hom f.1.hom g.2.hom f.2.hom

/-- Double braiding, as an automorphism of `X ⊠ Y`. -/
def monodromyAut (F : FusionChoice W) (X Y : Ordinary W) :
    CategoryTheory.Aut (tensorObj F X Y) := braiding F X Y ≪≫ braiding F Y X

/-- Balancing and finite conformal twists give finite monodromy order under
strong rationality. In particular, this applies to `X ⊠ A`. -/
theorem monodromyAut_finiteOrder (hW : StronglyRational W) (F : FusionChoice W)
    (X Y : Ordinary W) : IsOfFinOrder (monodromyAut F X Y) := by
  let t : CategoryTheory.Aut (tensorObj F X Y) := tensorAut F X Y (twistIso X, twistIso Y)
  let s : CategoryTheory.Aut (tensorObj F X Y) := twistIso (tensorObj F X Y)
  have ht : IsOfFinOrder t := (tensorAut F X Y).isOfFinOrder
    ((twistIso_finiteOrder hW X).prod_mk (twistIso_finiteOrder hW Y))
  have hs : IsOfFinOrder s := twistIso_finiteOrder hW _
  have hc : Commute s t⁻¹ := by
    apply Iso.ext
    exact twist_naturality t.inv
  have he : monodromyAut F X Y = s * t⁻¹ := by
    apply (mul_right_cancel (b := t))
    rw [inv_mul_cancel_right]
    apply Iso.ext
    exact (twist_balance F X Y).symm
  rw [he]
  exact hc.isOfFinOrder_mul hs ht.inv

/-- The induced monodromy as a linear endomorphism. -/
def monodromyEnd (F : FusionChoice W) (X Y : Ordinary W) :
    Module.End ℂ (tensorObj F X Y).carrier := autEnd _ (monodromyAut F X Y)

theorem monodromyEnd_finiteOrder (hW : StronglyRational W) (F : FusionChoice W)
    (X Y : Ordinary W) : IsOfFinOrder (monodromyEnd F X Y) :=
  (autEnd _).isOfFinOrder (monodromyAut_finiteOrder hW F X Y)

/-- Finite order in characteristic zero implies semisimplicity even on an
infinite-dimensional carrier. -/
theorem semisimple_of_finiteOrder {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : Module.End ℂ M) (hf : IsOfFinOrder f) : f.IsSemisimple := by
  obtain ⟨n, hn, hp⟩ := hf.exists_pow_eq_one
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hn.ne') one_ne_zero).squarefree
  simp [hp]

/-- A proved spectral prerequisite for the requested sector projections. This
does not say that eigenspaces are stable under the extension algebra action. -/
theorem inducedMonodromy_semisimple (hW : StronglyRational W) (F : FusionChoice W)
    (X A : Ordinary W) : (monodromyEnd F X A).IsSemisimple :=
  semisimple_of_finiteOrder _ (monodromyEnd_finiteOrder hW F X A)

end VOA.Classification.COne.OrbPos12
