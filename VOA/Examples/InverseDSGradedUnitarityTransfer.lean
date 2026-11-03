/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPositivityTransfer

/-!
# Conditional graded-unitarity transfer through inverse DS

This file isolates the strongest honest abstract implication from a graded-unitary ambient
realization to a filtered source.  It does not construct the isotropic-lattice VOA, Adamovic's
embedding, or its metric and filtration compatibilities.

A strict filtered isometry is not enough.  Already in a two-dimensional space with form
`diag(1,-1)`, ambient flag `G_0 = span(e_1)`, `G_1 = C^2`, and image line
`span(e_1 + a e_2)` for `0 < |a| < 1`, the induced source flag is strict and the pullback form is
positive.  Its only nonzero source layer has index one, however, so the required signed form is
negative.  Thus ambient graded unitarity does not transfer merely by intersecting cumulative
pieces with an image.

The sufficient replacement used below is that the image be **orthogonally reducing** at every
weight:

* the mapped source filtration pieces are the intersections of the image with the ambient pieces;
* the ambient bilinear form remains nondegenerate on every mapped source piece; and
* mapped source orthogonal layers are exactly the intersections of the image with ambient layers.

The last two requirements are the genuine metric additions to filtration strictness.  Under them,
an injective grading-preserving isometry commuting with the two real structures transfers
`GradedUnitaryAt`, and hence transfers `GradedUnitary` weight by weight.
-/

namespace VOA
namespace InverseDS

open VOA.VertexOperatorAlgebra
open LinearMap (BilinForm)

universe u v

variable {Affine : Type u} {Ambient : Type v}
variable [AddCommGroup Affine] [Module ℂ Affine]
variable [AddCommGroup Ambient] [Module ℂ Ambient]
variable {A : VertexOperatorAlgebra Affine} {T : VertexOperatorAlgebra Ambient}

/-! ## Small transport lemmas -/

namespace SesqForm

/-- Extensionality for the repository's bundled sesquilinear forms. -/
@[ext] theorem ext {E : Type*} [AddCommGroup E] [Module ℂ E]
    {h k : SesqForm E} (happly : ∀ x y, h x y = k x y) : h = k := by
  cases h with
  | mk hf ha hs hr hz =>
      cases k with
      | mk kf ka ks kr kz =>
          congr
          funext x y
          exact happly x y

/-- Positivity restricts to every smaller submodule. -/
theorem isPosOn_mono {E : Type*} [AddCommGroup E] [Module ℂ E]
    {h : SesqForm E} {S U : Submodule ℂ E} (hpos : IsPosOn h U) (hSU : S ≤ U) :
    IsPosOn h S := by
  intro x hx hne
  exact hpos x (hSU hx) hne

end SesqForm

namespace LinearMap.BilinForm

/-- Nondegeneracy on an image submodule pulls back through an injective isometry. -/
theorem nondegenerate_restrict_of_eq_pullback
    {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    {bE : BilinForm ℂ E} {bF : BilinForm ℂ F} {iota : E →ₗ[ℂ] F}
    (hiota : Function.Injective iota)
    (hcompat : bE = bF.compl₁₂ iota iota) (S : Submodule ℂ E)
    (hnd : (bF.restrict (S.map iota)).Nondegenerate) :
    (bE.restrict S).Nondegenerate := by
  let e : S ≃ₗ[ℂ] S.map iota := Submodule.equivMapOfInjective iota hiota S
  have hpush : LinearMap.BilinForm.congr e.symm (bF.restrict (S.map iota)) =
      bE.restrict S := by
    ext x y
    simp only [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.restrict_apply]
    rw [hcompat]
    rfl
  rw [← hpush]
  exact hnd.congr e.symm

end LinearMap.BilinForm

/-! ## Grading-preserving real isometries -/

/-- The linear and metric part of a hypothetical inverse-DS embedding.

No mode or Wick-product compatibility is included: those facts are needed to construct this data
for the concrete realization, but the implication theorem below consumes only grading,
injectivity, the invariant-form isometry, and covariance of the anti-linear real structures. -/
structure GradedIsometricEmbedding
    (A : VertexOperatorAlgebra Affine) (T : VertexOperatorAlgebra Ambient)
    (BA : InvariantForm A) (BT : InvariantForm T)
    (RA : RealStructure A) (RT : RealStructure T) where
  /-- The underlying complex-linear embedding. -/
  iota : Affine →ₗ[ℂ] Ambient
  /-- Injectivity of the realization. -/
  iota_injective : Function.Injective iota
  /-- The realization preserves conformal weight. -/
  map_grading : ∀ (n : ℤ) (x : Affine), x ∈ A.grading n → iota x ∈ T.grading n
  /-- The affine invariant form is the exact pullback of the ambient invariant form. -/
  form_isometry : ∀ x y, BA.form x y = BT.form (iota x) (iota y)
  /-- The realization intertwines the source and ambient anti-linear structures. -/
  rho_compatible : ∀ x, iota (RA.rho x) = RT.rho (iota x)

namespace GradedIsometricEmbedding

variable {BA : InvariantForm A} {BT : InvariantForm T}
variable {RA : RealStructure A} {RT : RealStructure T}

/-- Restriction of a graded embedding to one conformal-weight space. -/
def weightMap (E : GradedIsometricEmbedding A T BA BT RA RT) (n : ℤ) :
    A.grading n →ₗ[ℂ] T.grading n where
  toFun x := ⟨E.iota x, E.map_grading n x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact E.iota.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact E.iota.map_smul c x

/-- The weight-space restriction remains injective. -/
theorem weightMap_injective (E : GradedIsometricEmbedding A T BA BT RA RT) (n : ℤ) :
    Function.Injective (E.weightMap n) := by
  intro x y hxy
  apply Subtype.ext
  apply E.iota_injective
  exact congrArg Subtype.val hxy

/-- The level bilinear form is the pullback of the ambient level form. -/
theorem gradedForm_eq_pullback (E : GradedIsometricEmbedding A T BA BT RA RT) (n : ℤ) :
    LiRadical.gradedForm BA n =
      (LiRadical.gradedForm BT n).compl₁₂ (E.weightMap n) (E.weightMap n) := by
  apply LinearMap.BilinForm.ext
  intro x y
  exact E.form_isometry x y

/-- Real covariance upgrades the invariant-form isometry to the exact sesquilinear pullback
needed by signed positivity. -/
theorem gradedSesq_eq_pullback (E : GradedIsometricEmbedding A T BA BT RA RT) (n : ℤ) :
    gradedSesq BA RA n = (gradedSesq BT RT n).pullback (E.weightMap n) := by
  apply SesqForm.ext
  intro x y
  rw [gradedSesq_apply, SesqForm.pullback_apply, gradedSesq_apply]
  rw [E.form_isometry, E.rho_compatible]
  rfl

/-! ## The additional orthogonal-reduction hypothesis -/

/-- The exact filtration and orthogonal-layer compatibility needed at one weight.

`piece_strict` is ordinary strict filteredness on the image.  The counterexample in the module
docstring shows that it does not imply either of the remaining fields. -/
structure OrthogonallyReducingAt
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ) : Prop where
  /-- The source filtration is exactly induced from the ambient filtration on the image. -/
  piece_strict : ∀ p : ℕ,
    (FA.pieceIn p n).map (E.weightMap n) =
      LinearMap.range (E.weightMap n) ⊓ FT.pieceIn p n
  /-- Each mapped cumulative piece is nondegenerate for the ambient bilinear form. -/
  mapped_piece_nondegenerate : ∀ p : ℕ,
    ((LiRadical.gradedForm BT n).restrict
      ((FA.pieceIn p n).map (E.weightMap n))).Nondegenerate
  /-- Source orthogonal layers map to the image intersections with ambient orthogonal layers. -/
  layer_strict : ∀ p : ℕ,
    (FA.layer n (LiRadical.gradedForm BA n) p).map (E.weightMap n) =
      LinearMap.range (E.weightMap n) ⊓
        FT.layer n (LiRadical.gradedForm BT n) p

/-- Ambient graded unitarity at one weight transfers through an orthogonally reducing real
isometric embedding. -/
theorem gradedUnitaryAt_of_ambient
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ)
    (hreduce : E.OrthogonallyReducingAt FA FT n)
    (hambient : GradedUnitaryAt FT n (LiRadical.gradedForm BT n) (gradedSesq BT RT n)) :
    GradedUnitaryAt FA n (LiRadical.gradedForm BA n) (gradedSesq BA RA n) := by
  constructor
  · intro p
    exact LinearMap.BilinForm.nondegenerate_restrict_of_eq_pullback
      (E.weightMap_injective n) (E.gradedForm_eq_pullback n) (FA.pieceIn p n)
      (hreduce.mapped_piece_nondegenerate p)
  · intro p
    apply SesqForm.isPosOn_signedForm_of_eq_pullback
      (E.weightMap_injective n) (E.gradedSesq_eq_pullback n) p
    rw [hreduce.layer_strict p]
    exact SesqForm.isPosOn_mono (hambient.2 p) inf_le_right

/-- Weight-by-weight orthogonal reduction transfers the full conditional `GradedUnitary`
predicate from the ambient VOA to the source VOA. -/
theorem gradedUnitary_of_ambient
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T)
    (hreduce : ∀ n : ℤ, E.OrthogonallyReducingAt FA FT n)
    (hambient : GradedUnitary BT RT FT) :
    GradedUnitary BA RA FA := by
  intro n
  exact E.gradedUnitaryAt_of_ambient FA FT n (hreduce n) (hambient n)

end GradedIsometricEmbedding

end InverseDS
end VOA
