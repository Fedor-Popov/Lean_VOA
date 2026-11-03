/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.SesqFormTransport
import VOA.Examples.InverseDSRFiltration

/-!
# Conditional positivity transfer through inverse DS

This file states the metric input needed to use an inverse Drinfeld--Sokolov realization for
graded unitarity.  It deliberately does not construct the Adamovic embedding, a tensor-product
Hermitian form, or BRST descent.

The interface separates two mathematical hypotheses:

* `MetricComparison.form_eq_pullback` says that the source sesquilinear form is exactly the
  pullback of the ambient form along the proposed embedding;
* `MetricComparison.IsStrict` is the independent no-hidden-cancellation statement comparing the
  source and ambient filtrations.

Positivity is assumed only on the image of the relevant source piece, never on the whole ambient
tensor product.
-/

namespace VOA
namespace InverseDS

variable {Affine Ambient : Type*}
variable [AddCommGroup Affine] [Module ℂ Affine]
variable [AddCommGroup Ambient] [Module ℂ Ambient]

/-- Filtration data together with the exact metric comparison required for positivity transfer.
Strict filtration compatibility is intentionally not a field: it is a separate hypothesis on the
theorems that identify the mapped source piece with an ambient filtration intersection. -/
structure MetricComparison (Affine Ambient : Type*)
    [AddCommGroup Affine] [Module ℂ Affine]
    [AddCommGroup Ambient] [Module ℂ Ambient] where
  /-- The abstract inverse-DS filtration comparison. -/
  filtration : FiltrationComparison Affine Ambient
  /-- The sesquilinear form on the affine source. -/
  sourceForm : SesqForm Affine
  /-- The sesquilinear form on the ambient realization space. -/
  ambientForm : SesqForm Ambient
  /-- Exact isometry: the source form is the pullback of the ambient form. -/
  form_eq_pullback : sourceForm = ambientForm.pullback filtration.iota

namespace MetricComparison

/-- Strict filtration compatibility remains a separate mathematical requirement. -/
def IsStrict (M : MetricComparison Affine Ambient) : Prop :=
  M.filtration.IsStrict

/-- Under strict filtration compatibility, the mapped affine piece is precisely the intersection
of the affine range with the corresponding ambient piece. -/
theorem map_affinePiece_eq_range_inf (M : MetricComparison Affine Ambient)
    (hstrict : M.IsStrict) (p : ℕ) :
    (M.filtration.affineR.piece p).map M.filtration.iota =
      LinearMap.range M.filtration.iota ⊓ M.filtration.ambientR.piece (p : ℤ) := by
  exact hstrict.1 p

/-- Sign-corrected positivity on the mapped source piece transports back to the source piece.
No filtration strictness is needed for this purely metric statement. -/
theorem signedPositivity_on_affinePiece (M : MetricComparison Affine Ambient) (p : ℕ)
    (hpos : IsPosOn (signedForm M.ambientForm p)
      ((M.filtration.affineR.piece p).map M.filtration.iota)) :
    IsPosOn (signedForm M.sourceForm p) (M.filtration.affineR.piece p) :=
  SesqForm.isPosOn_signedForm_of_eq_pullback M.filtration.iota_injective
    M.form_eq_pullback p hpos

/-- Strictness lets one state the ambient positivity hypothesis intrinsically as positivity on the
intersection of the inverse-DS range with the ambient filtration piece. -/
theorem signedPositivity_on_affinePiece_of_strict
    (M : MetricComparison Affine Ambient) (hstrict : M.IsStrict) (p : ℕ)
    (hpos : IsPosOn (signedForm M.ambientForm p)
      (LinearMap.range M.filtration.iota ⊓ M.filtration.ambientR.piece (p : ℤ))) :
    IsPosOn (signedForm M.sourceForm p) (M.filtration.affineR.piece p) := by
  apply M.signedPositivity_on_affinePiece p
  rwa [M.map_affinePiece_eq_range_inf hstrict p]

end MetricComparison

end InverseDS
end VOA
