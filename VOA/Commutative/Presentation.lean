/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Presentations of commutative algebras

This file records the small presentation-theoretic interface used by the classical-freeness
program.  A family of proposed relations for an algebra map is separated from the stronger claim
that those relations generate its full kernel.

The two conditions are deliberately propositions about an existing algebra homomorphism:

* `RelationsVanish I φ` means that every relation in `I` is killed by `φ`;
* `IsExactPresentation I φ` means that `I` is exactly the kernel of `φ`.

The former constructs the descended map from `A ⧸ I`.  Surjectivity together with the latter
upgrades this descended map to an algebra equivalence by the first isomorphism theorem.
-/

namespace VOA.Presentation

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Every proposed relation in `I` vanishes under the algebra map `φ`. -/
def RelationsVanish (I : Ideal A) (φ : A →ₐ[R] B) : Prop :=
  I ≤ RingHom.ker φ

/-- The proposed relation ideal `I` is exactly the kernel of the algebra map `φ`. -/
def IsExactPresentation (I : Ideal A) (φ : A →ₐ[R] B) : Prop :=
  RingHom.ker φ = I

/-- Descend an algebra map through an ideal of relations that it kills. -/
def quotientMap (I : Ideal A) (φ : A →ₐ[R] B) (h : RelationsVanish I φ) :
    A ⧸ I →ₐ[R] B :=
  Ideal.Quotient.liftₐ I φ fun _ ha ↦ h ha

/-- A surjective algebra map with exact relation ideal presents its target as the corresponding
quotient algebra. -/
noncomputable def quotientEquiv (I : Ideal A) (φ : A →ₐ[R] B)
    (hsurj : Function.Surjective φ) (hexact : IsExactPresentation I φ) :
    (A ⧸ I) ≃ₐ[R] B := by
  rw [← hexact]
  exact Ideal.quotientKerAlgEquivOfSurjective hsurj

end VOA.Presentation
