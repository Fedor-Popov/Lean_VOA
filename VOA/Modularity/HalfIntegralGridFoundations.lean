/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.ThetaHalfAutFactor
import VOA.Modularity.SuperSpinRelationsSq
import VOA.Modularity.SuperSpinThetaBridge
import VOA.Modularity.SuperSpinS
import VOA.Modularity.SuperSpinDescentSq
import VOA.Modularity.SuperSpinDescentSqFinite
import VOA.Modularity.SuperHalfTwistedTrace
import VOA.Modularity.SuperHalfSpinRecursionBridge
import VOA.Modularity.SuperSectorSystem
import VOA.Modularity.SuperSignGroupFinite

/-!
# Audited foundations for the half-integral modularity grid

This file is the deliberately narrow, dependency-closed public boundary for the proved
half-integral foundations.  Conformal weight and parity are independent throughout: the spin
labels are not parity labels, and no spin--statistics hypothesis is made.  Consequently the
same imported infrastructure applies both to purely even half-integrally graded objects and to
genuine super objects whose parity grading need not agree with conformal weight modulo `ℤ`.

The imports below provide exactly the currently proved foundation layer:

* the theta group `Γ_θ = ⟨S, T²⟩` and a principal half-integral automorphy factor on it;
* the four independent characteristic coefficient families and their half-lattice support;
* the corrected square-bracket grading, covariance, and square-homogeneous formal relations;
* the grading-built conformal sign `kappa`, its finite abelian generated sign subgroup of
  exponent dividing two and cardinality at most four, and the outer `BoundaryPair` label and
  right-action foundations, whose full pair family has cardinality at most sixteen;
* analytic convergence, holomorphy, and the `T²` law for the coefficient functions;
* the characteristic-theta transformation kernel; and
* the proved invariant `(+,+)` `S`-cells, including the precise weight-two `G₂` anomaly.

For a supplied denominator-two twisted module, temporal intertwiner, and half-lattice spectrum,
the imported realization layer also provides actual finite-weight-block half-integral trace and
supertrace coefficient carriers.  It proves their half-lattice support and coefficientwise `T²`
phase law, together with the four `SpinPair` projector decomposition, matching-projector, and
nonmatching-projector identities for one fixed outer `BoundaryPair`.  The PP supertrace component
is promoted to a square-spin formal block only conditionally: the caller must supply the three
fields `x1`, `x2`, and `x3` of `SuperSpinSqRecursionData`.

This aggregator intentionally does **not** import `SuperSpinDescent`.  That development
uses an original-conformal-weight translation premise which is generally false for
`L[-1] = L(-1) + L(0)`.  It imports instead the fixed-outer-pair projector layer and
its corrected square-weight descent companions.  For one fixed outer `BoundaryPair` whose two
automorphisms are involutions, `SpinPair` indexes inner simultaneous state eigencharacters;
under `SuperC2Cofinite`, the associated square-spin cusp quotient is proved
finite-dimensional without a spin--statistics assumption or an extra C2 projection-stability
hypothesis.
The sign-subgroup and boundary-pair bounds retain all degeneracies: no exact cardinality or
spin--statistics identification is asserted.

The denominator-two twisted Jacobi/geometric-telescope derivation of those three recurrence
fields remains open, as do realization of the other outer/inner sectors, convergence of the
actual trace and supertrace carriers, spanning of a genus-one block space, a finite-rank analytic
block theorem, `Γ_θ` modularity, and a half-integral Arakawa--Kawasetsu differential equation.
No one of those downstream conclusions is asserted here.
-/
