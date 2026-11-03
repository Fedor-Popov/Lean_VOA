/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperHalfTwistedTrace
import VOA.Modularity.SuperSpinRelationsSq

/-!
# A narrow bridge from half-integral traces to square-spin formal blocks

`SuperHalfTwistedTrace` supplies genuine finite-weight-block trace and supertrace coefficient
families, while `SuperSpinRelationsSq` specifies the three nontrivial residue recurrences that
remain needed for a square-spin formal block.  The present file keeps those ingredients
separate.  In particular, it does not assume `IsSuperSpinSqFormalBlock` as a black box.

For the `(+,+)` inner component of one fixed outer `BoundaryPair`, half-lattice support follows
from the actual module spectrum and the non-invariant state-kill relation follows from the
four-projector selection theorem.  The only bundled input is therefore the three identities
which require the missing twisted Jacobi/geometric-telescope calculation: the invariant zero-mode
identity and the two `wp`/`P` recurrences.  No spin--statistics relation, sector existence,
convergence, spanning, or modularity assertion is made.
-/

namespace VOA

open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {M : Type v} [AddCommGroup M] [Module Complex M]

namespace SuperNearVOA

variable (W : SuperVertexOperatorAlgebra VType)
variable (hhalf : IsHalfIntegerGraded W)
variable (sector : SuperSpinSectors (VType := VType))

/-- The three genuine recurrence identities still needed after support and sector selection have
been established.  This is deliberately smaller than `IsSuperSpinSqFormalBlock`: it contains no
support and no non-invariant state-kill field. -/
structure SuperSpinSqRecursionData (S : VType →ₗ[Complex] FormalQSeries) : Prop where
  x1 : ∀ (K : Complex) (a b : VType), a ∈ sector SpinPair.pp →
    a ∈ W.toSuperNearVOA.superSqWeightSpace K →
      S (superSqModeHalf W hhalf 0 a b) = 0
  x2 : ∀ (Kwt : Complex) (R : Nat) (a b : VType), a ∈ sector SpinPair.pp →
    a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt →
    (∀ r : Nat, R ≤ r →
      superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b = 0) →
    S (superSqModeHalf W hhalf (-2) a b) +
      ∑ r ∈ Finset.range R,
        ((2 * (r + 2) - 1 : Nat) : Complex) •
          halfQConv (spinQNatCoeff SpinPair.pp (2 * (r + 2) - 1))
            (S (superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b)) = 0
  x3 : ∀ (p : SpinPair) (Kwt : Complex) (R : Nat) (a b : VType),
    p ≠ SpinPair.pp → a ∈ sector p →
    a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt →
    (∀ k : Nat, R ≤ k → superSqModeHalf W hhalf (k : Int) a b = 0) →
    -S (superSqModeHalf W hhalf (-1) a b) +
      ∑ k ∈ Finset.range R,
        halfQConv (spinQNatCoeff p k)
          (S (superSqModeHalf W hhalf (k : Int) a b)) = 0

/-- Add the two independent, already-proved gates to the three recurrence identities. -/
theorem isSuperSpinSqFormalBlock_of_recursionData
    {hbase : Complex} {S : VType →ₗ[Complex] FormalQSeries}
    (hsupport : ∀ v : VType, S v ∈ QHalfSeriesAt hbase)
    (hkill : ∀ (p : SpinPair) (a : VType), p ≠ SpinPair.pp →
      a ∈ sector p → S a = 0)
    (hrec : SuperSpinSqRecursionData W hhalf sector S) :
    IsSuperSpinSqFormalBlock W hhalf sector hbase S :=
  { support := hsupport
    x1 := hrec.x1
    x2 := hrec.x2
    kill := hkill
    x3 := hrec.x3 }

end SuperNearVOA

namespace BoundaryPair

variable (b : BoundaryPair W)
variable (T : SuperTwistedModule W b.spatial 2 M)
variable (phi : SuperTwistedIntertwiner T b.temporal)

/-- The actual `(+,+)` inner component of the temporal-inserted half-integral supertrace. -/
noncomputable def halfSuperPPSpinOnePoint (hhalf : IsHalfIntegerGraded W) :
    VType →ₗ[Complex] FormalQSeries :=
  b.halfSuperInnerSpinComponent T phi hhalf SpinPair.pp

/-- The actual `(+,+)` component has half-lattice support whenever the twisted module does. -/
theorem halfSuperPPSpinOnePoint_mem_QHalfSeriesAt
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (u : VType) :
    b.halfSuperPPSpinOnePoint T phi hhalf u ∈
      SuperNearVOA.QHalfSeriesAt (beta - W.centralCharge / 24) :=
  b.halfSuperInnerSpinComponent_mem_QHalfSeriesAt T phi hhalf beta hspec SpinPair.pp u

/-- The four-projector selection theorem supplies the state-kill relation for the actual
`(+,+)` component.  Only the temporal involution is additional here: the spatial involution is
already the denominator-two twist order of `T`. -/
theorem halfSuperPPSpinOnePoint_eq_zero_of_nonPP
    (hhalf : IsHalfIntegerGraded W) (htemporal : b.temporal ^ 2 = 1)
    {p : SpinPair} {u : VType} (hp : p ≠ SpinPair.pp)
    (hu : u ∈ b.spinEigenspace p) :
    b.halfSuperPPSpinOnePoint T phi hhalf u = 0 := by
  change b.IsSpinEigenvector p u at hu
  exact b.halfSuperInnerSpinComponent_eq_zero_of_isSpinEigenvector T phi hhalf htemporal
    (Ne.symm hp) hu

/-- This is the precise bridge to the existing square-spin relation carrier.  It turns the
actual finite-block supertrace into a formal block once, and only once, the three recurrence
identities represented by `SuperSpinSqRecursionData` have been proved. -/
theorem halfSuperPPSpinOnePoint_isSuperSpinSqFormalBlock
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (htemporal : b.temporal ^ 2 = 1)
    (hrec : SuperNearVOA.SuperSpinSqRecursionData W hhalf b.spinEigenspace
      (b.halfSuperPPSpinOnePoint T phi hhalf)) :
    SuperNearVOA.IsSuperSpinSqFormalBlock W hhalf b.spinEigenspace
      (beta - W.centralCharge / 24) (b.halfSuperPPSpinOnePoint T phi hhalf) :=
  SuperNearVOA.isSuperSpinSqFormalBlock_of_recursionData W hhalf b.spinEigenspace
    (b.halfSuperPPSpinOnePoint_mem_QHalfSeriesAt T phi hhalf beta hspec)
    (fun _ _ hp hu =>
      b.halfSuperPPSpinOnePoint_eq_zero_of_nonPP T phi hhalf htemporal hp hu)
    hrec

end BoundaryPair

end VOA
