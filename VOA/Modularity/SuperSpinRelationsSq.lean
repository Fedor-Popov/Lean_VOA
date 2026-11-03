/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperHalfSquareCovariance
import VOA.Modularity.SuperSpinRelations

/-!
# Square-weight spin-sector relations for super VOAs

This is the sound carrier replacing the original-conformal-weight spin relations of
`SuperSpinRelations`.
The left state is homogeneous for `superLsq 0`, and every bracket product is the global mode
`superSqModeHalf` assembled from the official half-integral grading.  Consequently `L[-1]`
raises the grading used by descent.

The coefficient normalization, tensor carrier, cusp specialization, and half-lattice Cauchy
action are reused unchanged from `SuperSpinRelations`: in particular the coefficients are
`spinQ`, not the unnormalized `spinP`.  Spin labels remain independent of parity.
-/

namespace VOA

open scoped BigOperators TensorProduct
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]

namespace SuperNearVOA

variable (W : SuperVertexOperatorAlgebra VType)
variable (hhalf : IsHalfIntegerGraded W)
variable (sector : SuperSpinSectors (VType := VType))

/-! ## Formal coefficient-space relations -/

/-- Invariant-sector zero-mode generators with square-homogeneous left state. -/
def superSpinSqX1Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | ∃ (K : Complex) (a b : VType), a ∈ sector SpinPair.pp ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace K ∧
      x = superSpinInclude (superSqModeHalf W hhalf 0 a b)}

/-- Invariant-sector `wp` generators, using the global half-weight square modes. -/
noncomputable def superSpinSqX2Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | ∃ (Kwt : Complex) (R : Nat) (a b : VType),
    a ∈ sector SpinPair.pp ∧ a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt ∧
    (∀ r : Nat, R ≤ r →
      superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b = 0) ∧
    x = superSpinInclude (superSqModeHalf W hhalf (-2) a b) +
      ∑ r ∈ Finset.range R,
        (((2 * (r + 2) - 1 : Nat) : Complex) • spinQ SpinPair.pp (2 * (r + 2) - 1))
          ⊗ₜ[Complex] superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b}

/-- Nontrivial spin-sector state-kill generators. -/
def superSpinSqKillSet : Set (SuperSpinQSpace (VType := VType)) :=
  {x | ∃ (p : SpinPair) (a : VType), p ≠ SpinPair.pp ∧
    a ∈ sector p ∧ x = superSpinInclude a}

/-- Nontrivial-sector `P`-series generators; the leading sign is minus. -/
noncomputable def superSpinSqX3Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | ∃ (p : SpinPair) (Kwt : Complex) (R : Nat) (a b : VType),
    p ≠ SpinPair.pp ∧ a ∈ sector p ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt ∧
    (∀ k : Nat, R ≤ k → superSqModeHalf W hhalf (k : Int) a b = 0) ∧
    x = -superSpinInclude (superSqModeHalf W hhalf (-1) a b) +
      ∑ k ∈ Finset.range R,
        spinQ p k ⊗ₜ[Complex] superSqModeHalf W hhalf (k : Int) a b}

/-- Formal square-weight spin relation submodule. -/
noncomputable def superSpinSqRelSpan :
    Submodule Complex (SuperSpinQSpace (VType := VType)) :=
  Submodule.span Complex
    (superSpinSqX1Set W hhalf sector ∪ superSpinSqX2Set W hhalf sector ∪
      superSpinSqKillSet sector ∪ superSpinSqX3Set W hhalf sector)

/-! ## Literal cusp relations -/

def superSpinSqCuspX1Set : Set VType :=
  {x | ∃ (K : Complex) (a b : VType), a ∈ sector SpinPair.pp ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace K ∧
      x = superSqModeHalf W hhalf 0 a b}

noncomputable def superSpinSqCuspX2Set : Set VType :=
  {x | ∃ (Kwt : Complex) (R : Nat) (a b : VType),
    a ∈ sector SpinPair.pp ∧ a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt ∧
    (∀ r : Nat, R ≤ r →
      superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b = 0) ∧
    x = superSqModeHalf W hhalf (-2) a b +
      ∑ r ∈ Finset.range R,
        (((2 * (r + 2) - 1 : Nat) : Complex) *
          spinQCusp SpinPair.pp (2 * (r + 2) - 1)) •
            superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a b}

def superSpinSqCuspKillSet : Set VType :=
  {x | ∃ (p : SpinPair) (a : VType), p ≠ SpinPair.pp ∧ a ∈ sector p ∧ x = a}

noncomputable def superSpinSqCuspX3Set : Set VType :=
  {x | ∃ (p : SpinPair) (Kwt : Complex) (R : Nat) (a b : VType),
    p ≠ SpinPair.pp ∧ a ∈ sector p ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt ∧
    (∀ k : Nat, R ≤ k → superSqModeHalf W hhalf (k : Int) a b = 0) ∧
    x = -superSqModeHalf W hhalf (-1) a b +
      ∑ k ∈ Finset.range R,
        spinQCusp p k • superSqModeHalf W hhalf (k : Int) a b}

/-- Literal constant-term square-weight spin relation submodule. -/
noncomputable def superSpinSqCuspRelSpan : Submodule Complex VType :=
  Submodule.span Complex
    (superSpinSqCuspX1Set W hhalf sector ∪ superSpinSqCuspX2Set W hhalf sector ∪
      superSpinSqCuspKillSet sector ∪ superSpinSqCuspX3Set W hhalf sector)

/-! ## Formal-block predicate -/

/-- The four residue identities on a half-lattice-supported coefficient-valued functional,
with square-weight homogeneity and global modes. -/
structure IsSuperSpinSqFormalBlock (hbase : Complex)
    (S : VType →ₗ[Complex] FormalQSeries) : Prop where
  support : ∀ v : VType, S v ∈ QHalfSeriesAt hbase
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
  kill : ∀ (p : SpinPair) (a : VType), p ≠ SpinPair.pp →
    a ∈ sector p → S a = 0
  x3 : ∀ (p : SpinPair) (Kwt : Complex) (R : Nat) (a b : VType),
    p ≠ SpinPair.pp → a ∈ sector p →
    a ∈ W.toSuperNearVOA.superSqWeightSpace Kwt →
    (∀ k : Nat, R ≤ k → superSqModeHalf W hhalf (k : Int) a b = 0) →
    -S (superSqModeHalf W hhalf (-1) a b) +
      ∑ k ∈ Finset.range R,
        halfQConv (spinQNatCoeff p k)
          (S (superSqModeHalf W hhalf (k : Int) a b)) = 0

/-! ## Basic generator membership -/

variable {W hhalf sector}

theorem superSpinSqX1_mem {K : Complex} {a b : VType}
    (hsec : a ∈ sector SpinPair.pp)
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace K) :
    superSpinInclude (superSqModeHalf W hhalf 0 a b) ∈
      superSpinSqRelSpan W hhalf sector := by
  apply Submodule.subset_span
  exact Or.inl (Or.inl (Or.inl ⟨K, a, b, hsec, ha, rfl⟩))

theorem superSpinSqCuspKill_mem {p : SpinPair} (hp : p ≠ SpinPair.pp)
    {a : VType} (hsec : a ∈ sector p) :
    a ∈ superSpinSqCuspRelSpan W hhalf sector := by
  apply Submodule.subset_span
  exact Or.inl (Or.inr ⟨p, a, hp, hsec, rfl⟩)

theorem sector_le_superSpinSqCuspRelSpan (p : SpinPair)
    (hp : p ≠ SpinPair.pp) :
    sector p ≤ superSpinSqCuspRelSpan W hhalf sector := by
  intro a ha
  exact superSpinSqCuspKill_mem hp ha

end SuperNearVOA

end VOA
