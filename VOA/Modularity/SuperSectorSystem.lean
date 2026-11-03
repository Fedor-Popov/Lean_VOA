/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperConformalSign
import VOA.Modularity.SuperSpinCoefficients

/-!
# Outer boundary pairs and inner spin eigensectors

This file separates two finite pieces of genus-one sector bookkeeping which must not be
identified:

* an **outer** `BoundaryPair W` is a commuting pair `(g,h)` of actual super-VOA
  automorphisms, transformed by the right `SL(2,Z)` action
  `(g,h) . A = (g^a h^c, g^b h^d)`;
* for one fixed outer pair, an **inner** `SpinPair` labels the simultaneous `±1`
  eigenconditions for `g` and `h`.

The inner eigenspaces are parameterized by the outer pair.  No global identification of all
outer pairs with the four values of `SpinPair` is made.  Likewise the canonical sign group is
the generated subgroup `superSignSubgroup`, not a four-element type; all degeneracies remain
visible.

## Trace convention

This is a label-and-eigenspace layer and intentionally defines no trace.  The audited trace
entry point is `SuperTwistedModule.twistedSuperOnePoint` in `SuperTwistedTrace.lean`: its
temporal argument is the literal module lift `Phi(h)`, while `supertrace` itself already
contains the parity sign.  A caller must therefore not replace the temporal insertion by
`parityAut * h` merely because an inner spin label is negative.  The inverse insertion used by
`TwistedSuperSymmetricFunctionals.lean` is separately exposed there for the opposite cyclic
orientation.

All weights mentioned by the canonical sign remain original `L(0)` weights.  No claim here
uses the square-bracket `L[0]` grading.
-/

namespace VOA

open scoped MatrixGroups

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}

/-! ## Commuting outer pairs -/

/-- A commuting pair of actual super-VOA automorphisms. -/
structure BoundaryPair (W : SuperVertexOperatorAlgebra VType) where
  /-- Spatial twist. -/
  spatial : SuperAut W
  /-- Temporal insertion. -/
  temporal : SuperAut W
  /-- Flat-torus consistency. -/
  commute : Commute spatial temporal

namespace BoundaryPair

@[ext] theorem ext {b c : BoundaryPair W}
    (hspatial : b.spatial = c.spatial) (htemporal : b.temporal = c.temporal) : b = c := by
  cases b
  cases c
  simp_all

/-- The word `g^a h^c` attached to a commuting boundary pair. -/
def word (b : BoundaryPair W) (a c : ℤ) : SuperAut W :=
  b.spatial ^ a * b.temporal ^ c

/-- Two words in a commuting boundary pair commute. -/
theorem word_commute (b : BoundaryPair W) (a c a' c' : ℤ) :
    Commute (b.word a c) (b.word a' c') := by
  have h₁ : Commute (b.spatial ^ a) (b.spatial ^ a' * b.temporal ^ c') :=
    (Commute.zpow_zpow_self b.spatial a a').mul_right
      (b.commute.zpow_zpow a c')
  have h₂ : Commute (b.temporal ^ c) (b.spatial ^ a' * b.temporal ^ c') :=
    (b.commute.symm.zpow_zpow c a').mul_right
      (Commute.zpow_zpow_self b.temporal c c')
  exact h₁.mul_left h₂

/-- Multiplication adds the exponent vectors of two boundary words. -/
theorem word_mul_word (b : BoundaryPair W) (a c a' c' : ℤ) :
    b.word a c * b.word a' c' = b.word (a + a') (c + c') := by
  rw [word, word, word,
    (b.commute.symm.zpow_zpow c a').mul_mul_mul_comm,
    ← zpow_add, ← zpow_add]

/-- Taking an integral power scales the exponent vector. -/
theorem word_zpow (b : BoundaryPair W) (a c m : ℤ) :
    (b.word a c) ^ m = b.word (a * m) (c * m) := by
  rw [word, word, (b.commute.zpow_zpow a c).mul_zpow,
    ← zpow_mul, ← zpow_mul]

/-- An integral matrix entry of an element of `SL(2,Z)`. -/
private def entry (A : SL(2, ℤ)) (i j : Fin 2) : ℤ :=
  A.1 i j

@[simp] private theorem entry_one_00 : entry (1 : SL(2, ℤ)) 0 0 = 1 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1
  simp

@[simp] private theorem entry_one_01 : entry (1 : SL(2, ℤ)) 0 1 = 0 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0
  simp

@[simp] private theorem entry_one_10 : entry (1 : SL(2, ℤ)) 1 0 = 0 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
  simp

@[simp] private theorem entry_one_11 : entry (1 : SL(2, ℤ)) 1 1 = 1 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1
  simp

@[simp] private theorem entry_mul_00 (A B : SL(2, ℤ)) :
    entry (A * B) 0 0 = entry A 0 0 * entry B 0 0 + entry A 0 1 * entry B 1 0 := by
  exact (Matrix.two_mul_expl (A : Matrix (Fin 2) (Fin 2) ℤ)
    (B : Matrix (Fin 2) (Fin 2) ℤ)).1

@[simp] private theorem entry_mul_01 (A B : SL(2, ℤ)) :
    entry (A * B) 0 1 = entry A 0 0 * entry B 0 1 + entry A 0 1 * entry B 1 1 := by
  exact (Matrix.two_mul_expl (A : Matrix (Fin 2) (Fin 2) ℤ)
    (B : Matrix (Fin 2) (Fin 2) ℤ)).2.1

@[simp] private theorem entry_mul_10 (A B : SL(2, ℤ)) :
    entry (A * B) 1 0 = entry A 1 0 * entry B 0 0 + entry A 1 1 * entry B 1 0 := by
  exact (Matrix.two_mul_expl (A : Matrix (Fin 2) (Fin 2) ℤ)
    (B : Matrix (Fin 2) (Fin 2) ℤ)).2.2.1

@[simp] private theorem entry_mul_11 (A B : SL(2, ℤ)) :
    entry (A * B) 1 1 = entry A 1 0 * entry B 0 1 + entry A 1 1 * entry B 1 1 := by
  exact (Matrix.two_mul_expl (A : Matrix (Fin 2) (Fin 2) ℤ)
    (B : Matrix (Fin 2) (Fin 2) ℤ)).2.2.2

/-- The right modular action on commuting boundary pairs. -/
def act (A : SL(2, ℤ)) (b : BoundaryPair W) : BoundaryPair W where
  spatial := b.word (entry A 0 0) (entry A 1 0)
  temporal := b.word (entry A 0 1) (entry A 1 1)
  commute := b.word_commute _ _ _ _

@[simp] theorem act_one (b : BoundaryPair W) : act 1 b = b := by
  apply BoundaryPair.ext <;> simp [act, word]

/-- The formula is a genuine right action: `b . (A*B) = (b . A) . B`. -/
theorem act_mul (A B : SL(2, ℤ)) (b : BoundaryPair W) :
    act (A * B) b = act B (act A b) := by
  apply BoundaryPair.ext
  · change b.word (entry (A * B) 0 0) (entry (A * B) 1 0) =
      (b.word (entry A 0 0) (entry A 1 0)) ^ entry B 0 0 *
        (b.word (entry A 0 1) (entry A 1 1)) ^ entry B 1 0
    rw [b.word_zpow, b.word_zpow, b.word_mul_word, entry_mul_00, entry_mul_10]
  · change b.word (entry (A * B) 0 1) (entry (A * B) 1 1) =
      (b.word (entry A 0 0) (entry A 1 0)) ^ entry B 0 1 *
        (b.word (entry A 0 1) (entry A 1 1)) ^ entry B 1 1
    rw [b.word_zpow, b.word_zpow, b.word_mul_word, entry_mul_01, entry_mul_11]

/-! ## Inner spin eigencharacters for a fixed outer pair -/

/-- A state has inner spin label `p` relative to the fixed outer pair `b` when it has the
advertised simultaneous `±1` eigenvalues. -/
def IsSpinEigenvector (b : BoundaryPair W) (p : SpinPair) (x : VType) : Prop :=
  b.spatial x = SpinPhase.value p.mu • x ∧
    b.temporal x = SpinPhase.value p.lambda • x

/-- The simultaneous inner spin eigenspace for one fixed outer boundary pair. -/
noncomputable def spinEigenspace (b : BoundaryPair W) (p : SpinPair) :
    Submodule ℂ VType where
  carrier := {x | b.IsSpinEigenvector p x}
  zero_mem' := by simp [IsSpinEigenvector]
  add_mem' := by
    intro x y hx hy
    constructor
    · rw [b.spatial.toLinearEquiv.map_add, hx.1, hy.1, smul_add]
    · rw [b.temporal.toLinearEquiv.map_add, hx.2, hy.2, smul_add]
  smul_mem' := by
    intro c x hx
    constructor
    · rw [b.spatial.toLinearEquiv.map_smul, hx.1, smul_smul, smul_smul, mul_comm]
    · rw [b.temporal.toLinearEquiv.map_smul, hx.2, smul_smul, smul_smul, mul_comm]

@[simp] theorem mem_spinEigenspace (b : BoundaryPair W) (p : SpinPair) (x : VType) :
    x ∈ b.spinEigenspace p ↔ b.IsSpinEigenvector p x := Iff.rfl

end BoundaryPair

/-! ## Boundary pairs supported on the generated sign subgroup -/

open GammaThetaStmt

/-- An outer boundary pair whose two automorphisms lie in the subgroup generated by `kappa`
and parity.  Commutation remains explicit rather than being inferred from a cardinality claim. -/
structure SignBoundaryPair (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) extends BoundaryPair W where
  spatial_mem : spatial ∈ W.superSignSubgroup hhalf
  temporal_mem : temporal ∈ W.superSignSubgroup hhalf

namespace SignBoundaryPair

@[ext] theorem ext {W : SuperVertexOperatorAlgebra VType}
    {hhalf : IsHalfIntegerGraded W} {b c : SignBoundaryPair W hhalf}
    (h : b.toBoundaryPair = c.toBoundaryPair) : b = c := by
  cases b
  cases c
  simp_all

/-- The canonical outer pair `(kappa, parity)`. -/
noncomputable def canonical (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) : SignBoundaryPair W hhalf where
  spatial := W.conformalSign hhalf
  temporal := W.parityAut
  commute := W.conformalSign_commute_parityAut hhalf
  spatial_mem := W.conformalSign_mem_superSignSubgroup hhalf
  temporal_mem := W.parityAut_mem_superSignSubgroup hhalf

/-- The modular action preserves support on the generated sign subgroup. -/
def act {W : SuperVertexOperatorAlgebra VType} {hhalf : IsHalfIntegerGraded W}
    (A : SL(2, ℤ)) (b : SignBoundaryPair W hhalf) : SignBoundaryPair W hhalf where
  toBoundaryPair := BoundaryPair.act A b.toBoundaryPair
  spatial_mem := (W.superSignSubgroup hhalf).mul_mem
    ((W.superSignSubgroup hhalf).zpow_mem b.spatial_mem _)
    ((W.superSignSubgroup hhalf).zpow_mem b.temporal_mem _)
  temporal_mem := (W.superSignSubgroup hhalf).mul_mem
    ((W.superSignSubgroup hhalf).zpow_mem b.spatial_mem _)
    ((W.superSignSubgroup hhalf).zpow_mem b.temporal_mem _)

@[simp] theorem act_toBoundaryPair {W : SuperVertexOperatorAlgebra VType}
    {hhalf : IsHalfIntegerGraded W} (A : SL(2, ℤ)) (b : SignBoundaryPair W hhalf) :
    (act A b).toBoundaryPair = BoundaryPair.act A b.toBoundaryPair := rfl

@[simp] theorem act_one {W : SuperVertexOperatorAlgebra VType}
    {hhalf : IsHalfIntegerGraded W} (b : SignBoundaryPair W hhalf) : act 1 b = b := by
  apply SignBoundaryPair.ext
  exact BoundaryPair.act_one b.toBoundaryPair

theorem act_mul {W : SuperVertexOperatorAlgebra VType}
    {hhalf : IsHalfIntegerGraded W} (A B : SL(2, ℤ)) (b : SignBoundaryPair W hhalf) :
    act (A * B) b = act B (act A b) := by
  apply SignBoundaryPair.ext
  exact BoundaryPair.act_mul A B b.toBoundaryPair

end SignBoundaryPair

end VOA
