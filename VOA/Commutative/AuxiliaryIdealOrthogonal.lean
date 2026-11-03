/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.ModeParticlePairing

/-!
# Finite orthogonal complements for the boundary affine auxiliary relations

This file turns the coefficient adjoint identities in `ModeParticlePairing.lean` into exact
orthogonal-complement statements for the linear spans of the relation coefficients multiplied by
all monomial spectators.

The `S` field uses the shifted series `S(z) = sum_(r >= 1) S_r z^r`.  Its ordered coefficient
blocks therefore have total power `arity + sum r_i`, not merely `sum r_i`.  The shifted power and
mixed-current constructions below record that offset explicitly.  In particular, there is no
unmentioned normalization in the `S^(n+1)` or `A S^n` conditions.

The final three theorems say precisely:

* the span of all coefficients of `S(z)^m`, with arbitrary `S` spectators, is annihilated exactly
  when all `m`-particle `S` diagonals vanish;
* the span of all coefficients of `A(z) S(z)^m`, with arbitrary `A` and `S` spectators, is
  annihilated exactly when all mixed diagonals vanish;
* the span of all coefficients of `X(z)Z(z)-Y(z)^2`, with arbitrary current spectators, is
  annihilated exactly when the polarized `XZ` and `YY` diagonals agree.

These are the finite linear-algebra core of the auxiliary-ideal orthogonal-complement argument:
arbitrary monomial multipliers are exactly the spectator configurations.  This file does not yet
identify the coefficient model with an `MvPolynomial` invariant subspace, package all
multidegrees into one restricted dual, or claim a carrier or classical-freeness theorem.
-/

namespace VOA.AuxiliaryIdealOrthogonal

open VOA.ModeParticlePairing

noncomputable section

universe u

variable {K : Type u} [Field K]

section AbstractSpan

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A linear functional annihilates the linear span of a set of relation vectors. -/
def AnnihilatesSpan (ell : V →ₗ[K] K) (relations : Set V) : Prop :=
  Submodule.span K relations ≤ LinearMap.ker ell

/-- To annihilate a relation span is exactly to annihilate every displayed relation vector. -/
theorem annihilatesSpan_iff (ell : V →ₗ[K] K) (relations : Set V) :
    AnnihilatesSpan ell relations ↔ ∀ r ∈ relations, ell r = 0 := by
  rw [AnnihilatesSpan, Submodule.span_le]
  rfl

end AbstractSpan

section PairingFunctionals

/-- A finite-jet particle coefficient family as a linear functional on mode coefficients. -/
def jetPairingFunctional {jetOrder n : ℕ} (F : JetParticleSpace K jetOrder n) :
    JetModeSpace K jetOrder n →ₗ[K] K where
  toFun u := jetModeParticlePairing u F
  map_add' u v := jetModeParticlePairing_add u v F
  map_smul' c u := by
    simp [jetModeParticlePairing, Finset.mul_sum, mul_assoc]

@[simp]
theorem jetPairingFunctional_apply {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) (u : JetModeSpace K jetOrder n) :
    jetPairingFunctional F u = jetModeParticlePairing u F :=
  rfl

/-- A two-species particle coefficient family as a linear functional on mode coefficients. -/
def twoSpeciesPairingFunctional {jetOrder a c : ℕ}
    (F : TwoSpeciesParticleSpace K jetOrder a c) :
    TwoSpeciesModeSpace K jetOrder a c →ₗ[K] K where
  toFun u := twoSpeciesPairing u F
  map_add' u v := by
    simp [twoSpeciesPairing, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    simp [twoSpeciesPairing, Finset.mul_sum, mul_assoc]

@[simp]
theorem twoSpeciesPairingFunctional_apply {jetOrder a c : ℕ}
    (F : TwoSpeciesParticleSpace K jetOrder a c)
    (u : TwoSpeciesModeSpace K jetOrder a c) :
    twoSpeciesPairingFunctional F u = twoSpeciesPairing u F :=
  rfl

/-- A polarized cone coefficient family as a linear functional on the direct sum of its `XZ` and
`YY` mode sectors. -/
def polarizedConePairingFunctional {jetOrder a b c : ℕ}
    (F : PolarizedConeCoefficients K jetOrder a b c) :
    PolarizedConeCoefficients K jetOrder a b c →ₗ[K] K where
  toFun u := polarizedConePairing u F
  map_add' u v := by
    simp [polarizedConePairing, currentPairing, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' d u := by
    simp [polarizedConePairing, currentPairing, Finset.mul_sum, mul_assoc,
      mul_add]

@[simp]
theorem polarizedConePairingFunctional_apply {jetOrder a b c : ℕ}
    (F u : PolarizedConeCoefficients K jetOrder a b c) :
    polarizedConePairingFunctional F u = polarizedConePairing u F :=
  rfl

end PairingFunctionals

section ShiftedSField

/-- Ordered blocks contributing to the coefficient of `z^q` in the shifted field power
`S(z)^arity`, where every inserted `S` particle contributes an initial power of `z`. -/
def shiftedCoefficientBlocks (jetOrder arity q : ℕ) :
    Finset (Fin arity → Fin (jetOrder + 1)) :=
  Finset.univ.filter (fun r ↦ arity + orderedBlockDegree r = q)

@[simp]
theorem mem_shiftedCoefficientBlocks {jetOrder arity q : ℕ}
    (r : Fin arity → Fin (jetOrder + 1)) :
    r ∈ shiftedCoefficientBlocks jetOrder arity q ↔
      arity + orderedBlockDegree r = q := by
  simp [shiftedCoefficientBlocks]

/-- The coefficient of the shifted field power `S(z)^arity`, multiplied by a fixed `S`
spectator monomial. -/
def shiftedFieldPowerMode {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount) :
    JetModeSpace K jetOrder (arity + spectatorCount) :=
  ∑ r ∈ shiftedCoefficientBlocks jetOrder arity q,
    jetDeltaMode (K := K) ((unorderedModeBlock r).append spectator)

/-- Literal shifted `S`-diagonal coefficient. -/
def shiftedFieldPowerDiagonalCoefficient {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) : K :=
  ∑ r ∈ shiftedCoefficientBlocks jetOrder arity q,
    F ((unorderedModeBlock r).append spectator)

/-- Shifted field-power multiplication is adjoint to literal coincidence of the new `S`
coordinates. -/
theorem shiftedFieldPower_adjoint_diagonal
    {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    jetModeParticlePairing (shiftedFieldPowerMode (K := K) q spectator) F =
      shiftedFieldPowerDiagonalCoefficient q spectator F := by
  rw [shiftedFieldPowerMode, jetModeParticlePairing_sum]
  simp [shiftedFieldPowerDiagonalCoefficient]

/-- Ordered blocks contributing to `A(z) S(z)^sArity`; only the `S` modes carry the unit shift. -/
def shiftedMixedCoefficientBlocks (jetOrder sArity q : ℕ) :
    Finset (Fin (jetOrder + 1) × (Fin sArity → Fin (jetOrder + 1))) :=
  Finset.univ.filter
    (fun r ↦ (r.1 : ℕ) + sArity + orderedBlockDegree r.2 = q)

@[simp]
theorem mem_shiftedMixedCoefficientBlocks {jetOrder sArity q : ℕ}
    (r : Fin (jetOrder + 1) × (Fin sArity → Fin (jetOrder + 1))) :
    r ∈ shiftedMixedCoefficientBlocks jetOrder sArity q ↔
      (r.1 : ℕ) + sArity + orderedBlockDegree r.2 = q := by
  simp [shiftedMixedCoefficientBlocks]

/-- The coefficient of `A(z) S(z)^sArity`, multiplied by fixed spectators. -/
def shiftedMixedFieldProductMode {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d) :
    TwoSpeciesModeSpace K jetOrder (a + 1) (sArity + d) :=
  ∑ r ∈ shiftedMixedCoefficientBlocks jetOrder sArity q,
    twoSpeciesDeltaMode (K := K)
      (r.1 ::ₛ aSpectator, (unorderedModeBlock r.2).append sSpectator)

/-- Literal mixed diagonal coefficient for the shifted relation `A(z) S(z)^sArity`. -/
def shiftedMixedDiagonalCoefficient {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) : K :=
  ∑ r ∈ shiftedMixedCoefficientBlocks jetOrder sArity q,
    F (r.1 ::ₛ aSpectator, (unorderedModeBlock r.2).append sSpectator)

/-- Shifted mixed-product multiplication is adjoint to literal mixed coincidence. -/
theorem shiftedMixedFieldProduct_adjoint_diagonal
    {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) :
    twoSpeciesPairing
        (shiftedMixedFieldProductMode (K := K) q aSpectator sSpectator) F =
      shiftedMixedDiagonalCoefficient q aSpectator sSpectator F := by
  rw [shiftedMixedFieldProductMode, twoSpeciesPairing_sum]
  simp [shiftedMixedDiagonalCoefficient]

end ShiftedSField

section RelationSpans

/-- All finite-jet coefficients of `S(z)^arity` multiplied by all fixed-size `S` spectator
monomials. -/
def shiftedFieldPowerRelationSet (jetOrder arity spectatorCount : ℕ) :
    Set (JetModeSpace K jetOrder (arity + spectatorCount)) :=
  Set.range (fun i : ℕ × ModeConfiguration jetOrder spectatorCount ↦
    shiftedFieldPowerMode (K := K) i.1 i.2)

/-- All finite-jet coefficients of `A(z) S(z)^sArity` multiplied by all fixed-size spectator
monomials of the two species. -/
def shiftedMixedRelationSet (jetOrder sArity a d : ℕ) :
    Set (TwoSpeciesModeSpace K jetOrder (a + 1) (sArity + d)) :=
  Set.range (fun i : ℕ ×
      (ModeConfiguration jetOrder a × ModeConfiguration jetOrder d) ↦
    shiftedMixedFieldProductMode (K := K) i.1 i.2.1 i.2.2)

/-- All finite-jet coefficients of `X(z)Z(z)-Y(z)^2` multiplied by all fixed current spectator
monomials. -/
def polarizedConeRelationSet (jetOrder a b c : ℕ) :
    Set (PolarizedConeCoefficients K jetOrder a b c) :=
  Set.range (fun i : ℕ ×
      (ModeConfiguration jetOrder a ×
        ModeConfiguration jetOrder b × ModeConfiguration jetOrder c) ↦
    polarizedConeRelationMode (K := K) i.1 i.2.1 i.2.2.1 i.2.2.2)

/-- Exact finite orthogonal complement for the shifted `S(z)^arity` relation family. -/
theorem shiftedFieldPower_span_orthogonal_iff_diagonal
    {jetOrder arity spectatorCount : ℕ}
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    AnnihilatesSpan (jetPairingFunctional F)
        (shiftedFieldPowerRelationSet (K := K) jetOrder arity spectatorCount) ↔
      ∀ q spectator, shiftedFieldPowerDiagonalCoefficient q spectator F = 0 := by
  rw [annihilatesSpan_iff]
  simp only [shiftedFieldPowerRelationSet, Set.forall_mem_range,
    jetPairingFunctional_apply, shiftedFieldPower_adjoint_diagonal, Prod.forall]

/-- Exact finite orthogonal complement for the shifted `A(z) S(z)^sArity` relation family. -/
theorem shiftedMixed_span_orthogonal_iff_diagonal
    {jetOrder sArity a d : ℕ}
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) :
    AnnihilatesSpan (twoSpeciesPairingFunctional F)
        (shiftedMixedRelationSet (K := K) jetOrder sArity a d) ↔
      ∀ q aSpectator sSpectator,
        shiftedMixedDiagonalCoefficient q aSpectator sSpectator F = 0 := by
  rw [annihilatesSpan_iff]
  simp only [shiftedMixedRelationSet, Set.forall_mem_range,
    twoSpeciesPairingFunctional_apply, shiftedMixedFieldProduct_adjoint_diagonal,
    Prod.forall]

/-- Exact finite orthogonal complement for the polarized cone relation.  The `YY` factorial is
the ordered square normalization proved in `ModeParticlePairing.lean`. -/
theorem polarizedCone_span_orthogonal_iff_diagonal
    {jetOrder a b c : ℕ}
    (F : PolarizedConeCoefficients K jetOrder a b c) :
    AnnihilatesSpan (polarizedConePairingFunctional F)
        (polarizedConeRelationSet (K := K) jetOrder a b c) ↔
      ∀ q bx byy bz,
        polarizedXZDiagonalCoefficient q bx byy bz F =
          polarizedYYDiagonalCoefficient q bx byy bz F := by
  rw [annihilatesSpan_iff]
  simp only [polarizedConeRelationSet, Set.forall_mem_range,
    polarizedConePairingFunctional_apply, polarizedConeRelation_adjoint_diagonal,
    sub_eq_zero, Prod.forall]

end RelationSpans

end

end VOA.AuxiliaryIdealOrthogonal
