/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3BoundaryRootEquiv

/-!
# A labelled invariant polynomial realization for the boundary `p = 3` sector

This file packages the already-defined labelled particle polynomial into the scalar polynomial
interface.  The construction is only finite type plumbing: it does not identify a cone carrier,
prove a common-factor theorem, or assert classical freeness.
-/

namespace VOA.P3InvariantPolynomialRealization

open VOA.P3BoundaryRootEquiv
open VOA.P3FunctionalModel
open VOA.MultispeciesParticlePolynomial
open VOA.ModeParticlePairing
open VOA.BoundaryCollisionDivisibility
open VOA.RootedMatching

noncomputable section

variable {K : Type*} [Field K]

/-- The boundary fixed-sector polynomial, renamed to the canonical current-plus-`S` root labels. -/
def p3BoundaryParticlePolynomial (jetOrder derivativeDegree a b c d : ℕ) :
    MultispeciesParticleSector K jetOrder
        (boundaryMultiplicity a b c d) derivativeDegree →
      MvPolynomial (Root (CurrentLabels (p3CurrentMultiplicity a b c)) (Fin d)) K :=
  fun F => MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
    (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F)

/-- Linear-map packaging of `p3BoundaryParticlePolynomial`. -/
def p3BoundaryParticlePolynomialLinearMap (jetOrder derivativeDegree a b c d : ℕ) :
    MultispeciesParticleSector K jetOrder
        (boundaryMultiplicity a b c d) derivativeDegree →ₗ[K]
      MvPolynomial (Root (CurrentLabels (p3CurrentMultiplicity a b c)) (Fin d)) K :=
  { toFun := p3BoundaryParticlePolynomial (K := K) jetOrder derivativeDegree a b c d
    map_add' := by
      intro F G
      simp only [p3BoundaryParticlePolynomial, boundaryFixedParticlePolynomial,
        shiftedMultispeciesParticlePolynomial, map_sum, map_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : multispeciesModeDegree (multispeciesUnorderedModeBlock r) = derivativeDegree
      · simp [extendFixedMultispeciesSector, h]
      · simp [extendFixedMultispeciesSector, h]
    map_smul' := by
      intro r F
      simp only [p3BoundaryParticlePolynomial, boundaryFixedParticlePolynomial,
        shiftedMultispeciesParticlePolynomial, map_sum, RingHom.id_apply,
        map_smul]
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : multispeciesModeDegree (multispeciesUnorderedModeBlock s) = derivativeDegree
      · simp only [extendFixedMultispeciesSector, dif_pos h]
        rw [MvPolynomial.rename_monomial, MvPolynomial.rename_monomial,
          MvPolynomial.smul_monomial]
        rfl
      · simp [extendFixedMultispeciesSector, h] }

@[simp] theorem p3BoundaryParticlePolynomialLinearMap_apply
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) :
    p3BoundaryParticlePolynomialLinearMap (K := K)
        jetOrder derivativeDegree a b c d F =
      p3BoundaryParticlePolynomial (K := K) jetOrder derivativeDegree a b c d F := rfl

theorem p3BoundaryParticlePolynomial_injective
    (jetOrder derivativeDegree a b c d : ℕ) :
    Function.Injective
      (p3BoundaryParticlePolynomial (K := K) jetOrder derivativeDegree a b c d) := by
  intro F G h
  apply boundaryFixedParticlePolynomial_injective (K := K)
      jetOrder derivativeDegree a b c d
  apply MvPolynomial.rename_injective (p3BoundaryRootEquiv a b c d)
      (p3BoundaryRootEquiv a b c d).injective
  exact h

theorem p3BoundaryParticlePolynomialLinearMap_injective
    (jetOrder derivativeDegree a b c d : ℕ) :
    Function.Injective
      (p3BoundaryParticlePolynomialLinearMap (K := K)
        jetOrder derivativeDegree a b c d) := by
  exact p3BoundaryParticlePolynomial_injective (K := K)
    jetOrder derivativeDegree a b c d

theorem p3BoundaryParticlePolynomial_source_invariant
    (jetOrder derivativeDegree a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)))
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) :
    MvPolynomial.rename
        (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
        (p3BoundaryParticlePolynomial (K := K) jetOrder derivativeDegree a b c d F) =
      p3BoundaryParticlePolynomial (K := K) jetOrder derivativeDegree a b c d F := by
  rw [p3BoundaryParticlePolynomial]
  rw [MvPolynomial.rename_rename]
  rw [show (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)) ∘
      p3BoundaryRootEquiv a b c d) =
      (p3BoundaryRootEquiv a b c d ∘
        speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)) by
        funext i
        exact (p3BoundarySpeciesPermutation_naturality a b c d g i).symm]
  rw [← MvPolynomial.rename_rename]
  exact congrArg (MvPolynomial.rename (p3BoundaryRootEquiv a b c d))
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (p3BoundarySpeciesPermutation a b c d g)
      (extendFixedMultispeciesSector F))

/-- The labelled boundary particle polynomial is an invariant scalar-polynomial realization. -/
def p3InvariantPolynomialRealization (jetOrder derivativeDegree a b c d : ℕ) :
    InvariantScalarPolynomialRealization (R := K)
      (S := Fin d)
      (V := MultispeciesParticleSector K jetOrder
        (boundaryMultiplicity a b c d) derivativeDegree)
      (currentSpecies (p3CurrentMultiplicity a b c)) where
  toPolynomial := p3BoundaryParticlePolynomialLinearMap
    (K := K) jetOrder derivativeDegree a b c d
  source_invariant := by
    intro g F
    exact p3BoundaryParticlePolynomial_source_invariant
      (K := K) jetOrder derivativeDegree a b c d g F

end

end VOA.P3InvariantPolynomialRealization
