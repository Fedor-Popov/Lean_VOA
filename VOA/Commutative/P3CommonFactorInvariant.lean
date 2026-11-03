/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3InvariantPolynomialRealization
import VOA.Commutative.P3RestrictedDualCommonFactor

/-!
# Invariance and explicit quotients for the labelled boundary factor

This file records the algebraic cancellation interface needed after extracting the labelled
boundary conductor.  Quotients are always supplied as factorization witnesses; no noncanonical
choice of quotient is made.  Nothing here identifies a cone carrier or proves freeness.
-/

namespace VOA.P3CommonFactorInvariant

open VOA.P3BoundaryRootEquiv
open VOA.P3FunctionalModel
open VOA.MultispeciesParticlePolynomial
open VOA.P3RestrictedDualCommonFactor
open VOA.BoundaryCollisionDivisibility
open VOA.CollisionCommonFactors
open VOA.ModeParticlePairing
open VOA.RootedMatching

noncomputable section

variable {K : Type*} [Field K]

private def increasingPairMap {I : Type*} [LinearOrder I]
    (e : Equiv.Perm I) (ij : IncreasingPair I) : IncreasingPair I := by
  by_cases h : e ij.1.1 < e ij.1.2
  · exact ⟨⟨e ij.1.1, e ij.1.2⟩, h⟩
  · have hrev : e ij.1.2 < e ij.1.1 :=
      lt_of_le_of_ne (le_of_not_gt h) (by
        intro heq
        exact (ne_of_gt ij.2) (e.injective heq))
    exact ⟨⟨e ij.1.2, e ij.1.1⟩, hrev⟩

private def increasingPairEquiv {I : Type*} [LinearOrder I]
    (e : Equiv.Perm I) : IncreasingPair I ≃ IncreasingPair I where
  toFun := increasingPairMap e
  invFun := increasingPairMap e.symm
  left_inv ij := by
    rcases ij with ⟨⟨i, j⟩, hij⟩
    apply Subtype.ext
    by_cases h : e i < e j
    · simp [increasingPairMap, h, hij]
    · have hrev : e j < e i :=
        lt_of_le_of_ne (le_of_not_gt h) (by
          intro heq
          exact (ne_of_gt hij) (e.injective heq))
      have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
      simp [increasingPairMap, h, hrev, hji]
  right_inv ij := by
    rcases ij with ⟨⟨i, j⟩, hij⟩
    apply Subtype.ext
    by_cases h : e.symm i < e.symm j
    · simp [increasingPairMap, h, hij]
    · have hrev : e.symm j < e.symm i :=
        lt_of_le_of_ne (le_of_not_gt h) (by
          intro heq
          exact (ne_of_gt hij) (e.symm.injective heq))
      have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
      simp [increasingPairMap, h, hrev, hji]

theorem p3SRootFactor_rename_invariant (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    MvPolynomial.rename
        (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g))
        (sRootFactor (K := K) a b c d) =
      sRootFactor (K := K) a b c d := by
  rw [sRootFactor, MvPolynomial.rename_monomial,
    mapDomain_speciesShiftExponent_speciesLabelEquiv]

/-- A general cancellation lemma for an invariant factor. -/
theorem quotient_source_invariant_of_factorization
    {G I : Type*} (action : G → Equiv.Perm I)
    (C p q : MvPolynomial I K)
    (hC0 : C ≠ 0)
    (hCinv : ∀ g, MvPolynomial.rename (action g) C = C)
    (hpInv : ∀ g, MvPolynomial.rename (action g) p = p)
    (hfac : p = C * q) :
    ∀ g, MvPolynomial.rename (action g) q = q := by
  intro g
  apply mul_left_cancel₀ hC0
  calc
    C * MvPolynomial.rename (action g) q =
        MvPolynomial.rename (action g) C * MvPolynomial.rename (action g) q := by
      rw [hCinv g]
    _ = MvPolynomial.rename (action g) (C * q) := by
      rw [map_mul]
    _ = MvPolynomial.rename (action g) p := by rw [hfac]
    _ = p := hpInv g
    _ = C * q := hfac

/-- An explicit factorization witness for a renamed boundary realization. -/
structure P3BoundaryFactorizationWitness
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) where
  quotient : MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K
  factorization :
    boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F =
      p3CommonFactor (K := K) a b c d * quotient

/-- The residual quotient obtained from an explicit boundary factorization witness. -/
def p3BoundaryResidualQuotient
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (w : P3BoundaryFactorizationWitness (K := K)
      jetOrder derivativeDegree a b c d F) :
    MvPolynomial (Root (CurrentLabels (p3CurrentMultiplicity a b c)) (Fin d)) K :=
  MvPolynomial.rename (p3BoundaryRootEquiv a b c d) w.quotient

theorem p3BoundaryParticlePolynomial_factorization
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (w : P3BoundaryFactorizationWitness (K := K)
      jetOrder derivativeDegree a b c d F) :
    VOA.P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
        jetOrder derivativeDegree a b c d F =
      MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
          (p3CommonFactor (K := K) a b c d) *
        p3BoundaryResidualQuotient (K := K)
          jetOrder derivativeDegree a b c d F w := by
  rw [VOA.P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial,
    w.factorization, map_mul]
  rfl

/-- If the renamed full polynomial and renamed common factor are invariant, an explicit
factorization witness yields an invariant residual quotient. -/
theorem p3BoundaryResidualQuotient_source_invariant
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (w : P3BoundaryFactorizationWitness (K := K)
      jetOrder derivativeDegree a b c d F)
    (hC0 : MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
        (p3CommonFactor (K := K) a b c d) ≠ 0)
    (hCinv : ∀ g : SourceRelabeling (S := Fin d)
        (currentSpecies (p3CurrentMultiplicity a b c)),
      MvPolynomial.rename (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
        (MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
          (p3CommonFactor (K := K) a b c d)) =
        MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
          (p3CommonFactor (K := K) a b c d))
    (hpInv : ∀ g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)),
      MvPolynomial.rename (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
          (VOA.P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
            jetOrder derivativeDegree a b c d F) =
        VOA.P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
          jetOrder derivativeDegree a b c d F) :
    ∀ g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)),
      MvPolynomial.rename (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
          (p3BoundaryResidualQuotient (K := K)
            jetOrder derivativeDegree a b c d F w) =
        p3BoundaryResidualQuotient (K := K)
          jetOrder derivativeDegree a b c d F w := by
  apply quotient_source_invariant_of_factorization
    (action := fun g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)) =>
      g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
    (C := MvPolynomial.rename (p3BoundaryRootEquiv a b c d)
      (p3CommonFactor (K := K) a b c d))
    (p := VOA.P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
      jetOrder derivativeDegree a b c d F)
    (q := p3BoundaryResidualQuotient (K := K)
      jetOrder derivativeDegree a b c d F w)
    hC0 hCinv hpInv
  exact p3BoundaryParticlePolynomial_factorization (K := K)
    jetOrder derivativeDegree a b c d F w

end

end VOA.P3CommonFactorInvariant
