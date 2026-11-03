/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3CommonFactorInvariant

/-!
# Source invariance of the labelled boundary conductor

The conductor is a product over unordered `S` pairs and current--`S` pairs.  This file supplies
the finite reindexing needed for arbitrary source relabelings.  Reversing an `S` pair changes a
collision factor by a sign, which disappears after the prescribed square.
-/

namespace VOA.P3CommonFactorSourceInvariant

open VOA.P3BoundaryRootEquiv
open VOA.P3CommonFactorInvariant
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
      simp [increasingPairMap, h, hji]
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
      simp [increasingPairMap, h, hji]

private def p3BoundaryCurrentPermutation (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    BoundaryCurrentLabel a b c ≃ BoundaryCurrentLabel a b c :=
  Equiv.sumCongr
    (Equiv.sumCongr (p3BoundarySpeciesPermutation a b c d g .X)
      (p3BoundarySpeciesPermutation a b c d g .Y))
    (p3BoundarySpeciesPermutation a b c d g .Z)

private theorem p3BoundaryCurrentPermutation_label (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)))
    (i : BoundaryCurrentLabel a b c) :
    boundaryCurrentLabel a b c d (p3BoundaryCurrentPermutation a b c d g i) =
      speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
        (boundaryCurrentLabel a b c d i) := by
  rcases i with ((i | i) | i)
  · change boundaryCurrentLabel a b c d
        (p3BoundaryCurrentPermutation a b c d g (.inl (.inl i))) =
      speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
        (boundaryCurrentLabel a b c d (.inl (.inl i)))
    rfl
  · change boundaryCurrentLabel a b c d
        (p3BoundaryCurrentPermutation a b c d g (.inl (.inr i))) =
      speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
        (boundaryCurrentLabel a b c d (.inl (.inr i)))
    rfl
  · change boundaryCurrentLabel a b c d
        (p3BoundaryCurrentPermutation a b c d g (.inr i)) =
      speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
        (boundaryCurrentLabel a b c d (.inr i))
    rfl

private def p3ConductorIndexEquiv (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    ConductorCollisionIndex a b c d ≃ ConductorCollisionIndex a b c d :=
  Equiv.sumCongr
    (increasingPairEquiv (p3BoundarySpeciesPermutation a b c d g .S))
    (Equiv.prodCongr (p3BoundaryCurrentPermutation a b c d g)
      (p3BoundarySpeciesPermutation a b c d g .S))

private theorem p3ConductorFactor_rename (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)))
    (i : ConductorCollisionIndex a b c d) :
    MvPolynomial.rename
        (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g))
        (conductorCollisionFactor (K := K) a b c d i) ^
          conductorCollisionMultiplicity i =
      conductorCollisionFactor (K := K) a b c d
        (p3ConductorIndexEquiv a b c d g i) ^
          conductorCollisionMultiplicity (p3ConductorIndexEquiv a b c d g i) := by
  rcases i with ij | is
  · simp only [conductorCollisionFactor, conductorCollisionMultiplicity]
    simp only [collisionFactor]
    rw [map_sub,
      MvPolynomial.rename_X, MvPolynomial.rename_X]
    have hs₁ :
        speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
            (boundarySLabel a b c d ij.1.1) =
          (⟨BoundarySpecies.S,
            p3BoundarySpeciesPermutation a b c d g .S ij.1.1⟩ :
              SpeciesLabel (boundaryMultiplicity a b c d)) := rfl
    have hs₂ :
        speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
            (boundarySLabel a b c d ij.1.2) =
          (⟨BoundarySpecies.S,
            p3BoundarySpeciesPermutation a b c d g .S ij.1.2⟩ :
              SpeciesLabel (boundaryMultiplicity a b c d)) := rfl
    rw [hs₁, hs₂]
    by_cases h : p3BoundarySpeciesPermutation a b c d g .S ij.1.1 <
        p3BoundarySpeciesPermutation a b c d g .S ij.1.2
    · have hmap :
          increasingPairEquiv (p3BoundarySpeciesPermutation a b c d g .S) ij =
            ⟨⟨p3BoundarySpeciesPermutation a b c d g .S ij.1.1,
                p3BoundarySpeciesPermutation a b c d g .S ij.1.2⟩, h⟩ := by
          simp [increasingPairEquiv, increasingPairMap, h]
      rw [show p3ConductorIndexEquiv a b c d g (Sum.inl ij) =
          Sum.inl (increasingPairEquiv
            (p3BoundarySpeciesPermutation a b c d g .S) ij) by rfl, hmap]
      rfl
    · have hrev : p3BoundarySpeciesPermutation a b c d g .S ij.1.2 <
          p3BoundarySpeciesPermutation a b c d g .S ij.1.1 :=
        lt_of_le_of_ne (le_of_not_gt h) (by
          intro heq
          exact (ne_of_gt ij.2) ((p3BoundarySpeciesPermutation a b c d g .S).injective heq))
      have hmap :
          increasingPairEquiv (p3BoundarySpeciesPermutation a b c d g .S) ij =
            ⟨⟨p3BoundarySpeciesPermutation a b c d g .S ij.1.2,
                p3BoundarySpeciesPermutation a b c d g .S ij.1.1⟩, hrev⟩ := by
          simp [increasingPairEquiv, increasingPairMap, h, hrev]
      rw [show p3ConductorIndexEquiv a b c d g (Sum.inl ij) =
          Sum.inl (increasingPairEquiv
            (p3BoundarySpeciesPermutation a b c d g .S) ij) by rfl, hmap]
      simp [boundarySLabel]
      ring
  · simp only [conductorCollisionFactor, conductorCollisionMultiplicity]
    simp only [collisionFactor]
    rw [map_sub,
      MvPolynomial.rename_X, MvPolynomial.rename_X]
    have hs :
        speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
            (boundarySLabel a b c d is.2) =
          (⟨BoundarySpecies.S,
            p3BoundarySpeciesPermutation a b c d g .S is.2⟩ :
              SpeciesLabel (boundaryMultiplicity a b c d)) := rfl
    have hc :
        speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g)
            (boundaryCurrentLabel a b c d is.1) =
          boundaryCurrentLabel a b c d
            (p3BoundaryCurrentPermutation a b c d g is.1) :=
      (p3BoundaryCurrentPermutation_label a b c d g is.1).symm
    rw [hs, hc]
    rw [show p3ConductorIndexEquiv a b c d g (Sum.inr is) =
        Sum.inr ((p3BoundaryCurrentPermutation a b c d g is.1,
          p3BoundarySpeciesPermutation a b c d g .S is.2)) by rfl]
    simp [p3BoundaryCurrentPermutation]
    exact (p3BoundarySpeciesPermutation_label a b c d g .S is.2).symm

theorem p3ConductorCollisionProduct_rename_invariant (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    MvPolynomial.rename
        (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g))
        (conductorCollisionProduct (K := K) a b c d) =
      conductorCollisionProduct (K := K) a b c d := by
  rw [conductorCollisionProduct, map_prod]
  simp only [map_pow]
  exact Fintype.prod_equiv (p3ConductorIndexEquiv a b c d g)
    (fun i => MvPolynomial.rename
      (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g))
      (conductorCollisionFactor (K := K) a b c d i) ^
        conductorCollisionMultiplicity i)
    (fun i => conductorCollisionFactor (K := K) a b c d i ^
      conductorCollisionMultiplicity i)
    (fun i => p3ConductorFactor_rename a b c d g i)

theorem p3CommonFactor_rename_invariant (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    MvPolynomial.rename
        (speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g))
        (p3CommonFactor (K := K) a b c d) =
      p3CommonFactor (K := K) a b c d := by
  rw [p3CommonFactor, map_mul]
  rw [p3SRootFactor_rename_invariant,
    p3ConductorCollisionProduct_rename_invariant]

theorem p3CommonFactor_rename_source_invariant (a b c d : ℕ)
    (g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c))) :
    MvPolynomial.rename
        (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
        (MvPolynomial.rename
          (p3BoundaryRootEquiv a b c d)
          (p3CommonFactor (K := K) a b c d)) =
      MvPolynomial.rename
        (p3BoundaryRootEquiv a b c d)
        (p3CommonFactor (K := K) a b c d) := by
  rw [MvPolynomial.rename_rename]
  rw [show g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)) ∘
      p3BoundaryRootEquiv a b c d =
        p3BoundaryRootEquiv a b c d ∘
          speciesLabelEquiv (p3BoundarySpeciesPermutation a b c d g) by
      funext i
      exact (p3BoundarySpeciesPermutation_naturality a b c d g i).symm]
  rw [← MvPolynomial.rename_rename]
  rw [p3CommonFactor_rename_invariant]

private theorem p3CollisionFactor_ne_zero
    (i j : SpeciesLabel (boundaryMultiplicity a b c d)) (hji : j ≠ i) :
    collisionFactor (K := K) i j ≠ 0 := by
  intro hzero
  have himage := congrArg (isolateVariable (K := K) i) hzero
  rw [map_zero, collisionFactor, map_sub, isolateVariable_X_self,
    isolateVariable_X_other i j hji] at himage
  exact Polynomial.X_sub_C_ne_zero _ himage

private theorem p3ConductorCollisionFactor_ne_zero (a b c d : ℕ)
    (i : ConductorCollisionIndex a b c d) :
    conductorCollisionFactor (K := K) a b c d i ≠ 0 := by
  rcases i with ij | is
  · apply p3CollisionFactor_ne_zero
    intro h
    exact ne_of_gt ij.2 (Fin.ext (by
      simpa [boundarySLabel] using
        congrArg (fun q : SpeciesLabel (boundaryMultiplicity a b c d) => (q.2 : ℕ)) h))
  · apply p3CollisionFactor_ne_zero
    intro h
    rcases is with ⟨(i | i) | i, j⟩ <;>
      simp [boundaryCurrentLabel, boundarySLabel] at h

private theorem p3CommonFactor_ne_zero (a b c d : ℕ) :
    p3CommonFactor (K := K) a b c d ≠ 0 := by
  rw [p3CommonFactor]
  apply mul_ne_zero
  · rw [sRootFactor]
    simp
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (p3ConductorCollisionFactor_ne_zero a b c d i)

theorem p3CommonFactor_rename_ne_zero (a b c d : ℕ) :
    MvPolynomial.rename
        (p3BoundaryRootEquiv a b c d)
        (p3CommonFactor (K := K) a b c d) ≠ 0 := by
  intro hzero
  have hzero' : p3CommonFactor (K := K) a b c d = 0 :=
    (MvPolynomial.rename_injective (p3BoundaryRootEquiv a b c d)
      (p3BoundaryRootEquiv a b c d).injective) (by
        simpa using hzero)
  exact (p3CommonFactor_ne_zero (K := K) a b c d) hzero'

theorem p3BoundaryResidualQuotient_source_invariant_of_full
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (w : P3BoundaryFactorizationWitness (K := K)
      jetOrder derivativeDegree a b c d F)
    (hpInv : ∀ g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)),
      MvPolynomial.rename (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
          (P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
            jetOrder derivativeDegree a b c d F) =
        P3InvariantPolynomialRealization.p3BoundaryParticlePolynomial (K := K)
          jetOrder derivativeDegree a b c d F) :
    ∀ g : SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)),
      MvPolynomial.rename (g.sumEquiv (currentSpecies (p3CurrentMultiplicity a b c)))
          (p3BoundaryResidualQuotient (K := K)
            jetOrder derivativeDegree a b c d F w) =
        p3BoundaryResidualQuotient (K := K)
          jetOrder derivativeDegree a b c d F w := by
  apply p3BoundaryResidualQuotient_source_invariant
    (K := K) jetOrder derivativeDegree a b c d F w
    (p3CommonFactor_rename_ne_zero (K := K) a b c d)
    (fun g => p3CommonFactor_rename_source_invariant (K := K) a b c d g)
    hpInv

end

end VOA.P3CommonFactorSourceInvariant
