/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryCoefficientFiber
import VOA.Commutative.BoundaryCollisionDivisibility

/-!
# The labelled p=3 conductor factor

This file assembles the literal common factor in one fixed four-species particle sector.  The
shifted `S` convention supplies one factor of every `S` variable.  Separate `S`--`S` and
current--`S` diagonal vanishings supply, respectively, the squared `S` Vandermonde and every
mixed collision factor.

The hypotheses are deliberately literal collision-map vanishings.  Orthogonality to `S^2` and
to `A S` is not silently identified with these hypotheses: the corresponding four-species
coefficient-to-polynomial bridges are a separate missing input.  Likewise, orthogonality to
`XZ-Y^2` gives equality of the two typed diagonal polynomials, not vanishing of either one.
-/

namespace VOA.P3RestrictedDualCommonFactor

open MvPolynomial
open VOA.CollisionCommonFactors
open VOA.BoundaryCollisionDivisibility
open VOA.MultispeciesParticlePolynomial
open VOA.ModeParticlePairing

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The labelled current variables in a boundary sector, without the `S` variables. -/
abbrev BoundaryCurrentLabel (a b c : ℕ) := (Fin a ⊕ Fin b) ⊕ Fin c

/-- Include a labelled current variable in the full four-species label type. -/
def boundaryCurrentLabel (a b c d : ℕ) :
    BoundaryCurrentLabel a b c → SpeciesLabel (boundaryMultiplicity a b c d)
  | .inl (.inl i) => ⟨BoundarySpecies.X, i⟩
  | .inl (.inr i) => ⟨BoundarySpecies.Y, i⟩
  | .inr i => ⟨BoundarySpecies.Z, i⟩

/-- Include a labelled `S` variable in the full four-species label type. -/
def boundarySLabel (a b c d : ℕ) :
    Fin d → SpeciesLabel (boundaryMultiplicity a b c d) :=
  fun i => ⟨BoundarySpecies.S, i⟩

private def boundaryCurrentProjection (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → Option (BoundaryCurrentLabel a b c)
  | ⟨BoundarySpecies.X, i⟩ => some (.inl (.inl i))
  | ⟨BoundarySpecies.Y, i⟩ => some (.inl (.inr i))
  | ⟨BoundarySpecies.Z, i⟩ => some (.inr i)
  | ⟨BoundarySpecies.S, _⟩ => none

private def boundarySProjection (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → Option (Fin d)
  | ⟨BoundarySpecies.S, i⟩ => some i
  | _ => none

theorem boundaryCurrentLabel_injective (a b c d : ℕ) :
    Function.Injective (boundaryCurrentLabel a b c d) := by
  intro i j h
  have h' := congrArg (boundaryCurrentProjection a b c d) h
  rcases i with ((i | i) | i) <;> rcases j with ((j | j) | j) <;>
    simp [boundaryCurrentLabel, boundaryCurrentProjection] at h' ⊢ <;> assumption

theorem boundarySLabel_injective (a b c d : ℕ) :
    Function.Injective (boundarySLabel a b c d) := by
  intro i j h
  have h' := congrArg (boundarySProjection a b c d) h
  simpa [boundarySLabel, boundarySProjection] using h'

theorem boundarySLabel_ne_boundaryCurrentLabel (a b c d : ℕ)
    (s : Fin d) (i : BoundaryCurrentLabel a b c) :
    boundarySLabel a b c d s ≠ boundaryCurrentLabel a b c d i := by
  intro h
  rcases i with ((i | i) | i) <;>
    simp [boundarySLabel, boundaryCurrentLabel] at h

/-- The monomial containing one copy of every labelled `S` variable. -/
def sRootFactor (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  MvPolynomial.monomial
    (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift) 1

/-- The collision factors needed after the initial `S`-root monomial has been removed. -/
abbrev ConductorCollisionIndex (a b c d : ℕ) :=
  IncreasingPair (Fin d) ⊕ (BoundaryCurrentLabel a b c × Fin d)

/-- A same-`S` collision has multiplicity two; a current--`S` collision has multiplicity one. -/
def conductorCollisionMultiplicity {a b c d : ℕ} :
    ConductorCollisionIndex a b c d → ℕ
  | .inl _ => 2
  | .inr _ => 1

/-- The collision factor indexed by either an increasing pair of `S` labels or a current--`S`
pair. -/
def conductorCollisionFactor (a b c d : ℕ) :
    ConductorCollisionIndex a b c d →
      MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K
  | .inl ij =>
      collisionFactor (K := K)
        (boundarySLabel a b c d ij.1.1) (boundarySLabel a b c d ij.1.2)
  | .inr is =>
      collisionFactor (K := K)
        (boundarySLabel a b c d is.2) (boundaryCurrentLabel a b c d is.1)

/-- The product of all `S`--`S` collision squares and all current--`S` collision factors. -/
def conductorCollisionProduct (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  ∏ i : ConductorCollisionIndex a b c d,
    conductorCollisionFactor (K := K) a b c d i ^ conductorCollisionMultiplicity i

/-- The complete labelled p=3 conductor divisor in multidegree `(a,b,c,d)`. -/
def p3CommonFactor (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  sRootFactor (K := K) a b c d * conductorCollisionProduct (K := K) a b c d

/-- Pairwise separated prime powers with varying exponents multiply to a common divisor. -/
private theorem prod_pow_dvd_of_pairwise_prime'
    {A M : Type*} [DecidableEq A] [CommMonoidWithZero M] [IsCancelMulZero M]
    (s : Finset A) (f : A → M) (n : A → ℕ) (p : M)
    (hprime : ∀ a ∈ s, Prime (f a))
    (hseparate : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬f a ∣ f b)
    (heach : ∀ a ∈ s, f a ^ n a ∣ p) :
    (∏ a ∈ s, f a ^ n a) ∣ p := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert a s ha ih =>
      have hadiv : f a ^ n a ∣ p := heach a (Finset.mem_insert_self a s)
      rcases hadiv with ⟨q, hpq⟩
      have htail : ∀ b ∈ s, f b ^ n b ∣ q := by
        intro b hb
        have hbprime : Prime (f b) := hprime b (Finset.mem_insert_of_mem hb)
        have hbnot : ¬f b ∣ f a ^ n a := by
          intro hbaPow
          have hba : f b ∣ f a := hbprime.dvd_of_dvd_pow hbaPow
          have hba_ne : b ≠ a := fun h => ha (h ▸ hb)
          exact hseparate b (Finset.mem_insert_of_mem hb) a
            (Finset.mem_insert_self a s) hba_ne hba
        exact hbprime.pow_dvd_of_dvd_mul_left (n b) hbnot (by
          rw [← hpq]
          exact heach b (Finset.mem_insert_of_mem hb))
      have htailProduct : (∏ b ∈ s, f b ^ n b) ∣ q :=
        ih q (fun b hb => hprime b (Finset.mem_insert_of_mem hb))
          (fun b hb c hc hbc => hseparate b (Finset.mem_insert_of_mem hb)
            c (Finset.mem_insert_of_mem hc) hbc)
          htail
      rw [Finset.prod_insert ha, hpq]
      exact mul_dvd_mul_left (f a ^ n a) htailProduct

/-- The initial shifted `S` monomial is nonzero after any relabeling, even if labels are
identified. -/
private theorem rename_sRootFactor_ne_zero {a b c d : ℕ} {I : Type*}
    (f : SpeciesLabel (boundaryMultiplicity a b c d) → I) :
    MvPolynomial.rename f (sRootFactor (K := K) a b c d) ≠ 0 := by
  rw [sRootFactor, MvPolynomial.rename_monomial]
  simp

/-- Removing the explicit `S`-root monomial preserves any literal collision vanishing. -/
private theorem collisionMap_unshifted_eq_zero
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (i j : SpeciesLabel (boundaryMultiplicity a b c d)) (hji : j ≠ i)
    (hzero : collisionMap (K := K) i j hji
      (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    collisionMap (K := K) i j hji (multispeciesParticlePolynomial F) = 0 := by
  rw [shiftedMultispeciesParticlePolynomial_factor, map_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left
    (rename_sRootFactor_ne_zero
      (K := K) (collisionIndex i j hji))

/-- The unshifted multispecies polynomial is invariant under a transposition within one boundary
species. -/
private theorem multispeciesParticlePolynomial_swap
    {jetOrder a b c d : ℕ}
    (A : BoundarySpecies) (i j : Fin (boundaryMultiplicity a b c d A))
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d)) :
    swapVariables (K := K) (boundarySpeciesLabel a b c d A i)
        (boundarySpeciesLabel a b c d A j)
      (multispeciesParticlePolynomial F) = multispeciesParticlePolynomial F := by
  simp only [boundarySpeciesLabel]
  rw [swapVariables,
    ← speciesLabelEquiv_boundarySpeciesTransposition (boundaryMultiplicity a b c d) A i j]
  exact multispeciesParticlePolynomial_rename
    (boundarySpeciesTransposition (boundaryMultiplicity a b c d) A i j) F

/-- Distinct conductor indices represent genuinely different unordered pairs of labels. -/
private theorem conductorCollisionFactor_not_dvd
    {a b c d : ℕ} {i j : ConductorCollisionIndex a b c d} (hij : i ≠ j) :
    ¬conductorCollisionFactor (K := K) a b c d i ∣
      conductorCollisionFactor (K := K) a b c d j := by
  rcases i with ii | is <;> rcases j with jj | jt
  · simp only [conductorCollisionFactor]
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
      ((boundarySLabel_injective a b c d).ne (ne_of_gt ii.2))
      ((boundarySLabel_injective a b c d).ne (ne_of_lt jj.2))
    · rintro ⟨hleft, hright⟩
      apply hij
      exact congrArg Sum.inl (Subtype.ext
        (Prod.ext (boundarySLabel_injective a b c d hleft).symm
          (boundarySLabel_injective a b c d hright).symm))
    · rintro ⟨hleft, hright⟩
      have hleft' := boundarySLabel_injective a b c d hleft
      have hright' := boundarySLabel_injective a b c d hright
      have hreverse : ii.1.2 < ii.1.1 := by simpa [hleft', hright'] using jj.2
      exact (not_lt_of_ge ii.2.le) hreverse
  · simp only [conductorCollisionFactor]
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
      ((boundarySLabel_injective a b c d).ne (ne_of_gt ii.2))
      (boundarySLabel_ne_boundaryCurrentLabel a b c d jt.2 jt.1)
    · rintro ⟨_, h⟩
      exact boundarySLabel_ne_boundaryCurrentLabel a b c d ii.1.2 jt.1 h.symm
    · rintro ⟨_, h⟩
      exact boundarySLabel_ne_boundaryCurrentLabel a b c d ii.1.1 jt.1 h.symm
  · simp only [conductorCollisionFactor]
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
      (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm
      ((boundarySLabel_injective a b c d).ne (ne_of_lt jj.2))
    · rintro ⟨_, h⟩
      exact boundarySLabel_ne_boundaryCurrentLabel a b c d jj.1.2 is.1 h
    · rintro ⟨h, _⟩
      exact boundarySLabel_ne_boundaryCurrentLabel a b c d jj.1.1 is.1 h
  · simp only [conductorCollisionFactor]
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
      (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm
      (boundarySLabel_ne_boundaryCurrentLabel a b c d jt.2 jt.1)
    · rintro ⟨hcurrent, hs⟩
      apply hij
      exact congrArg Sum.inr
        (Prod.ext (boundaryCurrentLabel_injective a b c d hs).symm
          (boundarySLabel_injective a b c d hcurrent).symm)
    · rintro ⟨h, _⟩
      exact boundarySLabel_ne_boundaryCurrentLabel a b c d jt.2 is.1 h

/-- The collision part of the p=3 common factor divides the unshifted particle polynomial as
soon as the separate `S^2` and `A S` literal diagonals vanish. -/
theorem conductorCollisionProduct_dvd_unshifted [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hSS : ∀ i j : Fin d, ∀ hji : boundarySLabel a b c d j ≠ boundarySLabel a b c d i,
      collisionMap (K := K) (boundarySLabel a b c d i) (boundarySLabel a b c d j) hji
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0)
    (hCS : ∀ i : BoundaryCurrentLabel a b c, ∀ s : Fin d,
      ∀ his : boundaryCurrentLabel a b c d i ≠ boundarySLabel a b c d s,
      collisionMap (K := K) (boundarySLabel a b c d s) (boundaryCurrentLabel a b c d i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    conductorCollisionProduct (K := K) a b c d ∣ multispeciesParticlePolynomial F := by
  classical
  apply prod_pow_dvd_of_pairwise_prime' Finset.univ
    (conductorCollisionFactor (K := K) a b c d) conductorCollisionMultiplicity
    (multispeciesParticlePolynomial F)
  · intro i _
    rcases i with ij | is
    · exact collisionFactor_prime _ _
        ((boundarySLabel_injective a b c d).ne (ne_of_gt ij.2))
    · exact collisionFactor_prime _ _
        (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm
  · intro i _ j _ hij
    exact conductorCollisionFactor_not_dvd (K := K) hij
  · intro i _
    rcases i with ij | is
    · exact collisionFactor_sq_dvd_of_swap_invariant
        (boundarySLabel a b c d ij.1.1) (boundarySLabel a b c d ij.1.2)
        ((boundarySLabel_injective a b c d).ne (ne_of_gt ij.2))
        (multispeciesParticlePolynomial F)
        (by simpa [boundarySLabel, boundarySpeciesLabel] using
          multispeciesParticlePolynomial_swap .S ij.1.1 ij.1.2 F)
        (collisionMap_unshifted_eq_zero F _ _ _
          (hSS ij.1.1 ij.1.2
            ((boundarySLabel_injective a b c d).ne (ne_of_gt ij.2))))
    · simpa only [conductorCollisionFactor, conductorCollisionMultiplicity, pow_one] using
        (collisionFactor_dvd_iff
          (boundarySLabel a b c d is.2) (boundaryCurrentLabel a b c d is.1)
          (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm
          (multispeciesParticlePolynomial F)).2
          (collisionMap_unshifted_eq_zero F _ _ _
            (hCS is.1 is.2
              (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm))

/-- Exact labelled p=3 common-factor assembly.  No cone factor is inferred: the separate
polarized orthogonality theorem supplies an equalizer condition after this divisor is removed. -/
theorem p3CommonFactor_dvd [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hSS : ∀ i j : Fin d, ∀ hji : boundarySLabel a b c d j ≠ boundarySLabel a b c d i,
      collisionMap (K := K) (boundarySLabel a b c d i) (boundarySLabel a b c d j) hji
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0)
    (hCS : ∀ i : BoundaryCurrentLabel a b c, ∀ s : Fin d,
      ∀ his : boundaryCurrentLabel a b c d i ≠ boundarySLabel a b c d s,
      collisionMap (K := K) (boundarySLabel a b c d s) (boundaryCurrentLabel a b c d i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    p3CommonFactor (K := K) a b c d ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  rcases conductorCollisionProduct_dvd_unshifted F hSS hCS with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [p3CommonFactor, shiftedMultispeciesParticlePolynomial_factor, hq, mul_assoc]
  rfl

/-- Fixed-derivative-degree version of `p3CommonFactor_dvd`. -/
theorem p3CommonFactor_dvd_boundaryFixed [CharZero K]
    {jetOrder derivativeDegree a b c d : ℕ}
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (hSS : ∀ i j : Fin d, ∀ hji : boundarySLabel a b c d j ≠ boundarySLabel a b c d i,
      collisionMap (K := K) (boundarySLabel a b c d i) (boundarySLabel a b c d j) hji
        (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F) = 0)
    (hCS : ∀ i : BoundaryCurrentLabel a b c, ∀ s : Fin d,
      ∀ his : boundaryCurrentLabel a b c d i ≠ boundarySLabel a b c d s,
      collisionMap (K := K) (boundarySLabel a b c d s) (boundaryCurrentLabel a b c d i) his
        (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F) = 0) :
    p3CommonFactor (K := K) a b c d ∣
      boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F := by
  exact p3CommonFactor_dvd (extendFixedMultispeciesSector F) hSS hCS

end

end VOA.P3RestrictedDualCommonFactor
