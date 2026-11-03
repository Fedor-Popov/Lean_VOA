/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.Division
import VOA.Commutative.RootedGordonConductor

/-!
# Prime-power assembly for the rooted Gordon conductor

The scalar rooted Gordon conductor is a finite product of coordinate primes and collision
primes, with nonuniform exponents.  This file proves that all of those displayed factors are
separated, then packages the elementary UFD-style assembly step: once the individual prime
powers divide a polynomial, their product divides that polynomial.
-/

namespace VOA.RootedGordonConductorDivisibility

open scoped BigOperators

open VOA.CollisionCommonFactors
open VOA.RootedGordonConductor
open VOA.RootedMatching

noncomputable section

universe u

variable {K : Type u} [Field K]

noncomputable local instance coloredSlotsFintype {n : ℕ} (rho : Fin n → ℕ) :
    Fintype (ColoredSlots rho) :=
  Fintype.ofFinite _

noncomputable local instance coloredSlotsLinearOrder {n : ℕ} (rho : Fin n → ℕ) :
    LinearOrder (ColoredSlots rho) :=
  LinearOrder.lift' (Fintype.equivFin (ColoredSlots rho))
    (Fintype.equivFin (ColoredSlots rho)).injective

/-- The two kinds of prime factors in the rooted Gordon conductor. -/
abbrev RootedGordonPrimeIndex {n : ℕ} (rho : Fin n → ℕ) :=
  Sum (ColoredSlots rho) (IncreasingPair (ColoredSlots rho))

/-- The prime factor indexed by a coordinate or an increasing collision pair. -/
def rootedGordonPrimeFactor {n : ℕ} (rho : Fin n → ℕ) :
    RootedGordonPrimeIndex rho → MvPolynomial (ColoredSlots rho) K
  | .inl i => MvPolynomial.X i
  | .inr ij => collisionFactor (K := K) ij.1.1 ij.1.2

/-- The required power of each displayed rooted Gordon prime. -/
def rootedGordonPrimeExponent {n : ℕ} (rho : Fin n → ℕ) :
    RootedGordonPrimeIndex rho → ℕ
  | .inl i => slotColor i
  | .inr ij => 2 * min (slotColor ij.1.1) (slotColor ij.1.2)

/-- The coordinate and collision prime powers multiply to the displayed conductor. -/
theorem prod_rootedGordonPrimeFactor_pow_eq_conductor {n : ℕ} (rho : Fin n → ℕ) :
    (∏ a : RootedGordonPrimeIndex rho,
      rootedGordonPrimeFactor (K := K) rho a ^ rootedGordonPrimeExponent rho a) =
      rootedGordonConductor (K := K) rho := by
  rw [Fintype.prod_sum_type]
  simp only [rootedGordonPrimeFactor, rootedGordonPrimeExponent]
  rw [rootedGordonConductor, rootedGordonRootFactor, rootedGordonPairFactor]

/-- Pairwise separated prime powers with varying exponents multiply inside a common divisor. -/
theorem prod_pow_dvd_of_pairwise_prime_varying
    {A M : Type*} [DecidableEq A] [CommMonoidWithZero M] [IsCancelMulZero M]
    (s : Finset A) (f : A → M) (e : A → ℕ) (p : M)
    (hprime : ∀ a ∈ s, Prime (f a))
    (hseparate : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ f a ∣ f b)
    (heach : ∀ a ∈ s, f a ^ e a ∣ p) :
    (∏ a ∈ s, f a ^ e a) ∣ p := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert a s ha ih =>
      have hadiv : f a ^ e a ∣ p := heach a (Finset.mem_insert_self a s)
      rcases hadiv with ⟨q, hpq⟩
      have htail : ∀ b ∈ s, f b ^ e b ∣ q := by
        intro b hb
        have hbprime : Prime (f b) := hprime b (Finset.mem_insert_of_mem hb)
        have hbnot : ¬ f b ∣ f a ^ e a := by
          intro hbaPow
          have hba : f b ∣ f a := hbprime.dvd_of_dvd_pow hbaPow
          have hba_ne : b ≠ a := fun h => ha (h ▸ hb)
          exact hseparate b (Finset.mem_insert_of_mem hb) a
            (Finset.mem_insert_self a s) hba_ne hba
        exact hbprime.pow_dvd_of_dvd_mul_left (e b) hbnot (by
          rw [← hpq]
          exact heach b (Finset.mem_insert_of_mem hb))
      have htailProduct : (∏ b ∈ s, f b ^ e b) ∣ q :=
        ih q (fun b hb => hprime b (Finset.mem_insert_of_mem hb))
          (fun b hb c hc hbc => hseparate b (Finset.mem_insert_of_mem hb)
            c (Finset.mem_insert_of_mem hc) hbc)
          htail
      rw [Finset.prod_insert ha, hpq]
      exact mul_dvd_mul_left (f a ^ e a) htailProduct

/-- Distinct coordinate variables do not divide one another. -/
theorem coordinatePrimeFactor_not_dvd_of_ne {I : Type*} [DecidableEq I]
    (i j : I) (hij : i ≠ j) :
    ¬ (MvPolynomial.X i : MvPolynomial I K) ∣ MvPolynomial.X j := by
  intro hdvd
  exact hij (MvPolynomial.X_dvd_X.mp hdvd)

/-- A coordinate variable does not divide a collision difference. -/
theorem coordinatePrimeFactor_not_dvd_collisionFactor {I : Type*} [DecidableEq I]
    (i a b : I) (hba : b ≠ a) :
    ¬ (MvPolynomial.X i : MvPolynomial I K) ∣ collisionFactor (K := K) a b := by
  intro hdvd
  by_cases hia : i = a
  · subst i
    let e := MvPolynomial.eval₂Hom (RingHom.id K) (fun k => if k = b then 1 else 0)
    have he := map_dvd e hdvd
    simp [collisionFactor, e, hba.symm] at he
  · by_cases hib : i = b
    · subst i
      let e := MvPolynomial.eval₂Hom (RingHom.id K) (fun k => if k = a then 1 else 0)
      have he := map_dvd e hdvd
      simp [collisionFactor, e, hba] at he
    · let e := MvPolynomial.eval₂Hom (RingHom.id K) (fun k => if k = a then 1 else 0)
      have he := map_dvd e hdvd
      simp [collisionFactor, e, hia, hba] at he

/-- A collision difference does not divide a coordinate variable. -/
theorem collisionFactor_not_dvd_coordinatePrimeFactor {I : Type*} [DecidableEq I]
    (a b i : I) (hba : b ≠ a) :
    ¬ collisionFactor (K := K) a b ∣ (MvPolynomial.X i : MvPolynomial I K) := by
  intro hdvd
  have hzero := (collisionFactor_dvd_iff (K := K) a b hba (MvPolynomial.X i)).1 hdvd
  by_cases hia : i = a
  · subst i
    rw [collisionMap_X_self] at hzero
    exact MvPolynomial.X_ne_zero _ hzero
  · rw [collisionMap_X_other (K := K) a b hba i hia] at hzero
    exact MvPolynomial.X_ne_zero _ hzero

/-- Collision factors of distinct increasing pairs do not divide one another. -/
theorem collisionPrimeFactor_not_dvd_of_ne {I : Type*} [DecidableEq I] [LinearOrder I]
    (ij kl : IncreasingPair I) (hij : ij ≠ kl) :
    ¬ collisionFactor (K := K) ij.1.1 ij.1.2 ∣ collisionFactor (K := K) kl.1.1 kl.1.2 := by
  apply collisionFactor_not_dvd_of_pairs_ne ij.2 kl.2
  intro hpairs
  apply hij
  apply Subtype.ext
  exact hpairs

/-- All coordinate and increasing-collision prime factors of a rooted Gordon conductor are
pairwise separated. -/
theorem rootedGordonPrimeFactor_separate {n : ℕ} (rho : Fin n → ℕ) :
    ∀ a b : RootedGordonPrimeIndex rho, a ≠ b →
      ¬ rootedGordonPrimeFactor (K := K) rho a ∣ rootedGordonPrimeFactor (K := K) rho b := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact coordinatePrimeFactor_not_dvd_of_ne i j (by
            intro hij
            exact hab (congrArg Sum.inl hij))
      | inr kl =>
          exact coordinatePrimeFactor_not_dvd_collisionFactor i kl.1.1 kl.1.2 (ne_of_gt kl.2)
  | inr ij =>
      cases b with
      | inl j =>
          exact collisionFactor_not_dvd_coordinatePrimeFactor ij.1.1 ij.1.2 j (ne_of_gt ij.2)
      | inr kl =>
          exact collisionPrimeFactor_not_dvd_of_ne ij kl (by
            intro hkl
            exact hab (congrArg Sum.inr hkl))

/-- The explicit rooted Gordon conductor divides any polynomial carrying all of its displayed
coordinate and collision prime powers. -/
theorem rootedGordonConductor_dvd_of_each_primePower {n : ℕ} (rho : Fin n → ℕ)
    (p : MvPolynomial (ColoredSlots rho) K)
    (hseparate : ∀ a b : RootedGordonPrimeIndex rho, a ≠ b →
      ¬ rootedGordonPrimeFactor (K := K) rho a ∣ rootedGordonPrimeFactor (K := K) rho b)
    (heach : ∀ a : RootedGordonPrimeIndex rho,
      rootedGordonPrimeFactor (K := K) rho a ^ rootedGordonPrimeExponent rho a ∣ p) :
    rootedGordonConductor (K := K) rho ∣ p := by
  rw [← prod_rootedGordonPrimeFactor_pow_eq_conductor rho]
  apply prod_pow_dvd_of_pairwise_prime_varying Finset.univ
    (rootedGordonPrimeFactor (K := K) rho) (rootedGordonPrimeExponent rho)
  · intro a _
    cases a with
    | inl i => exact MvPolynomial.X_prime
    | inr ij => exact collisionFactor_prime (K := K) ij.1.1 ij.1.2 (ne_of_gt ij.2)
  · intro a _ b _ hab
    exact hseparate a b hab
  · intro a _
    exact heach a

/-- A coordinate/collision form of
`rootedGordonConductor_dvd_of_each_primePower` retaining an explicit separation premise. -/
theorem rootedGordonConductor_dvd_of_root_and_collision_primePowers_of_separate
    {n : ℕ} (rho : Fin n → ℕ)
    (p : MvPolynomial (ColoredSlots rho) K)
    (hseparate : ∀ a b : RootedGordonPrimeIndex rho, a ≠ b →
      ¬ rootedGordonPrimeFactor (K := K) rho a ∣ rootedGordonPrimeFactor (K := K) rho b)
    (hroot : ∀ i : ColoredSlots rho, MvPolynomial.X i ^ slotColor i ∣ p)
    (hcollision : ∀ ij : IncreasingPair (ColoredSlots rho),
      collisionFactor (K := K) ij.1.1 ij.1.2 ^
        (2 * min (slotColor ij.1.1) (slotColor ij.1.2)) ∣ p) :
    rootedGordonConductor (K := K) rho ∣ p := by
  apply rootedGordonConductor_dvd_of_each_primePower rho p hseparate
  intro a
  cases a with
  | inl i => exact hroot i
  | inr ij => exact hcollision ij

/-- The explicit rooted Gordon conductor divides a polynomial whenever each required
root-coordinate and collision prime power divides it. -/
theorem rootedGordonConductor_dvd_of_root_and_collision_primePowers {n : ℕ} (rho : Fin n → ℕ)
    (p : MvPolynomial (ColoredSlots rho) K)
    (hroot : ∀ i : ColoredSlots rho, MvPolynomial.X i ^ slotColor i ∣ p)
    (hcollision : ∀ ij : IncreasingPair (ColoredSlots rho),
      collisionFactor (K := K) ij.1.1 ij.1.2 ^
        (2 * min (slotColor ij.1.1) (slotColor ij.1.2)) ∣ p) :
    rootedGordonConductor (K := K) rho ∣ p := by
  exact rootedGordonConductor_dvd_of_root_and_collision_primePowers_of_separate rho p
    (rootedGordonPrimeFactor_separate (K := K) rho) hroot hcollision

end

end VOA.RootedGordonConductorDivisibility

section AxiomAudit
open VOA.RootedGordonConductorDivisibility

#print axioms rootedGordonConductor_dvd_of_each_primePower
#print axioms rootedGordonPrimeFactor_separate
#print axioms rootedGordonConductor_dvd_of_root_and_collision_primePowers
end AxiomAudit
