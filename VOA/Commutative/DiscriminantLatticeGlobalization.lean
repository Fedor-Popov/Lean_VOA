/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FreeLatticeGlobalization

/-!
# Globalization from the generic locus and the discriminant divisors

For the Deligne current carrier, equality with the free cyclic module is
automatic after inverting the discriminant.  At a height-one prime which does
not contain the discriminant, a suitable discriminant power is therefore the
denominator witness required by `FreeLatticeGlobalization`.  The only local
comparisons that remain are the height-one primes containing the discriminant.

This file formalizes that reduction.  It does not assume that the discriminant
is irreducible, nor does it hide the double-root comparison: that comparison is
exactly the `hdivisor` hypothesis below.
-/

namespace VOA.DiscriminantLatticeGlobalization

open Module
open VOA.HeightOneGlobalization
open VOA.FreeLatticeGlobalization

noncomputable section

variable {R F V ι : Type*}
variable [CommRing R] [IsDomain R]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable [Finite ι]

variable {J : Type*}

omit [IsDomain R] [Algebra R F] [IsFractionRing R F] [IsScalarTower R F V] [Finite ι] in
/-- Generic equality after inverting one discriminant, together with the local
comparison along its height-one support, gives every denominator witness needed
for globalization. -/
theorem local_witnesses_of_generic_and_discriminant
    (b : Basis ι F V) (W : Submodule R V) (Δ : R)
    (hgeneric : ∀ x ∈ W, ∃ n : ℕ, (Δ ^ n) • x ∈ lattice (R := R) b)
    (hdivisor : ∀ x ∈ W, ∀ p : HeightOnePrime R, Δ ∈ p.asIdeal →
      ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    ∀ x ∈ W, ∀ p : HeightOnePrime R,
      ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b := by
  intro x hx p
  by_cases hΔ : Δ ∈ p.asIdeal
  · exact hdivisor x hx p hΔ
  · obtain ⟨n, hn⟩ := hgeneric x hx
    refine ⟨Δ ^ n, ?_, hn⟩
    intro hpow
    exact hΔ (p.isPrime.mem_of_pow_mem n hpow)

/-- Discriminant form of the free-lattice globalization theorem.  Once the
candidate carrier agrees generically with the free cyclic lattice, only the
generic double-root divisor comparison remains. -/
theorem carrier_eq_lattice_of_generic_and_discriminant
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (b : Basis ι F V) (W : Submodule R V) (Δ : R)
    (hMW : lattice (R := R) b ≤ W)
    (hgeneric : ∀ x ∈ W, ∃ n : ℕ, (Δ ^ n) • x ∈ lattice (R := R) b)
    (hdivisor : ∀ x ∈ W, ∀ p : HeightOnePrime R, Δ ∈ p.asIdeal →
      ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    W = lattice (R := R) b := by
  apply carrier_eq_lattice_of_local_witnesses b W hMW
  exact local_witnesses_of_generic_and_discriminant b W Δ hgeneric hdivisor

/-- Factorwise form used by the Deligne discriminant.  Primality ensures
that a height-one prime containing the full product contains one displayed
collision factor, so a local comparison for that factor is enough. -/
theorem carrier_eq_lattice_of_generic_and_factors
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (b : Basis ι F V) (W : Submodule R V)
    (factors : Finset J) (factor : J → R)
    (hMW : lattice (R := R) b ≤ W)
    (hgeneric : ∀ x ∈ W, ∃ n : ℕ,
      ((∏ j ∈ factors, factor j) ^ n) • x ∈ lattice (R := R) b)
    (hfactor : ∀ x ∈ W, ∀ p : HeightOnePrime R, ∀ j ∈ factors,
      factor j ∈ p.asIdeal →
        ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    W = lattice (R := R) b := by
  apply carrier_eq_lattice_of_generic_and_discriminant b W
    (∏ j ∈ factors, factor j) hMW hgeneric
  intro x hx p hproduct
  obtain ⟨j, hj, hjp⟩ := p.isPrime.prod_mem_iff.mp hproduct
  exact hfactor x hx p j hj hjp

end


end VOA.DiscriminantLatticeGlobalization

section AxiomAudit
#print axioms
  VOA.DiscriminantLatticeGlobalization.local_witnesses_of_generic_and_discriminant
#print axioms
  VOA.DiscriminantLatticeGlobalization.carrier_eq_lattice_of_generic_and_discriminant
#print axioms
  VOA.DiscriminantLatticeGlobalization.carrier_eq_lattice_of_generic_and_factors
end AxiomAudit
